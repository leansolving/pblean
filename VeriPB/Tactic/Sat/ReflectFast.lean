/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import VeriPB.Tactic.Sat.ReflectCheck

/-!
# Fast reflection checker (runtime replacement)

Runtime implementation of the verified reflection checker
(`VeriPB.Reflect.checkProofBool`, see `Reflect.lean`), installed via
`@[implemented_by Fast.checkProofBoolFast]`. Nothing in this file is used
by any proof.

**Extensional equality is the trust requirement.** The `nativeEqTrue` axiom
produced by `veripb_reflect` asserts that the *verified* `checkProofBool`
returns `true`; the code here must therefore accept exactly the proofs the
verified definition accepts. Every operation below mirrors its verified
counterpart in `ReflectCheck.lean` step by step, including term order:
normalization happens at the same points, produces the same term order
(`VeriPB.normalizeArrays` is an exact simulation of `VeriPB.normalizeConstr`),
weakening normalizes and then removes every term of the variable, and RUP
combination picks the first complementary pair in accumulator order.

**Representation.** A constraint is stored as two parallel `Array Nat`
fields: coefficients and literal codes (`2*v` for `x_v`, `2*v+1` for
`¬x_v`). Small `Nat`s are unboxed scalars in the Lean runtime, so this
avoids the per-term heap objects of `List (Nat × Literal)`.
-/

namespace VeriPB.Reflect.Fast

/-- Literal code of a `Sat.PB.Literal` (`2*v` positive, `2*v+1` negative): the
encoding `VeriPB.normalizeArrays` is specified against. -/
abbrev encLit : Sat.PB.Literal → Nat := VeriPB.litCode

/-- Inverse of `encLit`. -/
abbrev decLit : Nat → Sat.PB.Literal := VeriPB.litOfCode

/-- Constraint `Σ coeffs[i] * lit(lits[i]) ≥ degree` in parallel-array form.

`split` records structural knowledge used to pick a cheap exact
normalization path. A *block* is a term range with no zero coefficient, no
repeated literal and no complementary pair; the verified normalizer is the
identity on a block. The encoding is:
* `split = 0`: nothing known (general normalization);
* `0 < split = coeffs.size`: the whole term list is one block;
* `0 < split < coeffs.size`: `[0, split)` and `[split, size)` are both blocks
  (the result of adding two normalized constraints).
Every operation below maintains this invariant; it is never assumed without
having been established by `normalizeFConstr`, `blockOf`, or an operation
that provably preserves it. -/
structure FConstr where
  coeffs : Array Nat
  lits : Array Nat
  degree : Nat
  split : Nat := 0
  deriving Inhabited

/-- Checker state: constraint database plus bookkeeping. -/
structure FBoolCheckState where
  db : Std.HashMap Nat FConstr
  origConstrs : Array Constr
  nextId : Nat
  numVars : Nat
  formulaSize : Nat
  deriving Inhabited

/-- `true` iff the term list is a block: no zero coefficient, no repeated
literal, no complementary pair. -/
def isBlock (coeffs lits : Array Nat) : Bool := Id.run do
  let n := coeffs.size
  if n == 0 then return true
  let mut maxLit := 0
  for i in [:n] do
    if coeffs[i]! == 0 then return false
    if lits[i]! > maxLit then maxLit := lits[i]!
  if maxLit + 2 > n * n + 8 then
    -- sparse literal codes: pairwise scan instead of a bitmap
    for i in [:n] do
      let v := lits[i]! / 2
      for j in [i+1:n] do
        if lits[j]! / 2 == v then return false
    return true
  let mut seen : Array Bool := Array.replicate (maxLit + 2) false
  for i in [:n] do
    let l := lits[i]!
    if seen[l]! || seen[l ^^^ 1]! then return false
    seen := seen.set! l true
  return true

/-- `split` value for a term list: `size` if it is a block, else `0`. -/
def blockOf (coeffs lits : Array Nat) : Nat :=
  if isBlock coeffs lits then coeffs.size else 0

def toFConstr (c : Constr) : FConstr :=
  let ts := c.terms.toArray
  let coeffs := ts.map (·.1)
  let lits := ts.map (encLit ·.2)
  ⟨coeffs, lits, c.degree, blockOf coeffs lits⟩

def fromFConstr (c : FConstr) : Constr := Id.run do
  let mut terms : List Sat.PB.Term := []
  for k in [:c.coeffs.size] do
    let i := c.coeffs.size - 1 - k
    terms := (c.coeffs[i]!, decLit c.lits[i]!) :: terms
  return ⟨terms, c.degree⟩

def FConstr.coeffSum (c : FConstr) : Nat :=
  c.coeffs.foldl (· + ·) 0

def FConstr.isContra (c : FConstr) : Bool :=
  c.coeffSum < c.degree

/-- Negate with a precomputed coefficient sum `cs`. Flipping every literal
keeps blocks blocks. -/
def FConstr.negateWith (c : FConstr) (cs : Nat) : FConstr :=
  ⟨c.coeffs, c.lits.map (· ^^^ 1), cs - c.degree + 1, c.split⟩

def FConstr.negate (c : FConstr) : FConstr :=
  c.negateWith c.coeffSum

/-- Second half of `rupNegateF` (mirrors `VeriPB.Reflect.rupNegate`) on an
already normalized constraint: negate, or the trivial constraint when the
target is contradictory on its own. -/
def rupNegateWith (nf : FConstr) : FConstr :=
  let cs := nf.coeffSum
  if nf.degree ≤ cs then nf.negateWith cs else ⟨#[], #[], 0, 0⟩

/-- Concatenation (mirrors `VeriPB.addConstrs`). Two blocks give a two-block
constraint; anything else loses the structure. -/
def addFConstrs (c1 c2 : FConstr) : FConstr :=
  let n1 := c1.coeffs.size
  let n2 := c2.coeffs.size
  let split :=
    if n1 == 0 then c2.split
    else if n2 == 0 then c1.split
    else if c1.split == n1 && c2.split == n2 then n1
    else 0
  ⟨c1.coeffs ++ c2.coeffs, c1.lits ++ c2.lits, c1.degree + c2.degree, split⟩

/-- Scaling by `k > 0` keeps blocks blocks (no zeros, literals unchanged,
a blocked pair stays blocked); `k = 0` zeroes everything. -/
def mulFConstr (c : FConstr) (k : Nat) : FConstr :=
  ⟨c.coeffs.map (k * ·), c.lits, k * c.degree, if k == 0 then 0 else c.split⟩

/-- Ceiling division by `k > 0` keeps positive coefficients positive. Only
applied to normalized inputs, which have no complementary pair, so blocks
stay blocks. -/
def divFConstr (c : FConstr) (k : Nat) : FConstr :=
  ⟨c.coeffs.map (Sat.PB.ceilDiv · k), c.lits, Sat.PB.ceilDiv c.degree k,
    if k == 0 then 0 else c.split⟩

/-- Saturation keeps blocks blocks unless the degree is `0`, which zeroes
every coefficient. -/
def saturateFConstr (c : FConstr) : FConstr :=
  ⟨c.coeffs.map (min · c.degree), c.lits, c.degree,
    if c.degree == 0 then 0 else c.split⟩

/-- Remove every term of variable `varIdx` and subtract the removed
coefficients from the degree, truncated at 0 (mirrors
`VeriPB.weakenConstr`; the caller normalizes first, as the verified
`execPolOne` does). Removing terms from a block leaves a block, so the
structural flag is adjusted rather than dropped. -/
def weakenFConstr (c : FConstr) (varIdx : Nat) : FConstr := Id.run do
  let n := c.lits.size
  let mut cs : Array Nat := Array.mkEmpty n
  let mut ls : Array Nat := Array.mkEmpty n
  let mut removed := 0
  let mut removedBefore := 0  -- removed terms with index < c.split
  for i in [:n] do
    if c.lits[i]! / 2 == varIdx then
      removed := removed + c.coeffs[i]!
      if i < c.split then removedBefore := removedBefore + 1
    else
      cs := cs.push c.coeffs[i]!
      ls := ls.push c.lits[i]!
  let split := if c.split == 0 then 0 else c.split - removedBefore
  return ⟨cs, ls, c.degree - removed, split⟩

/-- General exact normalization through `VeriPB.normalizeArraysCore`; the
result is flagged as a block when the one-pass path completed. -/
def normalizeGeneralF (c : FConstr) : FConstr :=
  let (cs, ls, d, isBlk) := VeriPB.normalizeArraysCore c.coeffs c.lits c.degree
  ⟨cs, ls, d, if isBlk then cs.size else blockOf cs ls⟩

/-- Exact normalization of a two-block constraint (see `FConstr.split`).

On `c1 ++ c2` with both parts blocks, the verified normalizer
(`VeriPB.normalizeConstr`) proceeds as follows: for each term of `c1` in
order, its only possible complement is the unique term of `c2` with the
opposite literal; if `min ≤ degree` the pair is cancelled and the degree
reduced, otherwise the process is blocked (handled by the general
algorithm). No term of `c2` has a complement after it. Then like terms are
merged into their first occurrence, i.e. each `c2` term whose literal occurs
in `c1` is added to that `c1` term. The result lists the surviving `c1`
terms in order, then the surviving `c2` terms in order. A blocked pair, or
sparse literal codes, fall back to `VeriPB.normalizeArraysCore` on the
unmodified constraint; partial cancellations are discarded. -/
def normalizeTwoBlocks (c : FConstr) : FConstr := Id.run do
  let n := c.coeffs.size
  let split := c.split
  let n2 := n - split
  let mut maxLit := 0
  for i in [:n] do
    if c.lits[i]! > maxLit then maxLit := c.lits[i]!
  if maxLit + 2 > n * n + 8 then
    return normalizeGeneralF c
  let noIdx := n
  -- index of each c2 literal
  let mut idx : Array Nat := Array.replicate (maxLit + 2) noIdx
  for j in [split:n] do
    idx := idx.set! c.lits[j]! j
  -- remaining c2 coefficients after cancellation / merging (0 = consumed)
  let mut rem : Array Nat := Array.mkEmpty n2
  for j in [split:n] do
    rem := rem.push c.coeffs[j]!
  let mut deg := c.degree
  let mut outC : Array Nat := Array.mkEmpty n
  let mut outL : Array Nat := Array.mkEmpty n
  for i in [:split] do
    let l := c.lits[i]!
    let mut a := c.coeffs[i]!
    let j := idx[l ^^^ 1]!
    if j != noIdx then
      let b := rem[j - split]!
      let m := min a b
      if m > deg then
        -- blocked cancellation: replay the full process exactly
        return normalizeGeneralF c
      a := a - m
      rem := rem.set! (j - split) (b - m)
      deg := deg - m
    if a > 0 then
      let j' := idx[l]!
      if j' != noIdx then
        a := a + rem[j' - split]!
        rem := rem.set! (j' - split) 0
      outC := outC.push a
      outL := outL.push l
  for j in [split:n] do
    let b := rem[j - split]!
    if b > 0 then
      outC := outC.push b
      outL := outL.push c.lits[j]!
  return ⟨outC, outL, deg, outC.size⟩

/-- Exact simulation of `VeriPB.normalizeConstr`, dispatching on the known
structure: identity on a block, linear merge for two blocks, otherwise the
general algorithm `VeriPB.normalizeArraysCore`. -/
def normalizeFConstr (c : FConstr) : FConstr :=
  let n := c.coeffs.size
  if c.split == 0 || n == 0 then normalizeGeneralF c
  else if c.split == n then c
  else normalizeTwoBlocks c

/-- Mirrors `VeriPB.Reflect.rupNegate`. -/
def rupNegateF (c : FConstr) : FConstr :=
  rupNegateWith (normalizeFConstr c)

/-! ### Pol RPN -/

inductive FStackElem where
  | constr : FConstr → FStackElem
  | nat : Nat → FStackElem

def execFPolOne (db : Std.HashMap Nat FConstr)
    (stack : List FStackElem) (op : VeriPB.PolOp) :
    Option (List FStackElem) :=
  match op with
  | .pushId id => match db[id]? with
    | some c => some (.constr c :: stack)
    | none => none
  | .pushNat n => some (.nat n :: stack)
  | .pushLitAxiom lit => match VeriPB.opbLitToPB lit with
    | .ok pbLit => some (.constr ⟨#[1], #[encLit pbLit], 0, 1⟩ :: stack)
    | .error _ => none
  | .add => match stack with
    | .constr c2 :: .constr c1 :: rest =>
      some (.constr (addFConstrs c1 c2) :: rest)
    | _ => none
  | .mul => match stack with
    | .nat k :: .constr c :: rest =>
      some (.constr (mulFConstr c k) :: rest)
    | _ => none
  | .div => match stack with
    | .nat k :: .constr c :: rest =>
      if k == 0 then none
      else some (.constr (divFConstr (normalizeFConstr c) k) :: rest)
    | _ => none
  | .saturate => match stack with
    | .constr c :: rest =>
      some (.constr (saturateFConstr (normalizeFConstr c)) :: rest)
    | _ => none
  | .weaken varName => match stack with
    | .constr c :: rest =>
      if varName.startsWith "x" then
        match (varName.drop 1).toString.toNat? with
        | some n => if n > 0 then
            some (.constr (weakenFConstr (normalizeFConstr c) (n - 1)) :: rest)
          else none
        | none => none
      else none
    | _ => none

def execFPolOps (db : Std.HashMap Nat FConstr) :
    List VeriPB.PolOp → List FStackElem → Option (List FStackElem)
  | [], stack => some stack
  | op :: rest, stack =>
    match execFPolOne db stack op with
    | some s => execFPolOps db rest s
    | none => none

def execFPolRPNBool (ops : List VeriPB.PolOp)
    (db : Std.HashMap Nat FConstr) : Option FConstr :=
  match execFPolOps db ops [] with
  | some [.constr c] => some c
  | _ => none

/-! ### RUP verification -/

/-- First complementary pair in accumulator order (mirrors `findCompLitPairBool`). -/
def findFCompLitPairBool (acc hint : FConstr) :
    Option (Nat × Nat) := Id.run do
  for ia in [:acc.lits.size] do
    let comp := acc.lits[ia]! ^^^ 1
    for ih in [:hint.lits.size] do
      if hint.lits[ih]! == comp then return some (acc.coeffs[ia]!, hint.coeffs[ih]!)
  return none

@[inline] def evalLitPartialF (asgn : Array (Option Bool)) (l : Nat) : Option Bool :=
  let v := l / 2
  if h : v < asgn.size then
    if l % 2 == 0 then asgn[v] else asgn[v].map (!·)
  else none

/-- Mirrors `pbPropagateBool`: `forced` lists the unassigned literals with
coefficient above the slack, in reverse term order (as the verified version
builds it). -/
def pbFPropagateBool (asgn : Array (Option Bool)) (c : FConstr) :
    PropResultBool := Id.run do
  let mut totalActive : Nat := 0
  for i in [:c.lits.size] do
    match evalLitPartialF asgn c.lits[i]! with
    | some false => pure ()
    | _ => totalActive := totalActive + c.coeffs[i]!
  if totalActive < c.degree then return .conflict
  let slack := totalActive - c.degree
  let mut forced : List (Sat.PB.Literal × Bool) := []
  for i in [:c.lits.size] do
    let a := c.coeffs[i]!
    if a > slack then
      let l := c.lits[i]!
      if (evalLitPartialF asgn l).isNone then forced := (decLit l, true) :: forced
  if forced.isEmpty then .noPropagation
  else .propagated forced

/-- Mirrors `findConflictHintBool`; additionally returns the resolved hint
constraints so that the caller need not look them up again. -/
def findFConflictHintBool (negConstr : FConstr)
    (hints : List VeriPB.RupHint) (db : Std.HashMap Nat FConstr)
    (numVars : Nat) : Option (Nat × Array FConstr) := Id.run do
  let mut hintArr : Array FConstr := Array.mkEmpty hints.length
  for h in hints do
    match h with
    | .negC => hintArr := hintArr.push negConstr
    | .id n => match db[n]? with
      | some c => hintArr := hintArr.push c
      | none => return none
  let mut asgn : Array (Option Bool) := .replicate numVars none
  let mut conflictIdx : Option Nat := none
  let mut changed := true
  let maxIters := propagationIterLimit numVars hintArr.size
  let mut iters := 0
  while changed && iters < maxIters do
    iters := iters + 1
    changed := false
    for i in [:hintArr.size] do
      if conflictIdx.isSome then break
      let hintC := hintArr[i]!
      match pbFPropagateBool asgn hintC with
      | .conflict => conflictIdx := some i
      | .propagated forced =>
        changed := true
        for (l, val) in forced do
          if conflictIdx.isSome then break
          let varIdx := l.var
          let actualVal := match l with
            | .pos _ => val
            | .neg _ => !val
          if varIdx < asgn.size then
            match asgn[varIdx]! with
            | some existing =>
              if existing != actualVal then
                conflictIdx := some i
                break
            | none => asgn := asgn.set! varIdx (some actualVal)
      | .noPropagation => pure ()
  return conflictIdx.map fun i => (i, hintArr)

def combineFHintsRec (acc : FConstr) : List FConstr → FConstr
  | [] => acc
  | hintC :: rest =>
    if acc.isContra then acc
    else
      let combined := match findFCompLitPairBool acc hintC with
        | some (ca, ch) =>
          let accM := if ch == 1 then acc else mulFConstr acc ch
          let hintM := if ca == 1 then hintC else mulFConstr hintC ca
          normalizeFConstr (addFConstrs accM hintM)
        | none =>
          normalizeFConstr (addFConstrs acc hintC)
      combineFHintsRec combined rest

/-- Mirrors `verifyRupExtract`. The verified version resolves every hint a
second time after finding the conflict; the resolved array returned by
`findFConflictHintBool` holds the same constraints in the same order. -/
def verifyFRupExtract (negConstr : FConstr)
    (hints : List VeriPB.RupHint) (db : Std.HashMap Nat FConstr)
    (numVars : Nat) : Option (FConstr × List FConstr) :=
  if hints.isEmpty then none
  else
    match findFConflictHintBool negConstr hints db numVars with
    | none => none
    | some (conflictIdx, hintArr) =>
      let conflictC := hintArr[conflictIdx]!
      let otherHints := (List.range hintArr.size).filterMap fun i =>
        if i == conflictIdx then none else some hintArr[i]!
      some (conflictC, otherHints)

def verifyFRupBool (negConstr : FConstr)
    (hints : List VeriPB.RupHint) (db : Std.HashMap Nat FConstr)
    (numVars : Nat) : Bool :=
  match verifyFRupExtract negConstr (withNegHint hints) db numVars with
  | none => false
  | some (conflictC, otherHints) =>
    (combineFHintsRec (normalizeFConstr conflictC) otherHints).isContra

/-! ### Step execution -/

def FBoolCheckState.fromConstrs (constrs : Array Constr)
    (numVars : Nat) : FBoolCheckState :=
  { db := constrs.foldl (fun (db, i) c =>
      (db.insert i (toFConstr c), i + 1)) ({}, 1) |>.1
    origConstrs := constrs
    nextId := constrs.size + 1
    numVars := numVars
    formulaSize := constrs.size }

/-- Process red proof goals (mirrors `processRedGoalsBool`). -/
def processFRedGoalsBool
    (execFn : FBoolCheckState → List VeriPB.ProofStep → Option FBoolCheckState)
    (origConstrs : Array Constr) (numVars formulaSize : Nat)
    (subst : List (Nat × Sat.PB.SubstVal)) (pbConstr : Constr)
    (savedDb redDb : Std.HashMap Nat FConstr)
    (goals : List (String × Array VeriPB.ProofStep × Nat))
    (nextId : Nat) : Option Nat :=
  match goals with
  | [] => some nextId
  | (goalId, innerSteps, resultId) :: rest =>
    let goalConstr? :=
      if goalId.startsWith "#" then
        some (toFConstr (Sat.PB.applySubstConstr subst pbConstr))
      else match goalId.toNat? with
      | some dbId => match savedDb[dbId]? with
        | some c => some (toFConstr (Sat.PB.applySubstConstr subst (fromFConstr c)))
        | none => none
      | none => none
    match goalConstr? with
    | none => none
    | some goalFc =>
      if goalFc.degree > goalFc.coeffSum then none
      else
      let goalNeg := goalFc.negateWith goalFc.coeffSum
      let goalDb := redDb.insert nextId goalNeg
      let subState : FBoolCheckState :=
        { db := goalDb, origConstrs, nextId := nextId + 1,
          numVars, formulaSize }
      match execFn subState innerSteps.toList with
      | some finalSub =>
        match finalSub.db[resultId]? with
        | some c =>
          if !c.isContra then none
          else processFRedGoalsBool execFn origConstrs numVars formulaSize
            subst pbConstr savedDb redDb rest finalSub.nextId
        | none => none
      | none => none

def execFStepsFuel (fuel : Nat) (state : FBoolCheckState)
    (steps : List VeriPB.ProofStep) : Option FBoolCheckState :=
  match steps with
  | [] => some state
  | step :: rest =>
    let stepResult : Option FBoolCheckState := match step with
      | .formulaSize n =>
        if state.formulaSize != n then none else some state
      | .pol ops =>
        match execFPolRPNBool ops state.db with
        | some result =>
          let newDb := state.db.insert state.nextId
            (normalizeFConstr result)
          some { state with db := newDb, nextId := state.nextId + 1 }
        | none => none
      | .rup constr hints =>
        match VeriPB.opbConstrToPB constr with
        | .ok pbConstr =>
          let fc := toFConstr pbConstr
          if !verifyFRupBool (rupNegateF fc) hints state.db
              state.numVars then none
          else
            let newDb := state.db.insert state.nextId
              (normalizeFConstr fc)
            some { state with db := newDb, nextId := state.nextId + 1 }
        | .error _ => none
      | .pbc constr innerSteps resultId =>
        if innerSteps.any (fun s => match s with
            | .conclusion _ | .output => true | _ => false) then
          none
        else match fuel with
        | 0 => none
        | n + 1 =>
          match VeriPB.opbConstrToPB constr with
          | .ok pbConstr =>
            let fc := toFConstr pbConstr
            let cs := fc.coeffSum
            if fc.degree > cs then none
            else
              let savedDb := state.db
              let negId := state.nextId
              let dbWithNeg := state.db.insert negId (fc.negateWith cs)
              let subState : FBoolCheckState :=
                { state with db := dbWithNeg, nextId := negId + 1 }
              match execFStepsFuel n subState innerSteps.toList with
              | some finalSub =>
                match finalSub.db[resultId]? with
                | some c =>
                  if !c.isContra then none
                  else
                    let restoredDb := savedDb.insert finalSub.nextId
                      (normalizeFConstr fc)
                    some { state with
                      db := restoredDb
                      nextId := finalSub.nextId + 1 }
                | none => none
              | none => none
          | .error _ => none
      | .red constr substPairs goals =>
        match fuel with
        | 0 => none
        | n + 1 =>
          match VeriPB.opbConstrToPB constr with
          | .ok pbConstr =>
            let fc := toFConstr pbConstr
            let cs := fc.coeffSum
            if fc.degree > cs then none
            else
              match VeriPB.parseSubstPairs substPairs state.numVars with
              | .error _ => none
              | .ok subst =>
                let savedDb := state.db
                let negId := state.nextId
                let redDb := state.db.insert negId (fc.negateWith cs)
                -- Coverage check needs Constr db, convert from FConstr
                let constrDb := savedDb.fold (fun (m : Std.HashMap Nat Constr) k v =>
                  m.insert k (fromFConstr v)) {}
                if !checkRedCoverage state.origConstrs subst constrDb
                    goals.toList then none
                else
                match processFRedGoalsBool (execFStepsFuel n)
                    state.origConstrs state.numVars state.formulaSize
                    subst pbConstr savedDb redDb goals.toList
                    (negId + 1) with
                | some finalNextId =>
                  let restoredDb := savedDb.insert finalNextId
                    (normalizeFConstr fc)
                  some { state with
                    db := restoredDb
                    nextId := finalNextId + 1 }
                | none => none
          | .error _ => none
      | .deld ids | .delc ids =>
        some { state with
          db := ids.foldl (fun db id => db.erase id) state.db }
      | .output => some state
      | .conclusion id =>
        match state.db[id]? with
        | some c => if c.isContra then some state else none
        | none => none
      | .sol _ => some state
      | .soli _ => some state
      | .conclusionSat _ => some state
      | .conclusionBounds _ _ _ _ => some state
    match stepResult with
    | some s => execFStepsFuel fuel s rest
    | none => none
termination_by (fuel, steps.length)

def hasFUnsatConclusion (steps : Array VeriPB.ProofStep)
    (state : FBoolCheckState) : Bool :=
  steps.any fun step => match step with
    | .conclusion id => match state.db[id]? with
      | some c => c.isContra
      | none => false
    | _ => false

/-- Runtime implementation of `VeriPB.Reflect.checkProofBool`. -/
def checkProofBoolFast (constrs : Array Constr) (numVars : Nat)
    (proofStr : String) : Bool :=
  match VeriPB.parseVeriPBProof proofStr with
  | .error _ => false
  | .ok proofData =>
    let initState := FBoolCheckState.fromConstrs constrs numVars
    let stepsList := proofData.steps.toList
    let fuel := pbcDepth stepsList + 1
    match execFStepsFuel fuel initState stepsList with
    | some finalState =>
      hasFUnsatConclusion proofData.steps finalState
    | none => false

end VeriPB.Reflect.Fast
