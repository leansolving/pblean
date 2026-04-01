/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import Lean
import Std
import VeriPB.Tactic.Sat.PseudoBoolean
import VeriPB.Tactic.Sat.FromVeriPB

/-!
# Reflection-based VeriPB Proof Checking

This module provides a reflection-based approach to VeriPB proof verification.
Instead of building kernel proof terms for each step, we:

1. Define a checker function `checkProof : ... → Bool`
2. Prove soundness: `checkProof = true → formula is UNSAT`
3. Use `native_decide` to evaluate `checkProof` efficiently

This approach scales much better than explicit Expr construction because:
- The kernel proof term is tiny (just the soundness theorem + native_decide)
- The heavy computation runs as compiled Lean code, not kernel reduction
- Memory usage is bounded by the checker state, not accumulated Expr nodes

## Trust assumptions

Using `native_decide` adds the Lean compiler to the trusted code base.
This is the same trust model as Lean's built-in `bv_decide` tactic.

## Main definitions

* `VeriPB.Reflect.checkProofBool` — Boolean checker for VeriPB proofs
* `VeriPB.Reflect.checkProof_sound` — Soundness theorem
* `checkProofBoolFast` — Array-based runtime replacement via `@[implemented_by]`
* `veripb_reflect` — Command using reflection
-/

namespace VeriPB.Reflect

open Sat.PB

-- Re-export key types
abbrev Constr := Sat.PB.Constr
abbrev Valuation := Sat.PB.Valuation

/-- Propagation loop iteration limit: `(numVars + 1) * (numHints + 1)`.
    Each iteration must propagate at least one new assignment or find a
    conflict, so `numVars * numHints` is a tight bound; the `+1` factors
    absorb off-by-one edge cases. -/
private def propagationIterLimit (numVars numHints : Nat) : Nat :=
  (numVars + 1) * (numHints + 1)

/-! ## Boolean checker

Core checker functions (`execStepsFuel`, `execPolOps`, `combineHintsRec`)
are total and pure recursive to enable formal verification.
Helper functions (`pbPropagateBool`, `findConflictHintBool`) use
`Id.run do` for readability but are not part of the soundness proof.
-/

/-- Check state for the Boolean checker. Uses arrays for efficiency. -/
structure BoolCheckState where
  /-- Constraint database: maps ID to constraint -/
  db : Std.HashMap Nat Constr
  /-- Original formula constraints (for red coverage verification) -/
  origConstrs : Array Constr
  /-- Next available constraint ID -/
  nextId : Nat
  /-- Number of variables -/
  numVars : Nat
  /-- Expected formula size -/
  formulaSize : Nat
  deriving Inhabited

/-- Build HashMap from list with starting index (pure recursive). -/
private def mkDBRec : List Constr → Nat → Std.HashMap Nat Constr
  | [], _ => {}
  | c :: rest, i => (mkDBRec rest (i + 1)).insert i c

/-- Initialize check state from an array of constraints. -/
def BoolCheckState.fromConstrs (constrs : Array Constr) (numVars : Nat) :
    BoolCheckState :=
  { db := mkDBRec constrs.toList 1
    origConstrs := constrs
    nextId := constrs.size + 1
    numVars := numVars
    formulaSize := constrs.size }

/-! ### Pol RPN execution (pure recursive) -/

/-- Execute a single pol operation on the stack. -/
def execPolOne (db : Std.HashMap Nat Constr) (stack : List VeriPB.StackElem)
    (op : VeriPB.PolOp) : Option (List VeriPB.StackElem) :=
  match op with
  | .pushId id => match db[id]? with
    | some c => some (.constr c :: stack)
    | none => none
  | .pushNat n => some (.nat n :: stack)
  | .pushLitAxiom lit => match VeriPB.opbLitToPB lit with
    | .ok pbLit => some (.constr ⟨[(1, pbLit)], 0⟩ :: stack)
    | .error _ => none
  | .add => match stack with
    | .constr c2 :: .constr c1 :: rest =>
      some (.constr (VeriPB.addConstrs c1 c2) :: rest)
    | _ => none
  | .mul => match stack with
    | .nat k :: .constr c :: rest =>
      some (.constr (VeriPB.mulConstr c k) :: rest)
    | _ => none
  | .div => match stack with
    | .nat k :: .constr c :: rest =>
      if k == 0 then none
      else some (.constr (VeriPB.divConstr (VeriPB.normalizeConstr c) k) :: rest)
    | _ => none
  | .saturate => match stack with
    | .constr c :: rest =>
      some (.constr (VeriPB.saturateConstr (VeriPB.normalizeConstr c)) :: rest)
    | _ => none
  | .weaken varName => match stack with
    | .constr c :: rest =>
      if varName.startsWith "x" then
        match (varName.drop 1).toString.toNat? with
        | some n => if n > 0 then
            match VeriPB.weakenConstr c (n - 1) with
            | .ok result => some (.constr result :: rest)
            | .error _ => none
          else none
        | none => none
      else none
    | _ => none

/-- Execute pol RPN operations on a stack. Pure recursive. -/
def execPolOps (db : Std.HashMap Nat Constr) :
    List VeriPB.PolOp → List VeriPB.StackElem → Option (List VeriPB.StackElem)
  | [], stack => some stack
  | op :: rest, stack =>
    match execPolOne db stack op with
    | some s => execPolOps db rest s
    | none => none

/-- Execute pol RPN and return result constraint (or none on error). -/
def execPolRPNBool (ops : List VeriPB.PolOp) (db : Std.HashMap Nat Constr) :
    Option Constr :=
  match execPolOps db ops [] with
  | some [.constr c] => some c
  | _ => none

/-! ### RUP verification -/

/-- Find a complementary literal pair between accumulator and hint. -/
def findCompLitPairBool (acc hint : Constr) : Option (Nat × Nat) :=
  acc.terms.findSome? fun (ca, la) =>
    hint.terms.findSome? fun (ch, lh) =>
      if la.var == lh.var && la != lh then some (ca, ch)
      else none

/-- Evaluate a literal under a partial assignment. -/
def evalLitPartialBool (asgn : Array (Option Bool)) (l : Sat.PB.Literal) :
    Option Bool :=
  match l with
  | .pos i => if h : i < asgn.size then asgn[i] else none
  | .neg i => if h : i < asgn.size then asgn[i].map (!·) else none

/-- Result of propagating a single constraint. -/
inductive PropResultBool where
  | conflict
  | propagated (forced : List (Sat.PB.Literal × Bool))
  | noPropagation

/-- PB unit propagation on a constraint. -/
def pbPropagateBool (asgn : Array (Option Bool)) (c : Constr) :
    PropResultBool := Id.run do
  let mut totalActive : Nat := 0
  let mut unassigned : List (Nat × Sat.PB.Literal) := []
  for (a, l) in c.terms do
    match evalLitPartialBool asgn l with
    | some false => pure ()
    | none =>
      totalActive := totalActive + a
      unassigned := (a, l) :: unassigned
    | some true => totalActive := totalActive + a
  if totalActive < c.degree then return .conflict
  let slack := totalActive - c.degree
  let forced := unassigned.filterMap fun (a, l) =>
    if a > slack then some (l, true) else none
  if forced.isEmpty then .noPropagation
  else .propagated forced

/-- Find the conflict hint index via propagation. -/
def findConflictHintBool (negConstr : Constr) (hints : List VeriPB.RupHint)
    (db : Std.HashMap Nat Constr) (numVars : Nat) : Option Nat := Id.run do
  let mut hintArr : Array Constr := #[]
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
  let hintIdxs := List.range hintArr.size
  let mut iters := 0
  while changed && iters < maxIters do
    iters := iters + 1
    changed := false
    for i in hintIdxs do
      if conflictIdx.isSome then break
      let hintC := hintArr[i]!
      match pbPropagateBool asgn hintC with
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
  return conflictIdx

/-- Combine hints by adding with complementary literal cancellation.
    Pure recursive for provability. -/
def combineHintsRec (acc : Constr) : List Constr → Constr
  | [] => acc
  | hintC :: rest =>
    if acc.isContra then acc
    else
      let combined := match findCompLitPairBool acc hintC with
        | some (ca, ch) =>
          let accM := if ch == 1 then acc else VeriPB.mulConstr acc ch
          let hintM := if ca == 1 then hintC else VeriPB.mulConstr hintC ca
          VeriPB.normalizeConstr (VeriPB.addConstrs accM hintM)
        | none =>
          VeriPB.normalizeConstr (VeriPB.addConstrs acc hintC)
      combineHintsRec combined rest

/-- Resolve a RUP hint to a constraint. -/
def resolveHint (negConstr : Constr) (db : Std.HashMap Nat Constr)
    (h : VeriPB.RupHint) : Option Constr :=
  match h with
  | .negC => some negConstr
  | .id n => db[n]?

/-- Extract the conflict constraint and other hints from RUP data.
    Returns `none` if extraction fails (empty hints, no conflict, etc.). -/
def verifyRupExtract (negConstr : Constr) (hints : List VeriPB.RupHint)
    (db : Std.HashMap Nat Constr) (numVars : Nat) :
    Option (Constr × List Constr) :=
  if hints.isEmpty then none
  else
    let hintsArr := hints.toArray
    match findConflictHintBool negConstr hints db numVars with
    | none => none
    | some conflictIdx =>
      match resolveHint negConstr db (hintsArr[conflictIdx]!) with
      | none => none
      | some conflictC =>
        let otherHints := (List.range hintsArr.size).filterMap fun i =>
          if i == conflictIdx then none
          else resolveHint negConstr db (hintsArr[i]!)
        some (conflictC, otherHints)

/-- Verify RUP step using propagation + conflict-first combining. -/
def verifyRupBool (negConstr : Constr) (hints : List VeriPB.RupHint)
    (db : Std.HashMap Nat Constr) (numVars : Nat) : Bool :=
  match verifyRupExtract negConstr hints db numVars with
  | none => false
  | some (conflictC, otherHints) =>
    (combineHintsRec (VeriPB.normalizeConstr conflictC)
      otherHints).isContra

/-! ### Red coverage verification -/

/-- Check if two normalized constraints match (same degree and sorted terms). -/
private def constrMatchNorm (c1 c2 : Constr) : Bool :=
  c1.degree == c2.degree && c1.terms.length == c2.terms.length &&
  -- Compare sorted term lists
  let sort := fun (ts : List (Nat × Sat.PB.Literal)) =>
    ts.mergeSort fun a b =>
      Sat.PB.Literal.var a.2 < Sat.PB.Literal.var b.2 ||
      (Sat.PB.Literal.var a.2 == Sat.PB.Literal.var b.2 &&
       match a.2, b.2 with
       | .pos _, .neg _ => true
       | _, _ => false)
  sort c1.terms == sort c2.terms

/-- Check if a constraint (after normalization) is in the database. -/
private def constrInDB (c : Constr) (db : Std.HashMap Nat Constr) : Bool :=
  let nc := VeriPB.normalizeConstr c
  db.toList.any fun (_, dbC) => constrMatchNorm nc (VeriPB.normalizeConstr dbC)

/-- Verify red rule coverage for the red step.
    1. Must have a '#' goal (for the new constraint C itself).
    2. Every original constraint with affected variables must have a goal
       or be auto-satisfied (G|ω is already in the db). Rejects if any
       affected original constraint was deleted from savedDb.
    3. Every derived constraint in savedDb with affected variables must
       have a goal or be auto-satisfied. -/
def checkRedCoverage (_origConstrs : Array Constr)
    (subst : List (Nat × Sat.PB.SubstVal))
    (savedDb : Std.HashMap Nat Constr)
    (goals : List (String × Array VeriPB.ProofStep × Nat)) : Bool :=
  -- Must have at least one '#' goal (for C itself)
  let hasHashGoal := goals.any fun (gid, _, _) => gid.startsWith "#"
  if !hasHashGoal then false
  else
    -- Collect numeric goal IDs
    let goalIds := goals.filterMap fun (gid, _, _) =>
      if gid.startsWith "#" then none else gid.toNat?
    -- Helper: check if an affected constraint is covered
    let isCovered (id : Nat) (c : Constr) : Bool :=
      goalIds.contains id ||
      constrInDB (Sat.PB.applySubstConstr subst c) savedDb
    -- Check all constraints in savedDb (original and derived)
    savedDb.toList.all fun (id, c) =>
      if Sat.PB.termsAffected subst c.terms then isCovered id c
      else true

/-! ### Step execution (total, fuel-bounded) -/

/-- Process red proof goals using an executor callback.
    Separated from execStepsFuel to avoid mutual recursion issues. -/
def processRedGoalsBool
    (execFn : BoolCheckState → List VeriPB.ProofStep → Option BoolCheckState)
    (origConstrs : Array Constr) (numVars formulaSize : Nat)
    (subst : List (Nat × Sat.PB.SubstVal)) (pbConstr : Constr)
    (savedDb redDb : Std.HashMap Nat Constr)
    (goals : List (String × Array VeriPB.ProofStep × Nat))
    (nextId : Nat) : Option Nat :=
  match goals with
  | [] => some nextId
  | (goalId, innerSteps, resultId) :: rest =>
    let goalConstr? :=
      if goalId.startsWith "#" then
        some (Sat.PB.applySubstConstr subst pbConstr)
      else match goalId.toNat? with
      | some dbId => match savedDb[dbId]? with
        | some c => some (Sat.PB.applySubstConstr subst c)
        | none => none
      | none => none
    match goalConstr? with
    | none => none
    | some goalConstr =>
      -- Reject unsatisfiable goal constraints (negate is only a valid
      -- Boolean complement when degree ≤ coeffSum)
      if goalConstr.degree > goalConstr.coeffSum then none
      else
      let goalNeg := goalConstr.negate
      let goalDb := redDb.insert nextId goalNeg
      let subState : BoolCheckState :=
        { db := goalDb, origConstrs, nextId := nextId + 1,
          numVars, formulaSize }
      match execFn subState innerSteps.toList with
      | some finalSub =>
        match finalSub.db[resultId]? with
        | some c =>
          if !c.isContra then none
          else processRedGoalsBool execFn origConstrs numVars formulaSize
            subst pbConstr savedDb redDb rest finalSub.nextId
        | none => none
      | none => none

/-- Execute proof steps with fuel for pbc nesting depth.
    Returns the final state if all steps succeed.
    Fuel is consumed only for pbc subproof nesting. -/
def execStepsFuel (fuel : Nat) (state : BoolCheckState)
    (steps : List VeriPB.ProofStep) : Option BoolCheckState :=
  match steps with
  | [] => some state
  | step :: rest =>
    let stepResult : Option BoolCheckState := match step with
      | .formulaSize n =>
        if state.formulaSize != n then none else some state
      | .pol ops =>
        match execPolRPNBool ops state.db with
        | some result =>
          let newDb := state.db.insert state.nextId
            (VeriPB.normalizeConstr result)
          some { state with db := newDb, nextId := state.nextId + 1 }
        | none => none
      | .rup constr hints =>
        match VeriPB.opbConstrToPB constr with
        | .ok pbConstr =>
          if pbConstr.degree > pbConstr.coeffSum then none
          else if !verifyRupBool pbConstr.negate hints state.db
              state.numVars then none
          else
            let newDb := state.db.insert state.nextId
              (VeriPB.normalizeConstr pbConstr)
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
            if pbConstr.degree > pbConstr.coeffSum then none
            else
              let savedDb := state.db
              let negId := state.nextId
              let dbWithNeg := state.db.insert negId pbConstr.negate
              let subState : BoolCheckState :=
                { state with db := dbWithNeg, nextId := negId + 1 }
              match execStepsFuel n subState innerSteps.toList with
              | some finalSub =>
                match finalSub.db[resultId]? with
                | some c =>
                  if !c.isContra then none
                  else
                    let restoredDb := savedDb.insert finalSub.nextId
                      (VeriPB.normalizeConstr pbConstr)
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
            if pbConstr.degree > pbConstr.coeffSum then none
            else
              -- Convert string substitution pairs to kernel SubstVal
              match VeriPB.parseSubstPairs substPairs state.numVars with
              | .error _ => none
              | .ok subst =>
                let savedDb := state.db
                -- Verify coverage: all affected original constraints have goals
                if !checkRedCoverage state.origConstrs subst savedDb
                    goals.toList then none
                else
                let negId := state.nextId
                let redDb := state.db.insert negId pbConstr.negate
                match processRedGoalsBool (execStepsFuel n)
                    state.origConstrs state.numVars state.formulaSize
                    subst pbConstr savedDb redDb goals.toList
                    (negId + 1) with
                | some finalNextId =>
                  let restoredDb := savedDb.insert finalNextId
                    (VeriPB.normalizeConstr pbConstr)
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
    | some s => execStepsFuel fuel s rest
    | none => none
termination_by (fuel, steps.length)

/-- Check if any step is a valid UNSAT conclusion. -/
def hasUnsatConclusion (steps : Array VeriPB.ProofStep)
    (state : BoolCheckState) : Bool :=
  steps.any fun step => match step with
    | .conclusion id => match state.db[id]? with
      | some c => c.isContra
      | none => false
    | _ => false

/-- Count total pbc nesting depth for fuel computation. -/
partial def pbcDepth : List VeriPB.ProofStep → Nat
  | [] => 0
  | .pbc _ inner _ :: rest =>
    max (1 + pbcDepth inner.toList) (pbcDepth rest)
  | .red _ _ goals :: rest =>
    let goalDepth := goals.foldl (fun d (_, steps, _) =>
      max d (1 + pbcDepth steps.toList)) 0
    max goalDepth (pbcDepth rest)
  | _ :: rest => pbcDepth rest

/-! ## Array-based fast checker (runtime replacement via @[implemented_by])

All functions below use `Array (Nat × Sat.PB.Literal)` instead of
`List (Nat × Sat.PB.Literal)` for constraint terms. This avoids
O(n) cons-cell allocation on every append/map/normalize step.
The slow `checkProofBool` definition is kept for proofs; the kernel
type-checker calls `checkProofBoolFast` at runtime.
-/

private structure FConstr where
  terms : Array (Nat × Sat.PB.Literal)
  degree : Nat
  deriving Inhabited

private structure FBoolCheckState where
  db : Std.HashMap Nat FConstr
  origConstrs : Array Constr
  nextId : Nat
  numVars : Nat
  formulaSize : Nat
  deriving Inhabited

private def toFConstr (c : Constr) : FConstr :=
  ⟨c.terms.toArray, c.degree⟩

private def fromFConstr (c : FConstr) : Constr :=
  ⟨c.terms.toList, c.degree⟩

private def FConstr.coeffSum (c : FConstr) : Nat :=
  c.terms.foldl (fun acc (a, _) => acc + a) 0

private def FConstr.isContra (c : FConstr) : Bool :=
  c.coeffSum < c.degree

private def FConstr.negate (c : FConstr) : FConstr :=
  let m := c.coeffSum
  ⟨c.terms.map fun (a, l) => (a, l.negate), m - c.degree + 1⟩

private def FConstr.negateWith (c : FConstr) (cs : Nat) : FConstr :=
  ⟨c.terms.map fun (a, l) => (a, l.negate), cs - c.degree + 1⟩

private def addFConstrs (c1 c2 : FConstr) : FConstr :=
  ⟨c1.terms ++ c2.terms, c1.degree + c2.degree⟩

private def mulFConstr (c : FConstr) (k : Nat) : FConstr :=
  ⟨c.terms.map fun (a, l) => (k * a, l), k * c.degree⟩

private def divFConstr (c : FConstr) (k : Nat) : FConstr :=
  ⟨c.terms.map fun (a, l) => (Sat.PB.ceilDiv a k, l),
   Sat.PB.ceilDiv c.degree k⟩

private def saturateFConstr (c : FConstr) : FConstr :=
  ⟨c.terms.map fun (a, l) => (min a c.degree, l), c.degree⟩

private def weakenFConstr (c : FConstr) (varIdx : Nat) :
    Option FConstr := Id.run do
  for i in [:c.terms.size] do
    let (a, l) := c.terms[i]!
    if l.var == varIdx then
      if a ≤ c.degree then
        let rest := c.terms[:i] ++ c.terms[i+1:]
        return some ⟨rest, c.degree - a⟩
      else return none
  return none

-- HashMap-based O(n) normalization for FConstr
private def normalizeFConstr (c : FConstr) : FConstr :=
  -- Phase 1: merge like terms into HashMap
  let merged : Std.HashMap Sat.PB.Literal Nat :=
    c.terms.foldl (fun m (coeff, lit) =>
      if coeff == 0 then m
      else match m[lit]? with
        | some old => m.insert lit (old + coeff)
        | none     => m.insert lit coeff) ∅
  -- Phase 2: collect unique variable indices, sorted for deterministic order
  let vars : Array Nat :=
    (merged.fold (fun (s : Std.HashSet Nat) lit _ => s.insert lit.var) ∅).fold
      (fun (a : Array Nat) v => a.push v) #[]
  let vars := vars.qsort (· < ·)
  -- Phase 3: cancel complementary pairs, build result
  let initAcc : Array (Nat × Sat.PB.Literal) × Nat := (#[], c.degree)
  let (resultTerms, resultDeg) :=
    vars.foldl (fun (acc : Array (Nat × Sat.PB.Literal) × Nat) v =>
      let posLit := Sat.PB.Literal.pos v
      let negLit := Sat.PB.Literal.neg v
      let posCoeff := merged[posLit]?.getD 0
      let negCoeff := merged[negLit]?.getD 0
      let m := min posCoeff negCoeff
      let (deg, pc, nc) :=
        if m > 0 && m ≤ acc.2 then (acc.2 - m, posCoeff - m, negCoeff - m)
        else (acc.2, posCoeff, negCoeff)
      let terms := acc.1
      let terms := if pc > 0 then terms.push (pc, posLit) else terms
      let terms := if nc > 0 then terms.push (nc, negLit) else terms
      (terms, deg)) initAcc
  ⟨resultTerms, resultDeg⟩

/-! ### Fast pol RPN -/

private inductive FStackElem where
  | constr : FConstr → FStackElem
  | nat : Nat → FStackElem

private def execFPolOne (db : Std.HashMap Nat FConstr)
    (stack : List FStackElem) (op : VeriPB.PolOp) :
    Option (List FStackElem) :=
  match op with
  | .pushId id => match db[id]? with
    | some c => some (.constr c :: stack)
    | none => none
  | .pushNat n => some (.nat n :: stack)
  | .pushLitAxiom lit => match VeriPB.opbLitToPB lit with
    | .ok pbLit => some (.constr ⟨#[(1, pbLit)], 0⟩ :: stack)
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
            match weakenFConstr c (n - 1) with
            | some result => some (.constr result :: rest)
            | none => none
          else none
        | none => none
      else none
    | _ => none

private def execFPolOps (db : Std.HashMap Nat FConstr) :
    List VeriPB.PolOp → List FStackElem → Option (List FStackElem)
  | [], stack => some stack
  | op :: rest, stack =>
    match execFPolOne db stack op with
    | some s => execFPolOps db rest s
    | none => none

private def execFPolRPNBool (ops : List VeriPB.PolOp)
    (db : Std.HashMap Nat FConstr) : Option FConstr :=
  match execFPolOps db ops [] with
  | some [.constr c] => some c
  | _ => none

/-! ### Fast RUP verification -/

private def findFCompLitPairBool (acc hint : FConstr) :
    Option (Nat × Nat) := Id.run do
  for (ca, la) in acc.terms do
    for (ch, lh) in hint.terms do
      if la.var == lh.var && la != lh then return some (ca, ch)
  return none

private def pbFPropagateBool (asgn : Array (Option Bool)) (c : FConstr) :
    PropResultBool := Id.run do
  let mut totalActive : Nat := 0
  let mut unassigned : Array (Nat × Sat.PB.Literal) := #[]
  for (a, l) in c.terms do
    match evalLitPartialBool asgn l with
    | some false => pure ()
    | none =>
      totalActive := totalActive + a
      unassigned := unassigned.push (a, l)
    | some true => totalActive := totalActive + a
  if totalActive < c.degree then return .conflict
  let slack := totalActive - c.degree
  let mut forced : List (Sat.PB.Literal × Bool) := []
  for (a, l) in unassigned do
    if a > slack then forced := (l, true) :: forced
  if forced.isEmpty then .noPropagation
  else .propagated forced

private def findFConflictHintBool (negConstr : FConstr)
    (hints : List VeriPB.RupHint) (db : Std.HashMap Nat FConstr)
    (numVars : Nat) : Option Nat := Id.run do
  let mut hintArr : Array FConstr := #[]
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
  return conflictIdx

private def combineFHintsRec (acc : FConstr) : List FConstr → FConstr
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

private def resolveFHint (negConstr : FConstr)
    (db : Std.HashMap Nat FConstr) (h : VeriPB.RupHint) :
    Option FConstr :=
  match h with
  | .negC => some negConstr
  | .id n => db[n]?

private def verifyFRupExtract (negConstr : FConstr)
    (hints : List VeriPB.RupHint) (db : Std.HashMap Nat FConstr)
    (numVars : Nat) : Option (FConstr × List FConstr) :=
  if hints.isEmpty then none
  else
    let hintsArr := hints.toArray
    match findFConflictHintBool negConstr hints db numVars with
    | none => none
    | some conflictIdx =>
      match resolveFHint negConstr db (hintsArr[conflictIdx]!) with
      | none => none
      | some conflictC =>
        let otherHints := (List.range hintsArr.size).filterMap fun i =>
          if i == conflictIdx then none
          else resolveFHint negConstr db (hintsArr[i]!)
        some (conflictC, otherHints)

private def verifyFRupBool (negConstr : FConstr)
    (hints : List VeriPB.RupHint) (db : Std.HashMap Nat FConstr)
    (numVars : Nat) : Bool :=
  match verifyFRupExtract negConstr hints db numVars with
  | none => false
  | some (conflictC, otherHints) =>
    (combineFHintsRec (normalizeFConstr conflictC) otherHints).isContra

/-! ### Fast step execution -/

private def FBoolCheckState.fromConstrs (constrs : Array Constr)
    (numVars : Nat) : FBoolCheckState :=
  { db := constrs.foldl (fun (db, i) c =>
      (db.insert i (toFConstr c), i + 1)) ({}, 1) |>.1
    origConstrs := constrs
    nextId := constrs.size + 1
    numVars := numVars
    formulaSize := constrs.size }

/-- Process red proof goals for the fast (Array-based) checker. -/
private def processFRedGoalsBool
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

private def execFStepsFuel (fuel : Nat) (state : FBoolCheckState)
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
          let cs := fc.coeffSum
          if fc.degree > cs then none
          else if !verifyFRupBool (fc.negateWith cs) hints state.db
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

private def hasFUnsatConclusion (steps : Array VeriPB.ProofStep)
    (state : FBoolCheckState) : Bool :=
  steps.any fun step => match step with
    | .conclusion id => match state.db[id]? with
      | some c => c.isContra
      | none => false
    | _ => false

private def checkProofBoolFast (constrs : Array Constr) (numVars : Nat)
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

/-- Main Boolean checker: returns true iff proof is valid UNSAT proof. -/
@[implemented_by checkProofBoolFast]
def checkProofBool (constrs : Array Constr) (numVars : Nat)
    (proofStr : String) : Bool :=
  match VeriPB.parseVeriPBProof proofStr with
  | .error _ => false
  | .ok proofData =>
    let initState := BoolCheckState.fromConstrs constrs numVars
    let fuel := pbcDepth proofData.steps.toList + 1
    match execStepsFuel fuel initState proofData.steps.toList with
    | some finalState =>
      hasUnsatConclusion proofData.steps finalState
    | none => false

/-- Timed version for benchmarking (not used in proofs). -/
def checkProofBoolTimed (constrs : Array Constr) (numVars : Nat)
    (proofStr : String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let parseResult := VeriPB.parseVeriPBProof proofStr
  let t1 ← IO.monoMsNow
  match parseResult with
  | .error e => IO.println s!"Parse error: {e}"
  | .ok proofData =>
    IO.println s!"Parse: {t1-t0}ms ({proofData.steps.size} steps)"
    let initState := BoolCheckState.fromConstrs constrs numVars
    let fuel := pbcDepth proofData.steps.toList + 1
    let t2 ← IO.monoMsNow
    IO.println s!"Init+fuel: {t2-t1}ms (fuel={fuel})"
    -- Force evaluation by matching AND accessing nextId
    let result := execStepsFuel fuel initState proofData.steps.toList
    match result with
    | some finalState =>
      -- Force the HashMap by accessing a concrete field
      let dbSize := finalState.db.size
      let t3 ← IO.monoMsNow
      IO.println s!"Execution: {t3-t2}ms (db.size={dbSize})"
      let ok := hasUnsatConclusion proofData.steps finalState
      let t4 ← IO.monoMsNow
      IO.println s!"Conclusion: {t4-t3}ms, result={ok}"
      IO.println s!"Total: {t4-t0}ms"
    | none => IO.println "Execution failed"

/-! ## Soundness theorem infrastructure -/

/-- A formula is unsatisfiable if no valuation satisfies all constraints. -/
def formulaUnsat (constrs : Array Constr) : Prop :=
  ∀ v : Valuation, ∃ c ∈ constrs.toList, ¬c.sat v

/-- Legacy alias: implication-based soundness (stronger than DBPreserve).
    Every constraint in db is a consequence of the original formula.
    Used for pol/rup/pbc steps where the added constraint is implied. -/
def DBSound (original : Array Constr) (db : Std.HashMap Nat Constr) : Prop :=
  ∀ (id : Nat) (c : Constr), db.get? id = some c →
    ∀ v : Valuation, (∀ c' ∈ original.toList, Constr.sat c' v) →
      Constr.sat c v

/-- DB satisfiability: there exists a valuation satisfying all DB entries.
    Weaker than DBSound (no formula reference). Preserved by all proof steps
    including red/dom. -/
def DBSat (db : Std.HashMap Nat Constr) : Prop :=
  ∃ v : Valuation, ∀ (id : Nat) (c : Constr), db.get? id = some c →
    Constr.sat c v

/-- Bridge: construct a synthetic DBSound from a HashMap by using its
    toList values as the "formula". This lets us reuse existing pol/rup
    soundness lemmas in the DBSat-based proof. -/
theorem DBSound_of_toList (db : Std.HashMap Nat Constr) :
    DBSound ⟨db.toList.map Prod.snd⟩ db := by
  intro id c hget v hsat
  have hmem : (id, c) ∈ db.toList := by
    rw [Std.HashMap.get?_eq_getElem?] at hget
    exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hget
  have : c ∈ db.toList.map Prod.snd :=
    List.mem_map.mpr ⟨(id, c), hmem, rfl⟩
  exact hsat c (by simpa using this)

/-- The toList-based formula is satisfied by any valuation satisfying the DB. -/
theorem toList_sat_of_DBSat (db : Std.HashMap Nat Constr) (v : Valuation)
    (hdb : ∀ id c, db.get? id = some c → Constr.sat c v) :
    ∀ c ∈ (⟨db.toList.map Prod.snd⟩ : Array Constr).toList, Constr.sat c v := by
  intro c hmem
  have hmem' : c ∈ db.toList.map Prod.snd := by simpa using hmem
  obtain ⟨⟨id, _⟩, hmem'', rfl⟩ := List.mem_map.mp hmem'
  exact hdb id _ (by
    rw [Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem'')

theorem DBSat_erase (db : Std.HashMap Nat Constr) (id : Nat)
    (hsat : DBSat db) : DBSat (db.erase id) := by
  obtain ⟨v, hv⟩ := hsat
  exact ⟨v, fun id' c hget => hv id' c (by
    simp only [Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_erase] at hget ⊢
    by_cases heq : id == id'
    · simp [heq] at hget
    · simp [heq] at hget; exact hget)⟩

theorem DBSat_erase_fold (db : Std.HashMap Nat Constr) (ids : List Nat)
    (hsat : DBSat db) :
    DBSat (ids.foldl (fun db id => db.erase id) db) := by
  induction ids generalizing db with
  | nil => exact hsat
  | cons id rest ih => exact ih (db.erase id) (DBSat_erase db id hsat)

-- HashMap helper lemmas

theorem HashMap_get?_empty (k : Nat) :
    (∅ : Std.HashMap Nat Constr).get? k = none := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]

theorem HashMap_get?_insert (m : Std.HashMap Nat Constr) (k k' : Nat)
    (c : Constr) :
    (m.insert k c).get? k' = if k == k' then some c else m.get? k' := by
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

theorem DBSat_insert_dbImplied (db : Std.HashMap Nat Constr)
    (id : Nat) (c : Constr) (hsat : DBSat db)
    (himpl : ∀ v, (∀ id' c', db.get? id' = some c' → Constr.sat c' v) →
      Constr.sat c v) :
    DBSat (db.insert id c) := by
  obtain ⟨v, hv⟩ := hsat
  exact ⟨v, fun id' c' hget => by
    rw [HashMap_get?_insert] at hget
    by_cases heq : id == id'
    · simp [heq] at hget; subst hget; exact himpl v hv
    · simp [heq] at hget; exact hv id' c' hget⟩

-- mkDBRec properties

theorem mkDBRec_mem (cs : List Constr) (startIdx : Nat) (id : Nat)
    (c : Constr) :
    (mkDBRec cs startIdx).get? id = some c → c ∈ cs := by
  induction cs generalizing startIdx with
  | nil =>
    simp only [mkDBRec]
    intro h; rw [HashMap_get?_empty] at h; cases h
  | cons hd tl ih =>
    simp only [mkDBRec]
    intro hget; rw [HashMap_get?_insert] at hget
    by_cases heq : startIdx == id
    · simp only [heq, ↓reduceIte] at hget
      injection hget with hc; subst hc
      exact List.Mem.head _
    · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hget
      exact List.Mem.tail _ (ih (startIdx + 1) hget)

theorem init_sound (constrs : Array Constr) (numVars : Nat) :
    DBSound constrs (BoolCheckState.fromConstrs constrs numVars).db :=
  fun id c hc v hsat => by
    simp only [BoolCheckState.fromConstrs] at hc
    exact hsat c (mkDBRec_mem constrs.toList 1 id c hc)

/-! ## Soundness proofs -/

-- normalize_sat: normalization preserves satisfaction

theorem evalSum_singleton (v : Valuation) (t : Nat × Sat.PB.Literal) :
    Sat.PB.evalSum v [t] = t.1 * Sat.PB.evalLit v t.2 := by
  simp [Sat.PB.evalSum]

theorem list_take_drop_get (l : List α) (i : Nat) (hi : i < l.length) :
    l = l.take i ++ [l[i]] ++ l.drop (i + 1) := by
  induction l generalizing i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons x xs ih =>
    cases i with
    | zero => simp [List.take, List.drop]
    | succ j =>
      simp only [List.take_succ_cons, List.drop_succ_cons,
                 List.getElem_cons_succ, List.cons_append]
      congr 1
      have hj : j < xs.length := by
        simp only [List.length_cons] at hi; omega
      exact ih j hj

theorem evalSum_remove_zero (v : Valuation) (l : List (Nat × Sat.PB.Literal))
    (i : Nat) (hi : i < l.length) (hzero : l[i].1 = 0) :
    Sat.PB.evalSum v (l.take i ++ l.drop (i + 1)) =
      Sat.PB.evalSum v l := by
  have hdecomp := list_take_drop_get l i hi
  have hlhs : Sat.PB.evalSum v (l.take i ++ l.drop (i + 1)) =
    Sat.PB.evalSum v (l.take i) + Sat.PB.evalSum v (l.drop (i + 1)) :=
    Sat.PB.evalSum_append v _ _
  have hrhs1 : Sat.PB.evalSum v l =
    Sat.PB.evalSum v (l.take i ++ [l[i]] ++ l.drop (i + 1)) :=
    congrArg (Sat.PB.evalSum v) hdecomp
  have hrhs2 :
    Sat.PB.evalSum v (l.take i ++ [l[i]] ++ l.drop (i + 1)) =
    Sat.PB.evalSum v (l.take i ++ [l[i]]) +
      Sat.PB.evalSum v (l.drop (i + 1)) :=
    Sat.PB.evalSum_append v _ _
  have hrhs3 : Sat.PB.evalSum v (l.take i ++ [l[i]]) =
    Sat.PB.evalSum v (l.take i) + Sat.PB.evalSum v [l[i]] :=
    Sat.PB.evalSum_append v _ _
  have hmid : Sat.PB.evalSum v [l[i]] = 0 := by
    rw [evalSum_singleton, hzero]; simp
  calc Sat.PB.evalSum v (l.take i ++ l.drop (i + 1))
      = Sat.PB.evalSum v (l.take i) +
        Sat.PB.evalSum v (l.drop (i + 1)) := hlhs
    _ = Sat.PB.evalSum v (l.take i) + 0 +
        Sat.PB.evalSum v (l.drop (i + 1)) := by omega
    _ = Sat.PB.evalSum v (l.take i) + Sat.PB.evalSum v [l[i]] +
        Sat.PB.evalSum v (l.drop (i + 1)) := by rw [hmid]
    _ = Sat.PB.evalSum v (l.take i ++ [l[i]]) +
        Sat.PB.evalSum v (l.drop (i + 1)) := by rw [← hrhs3]
    _ = Sat.PB.evalSum v (l.take i ++ [l[i]] ++ l.drop (i + 1)) := by
        rw [← hrhs2]
    _ = Sat.PB.evalSum v l := by rw [← hrhs1]

-- findIdx helper lemmas

theorem findIdx_go_lt (l : List α) (p : α → Bool) (n i : Nat) :
    List.findIdx?.go p l n = some i → i < n + l.length := by
  induction l generalizing n i with
  | nil => intro h; simp only [List.findIdx?.go] at h; cases h
  | cons x xs ih =>
    intro h; simp only [List.findIdx?.go] at h
    by_cases hp : p x
    · simp [hp] at h; simp only [← h, List.length_cons]; omega
    · simp [hp] at h
      have := ih (n + 1) i h; simp only [List.length_cons]; omega

theorem findZeroIdx_lt (terms : List Sat.PB.Term) (idx : Nat)
    (h : VeriPB.findZeroIdx terms = some idx) : idx < terms.length := by
  simp only [VeriPB.findZeroIdx] at h
  have := findIdx_go_lt terms _ 0 idx h; omega

theorem findIdx_go_ge (l : List α) (p : α → Bool) (n i : Nat) :
    List.findIdx?.go p l n = some i → n ≤ i := by
  induction l generalizing n i with
  | nil => intro h; simp only [List.findIdx?.go] at h; cases h
  | cons x xs ih =>
    intro h; simp only [List.findIdx?.go] at h
    by_cases hp : p x
    · simp [hp] at h; omega
    · simp [hp] at h; have := ih (n + 1) i h; omega

theorem findIdx_go_getElem? (l : List α) (p : α → Bool) (n i : Nat)
    (h : List.findIdx?.go p l n = some i) :
    ∃ x, l[i - n]? = some x ∧ p x = true := by
  induction l generalizing n with
  | nil => simp [List.findIdx?.go] at h
  | cons x xs ih =>
    simp only [List.findIdx?.go] at h
    by_cases hp : p x
    · simp [hp] at h; subst h
      refine ⟨x, ?_, hp⟩; simp [Nat.sub_self]
    · simp [hp] at h
      have hge : n + 1 ≤ i := findIdx_go_ge xs p (n + 1) i h
      obtain ⟨y, hget, hpy⟩ := ih (n + 1) h
      refine ⟨y, ?_, hpy⟩
      have heq : i - n = (i - (n + 1)) + 1 := by omega
      simp only [heq, List.getElem?_cons_succ]; exact hget

theorem findZeroIdx_zero (terms : List Sat.PB.Term) (idx : Nat)
    (hlt : idx < terms.length)
    (h : VeriPB.findZeroIdx terms = some idx) : terms[idx].1 = 0 := by
  simp only [VeriPB.findZeroIdx] at h
  obtain ⟨x, hget, hpred⟩ :=
    findIdx_go_getElem? terms (fun (c, _) => c == 0) 0 idx h
  simp at hget
  have heq : terms[idx] = x := by
    rw [List.getElem?_eq_some_iff] at hget; exact hget.2
  rw [heq]; simp at hpred; exact hpred

-- Literal BEq-to-Eq bridge

private theorem Literal_beq_eq (l1 l2 : Sat.PB.Literal) :
    (l1 == l2) = true → l1 = l2 := by
  intro h; cases l1 <;> cases l2 <;>
    simp [BEq.beq, Sat.PB.instBEqLiteral.beq] at h <;> simp [h]

-- Two-point list decomposition

private theorem list_two_point_decomp {α : Type} (l : List α)
    (i j : Nat) (hi : i < l.length) (hj : j < l.length)
    (hij : i < j) :
    l = l.take i ++ l[i] ::
      (l.drop (i + 1)).take (j - i - 1) ++
        l[j] :: l.drop (j + 1) := by
  have hlen : j - i - 1 < (l.drop (i + 1)).length := by
    simp [List.length_drop]; omega
  have eq_inner_drop : (l.drop (i + 1)).drop (j - i - 1) =
      l[j] :: l.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hlen]
    congr 1
    · simp [List.getElem_drop]; congr 1; omega
    · rw [List.drop_drop]; congr 1; omega
  have eq_inner : l.drop (i + 1) =
      (l.drop (i + 1)).take (j - i - 1) ++
        l[j] :: l.drop (j + 1) := by
    have h := (List.take_append_drop (j - i - 1)
      (l.drop (i + 1))).symm
    rw [eq_inner_drop] at h; exact h
  have eq_outer := (List.take_append_drop i l).symm
  rw [List.drop_eq_getElem_cons hi] at eq_outer
  rw [eq_inner] at eq_outer
  have reassoc : ∀ (a : α) (xs ys zs : List α),
      xs ++ a :: (ys ++ zs) = (xs ++ a :: ys) ++ zs := by
    intros; simp [List.append_assoc, List.cons_append]
  rw [reassoc] at eq_outer
  exact eq_outer

-- normalize_sat proof via go_sat

theorem go_sat (fuel : Nat) (terms : List Sat.PB.Term) (degree : Nat)
    (v : Valuation) (h : Sat.PB.evalSum v terms ≥ degree) :
    (VeriPB.normalizeConstr.go fuel terms degree).sat v := by
  induction fuel generalizing terms degree with
  | zero => simp only [VeriPB.normalizeConstr.go]; exact h
  | succ n ih =>
    simp only [VeriPB.normalizeConstr.go]
    cases hzero : VeriPB.findZeroIdx terms with
    | some idx =>
      apply ih; have hidx := findZeroIdx_lt terms idx hzero
      have hcoeff := findZeroIdx_zero terms idx hidx hzero
      rw [evalSum_remove_zero v terms idx hidx hcoeff]; exact h
    | none =>
      cases hpair : VeriPB.findValidCompPairIdx terms degree with
      | some pair =>
        obtain ⟨i, j⟩ := pair
        simp only []
        -- Split through guards: hi, hj, hij, hlit, hle
        split
        · split
          · split
            · split
              · split
                · next hi hj hij hlit hle =>
                  apply ih
                  have hlit_eq := Literal_beq_eq _ _ hlit
                  have hj_eq : terms[j] =
                      (terms[j].1, terms[i].2.negate) :=
                    Prod.ext rfl hlit_eq
                  have hdecomp := list_two_point_decomp
                    terms i j hi hj hij
                  have hform : (Constr.mk terms degree).sat v :=
                    h
                  rw [hdecomp, hj_eq] at hform
                  exact cancel_pair_sat v (terms.take i)
                    ((terms.drop (i + 1)).take (j - i - 1))
                    (terms.drop (j + 1)) terms[i].2
                    terms[i].1 terms[j].1 degree hle hform
                · exact h
              · exact h
            · exact h
          · exact h
        · exact h
      | none =>
        cases hlike : VeriPB.findLikeTermIdx terms with
        | some pair =>
          obtain ⟨i, j⟩ := pair
          simp only []
          -- Split through guards: hi, hj, hij, hlit
          split
          · split
            · split
              · split
                · next hi hj hij hlit =>
                  apply ih
                  have hlit_eq := Literal_beq_eq _ _ hlit
                  have hj_eq : terms[j] =
                      (terms[j].1, terms[i].2) :=
                    Prod.ext rfl hlit_eq
                  have hdecomp := list_two_point_decomp
                    terms i j hi hj hij
                  have hform :
                      (Constr.mk terms degree).sat v := h
                  rw [hdecomp, hj_eq] at hform
                  exact merge_terms_sat v (terms.take i)
                    ((terms.drop (i + 1)).take (j - i - 1))
                    (terms.drop (j + 1)) terms[i].2
                    terms[i].1 terms[j].1 degree hform
                · exact h
              · exact h
            · exact h
          · exact h
        | none => exact h

theorem normalize_sat (c : Constr) (v : Valuation) (h : c.sat v) :
    (VeriPB.normalizeConstr c).sat v := by
  simp only [VeriPB.normalizeConstr, Constr.sat] at *
  exact go_sat _ _ _ v h

instance : LawfulBEq Sat.PB.Literal where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;>
      simp only [BEq.beq, Sat.PB.instBEqLiteral.beq] at h <;>
      (try exact absurd h Bool.false_ne_true)
    all_goals exact congrArg _ (of_decide_eq_true h)
  rfl {a} := by
    cases a <;> simp only [BEq.beq, Sat.PB.instBEqLiteral.beq] <;>
      exact decide_eq_true trivial

/-! ### Reverse normalization (for constrInDB soundness) -/

private theorem cancel_pair_sat_rev (v : Valuation) (pre mid post : List Sat.PB.Term)
    (l : Sat.PB.Literal) (a b d : Nat) (hle : min a b ≤ d)
    (h : (Constr.mk (pre ++ (a - min a b, l) :: mid ++
      (b - min a b, l.negate) :: post) (d - min a b)).sat v) :
    (Constr.mk (pre ++ (a, l) :: mid ++ (b, l.negate) :: post) d).sat v := by
  simp only [Constr.sat] at *
  have hkey := Sat.PB.complementary_sum v l a b
  rw [Sat.PB.evalSum_append] at h ⊢
  simp only [Sat.PB.evalSum] at h ⊢
  rw [Sat.PB.evalSum_append] at h ⊢
  simp only [Sat.PB.evalSum] at h ⊢
  omega

private theorem remove_zero_sat_rev (v : Valuation) (pre post : List Sat.PB.Term)
    (l : Sat.PB.Literal) (d : Nat)
    (h : (Constr.mk (pre ++ post) d).sat v) :
    (Constr.mk (pre ++ (0, l) :: post) d).sat v := by
  simp only [Constr.sat] at *
  rw [Sat.PB.evalSum_append] at h ⊢
  simp only [Sat.PB.evalSum] at h ⊢
  omega

private theorem merge_terms_sat_rev (v : Valuation) (pre mid post : List Sat.PB.Term)
    (l : Sat.PB.Literal) (a b d : Nat)
    (h : (Constr.mk (pre ++ (a + b, l) :: mid ++ post) d).sat v) :
    (Constr.mk (pre ++ (a, l) :: mid ++ (b, l) :: post) d).sat v := by
  simp only [Constr.sat] at *
  rw [Sat.PB.evalSum_append] at h ⊢
  simp only [Sat.PB.evalSum] at h ⊢
  rw [Sat.PB.evalSum_append] at h ⊢
  simp only [Sat.PB.evalSum] at h ⊢
  have hm : (a + b) * Sat.PB.evalLit v l = a * Sat.PB.evalLit v l + b * Sat.PB.evalLit v l :=
    Nat.add_mul a b _
  omega

theorem go_sat_rev (fuel : Nat) (terms : List Sat.PB.Term) (degree : Nat)
    (v : Valuation) (h : (VeriPB.normalizeConstr.go fuel terms degree).sat v) :
    Sat.PB.evalSum v terms ≥ degree := by
  induction fuel generalizing terms degree with
  | zero => simp only [VeriPB.normalizeConstr.go] at h; exact h
  | succ n ih =>
    simp only [VeriPB.normalizeConstr.go] at h
    cases hzero : VeriPB.findZeroIdx terms with
    | some idx =>
      rw [hzero] at h
      have hidx := findZeroIdx_lt terms idx hzero
      have hcoeff := findZeroIdx_zero terms idx hidx hzero
      have hih := ih _ _ h
      rw [← evalSum_remove_zero v terms idx hidx hcoeff]; exact hih
    | none =>
      rw [hzero] at h
      cases hpair : VeriPB.findValidCompPairIdx terms degree with
      | some pair =>
        rw [hpair] at h
        obtain ⟨i, j⟩ := pair
        simp only [] at h
        split at h
        · split at h
          · split at h
            · split at h
              · split at h
                · next hi hj hij hlit hle =>
                  have hih := ih _ _ h
                  have hlit_eq := Literal_beq_eq _ _ hlit
                  have hj_eq : terms[j] =
                      (terms[j].1, terms[i].2.negate) :=
                    Prod.ext rfl hlit_eq
                  have hdecomp := list_two_point_decomp
                    terms i j hi hj hij
                  rw [hdecomp, hj_eq]
                  exact cancel_pair_sat_rev v (terms.take i)
                    ((terms.drop (i + 1)).take (j - i - 1))
                    (terms.drop (j + 1)) terms[i].2
                    terms[i].1 terms[j].1 degree hle hih
                · exact h
              · exact h
            · exact h
          · exact h
        · exact h
      | none =>
        rw [hpair] at h
        cases hlike : VeriPB.findLikeTermIdx terms with
        | some pair =>
          rw [hlike] at h
          obtain ⟨i, j⟩ := pair
          simp only [] at h
          split at h
          · split at h
            · split at h
              · split at h
                · next hi hj hij hlit =>
                  have hih := ih _ _ h
                  have hlit_eq := Literal_beq_eq _ _ hlit
                  have hj_eq : terms[j] =
                      (terms[j].1, terms[i].2) :=
                    Prod.ext rfl hlit_eq
                  have hdecomp := list_two_point_decomp
                    terms i j hi hj hij
                  rw [hdecomp, hj_eq]
                  exact merge_terms_sat_rev v (terms.take i)
                    ((terms.drop (i + 1)).take (j - i - 1))
                    (terms.drop (j + 1)) terms[i].2
                    terms[i].1 terms[j].1 degree hih
                · exact h
              · exact h
            · exact h
          · exact h
        | none => rw [hlike] at h; exact h

theorem normalize_sat_rev (c : Constr) (v : Valuation)
    (h : (VeriPB.normalizeConstr c).sat v) : c.sat v := by
  simp only [VeriPB.normalizeConstr, Constr.sat] at *
  exact go_sat_rev _ _ _ v h

private theorem evalSum_perm (v : Valuation) (l1 l2 : List Sat.PB.Term)
    (hp : l1.Perm l2) : Sat.PB.evalSum v l1 = Sat.PB.evalSum v l2 := by
  induction hp with
  | nil => rfl
  | cons x _ ih => simp [Sat.PB.evalSum]; omega
  | swap x y l => simp [Sat.PB.evalSum]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem constrMatchNorm_sat (c1 c2 : Constr) (v : Valuation)
    (h : constrMatchNorm c1 c2 = true) (hsat : c2.sat v) : c1.sat v := by
  unfold constrMatchNorm at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hdeg, _⟩, hterms⟩ := h
  simp only [Constr.sat] at hsat ⊢
  rw [hdeg]
  -- sorted term lists are equal → evalSum is equal
  let cmp := fun (a b : Nat × Sat.PB.Literal) =>
    Sat.PB.Literal.var a.2 < Sat.PB.Literal.var b.2 ||
    (Sat.PB.Literal.var a.2 == Sat.PB.Literal.var b.2 &&
     match a.2, b.2 with | .pos _, .neg _ => true | _, _ => false)
  have hp1 : (c1.terms.mergeSort cmp).Perm c1.terms :=
    List.mergeSort_perm c1.terms cmp
  have hp2 : (c2.terms.mergeSort cmp).Perm c2.terms :=
    List.mergeSort_perm c2.terms cmp
  have heq_sort : c1.terms.mergeSort cmp = c2.terms.mergeSort cmp :=
    hterms
  have h1 := evalSum_perm v _ _ hp1
  have h2 := evalSum_perm v _ _ hp2
  rw [heq_sort] at h1
  omega

/-- If `constrInDB c db = true` and all DB entries are satisfied by `v`,
    then `c` is satisfied by `v`. -/
private theorem constrInDB_sat (c : Constr) (db : Std.HashMap Nat Constr)
    (v : Valuation)
    (h : constrInDB c db = true)
    (hdb : ∀ id c, db.get? id = some c → Constr.sat c v) :
    Constr.sat c v := by
  unfold constrInDB at h
  have hany := List.any_eq_true.mp h
  obtain ⟨⟨id, dbC⟩, hmem, hmatch⟩ := hany
  -- dbC is in the DB and its normalized form matches c's normalized form
  have hget : db.get? id = some dbC := by
    rw [Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem
  have hdbC_sat := hdb id dbC hget
  -- Chain: dbC.sat v → (normalize dbC).sat v → (normalize c).sat v → c.sat v
  have h1 := normalize_sat dbC v hdbC_sat
  -- hmatch : constrMatchNorm (normalize c) (normalize dbC) = true
  -- constrMatchNorm_sat gives c1.sat from c2.sat, so (normalize c).sat v
  have h2 := constrMatchNorm_sat (VeriPB.normalizeConstr c)
    (VeriPB.normalizeConstr dbC) v hmatch h1
  exact normalize_sat_rev c v h2

-- execPolOps soundness: each pol operation preserves implication

/-- All constraints on a stack are implied by the original formula. -/
def StackSound (original : Array Constr) (_db : Std.HashMap Nat Constr)
    (stack : List VeriPB.StackElem) : Prop :=
  ∀ se ∈ stack, match se with
    | .constr c => ∀ v : Valuation,
        (∀ c' ∈ original.toList, Constr.sat c' v) → Constr.sat c v
    | .nat _ => True

-- StackSound helpers
private theorem StackSound_cons_constr (original : Array Constr)
    (db : Std.HashMap Nat Constr) (c : Constr)
    (stack : List VeriPB.StackElem)
    (hstack : StackSound original db stack)
    (hc : ∀ v : Valuation,
      (∀ c' ∈ original.toList, Constr.sat c' v) → Constr.sat c v) :
    StackSound original db (.constr c :: stack) := by
  intro se hse
  cases hse with
  | head => exact hc
  | tail _ h => exact hstack se h

private theorem StackSound_cons_nat (original : Array Constr)
    (db : Std.HashMap Nat Constr) (n : Nat)
    (stack : List VeriPB.StackElem)
    (hstack : StackSound original db stack) :
    StackSound original db (.nat n :: stack) := by
  intro se hse
  cases hse with
  | head => exact True.intro
  | tail _ h => exact hstack se h

private theorem StackSound_tail (original : Array Constr)
    (db : Std.HashMap Nat Constr) (x : VeriPB.StackElem)
    (stack : List VeriPB.StackElem)
    (h : StackSound original db (x :: stack)) :
    StackSound original db stack :=
  fun se hse => h se (.tail _ hse)

private theorem StackSound_head_constr (original : Array Constr)
    (db : Std.HashMap Nat Constr) (c : Constr)
    (stack : List VeriPB.StackElem)
    (h : StackSound original db (.constr c :: stack)) :
    ∀ v : Valuation,
      (∀ c' ∈ original.toList, Constr.sat c' v) → Constr.sat c v :=
  h (.constr c) (.head _)

private theorem findAndRemove_sat (c : Constr) (varIdx : Nat)
    (pre : List Term) (remaining : List Term) (result : Constr)
    (v : Valuation)
    (hfind : VeriPB.weakenConstr.findAndRemove c varIdx pre remaining =
      .ok result)
    (hsat : Sat.PB.evalSum v (pre.reverse ++ remaining) ≥ c.degree) :
    result.sat v := by
  induction remaining generalizing pre with
  | nil => simp [VeriPB.weakenConstr.findAndRemove] at hfind
  | cons term rest ih =>
    obtain ⟨a, l⟩ := term
    simp only [VeriPB.weakenConstr.findAndRemove] at hfind
    by_cases hvar : l.var == varIdx
    · simp only [hvar, ite_true] at hfind
      by_cases hle : a ≤ c.degree
      · simp only [hle, ite_true] at hfind
        injection hfind with hfind; rw [← hfind]
        exact weaken_term_sat v pre.reverse rest a l c.degree hle hsat
      · simp [hle] at hfind
    · simp only [hvar] at hfind
      apply ih ((a, l) :: pre) hfind
      rw [List.reverse_cons, List.append_assoc]
      exact hsat

private theorem weakenConstr_sat (c : Constr) (varIdx : Nat)
    (result : Constr) (v : Valuation)
    (h : VeriPB.weakenConstr c varIdx = .ok result)
    (hsat : c.sat v) : result.sat v := by
  unfold VeriPB.weakenConstr at h
  exact findAndRemove_sat c varIdx [] c.terms result v h
    (by simp; exact hsat)

theorem execPolOne_sound (db : Std.HashMap Nat Constr)
    (original : Array Constr) (stack stack' : List VeriPB.StackElem)
    (op : VeriPB.PolOp)
    (hsound : DBSound original db)
    (hstack : StackSound original db stack)
    (hexec : execPolOne db stack op = some stack') :
    StackSound original db stack' := by
  cases op with
  | pushId id =>
    simp only [execPolOne] at hexec
    match hdb : db[id]? with
    | some c =>
      simp [hdb] at hexec; subst hexec
      exact StackSound_cons_constr _ _ c stack hstack fun v hsat =>
        hsound id c (by rwa [Std.HashMap.get?_eq_getElem?]) v hsat
    | none => simp [hdb] at hexec
  | pushNat n =>
    simp only [execPolOne] at hexec
    injection hexec with hexec; subst hexec
    exact StackSound_cons_nat _ _ n stack hstack
  | pushLitAxiom lit =>
    simp only [execPolOne] at hexec
    match hlit : VeriPB.opbLitToPB lit with
    | .ok pbLit =>
      simp [hlit] at hexec; subst hexec
      exact StackSound_cons_constr _ _ _ stack hstack fun v _ => by
        simp [Constr.sat, Sat.PB.evalSum]
    | .error _ => simp [hlit] at hexec
  | add =>
    simp only [execPolOne] at hexec
    match stack, hstack with
    | .constr c2 :: .constr c1 :: rest, hstack =>
      simp at hexec; subst hexec
      have h1 := StackSound_head_constr _ _ c1 rest
        (StackSound_tail _ _ _ _ hstack)
      have h2 := StackSound_head_constr _ _ c2 _ hstack
      exact StackSound_cons_constr _ _ _ rest
        (StackSound_tail _ _ _ _ (StackSound_tail _ _ _ _ hstack))
        fun v hsat => add_sat c1 c2 v (h1 v hsat) (h2 v hsat)
    | [], _ | [_], _ | .nat _ :: _, _
    | .constr _ :: .nat _ :: _, _ => simp at hexec
  | mul =>
    simp only [execPolOne] at hexec
    match stack, hstack with
    | .nat k :: .constr c :: rest, hstack =>
      simp at hexec; subst hexec
      have hc := StackSound_head_constr _ _ c rest
        (StackSound_tail _ _ _ _ hstack)
      exact StackSound_cons_constr _ _ _ rest
        (StackSound_tail _ _ _ _ (StackSound_tail _ _ _ _ hstack))
        fun v hsat => mul_sat c k v (hc v hsat)
    | [], _ | [_], _ | .constr _ :: _, _
    | .nat _ :: .nat _ :: _, _ => simp at hexec
  | div =>
    simp only [execPolOne] at hexec
    match stack, hstack with
    | .nat k :: .constr c :: rest, hstack =>
      by_cases hk : k == 0
      · simp [hk] at hexec
      · simp [hk] at hexec; subst hexec
        have hc := StackSound_head_constr _ _ c rest
          (StackSound_tail _ _ _ _ hstack)
        have hkpos : 0 < k := by
          simp [beq_iff_eq] at hk; omega
        exact StackSound_cons_constr _ _ _ rest
          (StackSound_tail _ _ _ _ (StackSound_tail _ _ _ _ hstack))
          fun v hsat => div_sat _ k hkpos v
            (normalize_sat c v (hc v hsat))
    | [], _ | [_], _ | .constr _ :: _, _ => simp at hexec
    | .nat _ :: .nat _ :: _, _ => simp at hexec
  | saturate =>
    simp only [execPolOne] at hexec
    match stack, hstack with
    | .constr c :: rest, hstack =>
      simp at hexec; subst hexec
      have hc := StackSound_head_constr _ _ c rest hstack
      exact StackSound_cons_constr _ _ _ rest
        (StackSound_tail _ _ _ _ hstack)
        fun v hsat => saturate_sat _ v (normalize_sat c v (hc v hsat))
    | [], _ | .nat _ :: _, _ => simp at hexec
  | weaken varName =>
    -- Weaken: remove a variable term, reduce degree
    unfold execPolOne at hexec
    match stack, hstack with
    | .constr c :: rest, hstack =>
      have hc := StackSound_head_constr _ _ c rest hstack
      have htail := StackSound_tail _ _ _ _ hstack
      simp only [] at hexec
      split at hexec
      · -- varName.startsWith "x" = true
        split at hexec
        · -- toNat? = some n
          rename_i nVal _
          split at hexec
          · -- nVal > 0
            match hweak : VeriPB.weakenConstr c (nVal - 1) with
            | .ok result =>
              simp only [hweak] at hexec
              injection hexec with hexec; subst hexec
              exact StackSound_cons_constr _ _ _ rest htail
                fun v hsat => weakenConstr_sat c (nVal - 1) result v
                  hweak (hc v hsat)
            | .error _ => simp [hweak] at hexec
          · exact absurd hexec (by simp)
        · exact absurd hexec (by simp)
      · exact absurd hexec (by simp)
    | [], _ | .nat _ :: _, _ => exact absurd hexec (by simp)

theorem execPolOps_sound (db : Std.HashMap Nat Constr)
    (original : Array Constr) (ops : List VeriPB.PolOp)
    (stack stack' : List VeriPB.StackElem)
    (hsound : DBSound original db)
    (hstack : StackSound original db stack)
    (hexec : execPolOps db ops stack = some stack') :
    StackSound original db stack' := by
  induction ops generalizing stack with
  | nil => simp [execPolOps] at hexec; subst hexec; exact hstack
  | cons op rest ih =>
    simp only [execPolOps] at hexec
    match hone : execPolOne db stack op with
    | some s =>
      simp [hone] at hexec
      exact ih s (execPolOne_sound db original stack s op hsound hstack
        hone) hexec
    | none => simp [hone] at hexec

theorem execPolRPNBool_implied (ops : List VeriPB.PolOp)
    (db : Std.HashMap Nat Constr) (original : Array Constr) (c : Constr)
    (hsound : DBSound original db)
    (hpol : execPolRPNBool ops db = some c) :
    ∀ v : Valuation,
      (∀ c' ∈ original.toList, Constr.sat c' v) → Constr.sat c v := by
  simp only [execPolRPNBool] at hpol
  -- execPolOps returns some [.constr c]
  match hexec : execPolOps db ops [] with
  | some [.constr c'] =>
    simp [hexec] at hpol; subst hpol
    have hss : StackSound original db [.constr c'] :=
      execPolOps_sound db original ops [] [.constr c'] hsound
        (fun _ h => nomatch h) hexec
    intro v hsat
    exact hss (.constr c') (List.Mem.head _) v hsat
  | some [] => simp [hexec] at hpol
  | some (.nat _ :: _) => simp [hexec] at hpol
  | some (.constr _ :: _ :: _) => simp [hexec] at hpol
  | none => simp [hexec] at hpol

-- combineHintsRec soundness

/-- A constraint is a consequence of the original formula and the
    negated constraint. -/
def ImpliedByDBAndNeg (original : Array Constr) (_db : Std.HashMap Nat Constr)
    (negConstr c : Constr) : Prop :=
  ∀ v : Valuation, (∀ c' ∈ original.toList, Constr.sat c' v) →
    negConstr.sat v → Constr.sat c v

theorem combineHintsRec_sound (original : Array Constr)
    (db : Std.HashMap Nat Constr) (negConstr acc : Constr)
    (hints : List Constr)
    (hacc : ImpliedByDBAndNeg original db negConstr acc)
    (hhints : ∀ h ∈ hints,
      ImpliedByDBAndNeg original db negConstr h) :
    ImpliedByDBAndNeg original db negConstr
      (combineHintsRec acc hints) := by
  induction hints generalizing acc with
  | nil => simp [combineHintsRec]; exact hacc
  | cons hintC rest ih =>
    simp only [combineHintsRec]
    by_cases hcontra : acc.isContra
    · simp [hcontra]; exact hacc
    · simp [hcontra]
      apply ih
      · -- Combined constraint is implied
        intro v hsat hneg
        have hacc_sat := hacc v hsat hneg
        have hhint_sat := hhints hintC (List.Mem.head _) v hsat hneg
        -- The combination of two satisfied constraints is satisfied
        match findCompLitPairBool acc hintC with
        | some (ca, ch) =>
          simp only []
          apply normalize_sat
          show (VeriPB.addConstrs _ _).sat v
          simp only [VeriPB.addConstrs, Constr.sat, Sat.PB.evalSum_append]
          simp only [Constr.sat] at hacc_sat hhint_sat
          -- mulConstr preserves satisfaction
          by_cases hch : ch = 1 <;> by_cases hca : ca = 1 <;>
            simp only [hch, hca, ite_true, ite_false] <;>
            exact Nat.add_le_add
              (by first | exact hacc_sat
                        | exact mul_sat acc ch v hacc_sat)
              (by first | exact hhint_sat
                        | exact mul_sat hintC ca v hhint_sat)
        | none =>
          simp only []
          apply normalize_sat
          show (VeriPB.addConstrs acc hintC).sat v
          simp only [VeriPB.addConstrs, Constr.sat, Sat.PB.evalSum_append]
          simp only [Constr.sat] at hacc_sat hhint_sat; omega
      · exact fun h hm => hhints h (List.Mem.tail _ hm)

private theorem resolveHint_implied (negConstr : Constr)
    (db : Std.HashMap Nat Constr) (original : Array Constr)
    (h : VeriPB.RupHint) (rc : Constr)
    (hsound : DBSound original db)
    (hres : resolveHint negConstr db h = some rc) :
    ImpliedByDBAndNeg original db negConstr rc := by
  cases h with
  | negC =>
    simp [resolveHint] at hres; subst hres
    exact fun _ _ hneg => hneg
  | id n =>
    simp [resolveHint] at hres
    exact fun v horiginal _ =>
      hsound n rc (by rwa [Std.HashMap.get?_eq_getElem?]) v horiginal

-- Extract properties from verifyRupExtract succeeding
private theorem verifyRupExtract_props (negConstr : Constr)
    (hints : List VeriPB.RupHint) (db : Std.HashMap Nat Constr)
    (numVars : Nat) (conflictC : Constr) (otherHints : List Constr)
    (hext : verifyRupExtract negConstr hints db numVars =
      some (conflictC, otherHints)) :
    (∃ rh : VeriPB.RupHint,
      resolveHint negConstr db rh = some conflictC) ∧
    (∀ rc ∈ otherHints, ∃ rh : VeriPB.RupHint,
      resolveHint negConstr db rh = some rc) := by
  -- Use match to case-split, preserving equations
  match hempty : hints.isEmpty with
  | true =>
    simp only [verifyRupExtract, hempty] at hext; cases hext
  | false =>
    match hfind : findConflictHintBool negConstr hints db numVars
    with
    | none =>
      simp only [verifyRupExtract, hempty, hfind] at hext
      cases hext
    | some conflictIdx =>
      match hres : resolveHint negConstr db
          (hints.toArray[conflictIdx]!) with
      | none =>
        -- verifyRupExtract returns none when resolveHint = none
        unfold verifyRupExtract at hext
        simp only [hempty, Bool.false_eq_true, ↓reduceIte,
          hfind] at hext
        split at hext
        · cases hext  -- none branch: none ≠ some
        · rename_i _ _ heq_c
          rw [hres] at heq_c; cases heq_c
      | some conflictC' =>
        unfold verifyRupExtract at hext
        simp only [hempty, Bool.false_eq_true, ↓reduceIte,
          hfind, hres] at hext
        injection hext with heq_pair
        injection heq_pair with h1 h2
        constructor
        · exact ⟨hints.toArray[conflictIdx]!,
            h1 ▸ hres⟩
        · rw [← h2]; intro rc hrc
          simp only [List.mem_filterMap] at hrc
          obtain ⟨i, _, hfi⟩ := hrc
          split at hfi
          · cases hfi
          · exact ⟨hints.toArray[i]!, hfi⟩

theorem verifyRupBool_implied (negConstr : Constr)
    (hints : List VeriPB.RupHint) (db : Std.HashMap Nat Constr)
    (numVars : Nat) (original : Array Constr) (c : Constr)
    (hsound : DBSound original db) (hcs : c.degree ≤ c.coeffSum)
    (hrup : verifyRupBool negConstr hints db numVars = true)
    (hneg : negConstr = c.negate) :
    ∀ v : Valuation,
      (∀ c' ∈ original.toList, Constr.sat c' v) → Constr.sat c v := by
  intro v horiginal
  apply Classical.byContradiction; intro hn
  have hneg_sat : negConstr.sat v := by
    rw [hneg]; exact negate_sat_of_not_sat c v hcs hn
  simp only [verifyRupBool] at hrup
  match hext : verifyRupExtract negConstr hints db numVars with
  | none => simp [hext] at hrup
  | some (conflictC, otherHints) =>
    simp only [hext] at hrup
    obtain ⟨⟨rh, hres⟩, hother⟩ :=
      verifyRupExtract_props negConstr hints db numVars
        conflictC otherHints hext
    have hconf := resolveHint_implied negConstr db original rh
      conflictC hsound hres
    have hnorm : ImpliedByDBAndNeg original db negConstr
        (VeriPB.normalizeConstr conflictC) :=
      fun v' hsat' hneg' =>
        normalize_sat conflictC v' (hconf v' hsat' hneg')
    have hothers : ∀ h ∈ otherHints,
        ImpliedByDBAndNeg original db negConstr h := by
      intro rc hrc
      obtain ⟨rh', hres'⟩ := hother rc hrc
      exact resolveHint_implied negConstr db original rh' rc
        hsound hres'
    have hresult := combineHintsRec_sound original db negConstr
      _ _ hnorm hothers
    simp [Constr.isContra] at hrup
    exact absurd (hresult v horiginal hneg_sat)
      (contra_unsat _ v hrup)

-- Main soundness chain

-- Monotonicity: weakening the original formula preserves DBSound

-- execStepsFuel_sound removed: checkProof_sound now uses execStepsFuel_sat_preserve
/-- If ¬(c.negate.sat v) and c.degree ≤ c.coeffSum, then c.sat v. -/
private theorem sat_of_not_negate_sat (c : Constr) (v : Valuation)
    (hd : c.degree ≤ c.coeffSum) (h : ¬ c.negate.sat v) : c.sat v :=
  Classical.byContradiction fun hn => h (negate_sat_of_not_sat c v hd hn)

/-- Resolve a goal ID to its constraint, mirroring processRedGoalsBool. -/
-- checkRedCoverage soundness: if coverage passes, every affected DB entry
-- is either listed as a numeric goal or auto-satisfied.
private theorem checkRedCoverage_sound
    (origConstrs : Array Constr)
    (subst : List (Nat × Sat.PB.SubstVal))
    (savedDb : Std.HashMap Nat Constr)
    (goals : List (String × Array VeriPB.ProofStep × Nat))
    (hcov : checkRedCoverage origConstrs subst savedDb goals = true)
    (id : Nat) (G : Constr)
    (hmem : savedDb.get? id = some G)
    (haff : Sat.PB.termsAffected subst G.terms = true) :
    (goals.filterMap fun (gid, _, _) =>
      if gid.startsWith "#" then none else gid.toNat?).contains id = true ∨
    constrInDB (Sat.PB.applySubstConstr subst G) savedDb = true := by
  unfold checkRedCoverage at hcov
  by_cases hh : goals.any fun g => g.1.startsWith "#"
  · simp only [hh] at hcov
    -- hcov : savedDb.toList.all (fun (id, c) => ...) = true
    have hmem_list : (id, G) ∈ savedDb.toList := by
      rw [Std.HashMap.get?_eq_getElem?] at hmem
      exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hmem
    have hall := List.all_eq_true.mp hcov (id, G) hmem_list
    simp only [haff, ite_true] at hall
    exact Bool.or_eq_true_iff.mp hall
  · simp [hh] at hcov

private def resolveGoalConstr (goalId : String)
    (subst : List (Nat × Sat.PB.SubstVal)) (pbConstr : Constr)
    (savedDb : Std.HashMap Nat Constr) : Option Constr :=
  if goalId.startsWith "#" then some (Sat.PB.applySubstConstr subst pbConstr)
  else match goalId.toNat? with
  | some dbId => match savedDb[dbId]? with
    | some c => some (Sat.PB.applySubstConstr subst c)
    | none => none
  | none => none

/-- Each goal in processRedGoalsBool is implied by redDb: if
    processRedGoalsBool succeeds and v satisfies all redDb entries,
    then every resolved goal constraint is satisfied by v. -/
private theorem processRedGoalsBool_goalSat
    (execFn : BoolCheckState → List VeriPB.ProofStep → Option BoolCheckState)
    (execFn_sound : ∀ st st' steps,
      DBSat st.db → execFn st steps = some st' → DBSat st'.db)
    (origConstrs : Array Constr) (numVars formulaSize : Nat)
    (subst : List (Nat × Sat.PB.SubstVal)) (pbConstr : Constr)
    (savedDb redDb : Std.HashMap Nat Constr)
    (goals : List (String × Array VeriPB.ProofStep × Nat))
    (nextId : Nat) (finalNextId : Nat)
    (hres : processRedGoalsBool execFn origConstrs numVars formulaSize
        subst pbConstr savedDb redDb goals nextId = some finalNextId)
    (v : Valuation) (hredDb : ∀ id c, redDb.get? id = some c → Constr.sat c v) :
    ∀ (goalId : String) (innerSteps : Array VeriPB.ProofStep) (resultId : Nat),
      (goalId, innerSteps, resultId) ∈ goals →
      ∀ gc : Constr,
        resolveGoalConstr goalId subst pbConstr savedDb = some gc →
        gc.sat v := by
  induction goals generalizing nextId with
  | nil => intro _ _ _ hmem; exact absurd hmem (by simp)
  | cons goal rest ih =>
    obtain ⟨gid, gsteps, gresult⟩ := goal
    intro goalId innerSteps resultId hmem gc hresolve
    -- Unfold processRedGoalsBool for the head
    simp only [processRedGoalsBool] at hres
    -- The head goal's constraint resolution
    have hgc_head : resolveGoalConstr gid subst pbConstr savedDb =
        (if gid.startsWith "#" then some (Sat.PB.applySubstConstr subst pbConstr)
         else match gid.toNat? with
              | some dbId => match savedDb[dbId]? with
                             | some c => some (Sat.PB.applySubstConstr subst c)
                             | none => none
              | none => none) := rfl
    -- Match on the head goal's constraint resolution in the execution
    match hgc_exec : (if gid.startsWith "#" then
        some (Sat.PB.applySubstConstr subst pbConstr)
      else match gid.toNat? with
        | some dbId => match savedDb[dbId]? with
          | some c => some (Sat.PB.applySubstConstr subst c)
          | none => none
        | none => none) with
    | none => simp [hgc_exec] at hres
    | some goalConstr =>
      simp only [hgc_exec] at hres
      -- Degree check passes (otherwise hres is absurd)
      by_cases hdeg_gc : goalConstr.degree > goalConstr.coeffSum
      · simp [hdeg_gc] at hres
      · simp [hdeg_gc] at hres
        have hdeg_gc' : goalConstr.degree ≤ goalConstr.coeffSum :=
          Nat.le_of_not_lt hdeg_gc
        -- Inner proof execution
        match hexec : execFn
          { db := redDb.insert nextId goalConstr.negate, origConstrs,
            nextId := nextId + 1, numVars, formulaSize }
          gsteps.toList with
      | none => simp [hexec] at hres
      | some finalSub =>
        simp only [hexec] at hres
        match hresult : finalSub.db[gresult]? with
        | none => simp [hresult] at hres
        | some c =>
          simp only [hresult] at hres
          by_cases hcontra : c.isContra
          · -- isContra = true: inner proof found contradiction
            simp only [hcontra] at hres
            -- hres : processRedGoalsBool ... rest ... = some finalNextId
            -- This means goalDb = redDb + goalConstr.negate is unsatisfiable
            have hgoalDbUnsat : ¬ DBSat (redDb.insert nextId goalConstr.negate) := by
              intro ⟨w, hw⟩
              have hfinalSat : DBSat finalSub.db :=
                execFn_sound _ _ _ ⟨w, hw⟩ hexec
              obtain ⟨u, hu⟩ := hfinalSat
              exact contra_unsat c u (by
                  simp [Constr.isContra] at hcontra; exact hcontra)
                (hu gresult c (by rwa [Std.HashMap.get?_eq_getElem?]))
            -- Case: is this the head goal or a rest goal?
            cases hmem with
            | head =>
              -- This IS the head goal: goalId = gid, so resolve matches
              rw [hgc_head, hgc_exec] at hresolve
              injection hresolve with hresolve; subst hresolve
              -- goalConstr.sat v from unsatisfiability of goalDb
              apply sat_of_not_negate_sat goalConstr v hdeg_gc'
              intro hneg_sat
              exact hgoalDbUnsat ⟨v, fun id' c' hget => by
                rw [HashMap_get?_insert] at hget
                by_cases heq : nextId == id'
                · simp [heq] at hget; subst hget; exact hneg_sat
                · simp [heq] at hget; exact hredDb id' c' hget⟩
            | tail _ hmem' =>
              -- This is a rest goal — use IH
              exact ih _ hres goalId innerSteps resultId hmem' gc hresolve
          · simp [hcontra] at hres

/-- Main soundness theorem: proof execution preserves DB satisfiability.
    Replaces execStepsFuel_sound with a weaker but red-compatible invariant. -/
theorem execStepsFuel_sat_preserve : ∀ (fuel : Nat)
    (state state' : BoolCheckState) (steps : List VeriPB.ProofStep),
    DBSat state.db →
    execStepsFuel fuel state steps = some state' →
    DBSat state'.db := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih_fuel =>
    intro state state' steps hsat hsteps
    induction steps generalizing state with
    | nil =>
      unfold execStepsFuel at hsteps
      injection hsteps with h; subst h; exact hsat
    | cons step rest ih_rest =>
      unfold execStepsFuel at hsteps
      simp only [] at hsteps
      cases step with
      | formulaSize n =>
        by_cases hfs : state.formulaSize != n
        · simp [hfs] at hsteps
        · simp [hfs] at hsteps; exact ih_rest state hsat hsteps
      | pol ops =>
        match hpol : execPolRPNBool ops state.db with
        | some result =>
          simp [hpol] at hsteps
          -- Bridge: pol result is implied by DB
          apply ih_rest _ _ hsteps
          apply DBSat_insert_dbImplied state.db state.nextId
            (VeriPB.normalizeConstr result) hsat
          intro v hdb
          exact normalize_sat result v
            (execPolRPNBool_implied ops state.db ⟨state.db.toList.map Prod.snd⟩
              result (DBSound_of_toList state.db) hpol v
              (toList_sat_of_DBSat state.db v hdb))
        | none => simp [hpol] at hsteps
      | rup constr hints =>
        match hparse : VeriPB.opbConstrToPB constr with
        | .ok pbConstr =>
          simp [hparse] at hsteps
          by_cases hcs : pbConstr.degree > pbConstr.coeffSum
          · simp [hcs] at hsteps
          · simp [hcs] at hsteps
            by_cases hrup : verifyRupBool pbConstr.negate hints
                state.db state.numVars = false
            · simp [hrup] at hsteps
            · simp [hrup] at hsteps
              have hcs' : pbConstr.degree ≤ pbConstr.coeffSum :=
                Nat.le_of_not_lt hcs
              have hrup' : verifyRupBool pbConstr.negate hints
                  state.db state.numVars = true := by
                cases h : verifyRupBool pbConstr.negate hints
                    state.db state.numVars
                · exact absurd h hrup
                · rfl
              apply ih_rest _ _ hsteps
              apply DBSat_insert_dbImplied state.db state.nextId
                (VeriPB.normalizeConstr pbConstr) hsat
              intro v hdb
              exact normalize_sat pbConstr v
                (verifyRupBool_implied pbConstr.negate hints state.db
                  state.numVars ⟨state.db.toList.map Prod.snd⟩ pbConstr
                  (DBSound_of_toList state.db) hcs' hrup' rfl v
                  (toList_sat_of_DBSat state.db v hdb))
        | .error _ => simp [hparse] at hsteps
      | pbc constr innerSteps resultId =>
        -- Proof by contradiction: inner proof with ¬C derives contradiction
        by_cases hany : innerSteps.any (fun s => match s with
            | .conclusion _ | .output => true | _ => false)
        · simp [hany] at hsteps
        · simp [hany] at hsteps
          match fuel with
          | 0 => simp at hsteps
          | n + 1 =>
            match hparse : VeriPB.opbConstrToPB constr with
            | .ok pbConstr =>
              simp [hparse] at hsteps
              by_cases hcs : pbConstr.degree > pbConstr.coeffSum
              · simp [hcs] at hsteps
              · simp [hcs] at hsteps
                have hcs' : pbConstr.degree ≤ pbConstr.coeffSum :=
                  Nat.le_of_not_lt hcs
                match hinner :
                    execStepsFuel n
                      { state with
                        db := state.db.insert state.nextId pbConstr.negate
                        nextId := state.nextId + 1 }
                      innerSteps.toList with
                | some finalSub =>
                  simp [hinner] at hsteps
                  match hres : finalSub.db[resultId]? with
                  | some c =>
                    simp [hres] at hsteps
                    by_cases hcontra : c.isContra
                    · simp [hcontra] at hsteps
                      -- PBC soundness via DBSat
                      -- Key: if DB is satisfiable, adding ¬C can't lead to
                      -- contradiction unless C was already implied by DB
                      apply ih_rest _ _ hsteps
                      apply DBSat_insert_dbImplied state.db finalSub.nextId
                        (VeriPB.normalizeConstr pbConstr) hsat
                      intro v hdb
                      apply normalize_sat
                      -- Show C.sat v by contradiction: if ¬C.sat v, then
                      -- DB + ¬C is satisfiable, but inner proof shows it's not
                      apply sat_of_not_negate_sat pbConstr v hcs'
                      intro hneg_sat
                      -- v satisfies state.db + pbConstr.negate
                      have hinnerSat : DBSat
                          (state.db.insert state.nextId pbConstr.negate) := by
                        exact ⟨v, fun id' c' hget => by
                          rw [HashMap_get?_insert] at hget
                          by_cases heq : state.nextId == id'
                          · simp [heq] at hget; subst hget; exact hneg_sat
                          · simp [heq] at hget; exact hdb id' c' hget⟩
                      -- But inner proof execution preserves DBSat
                      have hfinalSat : DBSat finalSub.db :=
                        ih_fuel n (by omega) _ finalSub innerSteps.toList
                          hinnerSat hinner
                      -- Yet finalSub.db has contradictory c
                      obtain ⟨w, hw⟩ := hfinalSat
                      exact contra_unsat c w (by
                        simp [Constr.isContra] at hcontra; exact hcontra)
                        (hw resultId c (by rwa [Std.HashMap.get?_eq_getElem?]))
                    · simp [hcontra] at hsteps
                  | none => simp [hres] at hsteps
                | none => simp [hinner] at hsteps
            | .error _ => simp [hparse] at hsteps
      | red constr substPairs goals =>
        -- Red/dom: equisatisfiable constraint addition
        -- If v satisfies DB but not C, construct ω(v) satisfying DB + C
        match fuel with
        | 0 => simp at hsteps
        | n + 1 =>
          match hparse : VeriPB.opbConstrToPB constr with
          | .error _ => simp [hparse] at hsteps
          | .ok pbConstr =>
            simp [hparse] at hsteps
            by_cases hcs : pbConstr.degree > pbConstr.coeffSum
            · simp [hcs] at hsteps
            · simp [hcs] at hsteps
              have hcs' : pbConstr.degree ≤ pbConstr.coeffSum :=
                Nat.le_of_not_lt hcs
              match hsubst : VeriPB.parseSubstPairs substPairs state.numVars with
              | .error _ => simp [hsubst] at hsteps
              | .ok subst =>
                simp [hsubst] at hsteps
                by_cases hcov :
                    checkRedCoverage state.origConstrs subst state.db
                      goals.toList
                · -- Coverage check passes
                  simp [hcov] at hsteps
                  -- Match on processRedGoalsBool result
                  match hgoals :
                      processRedGoalsBool (execStepsFuel n)
                        state.origConstrs state.numVars state.formulaSize
                        subst pbConstr state.db
                        (state.db.insert state.nextId pbConstr.negate)
                        goals.toList (state.nextId + 1) with
                  | none => simp [hgoals] at hsteps
                  | some finalNextId =>
                    simp [hgoals] at hsteps
                    -- restoredDb = savedDb.insert finalNextId (normalizeConstr C)
                    -- Need: DBSat restoredDb
                    apply ih_rest _ _ hsteps
                    -- Get satisfying assignment from DBSat
                    obtain ⟨v, hv⟩ := hsat
                    -- Case split: does v satisfy C?
                    by_cases hC : pbConstr.sat v
                    · -- Easy case: v ⊨ C, so v also satisfies restoredDb
                      exact ⟨v, fun id' c' hget => by
                        rw [HashMap_get?_insert] at hget
                        by_cases heq : finalNextId == id'
                        · simp [heq] at hget; subst hget
                          exact normalize_sat pbConstr v hC
                        · simp [heq] at hget; exact hv id' c' hget⟩
                    · -- Hard case: v ⊭ C, construct witness ω(v)
                      let ω := Sat.PB.applyValuation subst v
                      -- v satisfies ¬C
                      have hnegC : pbConstr.negate.sat v :=
                        negate_sat_of_not_sat pbConstr v hcs' hC
                      -- v satisfies redDb = state.db + ¬C
                      have hredDb : ∀ id c,
                          (state.db.insert state.nextId pbConstr.negate).get?
                            id = some c → Constr.sat c v := by
                        intro id' c' hget
                        rw [HashMap_get?_insert] at hget
                        by_cases heq : state.nextId == id'
                        · simp [heq] at hget; subst hget; exact hnegC
                        · simp [heq] at hget; exact hv id' c' hget
                      -- Goal proofs: each goal constraint satisfied by v
                      have hgoalsSat := processRedGoalsBool_goalSat
                        (execStepsFuel n)
                        (fun st st' steps hdbsat hexec =>
                          ih_fuel n (by omega) st st' steps hdbsat hexec)
                        state.origConstrs state.numVars state.formulaSize
                        subst pbConstr state.db
                        (state.db.insert state.nextId pbConstr.negate)
                        goals.toList (state.nextId + 1) finalNextId
                        hgoals v hredDb
                      -- Witness ω(v) satisfies restoredDb
                      refine ⟨ω, fun id' c' hget => ?_⟩
                      rw [HashMap_get?_insert] at hget
                      by_cases heq : finalNextId == id'
                      · -- c' = normalizeConstr C
                        simp [heq] at hget; subst hget
                        apply normalize_sat
                        -- '#' goal: extract from coverage (hasHashGoal)
                        -- and apply hgoalsSat + applySubstConstr_sat_rev
                        apply Sat.PB.applySubstConstr_sat_rev subst pbConstr v
                        -- Need: (applySubstConstr subst pbConstr).sat v
                        -- Extract the '#' goal from goals list
                        unfold checkRedCoverage at hcov
                        have hhasHash : (goals.toList.any fun g =>
                            g.1.startsWith "#") = true := by
                          by_cases h : goals.toList.any fun g =>
                              g.1.startsWith "#"
                          · exact h
                          · simp [h] at hcov
                        obtain ⟨⟨gid, gsteps, gresult⟩, hmem, hstart⟩ :=
                          List.any_eq_true.mp hhasHash
                        exact hgoalsSat gid gsteps gresult hmem
                          (Sat.PB.applySubstConstr subst pbConstr)
                          (by simp [resolveGoalConstr, hstart])
                      · -- c' ∈ savedDb, need ω(v) ⊨ c'
                        simp [heq] at hget
                        by_cases haff :
                            Sat.PB.termsAffected subst c'.terms = true
                        · -- c' is affected by substitution
                          -- By coverage: either goal or auto-satisfied
                          have hcov_entry := checkRedCoverage_sound
                            state.origConstrs subst state.db goals.toList
                            hcov id' c' hget haff
                          -- In either case, v ⊨ c'|σ, then ω(v) ⊨ c'
                          apply Sat.PB.applySubstConstr_sat_rev subst c' v
                          rcases hcov_entry with hgoal_id | hauto
                          · -- Goal covers this entry: goalIds.contains id'
                            have hmem_id := List.contains_iff_mem.mp hgoal_id
                            obtain ⟨⟨gid, gsteps, gresult⟩, hmem_goals, hfilter⟩ :=
                              List.mem_filterMap.mp hmem_id
                            -- hfilter: (if gid.startsWith "#" then none else gid.toNat?) = some id'
                            by_cases hh : gid.startsWith "#" = true
                            · simp [hh] at hfilter
                            · simp [Bool.eq_false_iff.mpr hh] at hfilter
                              -- hfilter : gid.toNat? = some id'
                              exact hgoalsSat gid gsteps gresult hmem_goals
                                (Sat.PB.applySubstConstr subst c') (by
                                  unfold resolveGoalConstr
                                  simp [hh, hfilter]
                                  rw [show state.db[id']? = state.db.get? id'
                                    from by simp [Std.HashMap.get?_eq_getElem?]]
                                  simp [hget])
                          · -- Auto-satisfied: c'|σ matches a DB entry
                            exact constrInDB_sat
                              (Sat.PB.applySubstConstr subst c') state.db v
                              hauto (fun id c hget' => hv id c hget')
                        · -- c' is unaffected: ω(v) ⊨ c' by noSubst
                          have hnotaff : Sat.PB.termsAffected subst
                              c'.terms = false := by
                            cases h : Sat.PB.termsAffected subst c'.terms
                            · rfl
                            · exact absurd h (by simp [haff])
                          exact Sat.PB.constr_sat_applyValuation_noSubst
                            subst c' v hnotaff (hv id' c' hget)
                · -- Coverage check fails → none
                  simp [hcov] at hsteps
      | deld ids | delc ids =>
        exact ih_rest _ (DBSat_erase_fold state.db ids hsat) hsteps
      | output => exact ih_rest state hsat hsteps
      | conclusion id =>
        match hdb : state.db[id]? with
        | some c =>
          simp [hdb] at hsteps
          by_cases hc : c.isContra
          · simp [hc] at hsteps; exact ih_rest state hsat hsteps
          · simp [hc] at hsteps
        | none => simp [hdb] at hsteps
      | sol _ => exact ih_rest state hsat hsteps
      | soli _ => exact ih_rest state hsat hsteps
      | conclusionSat _ => exact ih_rest state hsat hsteps
      | conclusionBounds _ _ _ _ => exact ih_rest state hsat hsteps

theorem checkProof_sound (constrs : Array Constr) (numVars : Nat)
    (proofStr : String)
    (h : checkProofBool constrs numVars proofStr = true) :
    formulaUnsat constrs := by
  unfold checkProofBool at h
  match hparse : VeriPB.parseVeriPBProof proofStr with
  | .error _ => simp [hparse] at h
  | .ok proofData =>
    simp only [hparse] at h
    match hexec : execStepsFuel (pbcDepth proofData.steps.toList + 1)
        (BoolCheckState.fromConstrs constrs numVars)
        proofData.steps.toList with
    | some finalState =>
      simp only [hexec] at h
      -- Extract conclusion information
      simp only [hasUnsatConclusion] at h
      obtain ⟨i, _, _, _, hpi⟩ := Array.any_iff_exists.mp h
      revert hpi
      generalize proofData.steps[i] = step
      intro hpi
      cases step with
      | conclusion id =>
        simp at hpi
        match hdb : finalState.db[id]? with
        | some c =>
          simp [hdb] at hpi
          -- hpi : c.isContra = true
          -- Prove UNSAT by contradiction using DBSat
          intro v
          exact Classical.byContradiction fun hne => by
            -- hne : ¬ (∃ c, c ∈ constrs.toList ∧ ¬c.sat v)
            -- So all constraints are satisfied by v
            have hall : ∀ c' ∈ constrs.toList, Constr.sat c' v :=
              fun c' hc' => Classical.byContradiction fun hn =>
                hne ⟨c', hc', hn⟩
            have hinit : DBSat (BoolCheckState.fromConstrs constrs numVars).db :=
              ⟨v, fun id' c' hget => init_sound constrs numVars id' c' hget v hall⟩
            have hfinal : DBSat finalState.db :=
              execStepsFuel_sat_preserve _ _ _ _ hinit hexec
            obtain ⟨w, hw⟩ := hfinal
            exact contra_unsat c w (by
              simp [Constr.isContra] at hpi; exact hpi)
              (hw id c (by rwa [Std.HashMap.get?_eq_getElem?]))
        | none => simp [hdb] at hpi
      | _ => simp at hpi
    | none => simp [hexec] at h

/-! ## Decidable instance for native_decide -/

instance (constrs : Array Constr) (numVars : Nat) (proofStr : String) :
    Decidable (checkProofBool constrs numVars proofStr = true) :=
  inferInstance

/-! ## Elaboration command using reflection -/

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

/-- Build Expr for array of constraints. -/
def mkConstrArrayExpr (constrs : Array Constr) : MetaM Expr := do
  let constrType := mkConst ``Constr
  let mut elems : Array Expr := #[]
  for c in constrs do
    let termsExpr ← mkTermsExpr c.terms
    let degreeExpr := mkRawNatLit c.degree
    let constrExpr := mkApp2 (mkConst ``Constr.mk) termsExpr degreeExpr
    elems := elems.push constrExpr
  mkArrayLit constrType elems.toList
where
  mkTermsExpr (terms : List (Nat × Sat.PB.Literal)) : MetaM Expr := do
    let termType := mkApp2 (mkConst ``Prod [.zero, .zero])
      (mkConst ``Nat) (mkConst ``Sat.PB.Literal)
    let mut elems : List Expr := []
    for (coeff, lit) in terms do
      let coeffExpr := mkRawNatLit coeff
      let litExpr := match lit with
        | .pos i => mkApp (mkConst ``Sat.PB.Literal.pos) (mkRawNatLit i)
        | .neg i => mkApp (mkConst ``Sat.PB.Literal.neg) (mkRawNatLit i)
      let termExpr := mkApp4 (mkConst ``Prod.mk [.zero, .zero])
        (mkConst ``Nat) (mkConst ``Sat.PB.Literal) coeffExpr litExpr
      elems := termExpr :: elems
    mkListLit termType elems.reverse

-- `veripb_reflect` command
elab "veripb_reflect " n:ident
    ppSpace opbFile:str ppSpace proofFile:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let opbPath := opbFile.getString
  let proofPath := proofFile.getString
  liftTermElabM do
    let opbStr ← IO.FS.readFile (System.FilePath.mk opbPath)
    let proofStr ← IO.FS.readFile (System.FilePath.mk proofPath)
    let (numVars, constrs) ← match VeriPB.parseOPB opbStr with
      | .ok r => pure r
      | .error e => throwError "OPB parse error: {e}"
    -- Interpreted pre-check removed for performance; native evaluation
    -- via ofReduceBool provides the verified check
    let constrsExpr ← mkConstrArrayExpr constrs
    let numVarsExpr := mkRawNatLit numVars
    let proofStrExpr := mkStrLit proofStr
    let unsatType := mkApp (mkConst ``formulaUnsat) constrsExpr
    let checkBoolExpr := mkApp3 (mkConst ``checkProofBool)
      constrsExpr numVarsExpr proofStrExpr
    -- Native evaluation via ofReduceBool (like native_decide)
    let auxName := name ++ `_check
    addAndCompile <| .defnDecl {
      name := auxName
      levelParams := []
      type := mkConst ``Bool
      value := checkBoolExpr
      hints := .abbrev
      safety := .safe
    }
    let auxConst := mkConst auxName
    let reduceBoolApp := mkApp (mkConst ``Lean.reduceBool) auxConst
    let rflPrf := mkApp2 (mkConst ``Eq.refl [.succ .zero])
      (mkConst ``Bool) reduceBoolApp
    let hEqTrue := mkApp3 (mkConst ``Lean.ofReduceBool)
      auxConst (mkConst ``Bool.true) rflPrf
    let proof := mkApp4 (mkConst ``checkProof_sound)
      constrsExpr numVarsExpr proofStrExpr hEqTrue
    addAndCompile <| Declaration.thmDecl {
      name
      levelParams := []
      type := unsatType
      value := proof
    }
    Lean.logInfo m!"Registered {name} : formulaUnsat \
      (checked via reflection)"

end VeriPB.Reflect
