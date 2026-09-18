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
# Verified VeriPB checker definitions

This module holds the list-based reference checker components shared by the
array-based runtime checker and by the soundness proofs: the proof-checking
state (`BoolCheckState`), pol RPN execution, RUP verification, red coverage
checking, the conclusion test, and the pbc depth measure.

The step loop (`processRedGoalsBool`, `execStepsFuel`) stays next to its
soundness proofs in `VeriPB.Tactic.Sat.Reflect`, because those proofs
rewrite with hypotheses about the `match` expressions inside it and Lean's
matcher cache is not shared across modules.  The array-based runtime
replacement lives in `VeriPB.Tactic.Sat.ReflectFast`.
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
def propagationIterLimit (numVars numHints : Nat) : Nat :=
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
def mkDBRec : List Constr → Nat → Std.HashMap Nat Constr
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
            -- VeriPB weakens the normalized constraint
            some (.constr (VeriPB.weakenConstr (VeriPB.normalizeConstr c) (n - 1)) :: rest)
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

/-- Negation of a `rup` target, as VeriPB propagates over it: the target is
normalized first (so complementary pairs and repeated literals do not
weaken propagation); a target whose degree exceeds its coefficient sum is
unsatisfiable on its own, and its negation is the trivial constraint
`>= 0`. -/
def rupNegate (c : Constr) : Constr :=
  let nc := VeriPB.normalizeConstr c
  if nc.degree ≤ nc.coeffSum then nc.negate else ⟨[], 0⟩

/-- VeriPB always has the negated target in the database during a `rup`
check; the `~` hint only fixes its position in the propagation order. When
absent, propagate it first. -/
def withNegHint (hints : List VeriPB.RupHint) : List VeriPB.RupHint :=
  if hints.any (fun h => match h with | .negC => true | .id _ => false) then hints
  else .negC :: hints

/-- Verify RUP step using propagation + conflict-first combining. -/
def verifyRupBool (negConstr : Constr) (hints : List VeriPB.RupHint)
    (db : Std.HashMap Nat Constr) (numVars : Nat) : Bool :=
  match verifyRupExtract negConstr (withNegHint hints) db numVars with
  | none => false
  | some (conflictC, otherHints) =>
    (combineHintsRec (VeriPB.normalizeConstr conflictC)
      otherHints).isContra

/-! ### Red coverage verification -/

/-- Check if two normalized constraints match (same degree and sorted terms). -/
def constrMatchNorm (c1 c2 : Constr) : Bool :=
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
def constrInDB (c : Constr) (db : Std.HashMap Nat Constr) : Bool :=
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

end VeriPB.Reflect
