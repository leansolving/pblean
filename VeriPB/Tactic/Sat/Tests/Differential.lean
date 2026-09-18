/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import VeriPB.Tactic.Sat.Reflect

/-!
# Fast checker differential test

`VeriPB.Reflect.checkProofBool` (verified, List-based) is replaced at
runtime by `VeriPB.Reflect.Fast.checkProofBoolFast` via `@[implemented_by]`.
The per-use axioms of `veripb_reflect` assert facts about the verified
definition, so the fast checker must accept exactly the same proofs. This
test runs the verified step function `execStepsFuel` and the fast step
function `Fast.execFStepsFuel` side by side, one proof step at a time, and
requires identical constraint databases (ids, terms in order, degrees) after
every step. The verified pipeline itself uses `normalizeConstr`, whose
runtime replacement is checked separately in `Tests/Normalize.lean`.

The same harness on the large `applications/` proofs (up to Paley(101),
62,922 steps) is run before releases; see `applications/difftest.lean`.
-/

namespace VeriPB.Tests.Differential

open VeriPB.Reflect

def constrEq (a b : Constr) : Bool :=
  a.degree == b.degree && a.terms.length == b.terms.length &&
    (a.terms.zip b.terms).all fun ((c1, l1), (c2, l2)) => c1 == c2 && l1 == l2

def showConstr (c : Constr) : String :=
  let ts := c.terms.map fun (a, l) => match l with
    | .pos v => s!"{a}·x{v}"
    | .neg v => s!"{a}·~x{v}"
  s!"{ts} ≥ {c.degree}"

/-- `none` if the two databases agree, otherwise a description of the first
difference found. -/
def dbDiff (slow : Std.HashMap Nat Constr) (fast : Std.HashMap Nat Fast.FConstr) :
    Option String := Id.run do
  if slow.size != fast.size then
    return some s!"db size differs: verified {slow.size} vs fast {fast.size}"
  for (id, c) in slow.toList do
    match fast[id]? with
    | none => return some s!"id {id} missing in fast db"
    | some fc =>
      let fcc := Fast.fromFConstr fc
      if !constrEq c fcc then
        return some s!"id {id} differs:\n  verified {showConstr c}\n  fast     {showConstr fcc}"
  return none

/-- Run both checkers step by step on one instance; throw on any difference.
`fullEvery` controls how often the whole database is compared (every step by
default); in between, only the size and the newly inserted constraint are
compared. -/
def runOne (name opbPath proofPath : String) (fullEvery : Nat := 1) : IO Unit := do
  let opbStr ← IO.FS.readFile opbPath
  let proofStr ← IO.FS.readFile proofPath
  let (numVars, constrs) ← match VeriPB.parseOPB opbStr with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"{name}: OPB parse error: {e}")
  let proof ← match VeriPB.parseVeriPBProof proofStr with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"{name}: proof parse error: {e}")
  let steps := proof.steps.toList
  let fuel := pbcDepth steps + 1
  let mut slow := BoolCheckState.fromConstrs constrs numVars
  let mut fast := Fast.FBoolCheckState.fromConstrs constrs numVars
  if let some msg := dbDiff slow.db fast.db then
    throw (IO.userError s!"{name}: initial state: {msg}")
  let mut k := 0
  for step in steps do
    let rs := execStepsFuel fuel slow [step]
    let rf := Fast.execFStepsFuel fuel fast [step]
    match rs, rf with
    | none, none =>
      throw (IO.userError s!"{name}: both checkers reject step {k}")
    | some _, none =>
      throw (IO.userError s!"{name}: MISMATCH at step {k}: verified accepts, fast rejects")
    | none, some _ =>
      throw (IO.userError s!"{name}: MISMATCH at step {k}: verified rejects, fast accepts")
    | some s, some f =>
      if s.nextId != f.nextId then
        throw (IO.userError s!"{name}: MISMATCH at step {k}: nextId {s.nextId} vs {f.nextId}")
      let diff? : Option String := Id.run do
        if s.db.size != f.db.size then
          return some s!"db size differs: verified {s.db.size} vs fast {f.db.size}"
        if s.nextId > slow.nextId then
          let id := s.nextId - 1
          match s.db[id]?, f.db[id]? with
          | some c, some fc =>
            let fcc := Fast.fromFConstr fc
            if !constrEq c fcc then
              return some s!"id {id} differs:\n  verified {showConstr c}\n  \
                fast     {showConstr fcc}"
          | none, none => pure ()
          | _, _ => return some s!"id {id} presence differs"
        if fullEvery != 0 && k % fullEvery == 0 then dbDiff s.db f.db else none
      if let some msg := diff? then
        throw (IO.userError s!"{name}: MISMATCH at step {k}: {msg}")
      slow := s
      fast := f
    k := k + 1
  if let some msg := dbDiff slow.db fast.db then
    throw (IO.userError s!"{name}: MISMATCH at end: {msg}")
  let okSlow := hasUnsatConclusion proof.steps slow
  let okFast := Fast.hasFUnsatConclusion proof.steps fast
  if okSlow != okFast then
    throw (IO.userError s!"{name}: conclusion differs: verified {okSlow}, fast {okFast}")
  IO.println s!"{name}: {k} steps identical, conclusion {okSlow}"

end VeriPB.Tests.Differential

open VeriPB.Tests.Differential in
#eval show IO Unit from do
  let d := "VeriPB/Tactic/Sat/Tests/data/"
  for n in ["php21", "red_subproof", "red_swap", "red_const", "red_neglit", "dom_basic"] do
    runOne n (d ++ n ++ ".opb") (d ++ n ++ "_kernel.pbp")
