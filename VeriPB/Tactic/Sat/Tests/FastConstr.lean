/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import VeriPB.Tactic.Sat.ReflectFast
import VeriPB.Tactic.Sat.Tests.Normalize

/-!
# Fast constraint operations: exactness test

The fast checker (`VeriPB.Reflect.Fast`) keeps structural knowledge about
each constraint (`FConstr.split`: a normalized block, or two blocks) and
uses it to pick cheaper exact normalization paths. This test applies random
sequences of the pol operations (add, multiply, divide, saturate, weaken,
negate, normalize) to random constraints, once through the fast
`FConstr` operations and once through the verified `Constr` operations with
the verbatim reference normalizer from `Tests/Normalize.lean`, and requires
identical results (terms in order and degree) after every operation.
-/

namespace VeriPB.Tests.FastConstr

open Sat.PB VeriPB.Reflect.Fast VeriPB.Tests.Normalize

/-- Reference: the verified data-level operations, with the verbatim copy of
the verified normalizer. -/
def refNormalize (c : Constr) : Constr := normalizeConstrRef c

def refWeaken (c : Constr) (v : Nat) : Option Constr :=
  match VeriPB.weakenConstr c v with
  | .ok r => some r
  | .error _ => none

def refNegate (c : Constr) : Constr := c.negate

/-- A random operation applied to a pair (fast, reference); `pool` supplies
operands for `add`. Returns `none` for an operation that does not apply
(weakening a variable with too large a coefficient), in which case both
sides must agree on that. -/
def step (r : Rng) (pool : Array (Constr × FConstr)) (f : FConstr) (c : Constr) :
    Option (FConstr × Constr) × Rng := Id.run do
  let (op, r1) := r.below 7
  let mut r := r1
  match op with
  | 0 =>
    let (k, r2) := r.below pool.size; r := r2
    let (pc, pf) := pool[k]!
    return (some (addFConstrs f pf, VeriPB.addConstrs c pc), r)
  | 1 =>
    let (k, r2) := r.below 4; r := r2
    return (some (mulFConstr f k, VeriPB.mulConstr c k), r)
  | 2 =>
    let (k, r2) := r.below 3; r := r2
    let k := k + 1
    return (some (divFConstr (normalizeFConstr f) k,
      VeriPB.divConstr (refNormalize c) k), r)
  | 3 =>
    return (some (saturateFConstr (normalizeFConstr f),
      VeriPB.saturateConstr (refNormalize c)), r)
  | 4 =>
    let (v, r2) := r.below 4; r := r2
    match weakenFConstr f v, refWeaken c v with
    | some f', some c' => return (some (f', c'), r)
    | none, none => return (none, r)
    | some _, none => return (some (f, ⟨[], 999999⟩), r)  -- force a mismatch report
    | none, some _ => return (some (⟨#[], #[], 999999, 0⟩, c), r)
  | 5 =>
    return (some (f.negate, refNegate c), r)
  | _ =>
    return (some (normalizeFConstr f, refNormalize c), r)

def runSeq (seed : UInt64) (rounds len : Nat) : IO Unit := do
  let mut r : Rng := ⟨seed⟩
  let mut checked := 0
  for _ in [:rounds] do
    -- a pool of random constraints, some normalized (blocks), some raw
    let mut pool : Array (Constr × FConstr) := #[]
    for k in [:4] do
      let (c, r') := randConstr r 3 4 6 6
      r := r'
      let f := toFConstr c
      if k % 2 == 0 then pool := pool.push (c, f)
      else pool := pool.push (refNormalize c, normalizeFConstr f)
    let (c0, r0) := randConstr r 3 4 6 6
    r := r0
    let mut f := toFConstr c0
    let mut c := c0
    for _ in [:len] do
      let (res, r') := step r pool f c
      r := r'
      match res with
      | none => pure ()
      | some (f', c') =>
        f := f'
        c := c'
        checked := checked + 1
        if !eqConstr (fromFConstr f) c then
          throw <| IO.userError
            s!"fast/verified mismatch (seed {seed}): fast {repr (fromFConstr f)} \
              (split {f.split}), verified {repr c}"
        -- the structural flag must be truthful
        if f.split > f.coeffs.size then
          throw <| IO.userError
            s!"split {f.split} exceeds size (seed {seed}): {repr (fromFConstr f)}"
        if f.split != 0 && f.split != f.coeffs.size then
          if !(isBlock (f.coeffs.extract 0 f.split) (f.lits.extract 0 f.split) &&
              isBlock (f.coeffs.extract f.split f.coeffs.size)
                (f.lits.extract f.split f.lits.size)) then
            throw <| IO.userError s!"two-block flag wrong (seed {seed}): {repr (fromFConstr f)}"
        else if f.split != 0 && !isBlock f.coeffs f.lits then
          throw <| IO.userError s!"block flag wrong (seed {seed}): {repr (fromFConstr f)}"
  IO.println s!"fast constraint ops: seed {seed}, {checked} operations OK"

end VeriPB.Tests.FastConstr

open VeriPB.Tests.FastConstr in
#eval show IO Unit from do
  runSeq 11 800 12
  runSeq 12 800 20
  runSeq 13 500 30
