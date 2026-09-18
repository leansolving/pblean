/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import VeriPB.Tactic.Sat.FromVeriPB

/-!
# Normalizer exactness test

`VeriPB.normalizeConstr` is the verified normalizer (List-based, used by the
soundness proofs). At runtime it is replaced by `VeriPB.normalizeArrays`
through `@[implemented_by]`, and the fast reflection checker calls
`normalizeArrays` directly. The `nativeEqTrue` axioms produced by
`veripb_reflect` assert facts about the *verified* definition, so the
runtime replacement must be extensionally equal to it, including the order
of the resulting terms (term order is observable: weakening removes the
first term of a variable, and RUP hint combination picks the first
complementary pair in accumulator order).

This test compares `normalizeArrays` and its general fallback
`normalizeArraysGeneral` against a verbatim copy of `normalizeConstr`
(copied so that the comparison does not go through the runtime replacement)
on random constraints with duplicate literals, both polarities, zero
coefficients and small degrees, which exercises the one-pass fast path, the
blocked-pair fallback, and the interplay of cancellation and merging.
-/

namespace VeriPB.Tests.Normalize

open Sat.PB

/-! ### Verbatim reference copy of `VeriPB.normalizeConstr` -/

def normalizeConstrRef (c : Sat.PB.Constr) : Sat.PB.Constr :=
  let rec go (fuel : Nat) (terms : List Sat.PB.Term) (degree : Nat) : Sat.PB.Constr :=
    match fuel with
    | 0 => ⟨terms, degree⟩
    | n + 1 =>
      match VeriPB.findZeroIdx terms with
      | some idx =>
        let pre := terms.take idx
        let post := terms.drop (idx + 1)
        go n (pre ++ post) degree
      | none =>
        match VeriPB.findValidCompPairIdx terms degree with
        | some (i, j) =>
          if hi : i < terms.length then
            if hj : j < terms.length then
              if hij : i < j then
                if hlit : terms[j].2 == terms[i].2.negate then
                  if hle : min terms[i].1 terms[j].1 ≤ degree then
                    let pre := terms.take i
                    let mid := (terms.drop (i + 1)).take (j - i - 1)
                    let post := terms.drop (j + 1)
                    go n (pre ++ (terms[i].1 - min terms[i].1 terms[j].1,
                            terms[i].2) :: mid ++
                          (terms[j].1 - min terms[i].1 terms[j].1,
                            terms[i].2.negate) :: post)
                      (degree - min terms[i].1 terms[j].1)
                  else ⟨terms, degree⟩
                else ⟨terms, degree⟩
              else ⟨terms, degree⟩
            else ⟨terms, degree⟩
          else ⟨terms, degree⟩
        | none =>
          match VeriPB.findLikeTermIdx terms with
          | some (i, j) =>
            if hi : i < terms.length then
              if hj : j < terms.length then
                if hij : i < j then
                  if hlit : terms[j].2 == terms[i].2 then
                    let pre := terms.take i
                    let mid := (terms.drop (i + 1)).take (j - i - 1)
                    let post := terms.drop (j + 1)
                    go n (pre ++ (terms[i].1 + terms[j].1,
                            terms[i].2) :: mid ++ post) degree
                  else ⟨terms, degree⟩
                else ⟨terms, degree⟩
              else ⟨terms, degree⟩
            else ⟨terms, degree⟩
          | none => ⟨terms, degree⟩
  go (VeriPB.normFuel c.terms.length) c.terms c.degree

/-! ### Random constraints -/

structure Rng where
  s : UInt64

def Rng.below (r : Rng) (k : Nat) : Nat × Rng :=
  let s := r.s * 6364136223846793005 + 1442695040888963407
  (((s >>> 33).toNat) % k, ⟨s⟩)

/-- Random constraint with up to `maxLen` terms over `nv` variables,
coefficients in `[0, maxC]`, degree in `[0, maxD]`. -/
def randConstr (r : Rng) (nv maxC maxD maxLen : Nat) : Constr × Rng := Id.run do
  let mut r := r
  let (len, r1) := r.below (maxLen + 1); r := r1
  let mut terms : List Term := []
  for _ in [:len] do
    let (v, r2) := r.below nv; r := r2
    let (sgn, r3) := r.below 2; r := r3
    let (a, r4) := r.below (maxC + 1); r := r4
    terms := (a, if sgn == 0 then .pos v else .neg v) :: terms
  let (d, r5) := r.below (maxD + 1); r := r5
  return (⟨terms, d⟩, r)

def eqConstr (a b : Constr) : Bool :=
  a.degree == b.degree && a.terms.length == b.terms.length &&
    (a.terms.zip b.terms).all fun ((c1, l1), (c2, l2)) => c1 == c2 && l1 == l2

/-- Run an array normalizer on a `Constr` through the literal encoding. -/
def viaArrays (f : Array Nat → Array Nat → Nat → Array Nat × Array Nat × Nat)
    (c : Constr) : Constr :=
  let ts := c.terms.toArray
  let (cs, ls, d) := f (ts.map (·.1)) (ts.map (VeriPB.litCode ·.2)) c.degree
  ⟨(List.range cs.size).map fun i => (cs[i]!, VeriPB.litOfCode ls[i]!), d⟩

def runTests (seed : UInt64) (count nv maxC maxD maxLen : Nat) : IO Unit := do
  let mut r : Rng := ⟨seed⟩
  for _ in [:count] do
    let (c, r') := randConstr r nv maxC maxD maxLen
    r := r'
    let expected := normalizeConstrRef c
    let fast := viaArrays VeriPB.normalizeArrays c
    let general := viaArrays VeriPB.normalizeArraysGeneral c
    if !eqConstr expected fast then
      throw <| IO.userError
        s!"normalizeArrays mismatch on {repr c}: expected {repr expected}, got {repr fast}"
    if !eqConstr expected general then
      throw <| IO.userError
        s!"normalizeArraysGeneral mismatch on {repr c}: \
          expected {repr expected}, got {repr general}"
  IO.println s!"normalizer exactness: seed {seed}, {count} random constraints OK"

end VeriPB.Tests.Normalize

open VeriPB.Tests.Normalize in
#eval show IO Unit from do
  runTests 1 5000 2 4 6 8
  runTests 2 5000 3 3 3 10
  runTests 3 5000 1 5 4 6
  runTests 4 2500 5 6 20 12
  runTests 5 2500 4 2 1 8
  -- sparse literal codes exercise the guard that routes to the general path
  runTests 6 2500 40 3 4 5
