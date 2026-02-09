/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import Lean
import Std
import VeriPB.Tactic.Sat.PseudoBoolean
import VeriPB.Tactic.Sat.FromVeriPB
import VeriPB.Tactic.Sat.Reflect

/-!
# Trusted Langford Pairing Encoding

Verified Langford pairing results for small n: existence for
n ≡ 0, 3 (mod 4) and impossibility for n ≡ 1, 2 (mod 4).

A Langford pairing of order n places each integer k ∈ {1,...,n} into
a sequence of length 2n such that the two occurrences of k are exactly
k+1 apart. L(2,n) exists iff n ≡ 0 or 3 (mod 4).

## Main results

* `langford1_impossible` -- L(2,1) impossible (omega)
* `langford2_impossible` -- L(2,2) impossible (omega)
* `langford6_impossible` -- L(2,6) impossible (VeriPB reflection checker)

## Existence results

* `langford3_exists` -- L(2,3) exists (witness: 3 1 2 1 3 2)
* `langford4_exists` -- L(2,4) exists (witness: 4 1 3 1 2 4 3 2)

## Infrastructure

* `Langford.encode` -- PB constraint encoding for VeriPB verification
* `Langford.toOPB` -- OPB format output
* `Langford.no_langford_of_unsat` -- encoding soundness
* `langford_decide` / `langford_reflect` -- elaboration commands
-/

namespace Langford

open Sat.PB

-- Mathematical predicate

/-- A Langford pairing of order n assigns a starting position to each
    integer k ∈ {1,...,n} such that:
    - Each start is valid (1 ≤ place k, place k + k + 1 ≤ 2n)
    - No two integers share a position (all 2n occupied positions
      are distinct) -/
def isLangfordPairing (n : Nat) (place : Nat → Nat) : Prop :=
  (∀ k, 1 ≤ k → k ≤ n →
    1 ≤ place k ∧ place k + k + 1 ≤ 2 * n) ∧
  (∀ k1 k2, 1 ≤ k1 → k1 ≤ n → 1 ≤ k2 → k2 ≤ n → k1 ≠ k2 →
    place k1 ≠ place k2 ∧
    place k1 ≠ place k2 + k2 + 1 ∧
    place k1 + k1 + 1 ≠ place k2 ∧
    place k1 + k1 + 1 ≠ place k2 + k2 + 1)

/-- There exists a Langford pairing of order n. -/
def hasLangfordPairing (n : Nat) : Prop :=
  ∃ place : Nat → Nat, isLangfordPairing n place

-- Small-case impossibility (n ≡ 1 or 2 mod 4)

/-- L(2,1) is impossible: sequence of length 2 cannot fit k=1 at
    distance 2. Proved directly by omega. -/
theorem langford1_impossible : ¬hasLangfordPairing 1 := by
  intro ⟨place, hvalid, _⟩
  have := hvalid 1 (by omega) (by omega)
  omega

/-- L(2,2) is impossible: four positions in {1,...,4} cannot all be
    distinct under the distance constraints. Proved by omega. -/
theorem langford2_impossible : ¬hasLangfordPairing 2 := by
  intro ⟨place, hvalid, hdisjoint⟩
  have h1 := hvalid 1 (by omega) (by omega)
  have h2 := hvalid 2 (by omega) (by omega)
  have d12 := hdisjoint 1 2 (by omega) (by omega) (by omega)
    (by omega) (by omega)
  obtain ⟨a, b, c, d⟩ := d12
  omega

-- Witness verification (n ≡ 0 or 3 mod 4)

/-- L(2,3) exists: sequence 3 1 2 1 3 2.
    Placement: place 1 = 2, place 2 = 3, place 3 = 1. -/
theorem langford3_exists : hasLangfordPairing 3 := by
  refine ⟨fun | 1 => 2 | 2 => 3 | 3 => 1 | _ => 0, ?_, ?_⟩
  · intro k hk1 hk3
    have : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases this with rfl | rfl | rfl <;> simp_all
  · intro k1 k2 hk1_1 hk1_n hk2_1 hk2_n hne
    have : k1 = 1 ∨ k1 = 2 ∨ k1 = 3 := by omega
    have : k2 = 1 ∨ k2 = 2 ∨ k2 = 3 := by omega
    rcases ‹k1 = 1 ∨ _› with rfl | rfl | rfl <;>
    rcases ‹k2 = 1 ∨ _› with rfl | rfl | rfl <;>
    simp_all

/-- L(2,4) exists: sequence 4 1 3 1 2 4 3 2.
    Placement: place 1 = 2, place 2 = 5, place 3 = 3, place 4 = 1. -/
theorem langford4_exists : hasLangfordPairing 4 := by
  refine ⟨fun | 1 => 2 | 2 => 5 | 3 => 3 | 4 => 1 | _ => 0, ?_, ?_⟩
  · intro k hk1 hk4
    have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp_all
  · intro k1 k2 hk1_1 hk1_n hk2_1 hk2_n hne
    have : k1 = 1 ∨ k1 = 2 ∨ k1 = 3 ∨ k1 = 4 := by omega
    have : k2 = 1 ∨ k2 = 2 ∨ k2 = 3 ∨ k2 = 4 := by omega
    rcases ‹k1 = 1 ∨ _› with rfl | rfl | rfl | rfl <;>
    rcases ‹k2 = 1 ∨ _› with rfl | rfl | rfl | rfl <;>
    simp_all

-- PB encoding (for VeriPB verification)

/-- Valid starting positions for integer k in a sequence of length 2n.
    Position j is valid if j ≥ 1 and j + k + 1 ≤ 2n. -/
def validStarts (n k : Nat) : List Nat :=
  (List.range (2 * n)).filterMap fun j0 =>
    let j := j0 + 1
    if j + k + 1 ≤ 2 * n then some j else none

/-- Variable index for placement (k, j): uniform grid layout.
    Row k (1-based) maps to row index (k-1), column j (1-based)
    maps to column index (j-1). -/
def varIdx (n k j : Nat) : Nat := (k - 1) * (2 * n) + (j - 1)

/-- Total number of PB variables: n rows × 2n columns. -/
def numVars (n : Nat) : Nat := n * (2 * n)

/-- ALO constraint: integer k has at least one starting position. -/
def mkALO (n k : Nat) : Constr :=
  let terms := (validStarts n k).map fun j =>
    (1, Literal.pos (varIdx n k j))
  ⟨terms, 1⟩

/-- Pairwise AMO for integer k: no two starting positions. -/
def mkIntAMO (n k : Nat) : List Constr :=
  let starts := validStarts n k
  starts.flatMap fun j1 =>
    starts.filterMap fun j2 =>
      if j1 < j2 then
        some ⟨[(1, Literal.neg (varIdx n k j1)),
               (1, Literal.neg (varIdx n k j2))], 1⟩
      else none

/-- All placements that cover position p. Returns (k, j) pairs
    where placing k at start j covers position p. -/
def coveringPlacements (n p : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun k0 =>
    let k := k0 + 1
    let fromStart := if p + k + 1 ≤ 2 * n ∧ 1 ≤ p
      then [(k, p)] else []
    let fromEnd := if p ≥ k + 2 ∧ p - k - 1 ≥ 1 ∧ p - k - 1 + k + 1 ≤ 2 * n
      then [(k, p - k - 1)] else []
    fromStart ++ fromEnd

/-- Pairwise AMO for position p: no two placements cover it. -/
def mkPosAMO (n p : Nat) : List Constr :=
  let pairs := coveringPlacements n p
  pairs.flatMap fun (k1, j1) =>
    pairs.filterMap fun (k2, j2) =>
      let v1 := varIdx n k1 j1
      let v2 := varIdx n k2 j2
      if v1 < v2 then
        some ⟨[(1, Literal.neg v1), (1, Literal.neg v2)], 1⟩
      else none

/-- Full PB encoding of the Langford placement problem. -/
def encode (n : Nat) : Array Constr :=
  let alo := (List.range n).map fun k0 => mkALO n (k0 + 1)
  let intAmo := (List.range n).flatMap fun k0 =>
    mkIntAMO n (k0 + 1)
  let posAmo := (List.range (2 * n)).flatMap fun p0 =>
    mkPosAMO n (p0 + 1)
  (alo ++ intAmo ++ posAmo).toArray

-- Encoding soundness

/-- Convert a Langford placement to a PB valuation.
    Variable varIdx n k j is true iff place k = j. -/
def pairingToVal (n : Nat) (place : Nat → Nat) : Valuation :=
  fun v =>
    let k := v / (2 * n) + 1
    let j := v % (2 * n) + 1
    k ≤ n && place k == j

private theorem varIdx_recover_k (n k j : Nat) (hn : 0 < n)
    (hk1 : 1 ≤ k) (_hkn : k ≤ n) (hj1 : 1 ≤ j) (hj2n : j ≤ 2 * n) :
    varIdx n k j / (2 * n) + 1 = k := by
  simp only [varIdx]
  have h2n : 0 < 2 * n := by omega
  have hjlt : j - 1 < 2 * n := by omega
  rw [Nat.mul_comm (k - 1) (2 * n), Nat.mul_add_div h2n, Nat.div_eq_of_lt hjlt]
  omega

private theorem varIdx_recover_j (n k j : Nat) (_hn : 0 < n)
    (_hk1 : 1 ≤ k) (_hkn : k ≤ n) (hj1 : 1 ≤ j) (hj2n : j ≤ 2 * n) :
    varIdx n k j % (2 * n) + 1 = j := by
  simp only [varIdx]
  have hjlt : j - 1 < 2 * n := by omega
  rw [Nat.mul_comm (k - 1) (2 * n), Nat.mul_add_mod, Nat.mod_eq_of_lt hjlt]
  omega

/-- pairingToVal evaluates to true at varIdx n k (place k) when
    k is in range. -/
private theorem pairingToVal_self (n : Nat) (place : Nat → Nat) (k : Nat)
    (hn : 0 < n) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hj1 : 1 ≤ place k) (hj2n : place k ≤ 2 * n) :
    pairingToVal n place (varIdx n k (place k)) = true := by
  simp only [pairingToVal]
  rw [varIdx_recover_k n k (place k) hn hk1 hkn hj1 hj2n]
  rw [varIdx_recover_j n k (place k) hn hk1 hkn hj1 hj2n]
  simp [hkn]

/-- pairingToVal at varIdx n k j is true iff place k = j
    (when k and j are in range). -/
private theorem pairingToVal_at (n : Nat) (place : Nat → Nat) (k j : Nat)
    (hn : 0 < n) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hj1 : 1 ≤ j) (hj2n : j ≤ 2 * n) :
    pairingToVal n place (varIdx n k j) = (k ≤ n && place k == j) := by
  simp only [pairingToVal]
  rw [varIdx_recover_k n k j hn hk1 hkn hj1 hj2n]
  rw [varIdx_recover_j n k j hn hk1 hkn hj1 hj2n]

/-- validStarts produces positions in range. -/
private theorem validStarts_mem (n k j : Nat) (hj : j ∈ validStarts n k) :
    1 ≤ j ∧ j + k + 1 ≤ 2 * n := by
  simp only [validStarts, List.mem_filterMap, List.mem_range] at hj
  obtain ⟨j0, _, hif⟩ := hj
  split at hif
  · next hcond => simp only [Option.some.injEq] at hif; subst hif; omega
  · simp at hif

/-- If place k is valid, it is in validStarts. -/
private theorem place_in_validStarts (n k : Nat) (place : Nat → Nat)
    (_hk1 : 1 ≤ k) (_hkn : k ≤ n)
    (hj1 : 1 ≤ place k) (hbound : place k + k + 1 ≤ 2 * n) :
    place k ∈ validStarts n k := by
  simp only [validStarts, List.mem_filterMap, List.mem_range]
  exact ⟨place k - 1, by omega, by simp; omega⟩

/-- If one positive literal in the sum is true, evalSum >= 1. -/
private theorem evalSum_pos_ge_one (val : Valuation)
    (vars : List Nat) (x : Nat)
    (hmem : x ∈ vars) (htrue : val x = true) :
    1 ≤ evalSum val (vars.map fun v => (1, Literal.pos v)) := by
  induction vars with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [List.map, evalSum, evalLit]
    cases List.mem_cons.mp hmem with
    | inl heq => subst heq; simp [htrue]
    | inr htl => have := ih htl; omega

/-- ALO constraint for integer k is satisfied: place k is a valid start. -/
private theorem alo_sat (n k : Nat) (place : Nat → Nat) (f : Valuation)
    (hn : 0 < n) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hf : f = pairingToVal n place)
    (hj1 : 1 ≤ place k) (hbound : place k + k + 1 ≤ 2 * n) :
    (mkALO n k).sat f := by
  simp only [mkALO, Constr.sat]
  have hmem : place k ∈ validStarts n k :=
    place_in_validStarts n k place hk1 hkn hj1 hbound
  have hj2n : place k ≤ 2 * n := by omega
  have hmap : (validStarts n k).map (fun j => (1, Literal.pos (varIdx n k j))) =
    ((validStarts n k).map (varIdx n k)).map (fun x => (1, Literal.pos x)) := by
    simp [List.map_map]
  rw [hmap]
  apply evalSum_pos_ge_one
  · simp only [List.mem_map]; exact ⟨place k, hmem, rfl⟩
  · subst hf; exact pairingToVal_self n place k hn hk1 hkn hj1 hj2n

/-- IntAMO constraint is satisfied: place k has a unique value. -/
private theorem intAmo_sat (n k j1 j2 : Nat) (place : Nat → Nat) (f : Valuation)
    (hn : 0 < n) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hf : f = pairingToVal n place)
    (hj1m : j1 ∈ validStarts n k) (hj2m : j2 ∈ validStarts n k)
    (hlt : j1 < j2) :
    (⟨[(1, Literal.neg (varIdx n k j1)),
       (1, Literal.neg (varIdx n k j2))], 1⟩ : Constr).sat f := by
  have hj1b := validStarts_mem n k j1 hj1m
  have hj2b := validStarts_mem n k j2 hj2m
  simp only [Constr.sat, evalSum, evalLit]
  subst hf
  rw [pairingToVal_at n place k j1 hn hk1 hkn hj1b.1 (by omega)]
  rw [pairingToVal_at n place k j2 hn hk1 hkn hj2b.1 (by omega)]
  simp [hkn]
  by_cases h1 : place k == j1 <;> by_cases h2 : place k == j2 <;> simp_all [beq_iff_eq]

/-- Every ALO constraint in the encoding is satisfied. -/
private theorem encode_alo_sat (n : Nat) (place : Nat → Nat)
    (hn : 0 < n)
    (hvalid : ∀ k, 1 ≤ k → k ≤ n → 1 ≤ place k ∧ place k + k + 1 ≤ 2 * n) :
    ∀ c ∈ (List.range n).map (fun k0 => mkALO n (k0 + 1)),
      c.sat (pairingToVal n place) := by
  intro c hc
  simp only [List.mem_map, List.mem_range] at hc
  obtain ⟨k0, hk0, rfl⟩ := hc
  have hk1 : 1 ≤ k0 + 1 := by omega
  have hkn : k0 + 1 ≤ n := by omega
  have hb := hvalid (k0 + 1) hk1 hkn
  exact alo_sat n (k0 + 1) place (pairingToVal n place) hn hk1 hkn rfl hb.1 hb.2

/-- Every IntAMO constraint in the encoding is satisfied. -/
private theorem encode_intAmo_sat (n : Nat) (place : Nat → Nat)
    (hn : 0 < n)
    (_hvalid : ∀ k, 1 ≤ k → k ≤ n → 1 ≤ place k ∧ place k + k + 1 ≤ 2 * n) :
    ∀ c ∈ (List.range n).flatMap (fun k0 => mkIntAMO n (k0 + 1)),
      c.sat (pairingToVal n place) := by
  intro c hc
  simp only [List.mem_flatMap, List.mem_range] at hc
  obtain ⟨k0, hk0, hc⟩ := hc
  simp only [mkIntAMO] at hc
  simp only [List.mem_flatMap, List.mem_filterMap] at hc
  obtain ⟨j1, hj1m, j2, hj2m, hif⟩ := hc
  split at hif
  · next hlt =>
    simp only [Option.some.injEq] at hif; rw [← hif]
    exact intAmo_sat n (k0 + 1) j1 j2 place (pairingToVal n place) hn
      (by omega) (by omega) rfl hj1m hj2m hlt
  · simp at hif

/-- Membership in coveringPlacements: extracts k range, j bounds, and
    which position is covered. -/
private theorem coveringPlacements_mem (n p : Nat) (k j : Nat)
    (hmem : (k, j) ∈ coveringPlacements n p) :
    1 ≤ k ∧ k ≤ n ∧ 1 ≤ j ∧ j ≤ 2 * n ∧ (p = j ∨ p = j + k + 1) := by
  simp only [coveringPlacements, List.mem_flatMap, List.mem_range] at hmem
  obtain ⟨k0, hk0, hmem'⟩ := hmem
  simp only [List.mem_append] at hmem'
  rcases hmem' with hmem' | hmem'
  · split at hmem' <;> simp_all (config := { decide := false })
    next hcond => obtain ⟨rfl, rfl⟩ := hmem'; omega
  · split at hmem' <;> simp_all (config := { decide := false })
    next hcond =>
      obtain ⟨rfl, rfl⟩ := hmem'
      obtain ⟨hge, hge1, hle⟩ := hcond
      omega

/-- Every PosAMO constraint in the encoding is satisfied.
    This uses the disjointness property: if two (k,j) pairs
    cover the same position p, a valid pairing cannot have
    both place k1 = j1 and place k2 = j2. -/
private theorem encode_posAmo_sat (n : Nat) (place : Nat → Nat)
    (hn : 0 < n)
    (_hvalid : ∀ k, 1 ≤ k → k ≤ n → 1 ≤ place k ∧ place k + k + 1 ≤ 2 * n)
    (hdisjoint : ∀ k1 k2, 1 ≤ k1 → k1 ≤ n → 1 ≤ k2 → k2 ≤ n → k1 ≠ k2 →
      place k1 ≠ place k2 ∧
      place k1 ≠ place k2 + k2 + 1 ∧
      place k1 + k1 + 1 ≠ place k2 ∧
      place k1 + k1 + 1 ≠ place k2 + k2 + 1) :
    ∀ c ∈ (List.range (2 * n)).flatMap (fun p0 => mkPosAMO n (p0 + 1)),
      c.sat (pairingToVal n place) := by
  intro c hc
  simp only [List.mem_flatMap, List.mem_range] at hc
  obtain ⟨p0, hp0, hc⟩ := hc
  simp only [mkPosAMO] at hc
  simp only [List.mem_flatMap, List.mem_filterMap] at hc
  obtain ⟨⟨k1, j1⟩, hm1, ⟨k2, j2⟩, hm2, hif⟩ := hc
  split at hif
  · next hvlt =>
    simp only [Option.some.injEq] at hif; rw [← hif]
    have ⟨hk1_1, hk1_n, hj1_1, hj1_2n, hcover1⟩ :=
      coveringPlacements_mem n (p0 + 1) k1 j1 hm1
    have ⟨hk2_1, hk2_n, hj2_1, hj2_2n, hcover2⟩ :=
      coveringPlacements_mem n (p0 + 1) k2 j2 hm2
    simp only [Constr.sat, evalSum, evalLit]
    rw [pairingToVal_at n place k1 j1 hn hk1_1 hk1_n hj1_1 hj1_2n]
    rw [pairingToVal_at n place k2 j2 hn hk2_1 hk2_n hj2_1 hj2_2n]
    simp [hk1_n, hk2_n]
    by_cases h1 : place k1 == j1 <;> by_cases h2 : place k2 == j2 <;>
      simp_all [beq_iff_eq]
    -- Both place k1 = j1 and place k2 = j2
    -- If k1 = k2, then j1 = j2, contradicting varIdx strict inequality
    by_cases hkeq : k1 = k2
    · subst hkeq; simp [varIdx] at hvlt; omega
    · -- k1 ≠ k2: use disjointness of occupied positions
      have hdis := hdisjoint k1 k2 hk1_1 hk1_n hk2_1 hk2_n hkeq
      obtain ⟨hd1, hd2, hd3, hd4⟩ := hdis
      rcases hcover1 with hc1 | hc1 <;> rcases hcover2 with hc2 | hc2 <;> omega
  · simp at hif

/-- If the encoding is unsatisfiable, no Langford pairing exists. -/
theorem no_langford_of_unsat (n : Nat) (hn : 0 < n)
    (hunsat : ∀ v : Valuation, ∃ c ∈ (encode n).toList, ¬c.sat v) :
    ¬hasLangfordPairing n := by
  intro ⟨place, hvalid, hdisjoint⟩
  let val := pairingToVal n place
  obtain ⟨c, hc, hnsat⟩ := hunsat val
  apply hnsat
  have henc : (encode n).toList =
      (List.range n).map (fun k0 => mkALO n (k0 + 1)) ++
      (List.range n).flatMap (fun k0 => mkIntAMO n (k0 + 1)) ++
      (List.range (2 * n)).flatMap (fun p0 => mkPosAMO n (p0 + 1)) := by
    simp [encode]
  rw [henc] at hc
  simp only [List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · exact encode_alo_sat n place hn hvalid c hc
  · exact encode_intAmo_sat n place hn hvalid c hc
  · exact encode_posAmo_sat n place hn hvalid hdisjoint c hc

-- Bridge theorem

private theorem exists_not_sat_of_allSat_false (ctx : PBFmla) (v : Valuation)
    (h : PBFmla.allSat v ctx → False) : ∃ c ∈ ctx, ¬c.sat v :=
  Classical.byContradiction fun hne =>
    h ⟨fun c hc =>
      Classical.byContradiction fun hnsat => hne ⟨c, hc, hnsat⟩⟩

/-- Bridge from PBFmla refutation to Langford pairing impossibility. -/
theorem bridge (n : Nat) (hn : 0 < n) (ctx : PBFmla)
    (hctx : ctx = (encode n).toList)
    (hunsat : ∀ v : Valuation, PBFmla.allSat v ctx → False) :
    ¬hasLangfordPairing n := by
  apply no_langford_of_unsat n hn
  intro v
  rw [← hctx]
  exact exists_not_sat_of_allSat_false ctx v (hunsat v)

-- OPB generation

/-- OPB header suffix (max coefficient bit-width). -/
private def opbIntSize : Nat := 6

/-- Generate OPB format string for the Langford encoding. -/
def toOPB (n : Nat) : String := Id.run do
  let constrs := encode n
  let nv := numVars n
  let mut s := s!"* #variable= {nv} #constraint= {constrs.size}"
  s := s ++ s!" #equal= 0 intsize= {opbIntSize}\n"
  for c in constrs.toList do
    for (coeff, lit) in c.terms do
      match lit with
      | Literal.pos v => s := s ++ s!"+{coeff} x{v + 1} "
      | Literal.neg v => s := s ++ s!"+{coeff} ~x{v + 1} "
    s := s ++ s!">= {c.degree} ;\n"
  return s

-- Elaboration commands

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

private def runCmdMeta (cmd : String) (args : Array String)
    (errCtx : String) : MetaM String := do
  let result ← IO.Process.output { cmd := cmd, args := args }
  if result.exitCode != 0 then
    throwError "{errCtx}: {cmd} failed (exit {result.exitCode})\
      \nstderr: {result.stderr}\nstdout: {result.stdout}"
  return result.stdout

private def buildBridgeProof (nExpr : Expr) (hnExpr : Expr)
    (ctx : Expr) (pbProofConst : Expr) : MetaM (Expr × Expr) := do
  let finalType := mkApp (mkConst ``Not)
    (mkApp (mkConst ``hasLangfordPairing) nExpr)
  let pbFmlaType := mkConst ``Sat.PB.PBFmla
  let hctxProof := mkApp2 (mkConst ``Eq.refl [← getLevel pbFmlaType])
    pbFmlaType ctx
  let finalProof := mkApp5 (mkConst ``Langford.bridge)
    nExpr hnExpr ctx hctxProof pbProofConst
  return (finalType, finalProof)

-- `langford_decide name n` proves ¬ hasLangfordPairing n via solver
elab "langford_decide " nm:ident ppSpace nTerm:num : command => do
  let name := (← getCurrNamespace) ++ nm.getId
  let n := nTerm.getNat
  liftTermElabM do
    let nExpr := mkRawNatLit n
    if n == 0 then throwError "n must be positive"
    let ltType := mkApp4 (mkConst ``LT.lt [.zero])
      (mkConst ``Nat) (mkConst ``instLTNat) (mkRawNatLit 0) nExpr
    let hnExpr ← mkDecideProof ltType
    let tmpDir ← IO.Process.output { cmd := "mktemp", args := #["-d"] }
    if tmpDir.exitCode != 0 then
      throwError "mktemp failed (exit {tmpDir.exitCode}): {tmpDir.stderr}"
    let tmpPath := tmpDir.stdout.trimAscii.toString
    if tmpPath.isEmpty then throwError "mktemp returned empty path"
    let opbPath := s!"{tmpPath}/instance.opb"
    let augPath := s!"{tmpPath}/proof_aug.pbp"
    let kernelPath := s!"{tmpPath}/proof_kernel.pbp"
    let cleanup : MetaM Unit := do
      let _ ← IO.Process.output { cmd := "rm", args := #["-rf", tmpPath] }
    try
      IO.FS.writeFile (System.FilePath.mk opbPath) (toOPB n)
      let _ ← runCmdMeta "roundingsat"
        #[opbPath, s!"--proof-log={augPath}"] "RoundingSat"
      let _ ← runCmdMeta "veripb"
        #["--elaborate", kernelPath, opbPath, augPath] "VeriPB"
    catch e =>
      cleanup
      throw e
    let proofStr ← IO.FS.readFile (System.FilePath.mk kernelPath)
    cleanup
    let constrs := encode n
    let auxName := name ++ `aux
    let (ctx, _ctx', pbProofConst) ←
      VeriPB.fromVeriPBDirect constrs (numVars n) proofStr auxName
    let (finalType, finalProof) ←
      buildBridgeProof nExpr hnExpr ctx pbProofConst
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := finalType
      value := finalProof
    }
    Lean.logInfo m!"Registered {name} : ¬ hasLangfordPairing {n}"

-- Reflection-based verification (uses native_decide)
elab "langford_reflect " nm:ident ppSpace nTerm:num
    ppSpace proofFile:str : command => do
  let name := (← getCurrNamespace) ++ nm.getId
  let n := nTerm.getNat
  let proofPath := proofFile.getString
  liftTermElabM do
    let nExpr := mkRawNatLit n
    let numVarsExpr := mkRawNatLit (numVars n)
    let proofStr ← IO.FS.readFile (System.FilePath.mk proofPath)
    let constrsExpr := mkApp (mkConst ``encode) nExpr
    let proofStrExpr := mkStrLit proofStr
    let checkExpr := mkApp3 (mkConst ``VeriPB.Reflect.checkProofBool)
      constrsExpr numVarsExpr proofStrExpr
    let auxName := name ++ `_check
    addAndCompile <| .defnDecl {
      name := auxName
      levelParams := []
      type := mkConst ``Bool
      value := checkExpr
      hints := .abbrev
      safety := .safe
    }
    let auxConst := mkConst auxName
    let reduceBoolApp := mkApp (mkConst ``Lean.reduceBool) auxConst
    let rflPrf := mkApp2 (mkConst ``Eq.refl [.succ .zero])
      (mkConst ``Bool) reduceBoolApp
    let hEqTrue := mkApp3 (mkConst ``Lean.ofReduceBool)
      auxConst (mkConst ``Bool.true) rflPrf
    let unsatProof := mkApp4
      (mkConst ``VeriPB.Reflect.checkProof_sound)
      constrsExpr numVarsExpr proofStrExpr hEqTrue
    -- Build hn : 0 < n proof
    if n == 0 then throwError "n must be positive"
    let ltType := mkApp4 (mkConst ``LT.lt [.zero])
      (mkConst ``Nat) (mkConst ``instLTNat) (mkRawNatLit 0) nExpr
    let hnExpr ← mkDecideProof ltType
    let finalProof := mkApp3 (mkConst ``no_langford_of_unsat)
      nExpr hnExpr unsatProof
    let finalType := mkApp (mkConst ``Not)
      (mkApp (mkConst ``hasLangfordPairing) nExpr)
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := finalType
      value := finalProof
    }
    Lean.logInfo m!"Registered {name} : ¬ hasLangfordPairing {n}"

-- L(2,6) impossibility verified via VeriPB reflection checker
-- 72 variables, 463 constraints
langford_reflect langford6_impossible 6
  "applications/langford/langford6_kernel.pbp"

end Langford
