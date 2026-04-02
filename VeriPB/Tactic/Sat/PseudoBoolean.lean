/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/

/-!
# Pseudo-Boolean Constraint Verification

Kernel-level types and soundness lemmas for verifying VeriPB proofs.
Constraints of the form `a₁·l₁ + a₂·l₂ + ... ≥ d` where `lᵢ` are
literals evaluated to 0 or 1.

## Main definitions

* `Sat.PB.Literal` — positive or negated Boolean variable
* `Sat.PB.Constr` — pseudo-Boolean constraint `Σ aᵢ·lᵢ ≥ d`
* `Sat.PB.Valuation` — Boolean assignment on variables
* `Sat.PB.PBFmla` — conjunction of PB constraints
* `Sat.PB.PropVal` — propositional reification infrastructure

## Main results

* `Sat.PB.add_sat` — addition rule soundness
* `Sat.PB.mul_sat` — multiplication rule soundness
* `Sat.PB.div_sat` — division rule soundness
* `Sat.PB.saturate_sat` — saturation rule soundness
* `Sat.PB.weaken_term_sat` — weakening rule soundness
* `Sat.PB.cancel_pair_sat` — complementary pair cancellation
* `Sat.PB.contra_unsat` — contradictory constraint unsatisfiability
* `Sat.PB.PBFmla.refuteProp` — main bridge from PB refutation to Prop
-/

namespace Sat.PB

/-- A pseudo-Boolean literal: either a positive or negated variable. -/
inductive Literal where
  | pos : Nat → Literal
  | neg : Nat → Literal
  deriving Repr, BEq, Hashable, Inhabited, DecidableEq

/-- Extract the variable index from a literal. -/
def Literal.var : Literal → Nat
  | .pos i => i
  | .neg i => i

/-- Negate a literal: `pos i ↦ neg i` and `neg i ↦ pos i`. -/
def Literal.negate : Literal → Literal
  | .pos i => .neg i
  | .neg i => .pos i

/-- A Boolean valuation: maps variable indices to `true`/`false`. -/
def Valuation := Nat → Bool

/-- Evaluate a literal under a valuation: 1 if satisfied, 0 otherwise. -/
def evalLit (v : Valuation) : Literal → Nat
  | .pos i => if v i then 1 else 0
  | .neg i => if v i then 0 else 1

/-- A weighted literal term: coefficient paired with a literal. -/
abbrev Term := Nat × Literal

/-- Evaluate a sum of weighted literal terms under a valuation. -/
def evalSum (v : Valuation) : List Term → Nat
  | [] => 0
  | (c, l) :: rest => c * evalLit v l + evalSum v rest

/-- Sum of all coefficients in a term list (upper bound on `evalSum`). -/
def coeffSumR : List Term → Nat
  | [] => 0
  | (c, _) :: rest => c + coeffSumR rest

/-- A pseudo-Boolean constraint: `Σ aᵢ·lᵢ ≥ d`. -/
structure Constr where
  terms : List Term
  degree : Nat
  deriving Repr, Inhabited

/-- A constraint is satisfied when the weighted sum meets the degree. -/
def Constr.sat (c : Constr) (v : Valuation) : Prop :=
  c.degree ≤ evalSum v c.terms

-- Basic evaluation lemmas

/-- Every literal evaluates to at most 1. -/
theorem evalLit_le_one (v : Valuation) (l : Literal) : evalLit v l ≤ 1 := by
  cases l <;> simp [evalLit] <;> split <;> omega

/-- A literal evaluates to exactly 0 or 1. -/
theorem evalLit_zero_or_one (v : Valuation) (l : Literal) :
    evalLit v l = 0 ∨ evalLit v l = 1 := by
  have h := evalLit_le_one v l; omega

/-- A literal and its negation sum to 1: `evalLit l + evalLit ~l = 1`. -/
theorem evalLit_negate_add (v : Valuation) (l : Literal) :
    evalLit v l + evalLit v l.negate = 1 := by
  cases l <;> simp [evalLit, Literal.negate] <;> split <;> simp

/-- Commuted version of `evalLit_negate_add`. -/
theorem evalLit_negate_add' (v : Valuation) (l : Literal) :
    evalLit v l.negate + evalLit v l = 1 := by
  have := evalLit_negate_add v l; omega

/-- A coefficient times a literal value is bounded by the coefficient. -/
theorem mul_evalLit_le (a : Nat) (v : Valuation) (l : Literal) :
    a * evalLit v l ≤ a := by
  have := evalLit_le_one v l
  calc a * evalLit v l ≤ a * 1 := Nat.mul_le_mul_left a this
    _ = a := Nat.mul_one a

/-- `evalSum` distributes over list append. -/
theorem evalSum_append (v : Valuation) (a b : List Term) :
    evalSum v (a ++ b) = evalSum v a + evalSum v b := by
  induction a with
  | nil => simp [evalSum]
  | cons hd tl ih => simp [evalSum, ih, Nat.add_assoc]

/-- Multiplying all coefficients by `k` scales the sum by `k`. -/
theorem evalSum_map_mul (v : Valuation) (k : Nat) (ts : List Term) :
    evalSum v (ts.map fun (a, l) => (k * a, l)) = k * evalSum v ts := by
  induction ts with
  | nil => simp [evalSum]
  | cons hd tl ih =>
    obtain ⟨a, l⟩ := hd
    simp [evalSum, List.map, ih, Nat.mul_add, Nat.mul_assoc]

/-- The evaluated sum is bounded by the coefficient sum. -/
theorem evalSum_le_coeffSumR (v : Valuation) (ts : List Term) :
    evalSum v ts ≤ coeffSumR ts := by
  induction ts with
  | nil => simp [evalSum, coeffSumR]
  | cons hd tl ih =>
    obtain ⟨a, l⟩ := hd
    simp only [evalSum, coeffSumR]
    exact Nat.add_le_add (mul_evalLit_le a v l) ih

-- Easy soundness: add, multiply, literal axioms

/-- **Addition rule**: the sum of two satisfied constraints is satisfied. -/
theorem add_sat (c1 c2 : Constr) (v : Valuation) (h1 : c1.sat v) (h2 : c2.sat v) :
    (Constr.mk (c1.terms ++ c2.terms) (c1.degree + c2.degree)).sat v := by
  simp only [Constr.sat] at *
  rw [evalSum_append]
  exact Nat.add_le_add h1 h2

/-- **Multiplication rule**: scaling a satisfied constraint preserves satisfaction. -/
theorem mul_sat (c : Constr) (k : Nat) (v : Valuation) (h : c.sat v) :
    (Constr.mk (c.terms.map fun (a, l) => (k * a, l)) (k * c.degree)).sat v := by
  simp only [Constr.sat] at *
  rw [evalSum_map_mul]
  exact Nat.mul_le_mul_left k h

/-- **Literal axiom (positive)**: `1·xᵢ ≥ 0` is always satisfied. -/
theorem lit_axiom_pos (i : Nat) (v : Valuation) :
    (Constr.mk [(1, .pos i)] 0).sat v := by
  simp [Constr.sat]

/-- **Literal axiom (negative)**: `1·¬xᵢ ≥ 0` is always satisfied. -/
theorem lit_axiom_neg (i : Nat) (v : Valuation) :
    (Constr.mk [(1, .neg i)] 0).sat v := by
  simp [Constr.sat]

-- Medium soundness: weaken, saturate

/-- **Weakening rule**: removing a term and subtracting its coefficient
from the degree preserves satisfaction. -/
theorem weaken_term_sat (v : Valuation) (pre post : List Term) (a : Nat) (l : Literal)
    (d : Nat) (hle : a ≤ d)
    (h : (Constr.mk (pre ++ (a, l) :: post) d).sat v) :
    (Constr.mk (pre ++ post) (d - a)).sat v := by
  simp only [Constr.sat] at *
  rw [evalSum_append] at h
  rw [evalSum_append]
  simp only [evalSum] at h
  have hlit := mul_evalLit_le a v l
  omega

/-- **Degree weakening**: lowering the degree preserves satisfaction. -/
theorem weaken_degree_sat (c : Constr) (d : Nat) (v : Valuation)
    (h : c.sat v) (hle : d ≤ c.degree) :
    (Constr.mk c.terms d).sat v := by
  simp only [Constr.sat] at *; omega

/-- **Propagation**: if a constraint is satisfied and the remaining
    coefficients (excluding one term) are less than the degree,
    then that term's literal must evaluate to 1. -/
theorem propagation_forces (v : Valuation) (pre post : List Term)
    (a : Nat) (l : Literal) (d : Nat)
    (hsat : (Constr.mk (pre ++ (a, l) :: post) d).sat v)
    (hforce : coeffSumR pre + coeffSumR post < d) :
    evalLit v l = 1 := by
  simp only [Constr.sat] at hsat
  rw [evalSum_append] at hsat
  simp only [evalSum] at hsat
  have hpre := evalSum_le_coeffSumR v pre
  have hpost := evalSum_le_coeffSumR v post
  rcases evalLit_zero_or_one v l with h0 | h1
  · -- evalLit v l = 0 → contradiction
    rw [h0, Nat.mul_zero] at hsat; omega
  · exact h1

private theorem min_le_min_right (a : Nat) {b c : Nat} (h : b ≤ c) : min a b ≤ min a c := by
  simp [Nat.min_def]; split <;> split <;> omega

private theorem saturate_mono (v : Valuation) (d1 d2 : Nat) (h12 : d1 ≤ d2) (ts : List Term) :
    evalSum v (ts.map fun (a, l) => (min a d1, l))
    ≤ evalSum v (ts.map fun (a, l) => (min a d2, l)) := by
  induction ts with
  | nil => simp [evalSum]
  | cons hd tl ih =>
    obtain ⟨a, l⟩ := hd
    simp only [evalSum, List.map]
    have : min a d1 ≤ min a d2 := min_le_min_right a h12
    exact Nat.add_le_add (Nat.mul_le_mul_right _ this) ih

private theorem saturate_aux (v : Valuation) (ts : List Term) :
    ∀ (d : Nat), d ≤ evalSum v ts → d ≤ evalSum v (ts.map fun (a, l) => (min a d, l)) := by
  induction ts with
  | nil => intro d; simp [evalSum]
  | cons hd tl ih =>
    obtain ⟨a, l⟩ := hd
    intro d hle
    simp only [evalSum, List.map]
    rcases evalLit_zero_or_one v l with h0 | h1
    · -- evalLit = 0: head term is 0 in both original and saturated
      have hle' : d ≤ evalSum v tl := by
        simp only [evalSum, h0, Nat.mul_zero, Nat.zero_add] at hle; exact hle
      simp only [h0, Nat.mul_zero, Nat.zero_add]
      exact ih d hle'
    · -- evalLit = 1: head contributes a (original) or min a d (saturated)
      have hle' : d ≤ a + evalSum v tl := by
        simp only [evalSum, h1, Nat.mul_one] at hle; exact hle
      simp only [h1, Nat.mul_one]
      by_cases had : d ≤ a
      · rw [Nat.min_eq_right had]; omega
      · have ha : a < d := by omega
        rw [Nat.min_eq_left (Nat.le_of_lt ha)]
        have htl : d - a ≤ evalSum v tl := by omega
        have hih := ih (d - a) htl
        have hmono := saturate_mono v (d - a) d (by omega) tl
        -- hih: d-a ≤ evalSum v (tl.map fun (a,l) => (min a (d-a), l))
        -- hmono: ... ≤ evalSum v (tl.map fun (a,l) => (min a d, l))
        -- goal uses the same lambda form as saturate_mono output, so:
        have hgoal : d - a ≤ evalSum v (tl.map fun (a, l) => (min a d, l)) :=
          Nat.le_trans hih hmono
        -- Bridge the lambda-form gap: goal uses `fun x => (min x.fst d, x.snd)`
        -- but hgoal uses `fun (a, l) => (min a d, l)`. They're defeq.
        have heq : evalSum v (tl.map fun x => (min x.fst d, x.snd))
                 = evalSum v (tl.map fun (a, l) => (min a d, l)) := rfl
        omega

theorem saturate_sum_ge (v : Valuation) (d : Nat) (ts : List Term)
    (h : d ≤ evalSum v ts) :
    d ≤ evalSum v (ts.map fun (a, l) => (min a d, l)) :=
  saturate_aux v ts d h

/-- **Saturation rule**: capping coefficients at the degree preserves satisfaction. -/
theorem saturate_sat (c : Constr) (v : Valuation) (h : c.sat v) :
    (Constr.mk (c.terms.map fun (a, l) => (min a c.degree, l)) c.degree).sat v := by
  simp only [Constr.sat] at *
  exact saturate_sum_ge v c.degree c.terms h

-- Division soundness

/-- Ceiling division: `⌈a / k⌉`. -/
def ceilDiv (a k : Nat) : Nat :=
  (a + k - 1) / k

private theorem ceilDiv_mul_ge (a k : Nat) (hk : 0 < k) : a ≤ ceilDiv a k * k := by
  unfold ceilDiv
  have h1 : k * ((a + k - 1) / k) + (a + k - 1) % k = a + k - 1 := Nat.div_add_mod _ _
  have h2 : (a + k - 1) % k < k := Nat.mod_lt _ hk
  have h3 : (a + k - 1) / k * k = k * ((a + k - 1) / k) := Nat.mul_comm _ _
  rw [h3]; omega

private theorem ceilDiv_le_of_mul_le (a b k : Nat) (hk : 0 < k) (h : a ≤ k * b) :
    ceilDiv a k ≤ b := by
  unfold ceilDiv
  have key : a + k - 1 < k * b + k := by omega
  have key2 : k * b + k = k * (b + 1) := by rw [Nat.mul_add, Nat.mul_one]
  rw [key2] at key
  have := Nat.div_lt_of_lt_mul key
  omega

theorem evalSum_ceilDiv_mul_k_ge (v : Valuation) (k : Nat) (hk : 0 < k) (ts : List Term) :
    evalSum v ts ≤ evalSum v (ts.map fun (a, l) => (ceilDiv a k * k, l)) := by
  induction ts with
  | nil => simp [evalSum]
  | cons hd tl ih =>
    obtain ⟨a, l⟩ := hd
    simp only [evalSum, List.map]
    have hterm : a * evalLit v l ≤ ceilDiv a k * k * evalLit v l := by
      rcases evalLit_zero_or_one v l with h0 | h1
      · simp [h0]
      · rw [h1]; simp only [Nat.mul_one]; exact ceilDiv_mul_ge a k hk
    exact Nat.add_le_add hterm ih

theorem evalSum_ceilDiv_factor (v : Valuation) (k : Nat) (_hk : 0 < k) (ts : List Term) :
    evalSum v (ts.map fun (a, l) => (ceilDiv a k * k, l))
    = k * evalSum v (ts.map fun (a, l) => (ceilDiv a k, l)) := by
  induction ts with
  | nil => simp [evalSum]
  | cons hd tl ih =>
    obtain ⟨a, l⟩ := hd
    simp only [evalSum, List.map, ih]
    rw [Nat.mul_add, Nat.mul_comm (ceilDiv a k) k, Nat.mul_assoc]

/-- **Division rule**: ceiling-dividing all coefficients and the degree preserves satisfaction. -/
theorem div_sat (c : Constr) (k : Nat) (hk : 0 < k) (v : Valuation) (h : c.sat v) :
    (Constr.mk (c.terms.map fun (a, l) => (ceilDiv a k, l)) (ceilDiv c.degree k)).sat v := by
  simp only [Constr.sat] at *
  have hge : evalSum v c.terms ≤ k * evalSum v (c.terms.map fun (a, l) => (ceilDiv a k, l)) := by
    calc evalSum v c.terms
        ≤ evalSum v (c.terms.map fun (a, l) => (ceilDiv a k * k, l)) :=
          evalSum_ceilDiv_mul_k_ge v k hk c.terms
      _ = k * evalSum v (c.terms.map fun (a, l) => (ceilDiv a k, l)) :=
          evalSum_ceilDiv_factor v k hk c.terms
  exact ceilDiv_le_of_mul_le c.degree _ k hk (Nat.le_trans h hge)

-- Negation (for RUP)

/-- Total coefficient sum of a constraint (upper bound on evaluation). -/
def Constr.coeffSum (c : Constr) : Nat := coeffSumR c.terms

theorem evalSum_negate_eq (v : Valuation) (ts : List Term) :
    evalSum v (ts.map fun (a, l) => (a, l.negate)) + evalSum v ts = coeffSumR ts := by
  induction ts with
  | nil => simp [evalSum, coeffSumR]
  | cons hd tl ih =>
    obtain ⟨a, l⟩ := hd
    simp only [evalSum, List.map, coeffSumR]
    -- goal: (a * evalLit v l.negate + neg_rest) + (a * evalLit v l + rest) = a + coeffSumR tl
    -- where ih: neg_rest + rest = coeffSumR tl
    -- and hmul: a * evalLit v l.negate + a * evalLit v l = a
    have hmul : a * evalLit v l.negate + a * evalLit v l = a := by
      rw [← Nat.mul_add, evalLit_negate_add' v l, Nat.mul_one]
    -- goal: (a * evalLit v l.negate + neg_rest) + (a * evalLit v l + rest) = a + coeffSumR tl
    -- Rearrange: = (a * neg + a * pos) + (neg_rest + rest) = a + coeffSumR tl
    -- = hmul + ih
    -- Explicit arithmetic rearrangement since omega can't handle the grouping
    -- with different lambda forms in ih vs goal
    have goal_eq :
        (a * evalLit v l.negate +
          evalSum v (List.map (fun x => (x.1, x.2.negate)) tl)) +
        (a * evalLit v l + evalSum v tl)
      = (a * evalLit v l.negate + a * evalLit v l) +
        (evalSum v (List.map (fun x => (x.1, x.2.negate)) tl) + evalSum v tl) := by
      omega
    rw [goal_eq, hmul, ih]

private theorem negate_ge (v : Valuation) (ts : List Term) (d : Nat)
    (hlt : evalSum v ts < d) (hle : d ≤ coeffSumR ts) :
    coeffSumR ts - d + 1 ≤ evalSum v (ts.map fun (a, l) => (a, l.negate)) := by
  have heq := evalSum_negate_eq v ts
  have hle2 := evalSum_le_coeffSumR v ts
  omega

private theorem negate_contradiction (v : Valuation) (ts : List Term) (d : Nat)
    (h : coeffSumR ts - d + 1 ≤ evalSum v (ts.map fun (a, l) => (a, l.negate)))
    (hsat : d ≤ evalSum v ts) : False := by
  have heq := evalSum_negate_eq v ts
  have hle := evalSum_le_coeffSumR v ts
  omega

/-- Negate a constraint: flip all literals, set degree to `coeffSum - degree + 1`. -/
def Constr.negate (c : Constr) : Constr :=
  let M := c.coeffSum
  ⟨c.terms.map fun (a, l) => (a, l.negate), M - c.degree + 1⟩

/-- If a constraint is not satisfied, its negation is satisfied (given `degree ≤ coeffSum`). -/
theorem negate_sat_of_not_sat (c : Constr) (v : Valuation) (hd : c.degree ≤ c.coeffSum)
    (h : ¬ c.sat v) : c.negate.sat v := by
  unfold Constr.sat at h
  have hlt : evalSum v c.terms < c.degree := by omega
  show c.negate.sat v
  unfold Constr.negate Constr.coeffSum Constr.sat
  exact negate_ge v c.terms c.degree hlt hd

theorem not_sat_of_negate_sat (c : Constr) (v : Valuation) (h : c.negate.sat v) :
    ¬ c.sat v := by
  unfold Constr.sat
  intro hsat
  have h' := h
  unfold Constr.negate Constr.coeffSum Constr.sat at h'
  exact negate_contradiction v c.terms c.degree h' hsat

-- Contradiction detection

/-- A constraint is contradictory when `coeffSum < degree` (unsatisfiable). -/
def Constr.isContra (c : Constr) : Bool :=
  c.coeffSum < c.degree

/-- A contradictory constraint is unsatisfiable. -/
theorem contra_unsat (c : Constr) (v : Valuation) (hc : c.coeffSum < c.degree) :
    ¬ c.sat v := by
  unfold Constr.sat Constr.coeffSum at *
  intro h
  have hle := evalSum_le_coeffSumR v c.terms
  omega

theorem empty_unsat (d : Nat) (hd : 0 < d) (v : Valuation) :
    ¬ (Constr.mk [] d).sat v := by
  simp [Constr.sat, evalSum]; omega

-- Normalization soundness lemmas

/-- Complementary pair decomposition:
`a·l + b·~l = (a-m)·l + (b-m)·~l + m` where `m = min a b`. -/
theorem complementary_sum (v : Valuation) (l : Literal) (a b : Nat) :
    a * evalLit v l + b * evalLit v l.negate =
    (a - min a b) * evalLit v l + (b - min a b) * evalLit v l.negate + min a b := by
  rcases evalLit_zero_or_one v l with h0 | h1
  · have hc := evalLit_negate_add v l; rw [h0] at hc; simp at hc
    rw [h0, hc]; simp; omega
  · have hc := evalLit_negate_add v l; rw [h1] at hc; simp at hc
    rw [h1, hc]; simp; omega

/-- **Cancel complementary pair**: reduce `a·l + b·~l` to
`(a-m)·l + (b-m)·~l` with degree reduced by `m`. -/
theorem cancel_pair_sat (v : Valuation) (pre mid post : List Term)
    (l : Literal) (a b d : Nat) (hle : min a b ≤ d)
    (h : (Constr.mk (pre ++ (a, l) :: mid ++ (b, l.negate) :: post) d).sat v) :
    (Constr.mk (pre ++ (a - min a b, l) :: mid ++
      (b - min a b, l.negate) :: post) (d - min a b)).sat v := by
  simp only [Constr.sat] at *
  have hkey := complementary_sum v l a b
  rw [evalSum_append] at h ⊢
  simp only [evalSum] at h ⊢
  rw [evalSum_append] at h ⊢
  simp only [evalSum] at h ⊢
  omega

/-- **Remove zero**: dropping a zero-coefficient term preserves satisfaction. -/
theorem remove_zero_sat (v : Valuation) (pre post : List Term) (l : Literal) (d : Nat)
    (h : (Constr.mk (pre ++ (0, l) :: post) d).sat v) :
    (Constr.mk (pre ++ post) d).sat v := by
  simp only [Constr.sat] at *
  rw [evalSum_append] at h ⊢
  simp only [evalSum] at h ⊢
  omega

/-- **Merge like terms**: combining `a·l + b·l` into `(a+b)·l` preserves satisfaction. -/
theorem merge_terms_sat (v : Valuation) (pre mid post : List Term)
    (l : Literal) (a b d : Nat)
    (h : (Constr.mk (pre ++ (a, l) :: mid ++ (b, l) :: post) d).sat v) :
    (Constr.mk (pre ++ (a + b, l) :: mid ++ post) d).sat v := by
  simp only [Constr.sat] at *
  rw [evalSum_append] at h ⊢
  simp only [evalSum] at h ⊢
  rw [evalSum_append] at h ⊢
  simp only [evalSum] at h ⊢
  have hm : (a + b) * evalLit v l = a * evalLit v l + b * evalLit v l := Nat.add_mul a b _
  omega

-- Formula infrastructure (for metaprogram)

/-- A PB formula: conjunction of constraints represented as a list. -/
abbrev PBFmla := List Constr

/-- A formula with a single constraint. -/
def PBFmla.one (c : Constr) : PBFmla := [c]

/-- Conjunction of two formulas. -/
def PBFmla.and (a b : PBFmla) : PBFmla := a ++ b

/-- Formula `f` subsumes `f'` if every constraint in `f'` appears in `f`. -/
structure PBFmla.subsumes (f f' : PBFmla) : Prop where
  prop : ∀ x, x ∈ f' → x ∈ f

theorem PBFmla.subsumes_self (f : PBFmla) : f.subsumes f := ⟨fun _ h => h⟩

theorem PBFmla.subsumes_left (f f₁ f₂ : PBFmla) (H : f.subsumes (f₁.and f₂)) :
    f.subsumes f₁ :=
  ⟨fun _ h => H.prop _ <| List.mem_append.2 <| Or.inl h⟩

theorem PBFmla.subsumes_right (f f₁ f₂ : PBFmla) (H : f.subsumes (f₁.and f₂)) :
    f.subsumes f₂ :=
  ⟨fun _ h => H.prop _ <| List.mem_append.2 <| Or.inr h⟩

/-- All constraints in a formula are simultaneously satisfied. -/
structure PBFmla.allSat (v : Valuation) (f : PBFmla) : Prop where
  prop : ∀ c, c ∈ f → c.sat v

/-- A constraint is a semantic consequence of a formula. -/
def PBFmla.proof (f : PBFmla) (c : Constr) : Prop :=
  ∀ v : Valuation, f.allSat v → c.sat v

/-- A constraint provable from a subsumed formula is provable from the original. -/
theorem PBFmla.proof_of_subsumes {f : PBFmla} {c : Constr}
    (H : f.subsumes (PBFmla.one c)) : f.proof c :=
  fun _ h => h.prop _ <| H.prop _ <| List.Mem.head ..

-- allSat helpers (for pbc subproof lifting)

/-- Extract satisfaction of the left formula from a conjunction. -/
theorem allSat_and_left {v : Valuation} {f₁ f₂ : PBFmla}
    (h : PBFmla.allSat v (f₁.and f₂)) : PBFmla.allSat v f₁ :=
  ⟨fun c hc => h.prop c (List.mem_append.mpr (Or.inl hc))⟩

/-- Build allSat for a conjunction from allSat for each part. -/
theorem allSat_and_intro {v : Valuation} {f₁ f₂ : PBFmla}
    (h₁ : PBFmla.allSat v f₁) (h₂ : PBFmla.allSat v f₂) :
    PBFmla.allSat v (f₁.and f₂) :=
  ⟨fun c hc => match List.mem_append.mp hc with
    | Or.inl h => h₁.prop c h
    | Or.inr h => h₂.prop c h⟩

/-- Build allSat for a single-constraint formula. -/
theorem allSat_one {v : Valuation} {c : Constr}
    (h : c.sat v) : PBFmla.allSat v (PBFmla.one c) :=
  ⟨fun | _, List.Mem.head .. => h⟩

-- Proof by contradiction (pbc)

/-- **Proof by contradiction**: if assuming the negation of `C` leads to
    a contradiction (given all constraints in `f`), then `C` is a
    consequence of `f`. This is the soundness lemma for VeriPB's
    `pbc ... : subproof ... qed` steps. -/
theorem pbc_sound (f : PBFmla) (C : Constr) (hd : C.degree ≤ C.coeffSum)
    (h : ∀ v, f.allSat v → C.negate.sat v → False) :
    f.proof C :=
  fun v hv => Classical.byContradiction fun hn =>
    h v hv (negate_sat_of_not_sat C v hd hn)

-- Propositional reification infrastructure

section Reification
open Classical

/-- Convert a propositional valuation to a Bool valuation, using classical logic.
    For each `i`, `toBool pv i = true` iff `pv i` holds. -/
noncomputable def PropVal.toBool (pv : Nat → Prop) : Valuation :=
  fun i => @decide (pv i) (propDecidable (pv i))

/-- Construct a propositional valuation from a list of Prop values. -/
def PropVal.mk : List Prop → (Nat → Prop)
  | [], _ => False
  | a :: _, 0 => a
  | _ :: as, n + 1 => PropVal.mk as n

/-- `pv.implies p [a₁, ..., aₙ] k` unfolds to
    `(pv k ↔ a₁) → (pv (k+1) ↔ a₂) → ... → p`. -/
def PropVal.implies (pv : Nat → Prop) (p : Prop) : List Prop → Nat → Prop
  | [], _ => p
  | a :: as, n => (pv n ↔ a) → PropVal.implies pv p as (n + 1)

/-- The fundamental relationship between `mk` and `implies`:
    `(mk ps).implies p ps 0` is equivalent to `p`. -/
theorem PropVal.mk_implies {p} {as ps} (as₁) : as = List.reverseAux as₁ ps →
    PropVal.implies (PropVal.mk as) p ps as₁.length → p := by
  induction ps generalizing as₁ with
  | nil => exact fun _ => id
  | cons a as ih =>
    refine fun e H => @ih (a :: as₁) e (H ?_)
    subst e; clear ih H
    suffices ∀ n n', n' = List.length as₁ + n →
      ∀ bs, PropVal.mk (as₁.reverseAux bs) n' ↔ PropVal.mk bs n from this 0 _ rfl (a :: as)
    induction as₁ with
    | nil => simp
    | cons b as₁ ih => simpa using fun n bs => ih (n + 1) _ (Nat.succ_add ..) _

-- toBool bridge lemmas

theorem PropVal.toBool_iff (pv : Nat → Prop) (i : Nat) :
    PropVal.toBool pv i = true ↔ pv i := by
  unfold PropVal.toBool
  exact @decide_eq_true_iff _ (propDecidable (pv i))

theorem PropVal.toBool_false_iff (pv : Nat → Prop) (i : Nat) :
    PropVal.toBool pv i = false ↔ ¬ pv i := by
  unfold PropVal.toBool
  exact @decide_eq_false_iff_not _ (propDecidable (pv i))

theorem evalLit_toBool_pos_zero {pv : Nat → Prop} {i : Nat} {a : Prop}
    (h : pv i ↔ a) (h0 : evalLit (PropVal.toBool pv) (.pos i) = 0) : ¬a := by
  unfold evalLit at h0
  have hf : PropVal.toBool pv i = false := by split at h0 <;> simp_all
  exact fun ha => absurd (h.mpr ha) ((PropVal.toBool_false_iff pv i).mp hf)

theorem evalLit_toBool_neg_zero {pv : Nat → Prop} {i : Nat} {a : Prop}
    (h : pv i ↔ a) (h0 : evalLit (PropVal.toBool pv) (.neg i) = 0) : a := by
  unfold evalLit at h0
  have ht : PropVal.toBool pv i = true := by split at h0 <;> simp_all
  exact h.mp ((PropVal.toBool_iff pv i).mp ht)

-- Reify structures

/-- Asserts that if the formula is NOT satisfied under `toBool pv`, then `p` holds. -/
structure PBFmla.Reify (pv : Nat → Prop) (f : PBFmla) (p : Prop) : Prop where
  prop : ¬ PBFmla.allSat (PropVal.toBool pv) f → p

/-- Asserts that if constraint `c` is NOT satisfied under `toBool pv`, then `p` holds. -/
structure Constr.Reify (pv : Nat → Prop) (c : Constr) (p : Prop) : Prop where
  prop : ¬ c.sat (PropVal.toBool pv) → p

/-- Asserts that if literal `l` evaluates to 0 under `toBool pv`, then `p` holds. -/
structure Literal.Reify (pv : Nat → Prop) (l : Literal) (p : Prop) : Prop where
  prop : evalLit (PropVal.toBool pv) l = 0 → p

-- Reification theorems

/-- Main bridge: if the PB formula is unsatisfiable and every propositional valuation
    yields a reification proof, then `p` holds. -/
theorem PBFmla.refuteProp {p : Prop} {ps} (f : PBFmla)
    (hf : ∀ v : Valuation, PBFmla.allSat v f → False)
    (hv : ∀ pv : Nat → Prop, PropVal.implies pv (PBFmla.Reify pv f p) ps 0) : p :=
  (PropVal.mk_implies [] rfl (hv (PropVal.mk ps))).1 (hf (PropVal.toBool (PropVal.mk ps)))

variable {pv : Nat → Prop}

/-- Negation turns formula conjunction into disjunction:
`¬(allSat v (f₁ ++ f₂)) → a ∨ b` from `¬(allSat v f₁) → a`
and `¬(allSat v f₂) → b`. -/
theorem PBFmla.Reify_or {f₁ : PBFmla} {a : Prop} {f₂ : PBFmla} {b : Prop}
    (h₁ : PBFmla.Reify pv f₁ a) (h₂ : PBFmla.Reify pv f₂ b) :
    PBFmla.Reify pv (f₁.and f₂) (a ∨ b) := by
  refine ⟨fun H => byContradiction fun hn => H ⟨fun c h => byContradiction fun hn' => ?_⟩⟩
  rcases List.mem_append.1 h with h | h
  · exact hn (Or.inl (h₁.1 fun Hc => hn' (Hc.1 _ h)))
  · exact hn (Or.inr (h₂.1 fun Hc => hn' (Hc.1 _ h)))

/-- Reification of a single-constraint formula. -/
theorem PBFmla.Reify_one {c : Constr} {a : Prop}
    (h : Constr.Reify pv c a) : PBFmla.Reify pv (PBFmla.one c) a :=
  ⟨fun H => h.1 fun hsat => H ⟨fun | _, List.Mem.head .. => hsat⟩⟩

/-- Literal reification: positive literal evaluating to 0 implies ¬a. -/
theorem Literal.Reify_pos {a : Prop} {n : Nat} (h : pv n ↔ a) :
    Literal.Reify pv (.pos n) (¬a) :=
  ⟨fun h0 => evalLit_toBool_pos_zero h h0⟩

/-- Literal reification: negative literal evaluating to 0 implies a. -/
theorem Literal.Reify_neg {a : Prop} {n : Nat} (h : pv n ↔ a) :
    Literal.Reify pv (.neg n) a :=
  ⟨fun h0 => evalLit_toBool_neg_zero h h0⟩

/-- For CNF constraints: if the constraint (1·l :: rest, degree 1) is not satisfied,
    then literal l evaluates to 0 AND the rest is also not satisfied. -/
theorem Constr.Reify_cnf_and {l : Literal} {a : Prop} {rest : List Term} {b : Prop}
    (h₁ : Literal.Reify pv l a) (h₂ : Constr.Reify pv ⟨rest, 1⟩ b) :
    Constr.Reify pv ⟨(1, l) :: rest, 1⟩ (a ∧ b) := by
  constructor
  intro H
  have H' : ¬ (1 ≤ 1 * evalLit (PropVal.toBool pv) l + evalSum (PropVal.toBool pv) rest) := by
    exact H
  have hle := evalLit_le_one (PropVal.toBool pv) l
  have hlit : evalLit (PropVal.toBool pv) l = 0 := by omega
  have hrest : ¬ (1 ≤ evalSum (PropVal.toBool pv) rest) := by omega
  exact ⟨h₁.1 hlit, h₂.1 hrest⟩

/-- Empty constraint ¬(1 ≤ 0) is trivially True. -/
theorem Constr.Reify_cnf_zero : Constr.Reify pv ⟨[], 1⟩ True :=
  ⟨fun _ => trivial⟩

/-- Singleton CNF constraint. -/
theorem Constr.Reify_cnf_one {l : Literal} {a : Prop}
    (h₁ : Literal.Reify pv l a) : Constr.Reify pv ⟨[(1, l)], 1⟩ a :=
  ⟨fun H => ((Constr.Reify_cnf_and h₁ Constr.Reify_cnf_zero).1 H).1⟩

end Reification

-- Substitution infrastructure for redundance-based strengthening

section Substitution

/-- A substitution value: what a variable maps to under witness omega. -/
inductive SubstVal where
  | zero : SubstVal       -- variable maps to 0 (false)
  | one : SubstVal        -- variable maps to 1 (true)
  | posLit : Nat → SubstVal -- variable maps to another variable
  | negLit : Nat → SubstVal -- variable maps to negation of variable
  deriving Repr, BEq, Inhabited

/-- Look up a variable in a substitution list. -/
def lookupSubst (subst : List (Nat × SubstVal)) (var : Nat) :
    Option SubstVal :=
  match subst with
  | [] => none
  | (v, sv) :: rest => if v == var then some sv else lookupSubst rest var

/-- Apply a substitution to a single literal.
    Returns (constant_contribution, optional_remaining_term).
    If the variable is substituted to 0/1, the term becomes a constant.
    If substituted to another literal, the term is rewritten. -/
def applySubstTerm (subst : List (Nat × SubstVal))
    (a : Nat) (l : Literal) : Nat × Option Term :=
  match lookupSubst subst l.var with
  | none => (0, some (a, l))
  | some .zero => match l with
    | .pos _ => (0, none)
    | .neg _ => (a, none)
  | some .one => match l with
    | .pos _ => (a, none)
    | .neg _ => (0, none)
  | some (.posLit j) => match l with
    | .pos _ => (0, some (a, .pos j))
    | .neg _ => (0, some (a, .neg j))
  | some (.negLit j) => match l with
    | .pos _ => (0, some (a, .neg j))
    | .neg _ => (0, some (a, .pos j))

/-- Constant sum accumulated when applying substitution to a term list. -/
def substConstSum (subst : List (Nat × SubstVal)) :
    List Term → Nat
  | [] => 0
  | (a, l) :: rest =>
    (applySubstTerm subst a l).1 + substConstSum subst rest

/-- Remaining terms after applying substitution to a term list. -/
def substRemainingTerms (subst : List (Nat × SubstVal)) :
    List Term → List Term
  | [] => []
  | (a, l) :: rest =>
    match (applySubstTerm subst a l).2 with
    | none => substRemainingTerms subst rest
    | some t => t :: substRemainingTerms subst rest

/-- Apply a substitution to a constraint: substitute variables,
    accumulate constants, adjust degree. -/
def applySubstConstr (subst : List (Nat × SubstVal))
    (c : Constr) : Constr :=
  let k := substConstSum subst c.terms
  ⟨substRemainingTerms subst c.terms, c.degree - min c.degree k⟩

/-- Apply a substitution to a valuation: use omega for mapped variables,
    original valuation for unmapped ones. -/
def applyValuation (subst : List (Nat × SubstVal))
    (v : Valuation) : Valuation :=
  fun i => match lookupSubst subst i with
  | none => v i
  | some .zero => false
  | some .one => true
  | some (.posLit j) => v j
  | some (.negLit j) => !(v j)

/-- Each term evaluates identically under the substituted valuation and
    the decomposed (constant + remaining) form. -/
private theorem applySubstTerm_eval (subst : List (Nat × SubstVal))
    (v : Valuation) (a : Nat) (l : Literal) :
    a * evalLit (applyValuation subst v) l =
    (applySubstTerm subst a l).1 +
    match (applySubstTerm subst a l).2 with
    | none => 0
    | some (a', l') => a' * evalLit v l' := by
  unfold applySubstTerm applyValuation evalLit Literal.var
  cases l with
  | pos i =>
    cases h : lookupSubst subst i <;> simp [h]
    case some sv => cases sv <;> simp
                    case negLit j => cases v j <;> simp
  | neg i =>
    cases h : lookupSubst subst i <;> simp [h]
    case some sv => cases sv <;> simp
                    case negLit j => cases v j <;> simp

/-- evalSum under substituted valuation = substConstSum + evalSum of remaining. -/
theorem evalSum_subst (subst : List (Nat × SubstVal))
    (v : Valuation) (ts : List Term) :
    evalSum (applyValuation subst v) ts =
    substConstSum subst ts + evalSum v (substRemainingTerms subst ts) := by
  induction ts with
  | nil => simp [evalSum, substConstSum, substRemainingTerms]
  | cons hd tl ih =>
    obtain ⟨a, l⟩ := hd
    simp only [evalSum, substConstSum, substRemainingTerms]
    rw [ih]
    have h := applySubstTerm_eval subst v a l
    cases hopt : (applySubstTerm subst a l).2 with
    | none => simp at h; simp; omega
    | some t =>
      obtain ⟨a', l'⟩ := t
      simp only [hopt] at h
      simp only [evalSum]
      -- After rw [h], goal is:
      -- d + (a' * g) + (b + c) = d + b + ((a' * g) + c)
      -- which is just associativity/commutativity of Nat.add
      rw [h]
      simp only [Nat.add_assoc]
      congr 1
      rw [Nat.add_left_comm]

/-- Main substitution soundness: if the original constraint is satisfied
    by the substituted valuation, the substituted constraint is satisfied
    by the original valuation. -/
theorem applySubstConstr_sound (subst : List (Nat × SubstVal))
    (c : Constr) (v : Valuation) :
    c.sat (applyValuation subst v) →
    (applySubstConstr subst c).sat v := by
  intro h
  simp only [Constr.sat] at h ⊢
  simp only [applySubstConstr]
  have heq := evalSum_subst subst v c.terms
  have hmin : min c.degree (substConstSum subst c.terms) ≤
    substConstSum subst c.terms := Nat.min_le_right _ _
  omega

/-- If a variable is not in the substitution domain, applyValuation preserves it. -/
theorem applyValuation_noSubst (subst : List (Nat × SubstVal))
    (v : Valuation) (i : Nat) (h : lookupSubst subst i = none) :
    applyValuation subst v i = v i := by
  simp [applyValuation, h]

/-- If a literal's variable is not in the substitution domain,
    evalLit is preserved under applyValuation. -/
theorem evalLit_applyValuation_noSubst (subst : List (Nat × SubstVal))
    (v : Valuation) (l : Literal) (h : lookupSubst subst l.var = none) :
    evalLit (applyValuation subst v) l = evalLit v l := by
  cases l with
  | pos i =>
    simp only [Literal.var] at h
    simp only [evalLit]
    rw [applyValuation_noSubst subst v i h]
  | neg i =>
    simp only [Literal.var] at h
    simp only [evalLit]
    rw [applyValuation_noSubst subst v i h]

/-- Check if any term variable is in the substitution domain. -/
def termsAffected (subst : List (Nat × SubstVal)) : List Term → Bool
  | [] => false
  | (_, l) :: rest =>
    (lookupSubst subst l.var).isSome || termsAffected subst rest

/-- If no term variables are in the substitution domain,
    evalSum is preserved under applyValuation. -/
theorem evalSum_applyValuation_noSubst (subst : List (Nat × SubstVal))
    (v : Valuation) (ts : List Term)
    (h : termsAffected subst ts = false) :
    evalSum (applyValuation subst v) ts = evalSum v ts := by
  induction ts with
  | nil => simp [evalSum]
  | cons hd tl ih =>
    obtain ⟨a, l⟩ := hd
    simp only [termsAffected, Bool.or_eq_false_iff] at h
    simp only [evalSum]
    congr 1
    · congr 1
      have hvar : lookupSubst subst l.var = none := by
        cases hx : lookupSubst subst l.var
        · rfl
        · simp [hx] at h
      exact evalLit_applyValuation_noSubst subst v l hvar
    · exact ih h.2

/-- If no constraint variables are in the substitution domain,
    constraint satisfaction is preserved under applyValuation. -/
theorem constr_sat_applyValuation_noSubst (subst : List (Nat × SubstVal))
    (c : Constr) (v : Valuation)
    (h : termsAffected subst c.terms = false)
    (hsat : c.sat v) :
    c.sat (applyValuation subst v) := by
  simp only [Constr.sat] at hsat ⊢
  rw [evalSum_applyValuation_noSubst subst v c.terms h]
  exact hsat

/-- Converse of applySubstConstr_sound: if the substituted constraint is
    satisfied by v, the original is satisfied by the substituted valuation.
    Needed for the red rule: goal proofs give (G|ω).sat v, need G.sat (ω v). -/
theorem applySubstConstr_sat_rev (subst : List (Nat × SubstVal))
    (c : Constr) (v : Valuation) :
    (applySubstConstr subst c).sat v →
    c.sat (applyValuation subst v) := by
  intro h
  simp only [Constr.sat] at h ⊢
  simp only [applySubstConstr] at h
  have heq := evalSum_subst subst v c.terms
  -- heq: evalSum (applyValuation subst v) c.terms = substConstSum + evalSum v remaining
  -- h: evalSum v remaining ≥ c.degree - min c.degree (substConstSum)
  -- goal: evalSum (applyValuation subst v) c.terms ≥ c.degree
  rw [heq]
  have hmin : min c.degree (substConstSum subst c.terms) ≤
    substConstSum subst c.terms := Nat.min_le_right _ _
  have hmin2 : min c.degree (substConstSum subst c.terms) ≤ c.degree :=
    Nat.min_le_left _ _
  omega

end Substitution

end Sat.PB
