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
# Trusted Equitable Coloring Encoding

End-to-end verified equitable chromatic number: Lean encodes the
equitable k-coloring decision problem as PB constraints, verifies
a VeriPB kernel proof, and produces a mathematical theorem.

A proper k-coloring is *equitable* if all color classes have size
in {floor(n/k), ceil(n/k)}. The equitable chromatic number chi_eq(G)
is the smallest k admitting an equitable k-coloring.

The balance constraints are native PB: they encode cardinality bounds
directly as linear inequalities, which is impossible in pure SAT
without auxiliary encoding variables.

## Main definitions

* `EqColoring.Graph` -- a graph as vertex count + edge list
* `EqColoring.encode` -- PB encoding with balance constraints
* `EqColoring.hasEquitableColoring` -- mathematical predicate
* `EqColoring.no_eq_coloring_of_unsat` -- encoding soundness
* `eq_coloring_decide` -- command that calls RoundingSat + VeriPB
-/

namespace EqColoring

open Sat.PB

-- Graph representation

/-- A graph: number of vertices (0-indexed) and edge list. -/
structure Graph where
  numVerts : Nat
  edges : List (Nat × Nat)
  deriving Repr

-- Encoding

/-- Number of PB variables: one per (vertex, color) pair.
    Variable for vertex v with color c: v * k + c (0-based). -/
def numVars (g : Graph) (k : Nat) : Nat := g.numVerts * k

/-- Variable index for vertex v, color c (0-based). -/
def colorVar (k v c : Nat) : Nat := v * k + c

/-- ALO: at least one color per vertex.
    sum_c x_{v,c} >= 1 for each vertex v. -/
def mkALO (n k : Nat) : List Constr :=
  (List.range n).map fun v =>
    ⟨(List.range k).map fun c =>
      (1, Literal.pos (colorVar k v c)), 1⟩

/-- AMO: at most one color per vertex (pairwise).
    ~x_{v,c1} + ~x_{v,c2} >= 1 for each vertex v, c1 < c2. -/
def mkAMO (n k : Nat) : List Constr :=
  (List.range n).flatMap fun v =>
    (List.range k).flatMap fun c1 =>
      (List.range k).filterMap fun c2 =>
        if c1 < c2 then
          some ⟨[(1, Literal.neg (colorVar k v c1)),
                 (1, Literal.neg (colorVar k v c2))], 1⟩
        else none

/-- Properness: adjacent vertices get different colors.
    ~x_{u,c} + ~x_{v,c} >= 1 for each edge (u,v), color c. -/
def mkProper (edges : List (Nat × Nat)) (k : Nat) :
    List Constr :=
  edges.flatMap fun (u, v) =>
    (List.range k).map fun c =>
      ⟨[(1, Literal.neg (colorVar k u c)),
        (1, Literal.neg (colorVar k v c))], 1⟩

/-- Balance lower bound: each color class has at least
    floor(n/k) vertices.
    sum_v x_{v,c} >= floor(n/k) for each color c. -/
def mkBalanceLB (n k : Nat) : List Constr :=
  let lb := n / k
  (List.range k).map fun c =>
    ⟨(List.range n).map fun v =>
      (1, Literal.pos (colorVar k v c)), lb⟩

/-- Balance upper bound: each color class has at most
    ceil(n/k) vertices.
    sum_v ~x_{v,c} >= n - ceil(n/k) for each color c.
    (Equivalently: sum_v x_{v,c} <= ceil(n/k).) -/
def mkBalanceUB (n k : Nat) : List Constr :=
  let ub := (n + k - 1) / k
  (List.range k).map fun c =>
    ⟨(List.range n).map fun v =>
      (1, Literal.neg (colorVar k v c)), n - ub⟩

/-- Full encoding: ALO + AMO + properness + balance bounds. -/
def encode (g : Graph) (k : Nat) : Array Constr :=
  let alo := mkALO g.numVerts k
  let amo := mkAMO g.numVerts k
  let proper := mkProper g.edges k
  let balLB := mkBalanceLB g.numVerts k
  let balUB := mkBalanceUB g.numVerts k
  (alo ++ amo ++ proper ++ balLB ++ balUB).toArray

-- Mathematical predicate

/-- Count vertices with a given color. -/
def classSize (f : Nat → Nat) (n c : Nat) : Nat :=
  (List.range n).filter (fun v => f v == c) |>.length

/-- A k-coloring f is equitable for graph g if:
    1. Valid colors: f v < k for all vertices v
    2. Proper: adjacent vertices get different colors
    3. Balanced: each color class has size in
       [floor(n/k), ceil(n/k)] -/
def isEquitableColoring (g : Graph) (k : Nat)
    (f : Nat → Nat) : Prop :=
  (∀ v, v < g.numVerts → f v < k) ∧
  (∀ e ∈ g.edges, f e.1 ≠ f e.2) ∧
  (∀ c, c < k →
    g.numVerts / k ≤ classSize f g.numVerts c ∧
    classSize f g.numVerts c ≤
      (g.numVerts + k - 1) / k)

/-- Graph g admits an equitable k-coloring. -/
def hasEquitableColoring (g : Graph) (k : Nat) : Prop :=
  ∃ f : Nat → Nat, isEquitableColoring g k f

/-- k is the equitable chromatic number of g. -/
def equitableChromaticNumber (g : Graph) (k : Nat) :
    Prop :=
  hasEquitableColoring g k ∧
  (k = 0 ∨ ¬hasEquitableColoring g (k - 1))

-- Encoding soundness

/-- Convert an equitable coloring to a PB valuation.
    x_{v,c} = true iff f(v) = c. -/
def coloringToVal (f : Nat → Nat) (k : Nat) :
    Nat → Bool :=
  fun var => f (var / k) == var % k

/-- Key lemma: coloringToVal at colorVar simplifies to
    a direct comparison f v == c. -/
private theorem coloringToVal_at (f : Nat → Nat)
    (k v c : Nat) (hk : 0 < k) (hc : c < k) :
    coloringToVal f k (colorVar k v c) =
      (f v == c) := by
  simp only [coloringToVal, colorVar]
  congr 1
  · congr 1
    rw [Nat.mul_comm, Nat.mul_add_div hk,
      Nat.div_eq_of_lt hc]; omega
  · rw [Nat.mul_comm, Nat.mul_add_mod,
      Nat.mod_eq_of_lt hc]

/-- If one positive literal in the sum is true,
    evalSum >= 1. -/
private theorem evalSum_pos_ge_one (val : Valuation)
    (vars : List Nat) (x : Nat)
    (hmem : x ∈ vars) (htrue : val x = true) :
    1 ≤ evalSum val
      (vars.map fun v => (1, Literal.pos v)) := by
  induction vars with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [List.map, evalSum, evalLit]
    cases List.mem_cons.mp hmem with
    | inl heq => subst heq; simp [htrue]
    | inr htl => have := ih htl; omega

/-- ALO constraint for vertex v is satisfied by any valid
    coloring. -/
theorem alo_sat (k : Nat) (f : Nat → Nat) (v : Nat)
    (hfv : f v < k) :
    (⟨(List.range k).map fun c =>
      (1, Literal.pos (colorVar k v c)), 1⟩ :
      Constr).sat (coloringToVal f k) := by
  have hk : 0 < k := by omega
  simp only [Constr.sat]
  have hmap : (List.range k).map (fun c =>
      (1, Literal.pos (colorVar k v c))) =
    ((List.range k).map (colorVar k v)).map
      (fun x => (1, Literal.pos x)) := by
    simp [List.map_map]
  rw [hmap]
  apply evalSum_pos_ge_one
  · simp only [List.mem_map, List.mem_range]
    exact ⟨f v, hfv, rfl⟩
  · rw [coloringToVal_at f k v (f v) hk hfv]; simp

/-- AMO constraint is satisfied: x_{v,c1} and x_{v,c2}
    cannot both be true for c1 != c2. -/
theorem amo_sat (k v c1 c2 : Nat) (f : Nat → Nat)
    (hlt : c1 < c2) (hc2 : c2 < k) :
    (⟨[(1, Literal.neg (colorVar k v c1)),
       (1, Literal.neg (colorVar k v c2))], 1⟩ :
      Constr).sat (coloringToVal f k) := by
  have hk : 0 < k := by omega
  simp only [Constr.sat, evalSum, evalLit]
  rw [coloringToVal_at f k v c1 hk (by omega)]
  rw [coloringToVal_at f k v c2 hk hc2]
  by_cases h1 : f v == c1 <;>
    by_cases h2 : f v == c2 <;>
    simp_all [beq_iff_eq]

/-- Properness constraint is satisfied. -/
theorem proper_sat (k u v : Nat) (c : Nat)
    (f : Nat → Nat) (hne : f u ≠ f v) (hc : c < k) :
    (⟨[(1, Literal.neg (colorVar k u c)),
       (1, Literal.neg (colorVar k v c))], 1⟩ :
      Constr).sat (coloringToVal f k) := by
  have hk : 0 < k := by omega
  simp only [Constr.sat, evalSum, evalLit]
  rw [coloringToVal_at f k u c hk hc]
  rw [coloringToVal_at f k v c hk hc]
  by_cases h1 : f u == c <;>
    by_cases h2 : f v == c <;>
    simp_all [beq_iff_eq]

-- Helper: evalSum of pos literals counts true values
private theorem evalSum_pos_count (f : Nat → Bool)
    (vars : List Nat) :
    evalSum f (vars.map fun v => (1, Literal.pos v)) =
    (vars.filter f).length := by
  induction vars with
  | nil => simp [evalSum]
  | cons v vs ih =>
    simp only [List.map, evalSum, List.filter, ih,
      evalLit]
    cases f v <;> simp <;> omega

-- Helper: evalSum of neg literals counts false values
private theorem evalSum_neg_count (f : Nat → Bool)
    (vars : List Nat) :
    evalSum f (vars.map fun v => (1, Literal.neg v)) =
    (vars.filter (fun v => !f v)).length := by
  induction vars with
  | nil => simp [evalSum]
  | cons v vs ih =>
    simp only [List.map, evalSum, List.filter, ih,
      evalLit]
    cases f v <;> simp <;> omega

-- Helper: filter complement length identity
private theorem filter_length_compl {α : Type}
    (l : List α) (p : α → Bool) :
    (l.filter p).length +
    (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter]
    cases p hd <;> simp <;> omega

/-- evalSum of positive colorVar literals equals
    classSize. -/
private theorem evalSum_pos_colorVar (f : Nat → Nat)
    (k n c : Nat) (hc : c < k) :
    evalSum (coloringToVal f k)
      ((List.range n).map fun v =>
        (1, Literal.pos (colorVar k v c))) =
    classSize f n c := by
  have hk : 0 < k := by omega
  have hmap : (List.range n).map (fun v =>
      (1, Literal.pos (colorVar k v c))) =
    ((List.range n).map (fun v =>
      colorVar k v c)).map
      (fun x => (1, Literal.pos x)) := by
    simp [List.map_map]
  rw [hmap, evalSum_pos_count, List.filter_map,
    List.length_map]
  simp only [classSize, Function.comp_def]
  congr 1; apply List.filter_congr
  intro v _
  exact coloringToVal_at f k v c hk hc

/-- evalSum of negative colorVar literals equals
    n - classSize. -/
private theorem evalSum_neg_colorVar (f : Nat → Nat)
    (k n c : Nat) (hc : c < k) :
    evalSum (coloringToVal f k)
      ((List.range n).map fun v =>
        (1, Literal.neg (colorVar k v c))) =
    n - classSize f n c := by
  have hk : 0 < k := by omega
  have hmap : (List.range n).map (fun v =>
      (1, Literal.neg (colorVar k v c))) =
    ((List.range n).map (fun v =>
      colorVar k v c)).map
      (fun x => (1, Literal.neg x)) := by
    simp [List.map_map]
  rw [hmap, evalSum_neg_count, List.filter_map,
    List.length_map]
  simp only [classSize, Function.comp_def]
  have hcong : (List.range n).filter
      (fun v => !coloringToVal f k (colorVar k v c)) =
    (List.range n).filter
      (fun v => !(f v == c)) := by
    apply List.filter_congr
    intro v _; congr 1
    exact coloringToVal_at f k v c hk hc
  rw [hcong]
  have htotal := filter_length_compl
    (List.range n) (fun v => f v == c)
  simp [List.length_range] at htotal
  omega

/-- Every ALO constraint is satisfied by coloringToVal. -/
private theorem mkALO_allSat (n k : Nat)
    (f : Nat → Nat)
    (hvalid : ∀ v, v < n → f v < k) :
    ∀ c ∈ mkALO n k, c.sat (coloringToVal f k) := by
  intro c hc
  simp only [mkALO, List.mem_map, List.mem_range] at hc
  obtain ⟨v, hv, rfl⟩ := hc
  exact alo_sat k f v (hvalid v hv)

/-- Every AMO constraint is satisfied by coloringToVal. -/
private theorem mkAMO_allSat (n k : Nat)
    (f : Nat → Nat) :
    ∀ c ∈ mkAMO n k, c.sat (coloringToVal f k) := by
  intro c hc
  simp only [mkAMO, List.mem_flatMap, List.mem_range,
    List.mem_filterMap] at hc
  obtain ⟨v, _, c1, _, c2, hc2k, hif⟩ := hc
  split at hif
  · next hlt =>
    simp only [Option.some.injEq] at hif
    rw [← hif]
    exact amo_sat k v c1 c2 f hlt hc2k
  · simp at hif

/-- Every properness constraint is satisfied. -/
private theorem mkProper_allSat
    (edges : List (Nat × Nat)) (k : Nat)
    (f : Nat → Nat)
    (hproper : ∀ e ∈ edges, f e.1 ≠ f e.2) :
    ∀ c ∈ mkProper edges k,
      c.sat (coloringToVal f k) := by
  intro c hc
  simp only [mkProper, List.mem_flatMap, List.mem_map,
    List.mem_range] at hc
  obtain ⟨⟨u, v⟩, he, col, hcolk, rfl⟩ := hc
  exact proper_sat k u v col f (hproper (u, v) he) hcolk

/-- Every balance LB constraint is satisfied. -/
private theorem mkBalanceLB_allSat (n k : Nat)
    (f : Nat → Nat)
    (hbalance : ∀ c, c < k →
      n / k ≤ classSize f n c ∧
      classSize f n c ≤ (n + k - 1) / k) :
    ∀ c ∈ mkBalanceLB n k,
      c.sat (coloringToVal f k) := by
  intro constr hc
  simp only [mkBalanceLB, List.mem_map,
    List.mem_range] at hc
  obtain ⟨col, hcol, rfl⟩ := hc
  simp only [Constr.sat]
  rw [evalSum_pos_colorVar f k n col hcol]
  exact (hbalance col hcol).1

/-- Every balance UB constraint is satisfied. -/
private theorem mkBalanceUB_allSat (n k : Nat)
    (f : Nat → Nat)
    (hbalance : ∀ c, c < k →
      n / k ≤ classSize f n c ∧
      classSize f n c ≤ (n + k - 1) / k) :
    ∀ c ∈ mkBalanceUB n k,
      c.sat (coloringToVal f k) := by
  intro constr hc
  simp only [mkBalanceUB, List.mem_map,
    List.mem_range] at hc
  obtain ⟨col, hcol, rfl⟩ := hc
  simp only [Constr.sat]
  rw [evalSum_neg_colorVar f k n col hcol]
  have hbal := (hbalance col hcol).2
  omega

/-- If the encoding is unsatisfiable, no equitable
    k-coloring exists. -/
theorem no_eq_coloring_of_unsat (g : Graph) (k : Nat)
    (hunsat : ∀ v : Valuation,
      ∃ c ∈ (encode g k).toList, ¬c.sat v) :
    ¬hasEquitableColoring g k := by
  intro ⟨f, hvalid, hproper, hbalance⟩
  let val := coloringToVal f k
  obtain ⟨c, hc, hnsat⟩ := hunsat val
  apply hnsat
  have henc : (encode g k).toList =
      mkALO g.numVerts k ++ mkAMO g.numVerts k ++
      mkProper g.edges k ++ mkBalanceLB g.numVerts k ++
      mkBalanceUB g.numVerts k := by
    simp [encode]
  rw [henc] at hc
  simp only [List.mem_append] at hc
  rcases hc with hc | hc
  · rcases hc with hc | hc
    · rcases hc with hc | hc
      · rcases hc with hc | hc
        · exact mkALO_allSat g.numVerts k f
            hvalid c hc
        · exact mkAMO_allSat g.numVerts k f c hc
      · exact mkProper_allSat g.edges k f
          hproper c hc
    · exact mkBalanceLB_allSat g.numVerts k f
        hbalance c hc
  · exact mkBalanceUB_allSat g.numVerts k f
      hbalance c hc

-- Bridge theorem

private theorem exists_not_sat_of_allSat_false
    (ctx : PBFmla) (v : Valuation)
    (h : PBFmla.allSat v ctx → False) :
    ∃ c ∈ ctx, ¬c.sat v :=
  Classical.byContradiction fun hne =>
    h ⟨fun c hc =>
      Classical.byContradiction fun hnsat =>
        hne ⟨c, hc, hnsat⟩⟩

/-- Bridge from PBFmla refutation to equitable coloring
    impossibility. -/
theorem bridge (g : Graph) (k : Nat) (ctx : PBFmla)
    (hctx : ctx = (encode g k).toList)
    (hunsat : ∀ v : Valuation,
      PBFmla.allSat v ctx → False) :
    ¬hasEquitableColoring g k := by
  apply no_eq_coloring_of_unsat g k
  intro v
  rw [← hctx]
  exact exists_not_sat_of_allSat_false ctx v (hunsat v)

-- OPB generation

/-- Generate OPB format string for the equitable coloring
    encoding. -/
def toOPB (g : Graph) (k : Nat) : String := Id.run do
  let n := g.numVerts
  let nv := numVars g k
  let alo := mkALO n k
  let amo := mkAMO n k
  let proper := mkProper g.edges k
  let balLB := mkBalanceLB n k
  let balUB := mkBalanceUB n k
  let all := alo ++ amo ++ proper ++ balLB ++ balUB
  let nc := all.length
  let mut s := s!"* #variable= {nv} #constraint= {nc}"
  s := s ++ " #equal= 0 intsize= 6\n"
  for constr in all do
    for (coeff, lit) in constr.terms do
      match lit with
      | .pos v => s := s ++ s!"+{coeff} x{v + 1} "
      | .neg v => s := s ++ s!"+{coeff} ~x{v + 1} "
    s := s ++ s!">= {constr.degree} ;\n"
  return s

-- Witness verification

/-- Check that a coloring is a valid equitable
    k-coloring. -/
def checkEquitableColoring (g : Graph) (k : Nat)
    (f : Nat → Nat) : Bool :=
  -- Valid colors
  (List.range g.numVerts).all (fun v => f v < k) &&
  -- Proper
  g.edges.all (fun (u, v) => f u != f v) &&
  -- Balanced
  (List.range k).all (fun c =>
    let sz := classSize f g.numVerts c
    g.numVerts / k ≤ sz &&
      sz ≤ (g.numVerts + k - 1) / k)

theorem checkEquitableColoring_spec (g : Graph)
    (k : Nat) (f : Nat → Nat)
    (hcheck : checkEquitableColoring g k f = true) :
    isEquitableColoring g k f := by
  simp only [checkEquitableColoring,
    List.all_eq_true, decide_eq_true_eq,
    Bool.and_eq_true] at hcheck
  obtain ⟨⟨hvalid, hproper⟩, hbalance⟩ := hcheck
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    exact hvalid v (List.mem_range.mpr hv)
  · intro e he hne
    have := hproper e he
    simp [bne_iff_ne] at this
    exact this hne
  · intro c hc
    have := hbalance c (List.mem_range.mpr hc)
    simp only [] at this
    exact this

/-- Provide a witness for equitable coloring
    existence. -/
theorem witness_eq_coloring (g : Graph) (k : Nat)
    (f : Nat → Nat)
    (hcheck : checkEquitableColoring g k f = true) :
    hasEquitableColoring g k :=
  ⟨f, checkEquitableColoring_spec g k f hcheck⟩

-- Exhaustive search

/-- Reverse of `checkEquitableColoring_spec`: an
    equitable coloring passes the boolean check. -/
theorem checkEquitableColoring_complete
    (g : Graph) (k : Nat) (f : Nat → Nat)
    (h : isEquitableColoring g k f) :
    checkEquitableColoring g k f = true := by
  obtain ⟨hvalid, hproper, hbalance⟩ := h
  simp only [checkEquitableColoring, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro v hv
    exact hvalid v (List.mem_range.mp hv)
  · intro e he
    simp [bne_iff_ne, hproper e he]
  · intro c hc
    exact hbalance c (List.mem_range.mp hc)

/-- All k^n colorings as lists of length n. -/
private def allColoringsAux :
    Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | n + 1, k =>
    (allColoringsAux n k).flatMap fun prev =>
      (List.range k).map fun c => prev ++ [c]

/-- Convert a list to a total function
    (default 0 outside the list). -/
private def listToFun (l : List Nat) : Nat → Nat :=
  fun v => l.getD v 0

/-- Exhaustive check: returns true if no equitable
    k-coloring of g exists among all k^n
    assignments. -/
def noEquitableColoringExhaustive (g : Graph)
    (k : Nat) : Bool :=
  (allColoringsAux g.numVerts k).all fun l =>
    !(checkEquitableColoring g k (listToFun l))

private theorem listToFun_map_range (n : Nat)
    (f : Nat → Nat) (v : Nat) (hv : v < n) :
    listToFun ((List.range n).map f) v = f v := by
  simp only [listToFun, List.getD]
  rw [List.getElem?_map]; simp [hv]

private theorem allColoringsAux_complete (n k : Nat)
    (f : Nat → Nat) (hf : ∀ v, v < n → f v < k) :
    (List.range n).map f ∈ allColoringsAux n k := by
  induction n with
  | zero => simp [allColoringsAux]
  | succ n ih =>
    simp only [allColoringsAux, List.mem_flatMap,
      List.mem_map, List.mem_range]
    exact ⟨(List.range n).map f,
      ih (fun v hv => hf v (by omega)),
      f n, hf n (by omega),
      by simp [List.range_succ, List.map_append]⟩

private theorem isEquitable_listToFun (g : Graph)
    (k : Nat) (f : Nat → Nat)
    (h : isEquitableColoring g k f)
    (hedge : ∀ e ∈ g.edges,
      e.1 < g.numVerts ∧ e.2 < g.numVerts) :
    isEquitableColoring g k
      (listToFun
        ((List.range g.numVerts).map f)) := by
  obtain ⟨hvalid, hproper, hbalance⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    rw [listToFun_map_range _ _ _ hv]
    exact hvalid v hv
  · intro e he
    have ⟨h1, h2⟩ := hedge e he
    rw [listToFun_map_range _ _ _ h1,
        listToFun_map_range _ _ _ h2]
    exact hproper e he
  · intro c hc
    have : classSize
        (listToFun
          ((List.range g.numVerts).map f))
        g.numVerts c =
        classSize f g.numVerts c := by
      simp only [classSize]; congr 1
      apply List.filter_congr; intro v hv
      rw [listToFun_map_range _ _ _
        (List.mem_range.mp hv)]
    rw [this]; exact hbalance c hc

/-- If the exhaustive search finds no equitable
    k-coloring, then none exists.
    Requires edge endpoints to be valid vertices. -/
theorem no_eq_coloring_of_exhaustive (g : Graph)
    (k : Nat)
    (hedge : ∀ e ∈ g.edges,
      e.1 < g.numVerts ∧ e.2 < g.numVerts)
    (h : noEquitableColoringExhaustive g k = true) :
    ¬hasEquitableColoring g k := by
  intro ⟨f, hf⟩
  let l := (List.range g.numVerts).map f
  have hmem := allColoringsAux_complete
    g.numVerts k f hf.1
  have heq := isEquitable_listToFun g k f hf hedge
  have hcheck := checkEquitableColoring_complete
    g k (listToFun l) heq
  simp only [noEquitableColoringExhaustive,
    List.all_eq_true] at h
  have hfalse := h l hmem
  simp [hcheck] at hfalse

-- Elaboration commands

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

private def runCmdMeta (cmd : String)
    (args : Array String) (errCtx : String) :
    MetaM String := do
  let result ← IO.Process.output
    { cmd := cmd, args := args }
  if result.exitCode != 0 then
    throwError "{errCtx}: {cmd} failed (exit \
      {result.exitCode})\nstderr: {result.stderr}\
      \nstdout: {result.stdout}"
  return result.stdout

private def extractEdgeList (e : Expr) :
    MetaM (List (Nat × Nat)) := do
  let mut result : List (Nat × Nat) := []
  let mut curr := e
  while true do
    if let some (_, hdExpr, tlExpr) :=
        curr.app3? ``List.cons then
      if let some (_, _, uExpr, vExpr) :=
          hdExpr.app4? ``Prod.mk then
        let some u := uExpr.rawNatLit?
          | throwError "edge vertex not a literal"
        let some v := vExpr.rawNatLit?
          | throwError "edge vertex not a literal"
        result := (u, v) :: result
        curr := tlExpr
      else throwError "edge not a Prod.mk"
    else if curr.isAppOf ``List.nil then break
    else throwError "edges not a proper list"
  return result.reverse

private def buildBridgeProof (gExpr kExpr : Expr)
    (ctx : Expr) (pbProofConst : Expr) :
    MetaM (Expr × Expr) := do
  let finalType := mkApp (mkConst ``Not)
    (mkApp2 (mkConst ``hasEquitableColoring)
      gExpr kExpr)
  let hctxProof := mkApp2
    (mkConst ``Eq.refl [.succ .zero])
    (mkConst ``Sat.PB.PBFmla) ctx
  let finalProof := mkApp5
    (mkConst ``EqColoring.bridge)
    gExpr kExpr ctx hctxProof pbProofConst
  return (finalType, finalProof)

-- `eq_coloring_decide name G k` proves
-- not hasEquitableColoring G k via solver
elab "eq_coloring_decide " nm:ident ppSpace
    gExpr:term:max ppSpace kTerm:term : command => do
  let name := (← getCurrNamespace) ++ nm.getId
  liftTermElabM do
    let gVal ← Lean.Elab.Term.elabTerm gExpr
      (some (mkConst ``Graph))
    let gVal ← instantiateMVars gVal
    let kVal ← Lean.Elab.Term.elabTerm kTerm
      (some (mkConst ``Nat))
    let kVal ← instantiateMVars kVal
    let gReduced ← withTransparency .all
      (reduce gVal (skipTypes := false)
        (skipProofs := true))
    let kReduced ← withTransparency .all
      (reduce kVal (skipTypes := false)
        (skipProofs := true))
    let some (numVertsExpr, edgesExpr) :=
        gReduced.app2? ``Graph.mk
      | throwError "could not reduce graph to Graph.mk"
    let some nv := numVertsExpr.rawNatLit?
      | throwError "could not extract numVerts"
    let edges ← extractEdgeList edgesExpr
    let some k := kReduced.rawNatLit?
      | throwError "could not extract k"
    let g : Graph := ⟨nv, edges⟩
    let tmpDir ← IO.Process.output
      { cmd := "mktemp", args := #["-d"] }
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
      IO.FS.writeFile (System.FilePath.mk opbPath)
        (toOPB g k)
      let _ ← runCmdMeta "roundingsat"
        #[opbPath, s!"--proof-log={augPath}"]
        "RoundingSat"
      let _ ← runCmdMeta "veripb"
        #["--elaborate", kernelPath, opbPath, augPath]
        "VeriPB"
    catch e =>
      cleanup
      throw e
    let proofStr ← IO.FS.readFile
      (System.FilePath.mk kernelPath)
    cleanup
    let constrs := encode g k
    let nvars := numVars g k
    let auxName := name ++ `aux
    let (ctx, _ctx', pbProofConst) ←
      VeriPB.fromVeriPBDirect constrs nvars proofStr
        auxName
    let (finalType, finalProof) ←
      buildBridgeProof gVal kVal ctx pbProofConst
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := finalType
      value := finalProof
    }
    Lean.logInfo
      m!"Registered {name} : \
        ¬ hasEquitableColoring G {k}"

-- Reflection-based verification
elab "eq_coloring_reflect " nm:ident ppSpace
    gExpr:term:max ppSpace kTerm:num
    ppSpace proofFile:str : command => do
  let name := (← getCurrNamespace) ++ nm.getId
  let k := kTerm.getNat
  let proofPath := proofFile.getString
  liftTermElabM do
    let gVal ← Lean.Elab.Term.elabTerm gExpr
      (some (mkConst ``Graph))
    let gVal ← instantiateMVars gVal
    let kVal := mkRawNatLit k
    let proofStr ← IO.FS.readFile
      (System.FilePath.mk proofPath)
    let constrsExpr := mkApp2
      (mkConst ``encode) gVal kVal
    let numVarsExpr := mkApp2
      (mkConst ``numVars) gVal kVal
    let proofStrExpr := mkStrLit proofStr
    let checkExpr := mkApp3
      (mkConst ``VeriPB.Reflect.checkProofBool)
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
    let reduceBoolApp :=
      mkApp (mkConst ``Lean.reduceBool) auxConst
    let rflPrf := mkApp2
      (mkConst ``Eq.refl [.succ .zero])
      (mkConst ``Bool) reduceBoolApp
    let hEqTrue := mkApp3
      (mkConst ``Lean.ofReduceBool)
      auxConst (mkConst ``Bool.true) rflPrf
    let unsatProof := mkApp4
      (mkConst ``VeriPB.Reflect.checkProof_sound)
      constrsExpr numVarsExpr proofStrExpr hEqTrue
    let finalProof := mkApp3
      (mkConst ``no_eq_coloring_of_unsat)
      gVal kVal unsatProof
    let finalType := mkApp (mkConst ``Not)
      (mkApp2 (mkConst ``hasEquitableColoring)
        gVal kVal)
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := finalType
      value := finalProof
    }
    Lean.logInfo
      m!"Registered {name} : \
        ¬ hasEquitableColoring (reflection)"

end EqColoring

-- ============================================================
-- Showcase: Equitable chromatic number of K_{3,3,1}
-- ============================================================

namespace EqColoringShowcase

open EqColoring

/-- The complete tripartite graph K_{3,3,1}:
    7 vertices, 15 edges. -/
def k331 : Graph :=
  ⟨7, [(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),
       (2,4),(2,5),(0,6),(1,6),(2,6),(3,6),(4,6),
       (5,6)]⟩

-- No equitable 4-coloring (verified via VeriPB reflection checker)
eq_coloring_reflect k331_no_eq4 k331 4
  "applications/eqcoloring/k331_4_kernel.pbp"

-- Witness: A uses {1,2}, B uses {3,4}, C uses {0}
private def k331_coloring5 : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 3
  | _ => 0

theorem k331_eq5_exists :
    hasEquitableColoring k331 5 :=
  witness_eq_coloring k331 5 k331_coloring5
    (by native_decide)

/-- The equitable chromatic number of K_{3,3,1} is 5. -/
theorem k331_eq_chromatic :
    equitableChromaticNumber k331 5 :=
  ⟨k331_eq5_exists, Or.inr k331_no_eq4⟩

end EqColoringShowcase
