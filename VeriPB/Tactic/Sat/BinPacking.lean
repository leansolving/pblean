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
# Trusted Bin Packing Encoding

End-to-end verified bin packing impossibility: Lean encodes the bin
packing decision problem as PB constraints, verifies a VeriPB kernel
proof, and produces a mathematical theorem that a set of items cannot
fit into the given number of bins with the given capacity.

Given items with sizes s_0, ..., s_{n-1}, m bins each of capacity C,
the question is whether there exists an assignment of items to bins
such that the total size in each bin is at most C.

## Main results

* `BinPacking.bp12_5_impossible` -- 12 items of sizes [10,9,8,8,6,5,4,4,4,4,4,4]
  do not fit into 5 bins of capacity 14

## Infrastructure

* `BinPacking.encode` -- PB constraint encoding
* `BinPacking.no_packing_of_unsat` -- encoding soundness
* `binpack_reflect` -- elaboration command
-/

namespace BinPacking

open Sat.PB

-- Instance

/-- A bin packing instance: item sizes, number of bins, bin capacity. -/
structure Instance where
  sizes : List Nat
  numBins : Nat
  capacity : Nat
  deriving Repr

/-- Number of items. -/
def Instance.numItems (inst : Instance) : Nat := inst.sizes.length

/-- Total size of all items. -/
def Instance.totalSize (inst : Instance) : Nat := inst.sizes.foldl (· + ·) 0

-- Variable indexing

/-- Variable index for "item i is in bin j" with m bins. -/
def varIdx (m : Nat) (i j : Nat) : Nat := i * m + j

theorem varIdx_div {m i j : Nat} (hm : 0 < m) (hj : j < m) :
    varIdx m i j / m = i := by
  simp only [varIdx]
  rw [show i * m + j = j + i * m by omega]
  rw [Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hj, Nat.zero_add]

theorem varIdx_mod {m i j : Nat} (_hm : 0 < m) (hj : j < m) :
    varIdx m i j % m = j := by
  simp only [varIdx]
  rw [show i * m + j = j + i * m by omega]
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

-- Mathematical predicate

/-- Load of bin j under assignment assign: sum of sizes[k] for k < bound with assign k = j. -/
def binLoad (sizes : List Nat) (assign : Nat → Nat) (j : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (if assign k = j then sizes[k]! else 0) + binLoad sizes assign j k

/-- A valid packing: each item goes to a valid bin, each bin within capacity. -/
def isValidPacking (inst : Instance) (assign : Nat → Nat) : Prop :=
  (∀ i, i < inst.numItems → assign i < inst.numBins) ∧
  (∀ j, j < inst.numBins → binLoad inst.sizes assign j inst.numItems ≤ inst.capacity)

/-- The instance has a valid packing. -/
def hasPacking (inst : Instance) : Prop :=
  ∃ assign : Nat → Nat, isValidPacking inst assign

-- Encoding

/-- Assignment constraint for item i: item must go in at least one bin. -/
def mkAssignConstr (m : Nat) (i : Nat) : Constr :=
  ⟨(List.range m).map fun j => (1, Literal.pos (varIdx m i j)), 1⟩

/-- Capacity constraint for bin j (negated form):
    sum_i sizes[i] * neg(x_{i,j}) >= totalSize - capacity. -/
def mkCapConstr (inst : Instance) (j : Nat) : Constr :=
  ⟨(List.range inst.numItems).map fun i =>
    (inst.sizes[i]!, Literal.neg (varIdx inst.numBins i j)),
   inst.totalSize - inst.capacity⟩

/-- Full encoding: n assignment constraints + m capacity constraints. -/
def encode (inst : Instance) : Array Constr :=
  let assignConstrs := (List.range inst.numItems).map (mkAssignConstr inst.numBins)
  let capConstrs := (List.range inst.numBins).map (mkCapConstr inst)
  (assignConstrs ++ capConstrs).toArray

-- Valuation from packing

/-- Valuation encoding an assignment: variable v encodes "item v/m is in bin v%m". -/
def packingVal (m : Nat) (assign : Nat → Nat) (v : Nat) : Bool :=
  if m == 0 then false else assign (v / m) == (v % m)

-- Helper lemmas

private theorem beq_nat_false_of_pos {m : Nat} (hm : 0 < m) : (m == 0) = false := by
  simp [Nat.ne_of_gt hm]

theorem evalLit_pos_packingVal (m : Nat) (assign : Nat → Nat) (i j : Nat)
    (hm : 0 < m) (hj : j < m) :
    evalLit (packingVal m assign) (Literal.pos (varIdx m i j)) =
      if assign i = j then 1 else 0 := by
  simp only [evalLit, packingVal, varIdx_div hm hj, varIdx_mod hm hj,
    beq_nat_false_of_pos hm, Bool.false_eq_true, ↓reduceIte]
  cases h : (assign i == j)
  · simp only [beq_eq_false_iff_ne] at h; simp [h]
  · simp only [beq_iff_eq] at h; simp [h]

theorem evalLit_neg_packingVal (m : Nat) (assign : Nat → Nat) (i j : Nat)
    (hm : 0 < m) (hj : j < m) :
    evalLit (packingVal m assign) (Literal.neg (varIdx m i j)) =
      if assign i = j then 0 else 1 := by
  simp only [evalLit, packingVal, varIdx_div hm hj, varIdx_mod hm hj,
    beq_nat_false_of_pos hm, Bool.false_eq_true, ↓reduceIte]
  cases h : (assign i == j)
  · simp only [beq_eq_false_iff_ne] at h; simp [h]
  · simp only [beq_iff_eq] at h; simp [h]

theorem evalSum_ge_mem (f : Valuation) :
    ∀ (ts : List Term) (t : Term), t ∈ ts →
    t.1 * evalLit f t.2 ≤ evalSum f ts := by
  intro ts t hmem; induction ts with
  | nil => exact absurd hmem (List.not_mem_nil)
  | cons hd tl ih =>
    simp only [evalSum]
    rcases List.mem_cons.mp hmem with rfl | htl
    · omega
    · have := ih htl; omega

-- Soundness: assignment constraints

theorem assignConstr_sat (m : Nat) (assign : Nat → Nat) (i : Nat)
    (hm : 0 < m) (hbin : assign i < m) :
    (mkAssignConstr m i).sat (packingVal m assign) := by
  simp only [Constr.sat, mkAssignConstr]
  have hmem : (1, Literal.pos (varIdx m i (assign i))) ∈
      (List.range m).map fun j => (1, Literal.pos (varIdx m i j)) :=
    List.mem_map.mpr ⟨assign i, List.mem_range.mpr hbin, rfl⟩
  have hge := evalSum_ge_mem (packingVal m assign) _ _ hmem
  rw [evalLit_pos_packingVal m assign i (assign i) hm hbin] at hge
  simp at hge; omega

-- Soundness: capacity constraints
-- Strategy: connect evalSum of negated literals to sumIf, use complement identity

/-- Sum of sizes[k] for k < bound where p k is true. -/
def sumIf (sizes : List Nat) (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => (if p k then sizes[k]! else 0) + sumIf sizes p k

/-- Sum of all sizes[k] for k < bound. -/
def sumAll (sizes : List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => sizes[k]! + sumAll sizes k

theorem sumIf_complement (sizes : List Nat) (p : Nat → Bool) :
    ∀ k, sumIf sizes p k + sumIf sizes (fun i => !p i) k = sumAll sizes k := by
  intro k; induction k with
  | zero => simp [sumIf, sumAll]
  | succ n ih =>
    show (if p n = true then sizes[n]! else 0) + sumIf sizes p n +
        ((if (!p n) = true then sizes[n]! else 0) + sumIf sizes (fun i => !p i) n) =
        sizes[n]! + sumAll sizes n
    have hrearr : (if p n = true then sizes[n]! else 0) + sumIf sizes p n +
        ((if (!p n) = true then sizes[n]! else 0) + sumIf sizes (fun i => !p i) n) =
        ((if p n = true then sizes[n]! else 0) + (if (!p n) = true then sizes[n]! else 0)) +
        (sumIf sizes p n + sumIf sizes (fun i => !p i) n) := by omega
    rw [hrearr, ih]
    cases p n <;> simp

/-- binLoad equals sumIf with the predicate "assign k = j". -/
theorem binLoad_eq_sumIf (sizes : List Nat) (assign : Nat → Nat) (j : Nat) :
    ∀ k, binLoad sizes assign j k = sumIf sizes (fun i => decide (assign i = j)) k := by
  intro k; induction k with
  | zero => simp [binLoad, sumIf]
  | succ n ih =>
    simp only [binLoad, sumIf, ih]
    congr 1
    split
    · next h => simp [h]
    · next h => simp [h]

/-- evalSum of negated literal terms equals sumIf of negated predicate. -/
theorem evalSum_neg_eq_sumIf (sizes : List Nat) (m : Nat) (assign : Nat → Nat) (j : Nat)
    (hm : 0 < m) (hj : j < m) :
    ∀ k, evalSum (packingVal m assign)
      ((List.range k).map fun i => (sizes[i]!, Literal.neg (varIdx m i j))) =
    sumIf sizes (fun i => !(decide (assign i = j))) k := by
  intro k; induction k with
  | zero => simp [evalSum, sumIf]
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      evalSum_append]
    rw [ih]
    simp only [evalSum, Nat.add_zero]
    rw [Nat.add_comm]
    congr 1
    rw [evalLit_neg_packingVal m assign n j hm hj]
    split
    · next h => simp [h]
    · next h => simp [h]

/-- Helper: foldl (· + ·) acc l = acc + foldl (· + ·) 0 l -/
theorem foldl_add_acc : ∀ (l : List Nat) (acc : Nat),
    l.foldl (· + ·) acc = acc + l.foldl (· + ·) 0 := by
  intro l; induction l with
  | nil => simp [List.foldl]
  | cons h t ih =>
    intro acc
    show List.foldl (· + ·) (acc + h) t = acc + List.foldl (· + ·) (0 + h) t
    rw [ih (acc + h), ih (0 + h)]
    omega

/-- sumAll over the full list equals foldl sum. -/
theorem sumAll_eq_foldl (sizes : List Nat) :
    ∀ k, k ≤ sizes.length →
    sumAll sizes k + (sizes.drop k).foldl (· + ·) 0 = sizes.foldl (· + ·) 0 := by
  intro k hk; induction k with
  | zero => simp [sumAll, List.drop]
  | succ n ih =>
    have hn : n < sizes.length := by omega
    simp only [sumAll]
    have hdrop : sizes.drop n = sizes[n] :: sizes.drop (n + 1) :=
      List.drop_eq_getElem_cons hn
    have h_prev := ih (by omega)
    rw [hdrop] at h_prev
    -- h_prev now has foldl (· + ·) (0 + sizes[n]) ...
    -- goal needs foldl (· + ·) 0 (drop (n+1))
    rw [show sizes[n]! = sizes[n] from by simp [getElem!_def, List.getElem?_eq_getElem hn]]
    -- Use foldl_add_acc to rewrite h_prev
    show sizes[n] + sumAll sizes n + List.foldl (· + ·) 0 (sizes.drop (n + 1)) =
        List.foldl (· + ·) 0 sizes
    have hfoldl : List.foldl (· + ·) (0 + sizes[n]) (sizes.drop (n + 1)) =
        sizes[n] + List.foldl (· + ·) 0 (sizes.drop (n + 1)) := by
      rw [foldl_add_acc]; omega
    simp only [List.foldl] at h_prev
    rw [hfoldl] at h_prev
    omega

theorem totalSize_eq_sumAll_full (inst : Instance) :
    inst.totalSize = sumAll inst.sizes inst.numItems := by
  simp only [Instance.totalSize, Instance.numItems]
  have h := sumAll_eq_foldl inst.sizes inst.sizes.length (Nat.le_refl _)
  simp [List.drop_length] at h
  omega

theorem capConstr_sat (inst : Instance) (assign : Nat → Nat) (j : Nat)
    (hm : 0 < inst.numBins) (hj : j < inst.numBins)
    (hcap : binLoad inst.sizes assign j inst.numItems ≤ inst.capacity)
    (hle : inst.capacity ≤ inst.totalSize) :
    (mkCapConstr inst j).sat (packingVal inst.numBins assign) := by
  simp only [Constr.sat, mkCapConstr]
  rw [evalSum_neg_eq_sumIf inst.sizes inst.numBins assign j hm hj inst.numItems]
  -- Need: inst.totalSize - inst.capacity ≤ sumIf(¬inBin, n)
  -- From complement: sumIf(inBin) + sumIf(¬inBin) = sumAll = totalSize
  -- From hcap: sumIf(inBin) ≤ capacity (after rewriting binLoad)
  -- So: sumIf(¬inBin) = totalSize - sumIf(inBin) ≥ totalSize - capacity
  rw [binLoad_eq_sumIf] at hcap
  have hcomp := sumIf_complement inst.sizes (fun i => decide (assign i = j)) inst.numItems
  rw [totalSize_eq_sumAll_full] at hle
  -- hle : inst.capacity ≤ sumAll inst.sizes inst.numItems
  -- hcomp : sumIf(inBin) + sumIf(¬inBin) = sumAll
  -- hcap : sumIf(inBin) ≤ inst.capacity
  -- goal : inst.totalSize - inst.capacity ≤ sumIf(¬inBin)
  -- Since totalSize = sumAll (from hle direction), and totalSize - cap is Nat sub
  show inst.totalSize - inst.capacity ≤
    sumIf inst.sizes (fun i => !decide (assign i = j)) inst.numItems
  rw [totalSize_eq_sumAll_full]
  omega

-- Main soundness theorem

theorem encode_mem_sat (inst : Instance) (assign : Nat → Nat)
    (hm : 0 < inst.numBins)
    (hle : inst.capacity ≤ inst.totalSize)
    (hpacking : isValidPacking inst assign) :
    ∀ c ∈ (encode inst).toList, c.sat (packingVal inst.numBins assign) := by
  intro c hc
  have henc : (encode inst).toList =
      (List.range inst.numItems).map (mkAssignConstr inst.numBins) ++
      (List.range inst.numBins).map (mkCapConstr inst) := by
    simp [encode]
  rw [henc] at hc
  simp only [List.mem_append] at hc
  obtain ⟨hbin, hcapacity⟩ := hpacking
  rcases hc with hc | hc
  · simp only [List.mem_map, List.mem_range] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    exact assignConstr_sat inst.numBins assign i hm (hbin i hi)
  · simp only [List.mem_map, List.mem_range] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    exact capConstr_sat inst assign j hm hj (hcapacity j hj) hle

/-- If the encoding is UNSAT, no valid packing exists (assuming capacity <= totalSize). -/
theorem no_packing_of_unsat (inst : Instance)
    (hm : 0 < inst.numBins)
    (hle : inst.capacity ≤ inst.totalSize)
    (hunsat : ∀ v : Valuation, ∃ c ∈ (encode inst).toList, ¬c.sat v) :
    ¬hasPacking inst := by
  intro ⟨assign, hpacking⟩
  obtain ⟨c, hc, hnsat⟩ := hunsat (packingVal inst.numBins assign)
  exact hnsat (encode_mem_sat inst assign hm hle hpacking c hc)

-- OPB generation

/-- Generate OPB format string for the bin packing encoding. -/
def toOPB (inst : Instance) : String := Id.run do
  let n := inst.numItems
  let m := inst.numBins
  let totalVars := n * m
  let numConstrs := n + m
  let mut s := s!"* #variable= {totalVars} #constraint= {numConstrs} #equal= 0 intsize= 6\n"
  for i in List.range n do
    for j in List.range m do
      s := s ++ s!"+1 x{varIdx m i j + 1} "
    s := s ++ ">= 1 ;\n"
  let ts := inst.totalSize
  for j in List.range m do
    for i in List.range n do
      s := s ++ s!"+{inst.sizes[i]!} ~x{varIdx m i j + 1} "
    s := s ++ s!">= {ts - inst.capacity} ;\n"
  return s

-- Elaboration commands

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

-- Reflection-based verification
elab "binpack_reflect " nm:ident ppSpace instTerm:term:max ppSpace proofFile:str : command => do
  let name := (← getCurrNamespace) ++ nm.getId
  let proofPath := proofFile.getString
  liftTermElabM do
    let instExpr ← Lean.Elab.Term.elabTerm instTerm (some (mkConst ``Instance))
    let instExpr ← instantiateMVars instExpr
    -- Reduce to get concrete values for numItems, numBins
    let instVal ← withTransparency .all <| reduce instExpr
    -- Extract fields: Instance.mk sizes numBins capacity (3 explicit args)
    let some (sizesExpr, numBinsExpr, _capExpr) := instVal.app3? ``Instance.mk
      | throwError "could not reduce Instance to Instance.mk"
    let numItemsExpr := mkApp2 (mkConst ``List.length [.zero]) (mkConst ``Nat) sizesExpr
    let numItemsVal ← withTransparency .all <| reduce numItemsExpr
    let some numItems := numItemsVal.rawNatLit?
      | throwError "could not reduce numItems to a literal"
    let numBinsVal ← withTransparency .all <| reduce numBinsExpr
    let some numBins := numBinsVal.rawNatLit?
      | throwError "could not reduce numBins to a literal"
    let numVars := numItems * numBins
    let numVarsExpr := mkRawNatLit numVars
    let proofStr ← IO.FS.readFile (System.FilePath.mk proofPath)
    let constrsExpr := mkApp (mkConst ``encode) instExpr
    let proofStrExpr := mkStrLit proofStr
    let checkExpr := mkApp3 (mkConst ``VeriPB.Reflect.checkProofBool)
      constrsExpr numVarsExpr proofStrExpr
    let hEqTrue ← match ← Lean.Meta.nativeEqTrue `binpack_reflect checkExpr
        (axiomDeclRange? := (← getRef)) with
      | .success prf => pure prf
      | .notTrue => throwError "Reflection checker returned false for {name}"
    let unsatProof := mkApp4
      (mkConst ``VeriPB.Reflect.checkProof_sound)
      constrsExpr numVarsExpr proofStrExpr hEqTrue
    -- Build side-condition proofs via mkDecideProof
    if numBins == 0 then throwError "numBins must be positive"
    let hmType := mkApp4 (mkConst ``LT.lt [.zero])
      (mkConst ``Nat) (mkConst ``instLTNat) (mkRawNatLit 0)
      (mkApp (mkConst ``Instance.numBins) instExpr)
    let hmProof ← mkDecideProof hmType
    let hleType := mkApp4 (mkConst ``LE.le [.zero])
      (mkConst ``Nat) (mkConst ``instLENat)
      (mkApp (mkConst ``Instance.capacity) instExpr)
      (mkApp (mkConst ``Instance.totalSize) instExpr)
    let hleProof ← mkDecideProof hleType
    let finalProof := mkApp4 (mkConst ``no_packing_of_unsat)
      instExpr hmProof hleProof unsatProof
    let finalType := mkApp (mkConst ``Not)
      (mkApp (mkConst ``hasPacking) instExpr)
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := finalType
      value := finalProof
    }
    Lean.logInfo m!"Registered {name} : ¬ hasPacking"

-- Concrete instance

/-- 12 items (sizes [10,9,8,8,6,5,4,4,4,4,4,4]), 5 bins, capacity 14.
    Total size = 70 = 5×14, so not refutable by total weight alone.
    UNSAT via rounding: with m=4, heavy items (≥8) need 2 slots,
    light items (≥4) need 1 slot, each bin has ≤3 slots (14/4=3),
    but total demand is 2×4+8=16 > 15=3×5. Not AMO-reducible:
    pairs like 10+4=14 and triples like 4+4+4=12 fit. -/
def inst12_5 : Instance :=
  { sizes := [10, 9, 8, 8, 6, 5, 4, 4, 4, 4, 4, 4]
    numBins := 5
    capacity := 14 }

-- Impossibility verified via VeriPB reflection checker
binpack_reflect bp12_5_impossible inst12_5
  "applications/binpack/bp12_5_kernel.pbp"

end BinPacking
