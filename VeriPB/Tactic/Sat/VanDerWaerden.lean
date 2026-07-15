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
# Trusted Van der Waerden Encoding

End-to-end verified Van der Waerden numbers: Lean encodes the
AP-freeness decision problem as PB constraints, verifies a VeriPB
kernel proof, and produces a mathematical theorem about W(2,3).

A 2-coloring of {1,...,n} is *AP-free* if there is no monochromatic
3-term arithmetic progression (a, a+d, a+2d). The Van der Waerden
number W(2,3) = 9 means {1,...,8} can be 2-colored without a
monochromatic 3-AP, but {1,...,9} cannot.

## Main results

* `vdw8_exists` -- W(2,3) lower bound: {1,...,8} is AP-free
* `vdw9_impossible` -- W(2,3) upper bound: {1,...,9} is not
* `vdw_number_2_3` -- W(2,3) = 9

## Infrastructure

* `VanDerWaerden.apTriples` -- enumerate 3-APs (a,a+d,a+2d)
* `VanDerWaerden.encode` -- PB constraint encoding
* `VanDerWaerden.no_ap_free_of_unsat` -- encoding soundness
* `vdw_decide` / `vdw_reflect` -- elaboration commands
-/

namespace VanDerWaerden

open Sat.PB

-- Arithmetic progressions

/-- 3-term APs (a, a+d, a+2*d) with a ≥ 1, d ≥ 1, a+2*d ≤ n. -/
def apTriples (n : Nat) : List (Nat × Nat × Nat) :=
  (List.range n).flatMap fun d0 =>
    (List.range n).filterMap fun a0 =>
      let d := d0 + 1
      let a := a0 + 1
      if a + 2 * d ≤ n then some (a, a + d, a + 2 * d) else none

-- Encoding

/-- Two constraints per AP: not-all-true and not-all-false. -/
def mkAPConstrs (a b c : Nat) : List Constr :=
  [⟨[(1, Literal.neg a), (1, Literal.neg b), (1, Literal.neg c)], 1⟩,
   ⟨[(1, Literal.pos a), (1, Literal.pos b), (1, Literal.pos c)], 1⟩]

/-- Build all PB constraints from a list of AP triples. -/
def mkAllConstrs : List (Nat × Nat × Nat) → List Constr
  | [] => []
  | (a, b, c) :: rest => mkAPConstrs a b c ++ mkAllConstrs rest

/-- Encode: satisfiable iff {1,...,n} has an AP-free 2-coloring. -/
def encode (n : Nat) : Array Constr :=
  (mkAllConstrs (apTriples n)).toArray

-- Mathematical predicate

/-- A 2-coloring f of {1,...,n} is AP-free if no monochromatic
    3-term AP (a, a+d, a+2d) exists. -/
def isAPFree (n : Nat) (f : Nat → Bool) : Prop :=
  ∀ a d : Nat, 1 ≤ a → 1 ≤ d → a + 2 * d ≤ n →
    ¬(f a = f (a + d) ∧ f (a + d) = f (a + 2 * d))

/-- There exists an AP-free 2-coloring of {1,...,n}. -/
def hasAPFreeColoring (n : Nat) : Prop :=
  ∃ f : Nat → Bool, isAPFree n f

/-- n is the Van der Waerden number W(2,3). -/
def vanDerWaerdenNumber (n : Nat) : Prop :=
  hasAPFreeColoring n ∧ ¬hasAPFreeColoring (n + 1)

-- Per-constraint soundness

theorem negAPSat (a d n : Nat) (f : Valuation)
    (ha : 1 ≤ a) (hd : 1 ≤ d) (hle : a + 2 * d ≤ n)
    (hfree : isAPFree n f) :
    (⟨[(1, Literal.neg a), (1, Literal.neg (a + d)),
       (1, Literal.neg (a + 2 * d))], 1⟩ : Constr).sat f := by
  simp only [Constr.sat, evalSum, evalLit]
  have hmon : ¬(f a = true ∧ f (a + d) = true
      ∧ f (a + 2 * d) = true) := by
    intro ⟨hfa, hfb, hfc⟩
    exact hfree a d ha hd hle
      ⟨hfa.trans hfb.symm, hfb.trans hfc.symm⟩
  cases hfa : f a <;> cases hfb : f (a + d) <;>
    cases hfc : f (a + 2 * d) <;> simp_all

theorem posAPSat (a d n : Nat) (f : Valuation)
    (ha : 1 ≤ a) (hd : 1 ≤ d) (hle : a + 2 * d ≤ n)
    (hfree : isAPFree n f) :
    (⟨[(1, Literal.pos a), (1, Literal.pos (a + d)),
       (1, Literal.pos (a + 2 * d))], 1⟩ : Constr).sat f := by
  simp only [Constr.sat, evalSum, evalLit]
  have hmon : ¬(f a = false ∧ f (a + d) = false
      ∧ f (a + 2 * d) = false) := by
    intro ⟨hfa, hfb, hfc⟩
    exact hfree a d ha hd hle
      ⟨hfa.trans hfb.symm, hfb.trans hfc.symm⟩
  cases hfa : f a <;> cases hfb : f (a + d) <;>
    cases hfc : f (a + 2 * d) <;> simp_all

-- Constraint list soundness

theorem mkAPConstrs_sat (a d n : Nat) (f : Valuation)
    (ha : 1 ≤ a) (hd : 1 ≤ d) (hle : a + 2 * d ≤ n)
    (hfree : isAPFree n f) :
    ∀ c ∈ mkAPConstrs a (a + d) (a + 2 * d), c.sat f := by
  intro c hc
  simp only [mkAPConstrs, List.mem_cons, List.mem_nil_iff,
    or_false] at hc
  rcases hc with rfl | rfl
  · exact negAPSat a d n f ha hd hle hfree
  · exact posAPSat a d n f ha hd hle hfree

theorem mkAllConstrs_mem (triples : List (Nat × Nat × Nat))
    (c : Constr) (hc : c ∈ mkAllConstrs triples) :
    ∃ t ∈ triples, c ∈ mkAPConstrs t.1 t.2.1 t.2.2 := by
  induction triples with
  | nil => simp [mkAllConstrs] at hc
  | cons t rest ih =>
    simp only [mkAllConstrs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact ⟨t, List.Mem.head _, hc⟩
    · obtain ⟨t', ht', hct'⟩ := ih hc
      exact ⟨t', List.mem_cons_of_mem _ ht', hct'⟩

-- AP triples are valid
theorem apTriples_valid (n : Nat) (t : Nat × Nat × Nat)
    (ht : t ∈ apTriples n) :
    ∃ d, 1 ≤ t.1 ∧ 1 ≤ d ∧ t.2.1 = t.1 + d
      ∧ t.2.2 = t.1 + 2 * d ∧ t.2.2 ≤ n := by
  simp only [apTriples, List.mem_flatMap, List.mem_range,
    List.mem_filterMap] at ht
  obtain ⟨d0, _, a0, _, hcond⟩ := ht
  split at hcond
  · next hle =>
    simp only [Option.some.injEq] at hcond
    cases hcond
    exact ⟨d0 + 1, by omega, by omega, rfl, rfl, hle⟩
  · simp at hcond

/-- Main soundness: if the encoding is UNSAT, no AP-free 2-coloring
    of {1,...,n} exists. -/
theorem no_ap_free_of_unsat (n : Nat)
    (hunsat : ∀ v : Valuation, ∃ c ∈ (encode n).toList, ¬c.sat v) :
    ¬hasAPFreeColoring n := by
  intro ⟨f, hfree⟩
  obtain ⟨c, hc, hnsat⟩ := hunsat f
  apply hnsat
  have henc : (encode n).toList = mkAllConstrs (apTriples n) := by
    simp [encode]
  rw [henc] at hc
  obtain ⟨t, ht, htc⟩ := mkAllConstrs_mem _ c hc
  obtain ⟨d, ha, hd, hmid, htop, hle⟩ := apTriples_valid n t ht
  rw [hmid, htop] at htc
  exact mkAPConstrs_sat t.1 d n f ha hd (by rw [← htop]; exact hle)
    hfree c htc

-- Bridge theorem

private theorem exists_not_sat_of_allSat_false
    (ctx : PBFmla) (v : Valuation)
    (h : PBFmla.allSat v ctx → False) : ∃ c ∈ ctx, ¬c.sat v :=
  Classical.byContradiction fun hne =>
    h ⟨fun c hc =>
      Classical.byContradiction fun hnsat =>
        hne ⟨c, hc, hnsat⟩⟩

/-- Bridge from PBFmla refutation to AP-freeness impossibility. -/
theorem bridge (n : Nat) (ctx : PBFmla)
    (hctx : ctx = (encode n).toList)
    (hunsat : ∀ v : Valuation, PBFmla.allSat v ctx → False) :
    ¬hasAPFreeColoring n := by
  apply no_ap_free_of_unsat n
  intro v
  rw [← hctx]
  exact exists_not_sat_of_allSat_false ctx v (hunsat v)

-- OPB generation

/-- Generate OPB format string for the VdW encoding. -/
def toOPB (n : Nat) : String := Id.run do
  let triples := apTriples n
  let numConstrs := triples.length * 2
  let mut s := s!"* #variable= {n + 1} #constraint= {numConstrs}"
  s := s ++ " #equal= 0 intsize= 6\n"
  for (a, b, c) in triples do
    -- encode uses 1-based indices; OPB x{a+1} parses to index a
    s := s ++ s!"+1 ~x{a + 1} +1 ~x{b + 1} +1 ~x{c + 1} >= 1 ;\n"
    s := s ++ s!"+1 x{a + 1} +1 x{b + 1} +1 x{c + 1} >= 1 ;\n"
  return s

-- Witness verification

/-- Check that a coloring is AP-free by testing all triples. -/
def checkAPFree (n : Nat) (f : Nat → Bool) : Bool :=
  (apTriples n).all fun (a, b, c) =>
    !(f a == f b && f b == f c)

theorem checkAPFree_spec (n : Nat) (f : Nat → Bool)
    (hcheck : checkAPFree n f = true) : isAPFree n f := by
  intro a d ha hd hle hmon
  simp only [checkAPFree, List.all_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hcheck
  have hmem : (a, a + d, a + 2 * d) ∈ apTriples n := by
    simp only [apTriples, List.mem_flatMap, List.mem_range,
      List.mem_filterMap]
    exact ⟨d - 1, by omega, a - 1, by omega,
      by simp [show d - 1 + 1 = d by omega,
               show a - 1 + 1 = a by omega, hle]⟩
  have := hcheck (a, a + d, a + 2 * d) hmem
  obtain ⟨h1, h2⟩ := hmon
  simp [h1, h2] at this

/-- Provide a witness for the lower bound. -/
theorem witness_ap_free (n : Nat) (f : Nat → Bool)
    (hcheck : checkAPFree n f = true) :
    hasAPFreeColoring n :=
  ⟨f, checkAPFree_spec n f hcheck⟩

-- Elaboration commands

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

private def runCmdMeta (cmd : String) (args : Array String)
    (errCtx : String) : MetaM String := do
  let result ← IO.Process.output { cmd := cmd, args := args }
  if result.exitCode != 0 then
    throwError "{errCtx}: {cmd} failed (exit {result.exitCode})\
      \nstderr: {result.stderr}\nstdout: {result.stdout}"
  return result.stdout

private def buildBridgeProof (nExpr : Expr) (ctx : Expr)
    (pbProofConst : Expr) : MetaM (Expr × Expr) := do
  let finalType := mkApp (mkConst ``Not)
    (mkApp (mkConst ``hasAPFreeColoring) nExpr)
  let hctxProof := mkApp2 (mkConst ``Eq.refl [.succ .zero])
    (mkConst ``Sat.PB.PBFmla) ctx
  let finalProof := mkApp4 (mkConst ``VanDerWaerden.bridge)
    nExpr ctx hctxProof pbProofConst
  return (finalType, finalProof)

-- `vdw_decide name n` proves ¬ hasAPFreeColoring n via solver
elab "vdw_decide " nm:ident ppSpace nTerm:num : command => do
  let name := (← getCurrNamespace) ++ nm.getId
  let n := nTerm.getNat
  liftTermElabM do
    let nExpr := mkRawNatLit n
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
      VeriPB.fromVeriPBDirect constrs (n + 1) proofStr auxName
    let (finalType, finalProof) ←
      buildBridgeProof nExpr ctx pbProofConst
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := finalType
      value := finalProof
    }
    Lean.logInfo m!"Registered {name} : ¬ hasAPFreeColoring {n}"

-- Reflection-based verification (uses native_decide)
elab "vdw_reflect " nm:ident ppSpace nTerm:num
    ppSpace proofFile:str : command => do
  let name := (← getCurrNamespace) ++ nm.getId
  let n := nTerm.getNat
  let proofPath := proofFile.getString
  liftTermElabM do
    let nExpr := mkRawNatLit n
    let numVarsExpr := mkRawNatLit (n + 1)
    let proofStr ← IO.FS.readFile (System.FilePath.mk proofPath)
    let constrsExpr := mkApp (mkConst ``encode) nExpr
    let proofStrExpr := mkStrLit proofStr
    let checkExpr := mkApp3
      (mkConst ``VeriPB.Reflect.checkProofBool)
      constrsExpr numVarsExpr proofStrExpr
    let hEqTrue ← match ← Lean.Meta.nativeEqTrue `vdw_reflect checkExpr
        (axiomDeclRange? := (← getRef)) with
      | .success prf => pure prf
      | .notTrue => throwError "Reflection checker returned false for {name}"
    let unsatProof := mkApp4
      (mkConst ``VeriPB.Reflect.checkProof_sound)
      constrsExpr numVarsExpr proofStrExpr hEqTrue
    let finalProof := mkApp2
      (mkConst ``no_ap_free_of_unsat)
      nExpr unsatProof
    let finalType := mkApp (mkConst ``Not)
      (mkApp (mkConst ``hasAPFreeColoring) nExpr)
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := finalType
      value := finalProof
    }
    Lean.logInfo m!"Registered {name} : ¬ hasAPFreeColoring {n}"

-- Concrete Van der Waerden number theorems

/-- W(2,3) lower bound: {1,...,8} has an AP-free 2-coloring.
    Coloring RRBBRRBB: {1,2,5,6} → true, {3,4,7,8} → false. -/
theorem vdw8_exists : hasAPFreeColoring 8 :=
  witness_ap_free 8
    (fun | 1 | 2 | 5 | 6 => true | _ => false) (by native_decide)

-- W(2,3) upper bound: verified via VeriPB reflection checker
vdw_reflect vdw9_impossible 9
  "applications/vdw/vdw9_kernel.pbp"

/-- W(2,3) = 9: the largest AP-free 2-colorable interval has 8
    elements. -/
theorem vdw_number_2_3 : vanDerWaerdenNumber 8 :=
  ⟨vdw8_exists, vdw9_impossible⟩

-- ============================================================
-- Generalized W(2,k): arbitrary AP length
-- ============================================================

/-- k-term APs [a, a+d, ..., a+(k-1)*d] in {1,...,n}. -/
def apKTuples (k n : Nat) : List (List Nat) :=
  (List.range n).flatMap fun d0 =>
    (List.range n).filterMap fun a0 =>
      let d := d0 + 1
      let a := a0 + 1
      let ap := (List.range k).map fun i => a + i * d
      if ap.all (· ≤ n) then some ap else none

/-- Two constraints per k-AP: not-all-true and not-all-false. -/
def mkKAPConstrs (vars : List Nat) : List Constr :=
  [⟨vars.map fun v => (1, Literal.neg v), 1⟩,
   ⟨vars.map fun v => (1, Literal.pos v), 1⟩]

/-- Build all constraints from a list of k-APs. -/
def mkKAllConstrs : List (List Nat) → List Constr
  | [] => []
  | ap :: rest => mkKAPConstrs ap ++ mkKAllConstrs rest

/-- Encode: satisfiable iff {1,...,n} has a 2-coloring with no
    monochromatic k-AP. -/
def encodeK (k n : Nat) : Array Constr :=
  (mkKAllConstrs (apKTuples k n)).toArray

-- Mathematical predicate for k-APs

/-- A 2-coloring f of {1,...,n} is k-AP-free if no monochromatic
    k-term AP exists. -/
def isKAPFree (k n : Nat) (f : Nat → Bool) : Prop :=
  ∀ a d : Nat, 1 ≤ a → 1 ≤ d →
    (∀ i, i < k → a + i * d ≤ n) →
    ¬(∀ i, i < k → f (a + i * d) = f a)

/-- There exists a k-AP-free 2-coloring of {1,...,n}. -/
def hasKAPFreeColoring (k n : Nat) : Prop :=
  ∃ f : Nat → Bool, isKAPFree k n f

-- Soundness: evalSum of mapped list

private theorem evalSum_neg_map_ge_one (f : Valuation)
    (vars : List Nat) (v : Nat) (hv : v ∈ vars) (hf : f v = false) :
    1 ≤ evalSum f (vars.map fun v => (1, Literal.neg v)) := by
  induction vars with
  | nil => exact absurd hv (List.not_mem_nil)
  | cons hd tl ih =>
    simp only [List.map_cons, evalSum]
    rcases List.mem_cons.mp hv with rfl | htl
    · simp [evalLit, hf]
    · have := ih htl; omega

private theorem evalSum_pos_map_ge_one (f : Valuation)
    (vars : List Nat) (v : Nat) (hv : v ∈ vars) (hf : f v = true) :
    1 ≤ evalSum f (vars.map fun v => (1, Literal.pos v)) := by
  induction vars with
  | nil => exact absurd hv (List.not_mem_nil)
  | cons hd tl ih =>
    simp only [List.map_cons, evalSum]
    rcases List.mem_cons.mp hv with rfl | htl
    · simp [evalLit, hf]
    · have := ih htl; omega

-- Bridge: List.all bounds to ∀ bounds
private theorem all_bounds_to_forall (k n a d : Nat)
    (h : ((List.range k).map fun i => a + i * d).all (· ≤ n) = true) :
    ∀ i, i < k → a + i * d ≤ n := by
  intro i hi
  have hmem : a + i * d ∈ (List.range k).map (fun i => a + i * d) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have := List.all_eq_true.mp h _ hmem
  exact of_decide_eq_true this

theorem mkKAPConstrs_sat (k n : Nat) (f : Valuation)
    (a d : Nat) (ha : 1 ≤ a) (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hbounds : ∀ i, i < k → a + i * d ≤ n)
    (hfree : isKAPFree k n f) :
    let ap := (List.range k).map fun i => a + i * d
    ∀ c ∈ mkKAPConstrs ap, c.sat f := by
  intro ap c hc
  have hmono := hfree a d ha hd hbounds
  have ha_mem : a ∈ ap :=
    List.mem_map.mpr ⟨0, List.mem_range.mpr hk, by simp⟩
  have hdiff : ∃ i, i < k ∧ f (a + i * d) ≠ f a :=
    Classical.byContradiction fun hall =>
      hmono fun i hi =>
        Classical.byContradiction fun hne =>
          hall ⟨i, hi, hne⟩
  obtain ⟨j, hj, hjne⟩ := hdiff
  have hj_mem : a + j * d ∈ ap :=
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  simp only [mkKAPConstrs, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl
  · simp only [Constr.sat]
    cases hfa : f a with
    | false => exact evalSum_neg_map_ge_one f ap a ha_mem hfa
    | true =>
      have : f (a + j * d) = false := by
        cases h : f (a + j * d)
        · rfl
        · exact absurd (by rw [h, hfa]) hjne
      exact evalSum_neg_map_ge_one f ap _ hj_mem this
  · simp only [Constr.sat]
    cases hfa : f a with
    | true => exact evalSum_pos_map_ge_one f ap a ha_mem hfa
    | false =>
      have : f (a + j * d) = true := by
        cases h : f (a + j * d)
        · exact absurd (by rw [h, hfa]) hjne
        · rfl
      exact evalSum_pos_map_ge_one f ap _ hj_mem this

theorem mkKAllConstrs_mem (aps : List (List Nat))
    (c : Constr) (hc : c ∈ mkKAllConstrs aps) :
    ∃ ap ∈ aps, c ∈ mkKAPConstrs ap := by
  induction aps with
  | nil => simp [mkKAllConstrs] at hc
  | cons ap rest ih =>
    simp only [mkKAllConstrs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact ⟨ap, List.Mem.head _, hc⟩
    · obtain ⟨ap', hap', hc'⟩ := ih hc
      exact ⟨ap', List.mem_cons_of_mem _ hap', hc'⟩

theorem apKTuples_valid (k n : Nat) (ap : List Nat)
    (hap : ap ∈ apKTuples k n) :
    ∃ a d, 1 ≤ a ∧ 1 ≤ d
      ∧ ap = (List.range k).map (fun i => a + i * d)
      ∧ (∀ i, i < k → a + i * d ≤ n) := by
  simp only [apKTuples, List.mem_flatMap, List.mem_range,
    List.mem_filterMap] at hap
  obtain ⟨d0, _, a0, _, hcond⟩ := hap
  split at hcond
  · next hbounds =>
    simp only [Option.some.injEq] at hcond
    refine ⟨a0 + 1, d0 + 1, by omega, by omega, hcond.symm, ?_⟩
    exact all_bounds_to_forall k n (a0 + 1) (d0 + 1) hbounds
  · simp at hcond

/-- Main soundness for k-APs: if encoding is UNSAT, no k-AP-free
    2-coloring exists. -/
theorem no_k_ap_free_of_unsat (k n : Nat) (hk : 1 ≤ k)
    (hunsat : ∀ v : Valuation, ∃ c ∈ (encodeK k n).toList, ¬c.sat v) :
    ¬hasKAPFreeColoring k n := by
  intro ⟨f, hfree⟩
  obtain ⟨c, hc, hnsat⟩ := hunsat f
  apply hnsat
  have henc : (encodeK k n).toList = mkKAllConstrs (apKTuples k n) := by
    simp [encodeK]
  rw [henc] at hc
  obtain ⟨ap, hap, hcap⟩ := mkKAllConstrs_mem _ c hc
  obtain ⟨a, d, ha, hd, hapdef, hbounds⟩ := apKTuples_valid k n ap hap
  rw [hapdef] at hcap
  exact mkKAPConstrs_sat k n f a d ha hd hk hbounds hfree c hcap

-- OPB generation for k-APs

def toOPBK (k n : Nat) : String := Id.run do
  let aps := apKTuples k n
  let numConstrs := aps.length * 2
  let mut s := s!"* #variable= {n + 1} #constraint= {numConstrs}"
  s := s ++ " #equal= 0 intsize= 6\n"
  for ap in aps do
    for v in ap do
      s := s ++ s!"+1 ~x{v + 1} "
    s := s ++ ">= 1 ;\n"
    for v in ap do
      s := s ++ s!"+1 x{v + 1} "
    s := s ++ ">= 1 ;\n"
  return s

-- Reflection command for generalized k-APs
elab "vdwk_reflect " nm:ident ppSpace kTerm:num ppSpace nTerm:num
    ppSpace proofFile:str : command => do
  let name := (← getCurrNamespace) ++ nm.getId
  let k := kTerm.getNat
  let n := nTerm.getNat
  let proofPath := proofFile.getString
  liftTermElabM do
    let kExpr := mkRawNatLit k
    let nExpr := mkRawNatLit n
    let numVarsExpr := mkRawNatLit (n + 1)
    let proofStr ← IO.FS.readFile (System.FilePath.mk proofPath)
    let constrsExpr := mkApp2 (mkConst ``encodeK) kExpr nExpr
    let proofStrExpr := mkStrLit proofStr
    let checkExpr := mkApp3
      (mkConst ``VeriPB.Reflect.checkProofBool)
      constrsExpr numVarsExpr proofStrExpr
    let hEqTrue ← match ← Lean.Meta.nativeEqTrue `vdwk_reflect checkExpr
        (axiomDeclRange? := (← getRef)) with
      | .success prf => pure prf
      | .notTrue => throwError "Reflection checker returned false for {name}"
    let unsatProof := mkApp4
      (mkConst ``VeriPB.Reflect.checkProof_sound)
      constrsExpr numVarsExpr proofStrExpr hEqTrue
    -- Build hk : 1 ≤ k
    if k == 0 then throwError "k must be positive"
    let hkType := mkApp4 (mkConst ``LE.le [.zero])
      (mkConst ``Nat) (mkConst ``instLENat) (mkRawNatLit 1) kExpr
    let hkProof ← mkDecideProof hkType
    let finalProof := mkApp4
      (mkConst ``no_k_ap_free_of_unsat)
      kExpr nExpr hkProof unsatProof
    let finalType := mkApp (mkConst ``Not)
      (mkApp2 (mkConst ``hasKAPFreeColoring) kExpr nExpr)
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := finalType
      value := finalProof
    }
    Lean.logInfo m!"Registered {name} : ¬ hasKAPFreeColoring {k} {n}"

-- W(2,4) upper bound: verified via VeriPB reflection checker
-- 35 variables, 374 constraints
vdwk_reflect vdw35_impossible 4 35
  "applications/vdw/vdw35_kernel.pbp"

end VanDerWaerden
