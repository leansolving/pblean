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

end VanDerWaerden
