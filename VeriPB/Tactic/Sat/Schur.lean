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
# Trusted Schur Number Encoding

End-to-end verified Schur numbers: Lean encodes the Schur-freeness decision
problem as PB constraints, verifies a VeriPB kernel proof, and produces a
mathematical theorem about the Schur number S(2).

A 2-coloring of {1,...,n} is *Schur-free* if there is no monochromatic triple
(a, b, a+b). The Schur number S(2) = 4 means {1,...,4} can be 2-colored
without monochromatic sum triples, but {1,...,5} cannot.

## Main results

* `schur4_exists` -- S(2) lower bound: {1,...,4} is Schur-free
* `schur5_impossible` -- S(2) upper bound: {1,...,5} is not
* `schur_number_2` -- S(2) = 4

## Infrastructure

* `Schur.schurTriples` -- enumerate Schur triples (a,b,a+b)
* `Schur.encode` -- PB constraint encoding
* `Schur.no_schur_free_of_unsat` -- encoding soundness
* `schur_decide` / `schur_reflect` -- elaboration commands
-/

namespace Schur

open Sat.PB

-- Schur triples

/-- Schur triples (a, b, a+b) with 1 ≤ a ≤ b, a+b ≤ n. -/
def schurTriples (n : Nat) : List (Nat × Nat × Nat) :=
  (List.range n).flatMap fun a0 =>
    (List.range n).filterMap fun b0 =>
      let a := a0 + 1
      let b := b0 + 1
      if a ≤ b && a + b ≤ n then some (a, b, a + b) else none

-- Encoding

/-- Two constraints per triple: not-all-true and not-all-false.
    Works correctly for both a < b and a = b cases. -/
def mkTripleConstrs (a b c : Nat) : List Constr :=
  [⟨[(1, Literal.neg a), (1, Literal.neg b), (1, Literal.neg c)], 1⟩,
   ⟨[(1, Literal.pos a), (1, Literal.pos b), (1, Literal.pos c)], 1⟩]

/-- Build all PB constraints from a list of Schur triples. -/
def mkAllConstrs : List (Nat × Nat × Nat) → List Constr
  | [] => []
  | (a, b, c) :: rest => mkTripleConstrs a b c ++ mkAllConstrs rest

/-- Encode: satisfiable iff {1,...,n} has a sum-free 2-coloring. -/
def encode (n : Nat) : Array Constr :=
  (mkAllConstrs (schurTriples n)).toArray

-- Mathematical predicate

/-- A 2-coloring f of {1,...,n} is Schur-free if no monochromatic
    triple (a, b, a+b) exists. -/
def isSchurFree (n : Nat) (f : Nat → Bool) : Prop :=
  ∀ a b : Nat, 1 ≤ a → a ≤ b → a + b ≤ n →
    ¬(f a = f b ∧ f b = f (a + b))

/-- There exists a Schur-free 2-coloring of {1,...,n}. -/
def hasSchurFreeColoring (n : Nat) : Prop :=
  ∃ f : Nat → Bool, isSchurFree n f

/-- n is the Schur number S(2). -/
def schurNumber (n : Nat) : Prop :=
  hasSchurFreeColoring n ∧ ¬hasSchurFreeColoring (n + 1)

-- Per-constraint soundness

theorem negTripleSat (a b n : Nat) (f : Valuation)
    (ha : 1 ≤ a) (hab : a ≤ b) (hle : a + b ≤ n)
    (hfree : isSchurFree n f) :
    (⟨[(1, Literal.neg a), (1, Literal.neg b),
       (1, Literal.neg (a + b))], 1⟩ : Constr).sat f := by
  simp only [Constr.sat, evalSum, evalLit]
  have hmon : ¬(f a = true ∧ f b = true ∧ f (a + b) = true) := by
    intro ⟨hfa, hfb, hfc⟩
    exact hfree a b ha hab hle ⟨hfa.trans hfb.symm, hfb.trans hfc.symm⟩
  cases hfa : f a <;> cases hfb : f b <;> cases hfc : f (a + b) <;>
    simp_all

theorem posTripleSat (a b n : Nat) (f : Valuation)
    (ha : 1 ≤ a) (hab : a ≤ b) (hle : a + b ≤ n)
    (hfree : isSchurFree n f) :
    (⟨[(1, Literal.pos a), (1, Literal.pos b),
       (1, Literal.pos (a + b))], 1⟩ : Constr).sat f := by
  simp only [Constr.sat, evalSum, evalLit]
  have hmon : ¬(f a = false ∧ f b = false ∧ f (a + b) = false) := by
    intro ⟨hfa, hfb, hfc⟩
    exact hfree a b ha hab hle ⟨hfa.trans hfb.symm, hfb.trans hfc.symm⟩
  cases hfa : f a <;> cases hfb : f b <;> cases hfc : f (a + b) <;>
    simp_all

-- Constraint list soundness

theorem mkTripleConstrs_sat (a b n : Nat) (f : Valuation)
    (ha : 1 ≤ a) (hab : a ≤ b) (hle : a + b ≤ n)
    (hfree : isSchurFree n f) :
    ∀ c ∈ mkTripleConstrs a b (a + b), c.sat f := by
  intro c hc
  simp only [mkTripleConstrs, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl
  · exact negTripleSat a b n f ha hab hle hfree
  · exact posTripleSat a b n f ha hab hle hfree

-- Helper: membership in mkAllConstrs implies membership in some triple's constrs
theorem mkAllConstrs_mem (triples : List (Nat × Nat × Nat)) (c : Constr)
    (hc : c ∈ mkAllConstrs triples) :
    ∃ t ∈ triples, c ∈ mkTripleConstrs t.1 t.2.1 t.2.2 := by
  induction triples with
  | nil => simp [mkAllConstrs] at hc
  | cons t rest ih =>
    simp only [mkAllConstrs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact ⟨t, List.Mem.head _, hc⟩
    · obtain ⟨t', ht', hct'⟩ := ih hc
      exact ⟨t', List.mem_cons_of_mem _ ht', hct'⟩

-- Schur triples are valid
theorem schurTriples_valid (n : Nat) (t : Nat × Nat × Nat)
    (ht : t ∈ schurTriples n) :
    1 ≤ t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.2 = t.1 + t.2.1 ∧ t.2.2 ≤ n := by
  simp only [schurTriples, List.mem_flatMap, List.mem_range,
    List.mem_filterMap] at ht
  obtain ⟨a0, _, b0, _, hb0⟩ := ht
  split at hb0
  · next hcond =>
    simp only [Option.some.injEq] at hb0
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    obtain ⟨hab, hle⟩ := hcond
    cases hb0
    exact ⟨by omega, hab, rfl, hle⟩
  · simp at hb0

/-- Main soundness: if the encoding is UNSAT, no Schur-free 2-coloring
    of {1,...,n} exists. -/
theorem no_schur_free_of_unsat (n : Nat)
    (hunsat : ∀ v : Valuation, ∃ c ∈ (encode n).toList, ¬c.sat v) :
    ¬hasSchurFreeColoring n := by
  intro ⟨f, hfree⟩
  obtain ⟨c, hc, hnsat⟩ := hunsat f
  apply hnsat
  -- c is in the encoding, so it came from some triple
  have henc : (encode n).toList = mkAllConstrs (schurTriples n) := by
    simp [encode]
  rw [henc] at hc
  obtain ⟨t, ht, htc⟩ := mkAllConstrs_mem _ c hc
  obtain ⟨ha, hab, hsum, hle⟩ := schurTriples_valid n t ht
  rw [hsum] at htc hle
  exact mkTripleConstrs_sat t.1 t.2.1 n f ha hab hle hfree c htc

-- Bridge theorem

private theorem exists_not_sat_of_allSat_false (ctx : PBFmla) (v : Valuation)
    (h : PBFmla.allSat v ctx → False) : ∃ c ∈ ctx, ¬c.sat v :=
  Classical.byContradiction fun hne =>
    h ⟨fun c hc =>
      Classical.byContradiction fun hnsat => hne ⟨c, hc, hnsat⟩⟩

/-- Bridge from PBFmla refutation to Schur-freeness impossibility. -/
theorem bridge (n : Nat) (ctx : PBFmla)
    (hctx : ctx = (encode n).toList)
    (hunsat : ∀ v : Valuation, PBFmla.allSat v ctx → False) :
    ¬hasSchurFreeColoring n := by
  apply no_schur_free_of_unsat n
  intro v
  rw [← hctx]
  exact exists_not_sat_of_allSat_false ctx v (hunsat v)

-- OPB generation

/-- Generate OPB format string for the Schur encoding. -/
def toOPB (n : Nat) : String := Id.run do
  let triples := schurTriples n
  let numConstrs := triples.length * 2
  let mut s := s!"* #variable= {n + 1} #constraint= {numConstrs}"
  s := s ++ " #equal= 0 intsize= 6\n"
  for (a, b, c) in triples do
    -- encode uses 1-based indices; OPB x{a+1} parses to index a
    s := s ++ s!"+1 ~x{a + 1} +1 ~x{b + 1} +1 ~x{c + 1} >= 1 ;\n"
    s := s ++ s!"+1 x{a + 1} +1 x{b + 1} +1 x{c + 1} >= 1 ;\n"
  return s

-- Witness verification

/-- Check that a coloring is Schur-free by testing all triples. -/
def checkSchurFree (n : Nat) (f : Nat → Bool) : Bool :=
  (schurTriples n).all fun (a, b, c) =>
    !(f a == f b && f b == f c)

theorem checkSchurFree_spec (n : Nat) (f : Nat → Bool)
    (hcheck : checkSchurFree n f = true) : isSchurFree n f := by
  intro a b ha hab hle hmon
  simp only [checkSchurFree, List.all_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hcheck
  have hmem : (a, b, a + b) ∈ schurTriples n := by
    simp only [schurTriples, List.mem_flatMap, List.mem_range,
      List.mem_filterMap]
    exact ⟨a - 1, by omega, b - 1, by omega,
      by simp [show a - 1 + 1 = a by omega,
               show b - 1 + 1 = b by omega, hab, hle]⟩
  have := hcheck (a, b, a + b) hmem
  obtain ⟨h1, h2⟩ := hmon
  simp [h1, h2] at this

/-- Provide a witness for the lower bound. -/
theorem witness_schur_free (n : Nat) (f : Nat → Bool)
    (hcheck : checkSchurFree n f = true) :
    hasSchurFreeColoring n :=
  ⟨f, checkSchurFree_spec n f hcheck⟩

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
    (mkApp (mkConst ``hasSchurFreeColoring) nExpr)
  let hctxProof := mkApp2 (mkConst ``Eq.refl [.succ .zero])
    (mkConst ``Sat.PB.PBFmla) ctx
  let finalProof := mkApp4 (mkConst ``Schur.bridge)
    nExpr ctx hctxProof pbProofConst
  return (finalType, finalProof)

-- `schur_decide name n` proves ¬ hasSchurFreeColoring n via solver
elab "schur_decide " nm:ident ppSpace nTerm:num : command => do
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
    Lean.logInfo m!"Registered {name} : ¬ hasSchurFreeColoring {n}"

-- Reflection-based verification (uses native_decide)
elab "schur_reflect " nm:ident ppSpace nTerm:num
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
    let finalProof := mkApp2 (mkConst ``no_schur_free_of_unsat)
      nExpr unsatProof
    let finalType := mkApp (mkConst ``Not)
      (mkApp (mkConst ``hasSchurFreeColoring) nExpr)
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := finalType
      value := finalProof
    }
    Lean.logInfo m!"Registered {name} : ¬ hasSchurFreeColoring {n}"

-- Concrete Schur number theorems

/-- S(2) lower bound: {1,...,4} has a Schur-free 2-coloring.
    Coloring: {1, 4} → true, {2, 3} → false. -/
theorem schur4_exists : hasSchurFreeColoring 4 :=
  witness_schur_free 4
    (fun | 1 | 4 => true | _ => false) (by native_decide)

-- S(2) upper bound: verified via VeriPB reflection checker
schur_reflect schur5_impossible 5
  "applications/schur/schur5_kernel.pbp"

/-- The Schur number S(2) = 4. -/
theorem schur_number_2 : schurNumber 4 :=
  ⟨schur4_exists, schur5_impossible⟩

end Schur
