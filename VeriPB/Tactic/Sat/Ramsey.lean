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
# Trusted Ramsey Number Encoding

End-to-end verified Ramsey numbers: Lean encodes the 2-coloring
decision problem on complete graph edges as PB constraints, verifies
a VeriPB kernel proof, and produces a mathematical theorem about
R(3,3).

A 2-coloring of the edges of K_n is *Ramsey-free* if there is no
monochromatic triangle. The Ramsey number R(3,3) = 6 means K_5 can
be 2-colored without a monochromatic triangle, but K_6 cannot.

## Main results

* `ramsey5_exists` -- R(3,3) lower bound: K_5 is Ramsey-free
* `ramsey6_impossible` -- R(3,3) upper bound (solver-verified)
* `ramsey_3_3` -- R(3,3) = 6

## Infrastructure

* `Ramsey.triangles` -- enumerate triangles (i,j,k)
* `Ramsey.encode` -- PB constraint encoding
* `Ramsey.no_ramsey_free_of_unsat` -- encoding soundness
* `ramsey_decide` / `ramsey_reflect` -- elaboration commands
-/

namespace Ramsey

open Sat.PB

-- Edge variables

/-- Number of edge variables for K_n: C(n,2). -/
def numEdgeVars (n : Nat) : Nat := n * (n - 1) / 2

/-- Internal variable count for propagation arrays.
    Edge variables are 0-based (0..numEdgeVars n - 1). -/
def numVarsInternal (n : Nat) : Nat := numEdgeVars n

/-- Map edge (i,j) with i < j to a 0-based variable index. -/
def edgeVar (n i j : Nat) : Nat :=
  i * (2 * n - i - 1) / 2 + (j - i - 1)

-- Triangles

/-- All triangles (i,j,k) with 0 <= i < j < k < n. -/
def triangles (n : Nat) : List (Nat × Nat × Nat) :=
  (List.range n).flatMap fun i =>
    (List.range n).flatMap fun j =>
      (List.range n).filterMap fun k =>
        if i < j && j < k then some (i, j, k) else none

-- Encoding

/-- Two constraints per triangle: not-all-same-color.
    For edge variables e1=(i,j), e2=(i,k), e3=(j,k):
    - Not-all-true: ~e1 + ~e2 + ~e3 >= 1
    - Not-all-false: e1 + e2 + e3 >= 1 -/
def mkTriangleConstrs (e1 e2 e3 : Nat) : List Constr :=
  [⟨[(1, Literal.neg e1), (1, Literal.neg e2),
     (1, Literal.neg e3)], 1⟩,
   ⟨[(1, Literal.pos e1), (1, Literal.pos e2),
     (1, Literal.pos e3)], 1⟩]

/-- Build all PB constraints from a list of triangles. -/
def mkAllConstrs (n : Nat) :
    List (Nat × Nat × Nat) → List Constr
  | [] => []
  | (i, j, k) :: rest =>
    mkTriangleConstrs (edgeVar n i j) (edgeVar n i k)
      (edgeVar n j k) ++ mkAllConstrs n rest

/-- Encode: satisfiable iff K_n has a Ramsey-free 2-coloring. -/
def encode (n : Nat) : Array Constr :=
  (mkAllConstrs n (triangles n)).toArray

-- Mathematical predicate

/-- A 2-coloring f of K_n edges is Ramsey-free if no
    monochromatic triangle exists. f maps edge variables to
    Bool. -/
def isRamseyFree (n : Nat) (f : Nat → Bool) : Prop :=
  ∀ i j k : Nat, i < j → j < k → k < n →
    ¬(f (edgeVar n i j) = f (edgeVar n i k) ∧
      f (edgeVar n i k) = f (edgeVar n j k))

/-- There exists a Ramsey-free 2-coloring of K_n. -/
def hasRamseyFreeColoring (n : Nat) : Prop :=
  ∃ f : Nat → Bool, isRamseyFree n f

/-- n is the Ramsey number R(3,3): K_n has a Ramsey-free
    coloring but K_{n+1} does not. -/
def ramseyNumber (n : Nat) : Prop :=
  hasRamseyFreeColoring n ∧ ¬hasRamseyFreeColoring (n + 1)

-- Per-constraint soundness

theorem negTriangleSat (i j k n : Nat) (f : Valuation)
    (hij : i < j) (hjk : j < k) (hkn : k < n)
    (hfree : isRamseyFree n f) :
    (⟨[(1, Literal.neg (edgeVar n i j)),
       (1, Literal.neg (edgeVar n i k)),
       (1, Literal.neg (edgeVar n j k))], 1⟩ :
      Constr).sat f := by
  simp only [Constr.sat, evalSum, evalLit]
  have hmon : ¬(f (edgeVar n i j) = true
      ∧ f (edgeVar n i k) = true
      ∧ f (edgeVar n j k) = true) := by
    intro ⟨hfa, hfb, hfc⟩
    exact hfree i j k hij hjk hkn
      ⟨hfa.trans hfb.symm, hfb.trans hfc.symm⟩
  cases hfa : f (edgeVar n i j) <;>
    cases hfb : f (edgeVar n i k) <;>
    cases hfc : f (edgeVar n j k) <;> simp_all

theorem posTriangleSat (i j k n : Nat) (f : Valuation)
    (hij : i < j) (hjk : j < k) (hkn : k < n)
    (hfree : isRamseyFree n f) :
    (⟨[(1, Literal.pos (edgeVar n i j)),
       (1, Literal.pos (edgeVar n i k)),
       (1, Literal.pos (edgeVar n j k))], 1⟩ :
      Constr).sat f := by
  simp only [Constr.sat, evalSum, evalLit]
  have hmon : ¬(f (edgeVar n i j) = false
      ∧ f (edgeVar n i k) = false
      ∧ f (edgeVar n j k) = false) := by
    intro ⟨hfa, hfb, hfc⟩
    exact hfree i j k hij hjk hkn
      ⟨hfa.trans hfb.symm, hfb.trans hfc.symm⟩
  cases hfa : f (edgeVar n i j) <;>
    cases hfb : f (edgeVar n i k) <;>
    cases hfc : f (edgeVar n j k) <;> simp_all

-- Constraint list soundness

theorem mkTriangleConstrs_sat (i j k n : Nat)
    (f : Valuation) (hij : i < j) (hjk : j < k)
    (hkn : k < n) (hfree : isRamseyFree n f) :
    ∀ c ∈ mkTriangleConstrs (edgeVar n i j)
      (edgeVar n i k) (edgeVar n j k), c.sat f := by
  intro c hc
  simp only [mkTriangleConstrs, List.mem_cons,
    List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl
  · exact negTriangleSat i j k n f hij hjk hkn hfree
  · exact posTriangleSat i j k n f hij hjk hkn hfree

-- Helper: membership in mkAllConstrs
theorem mkAllConstrs_mem (n : Nat)
    (tris : List (Nat × Nat × Nat)) (c : Constr)
    (hc : c ∈ mkAllConstrs n tris) :
    ∃ t ∈ tris,
      c ∈ mkTriangleConstrs (edgeVar n t.1 t.2.1)
        (edgeVar n t.1 t.2.2)
        (edgeVar n t.2.1 t.2.2) := by
  induction tris with
  | nil => simp [mkAllConstrs] at hc
  | cons t rest ih =>
    simp only [mkAllConstrs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact ⟨t, List.Mem.head _, hc⟩
    · obtain ⟨t', ht', hct'⟩ := ih hc
      exact ⟨t', List.mem_cons_of_mem _ ht', hct'⟩

-- Triangles have valid indices
theorem triangles_valid (n : Nat) (t : Nat × Nat × Nat)
    (ht : t ∈ triangles n) :
    t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 < n := by
  simp only [triangles, List.mem_flatMap, List.mem_range,
    List.mem_filterMap] at ht
  obtain ⟨i, _, j, _, k, _, hcond⟩ := ht
  split at hcond
  · next hc =>
    simp only [Option.some.injEq] at hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    cases hcond
    exact ⟨hc.1, hc.2, by omega⟩
  · simp at hcond

/-- Main soundness: if the encoding is UNSAT, no Ramsey-free
    2-coloring of K_n exists. -/
theorem no_ramsey_free_of_unsat (n : Nat)
    (hunsat : ∀ v : Valuation,
      ∃ c ∈ (encode n).toList, ¬c.sat v) :
    ¬hasRamseyFreeColoring n := by
  intro ⟨f, hfree⟩
  obtain ⟨c, hc, hnsat⟩ := hunsat f
  apply hnsat
  have henc : (encode n).toList =
      mkAllConstrs n (triangles n) := by
    simp [encode]
  rw [henc] at hc
  obtain ⟨t, ht, htc⟩ := mkAllConstrs_mem n _ c hc
  obtain ⟨hij, hjk, hkn⟩ := triangles_valid n t ht
  exact mkTriangleConstrs_sat t.1 t.2.1 t.2.2 n f
    hij hjk hkn hfree c htc

-- Bridge theorem

private theorem exists_not_sat_of_allSat_false
    (ctx : PBFmla) (v : Valuation)
    (h : PBFmla.allSat v ctx → False) :
    ∃ c ∈ ctx, ¬c.sat v :=
  Classical.byContradiction fun hne =>
    h ⟨fun c hc =>
      Classical.byContradiction fun hnsat =>
        hne ⟨c, hc, hnsat⟩⟩

/-- Bridge from PBFmla refutation to Ramsey-freeness
    impossibility. -/
theorem bridge (n : Nat) (ctx : PBFmla)
    (hctx : ctx = (encode n).toList)
    (hunsat : ∀ v : Valuation,
      PBFmla.allSat v ctx → False) :
    ¬hasRamseyFreeColoring n := by
  apply no_ramsey_free_of_unsat n
  intro v
  rw [← hctx]
  exact exists_not_sat_of_allSat_false ctx v (hunsat v)

-- OPB generation

/-- Generate OPB format string for the Ramsey encoding. -/
def toOPB (n : Nat) : String := Id.run do
  let tris := triangles n
  let numVars := numEdgeVars n
  let numConstrs := tris.length * 2
  let mut s := s!"* #variable= {numVars} #constraint= "
  s := s ++ s!"{numConstrs} #equal= 0 intsize= 6\n"
  for (i, j, k) in tris do
    let e1 := edgeVar n i j + 1  -- OPB is 1-based
    let e2 := edgeVar n i k + 1
    let e3 := edgeVar n j k + 1
    s := s ++ s!"+1 ~x{e1} +1 ~x{e2} +1 ~x{e3} >= 1 ;\n"
    s := s ++ s!"+1 x{e1} +1 x{e2} +1 x{e3} >= 1 ;\n"
  return s

-- Witness verification

/-- Check that a coloring is Ramsey-free by testing all
    triangles. -/
def checkRamseyFree (n : Nat) (f : Nat → Bool) : Bool :=
  (triangles n).all fun (i, j, k) =>
    let e1 := edgeVar n i j
    let e2 := edgeVar n i k
    let e3 := edgeVar n j k
    !(f e1 == f e2 && f e2 == f e3)

theorem checkRamseyFree_spec (n : Nat) (f : Nat → Bool)
    (hcheck : checkRamseyFree n f = true) :
    isRamseyFree n f := by
  intro i j k hij hjk hkn hmon
  simp only [checkRamseyFree, List.all_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff,
    beq_eq_false_iff_ne] at hcheck
  have hmem : (i, j, k) ∈ triangles n := by
    simp only [triangles, List.mem_flatMap, List.mem_range,
      List.mem_filterMap]
    exact ⟨i, by omega, j, by omega, k, by omega,
      by simp [hij, hjk]⟩
  have := hcheck (i, j, k) hmem
  simp only at this
  obtain ⟨h1, h2⟩ := hmon
  simp [h1, h2] at this

/-- Provide a witness for the lower bound. -/
theorem witness_ramsey_free (n : Nat) (f : Nat → Bool)
    (hcheck : checkRamseyFree n f = true) :
    hasRamseyFreeColoring n :=
  ⟨f, checkRamseyFree_spec n f hcheck⟩

-- Concrete Ramsey number theorems

/-- R(3,3) lower bound: K_5 has a Ramsey-free 2-coloring.
    The C_5 coloring: edges of the 5-cycle (0,1),(1,2),(2,3),
    (3,4),(0,4) are true; diagonals are false.
    Edge variables (0-based): (0,1)=0, (0,4)=3, (1,2)=4,
    (2,3)=7, (3,4)=9. -/
theorem ramsey5_exists : hasRamseyFreeColoring 5 :=
  witness_ramsey_free 5
    (fun | 0 | 3 | 4 | 7 | 9 => true | _ => false)
    (by native_decide)

-- Elaboration commands

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

private def runCmdMeta (cmd : String) (args : Array String)
    (errCtx : String) : MetaM String := do
  let result ← IO.Process.output
    { cmd := cmd, args := args }
  if result.exitCode != 0 then
    throwError "{errCtx}: {cmd} failed (exit \
      {result.exitCode})\nstderr: {result.stderr}\
      \nstdout: {result.stdout}"
  return result.stdout

private def buildBridgeProof (nExpr : Expr) (ctx : Expr)
    (pbProofConst : Expr) : MetaM (Expr × Expr) := do
  let finalType := mkApp (mkConst ``Not)
    (mkApp (mkConst ``hasRamseyFreeColoring) nExpr)
  let hctxProof := mkApp2
    (mkConst ``Eq.refl [.succ .zero])
    (mkConst ``Sat.PB.PBFmla) ctx
  let finalProof := mkApp4 (mkConst ``Ramsey.bridge)
    nExpr ctx hctxProof pbProofConst
  return (finalType, finalProof)

-- `ramsey_decide name n` proves not hasRamseyFreeColoring n
elab "ramsey_decide " nm:ident ppSpace nTerm:num
    : command => do
  let name := (← getCurrNamespace) ++ nm.getId
  let n := nTerm.getNat
  liftTermElabM do
    let nExpr := mkRawNatLit n
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
        (toOPB n)
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
    let constrs := encode n
    let numVars := numVarsInternal n
    let auxName := name ++ `aux
    let (ctx, _ctx', pbProofConst) ←
      VeriPB.fromVeriPBDirect constrs numVars proofStr
        auxName
    let (finalType, finalProof) ←
      buildBridgeProof nExpr ctx pbProofConst
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := finalType
      value := finalProof
    }
    Lean.logInfo
      m!"Registered {name} : ¬ hasRamseyFreeColoring {n}"

-- Reflection-based verification (uses native_decide)
elab "ramsey_reflect " nm:ident ppSpace nTerm:num
    ppSpace proofFile:str : command => do
  let name := (← getCurrNamespace) ++ nm.getId
  let n := nTerm.getNat
  let proofPath := proofFile.getString
  liftTermElabM do
    let nExpr := mkRawNatLit n
    let proofStr ← IO.FS.readFile
      (System.FilePath.mk proofPath)
    let constrsExpr := mkApp (mkConst ``encode) nExpr
    let numVarsExpr :=
      mkApp (mkConst ``numVarsInternal) nExpr
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
    let finalProof := mkApp2
      (mkConst ``no_ramsey_free_of_unsat)
      nExpr unsatProof
    let finalType := mkApp (mkConst ``Not)
      (mkApp (mkConst ``hasRamseyFreeColoring) nExpr)
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := finalType
      value := finalProof
    }
    Lean.logInfo
      m!"Registered {name} : \
        ¬ hasRamseyFreeColoring {n}"

-- K_6: 15 variables, 20 triangles, 40 constraints
ramsey_reflect ramsey6_impossible 6
  "applications/ramsey/ramsey6_kernel.pbp"

/-- The Ramsey number R(3,3) = 6. -/
theorem ramsey_3_3 : ramseyNumber 5 :=
  ⟨ramsey5_exists, ramsey6_impossible⟩

end Ramsey
