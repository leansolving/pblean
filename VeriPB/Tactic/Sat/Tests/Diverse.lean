/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import VeriPB.Tactic.Sat.FromVeriPB

/-!
# Diverse Kernel Rule Tests

Coverage-focused end-to-end tests exercising underrepresented kernel rules.
Each test produces a kernel-verified Lean theorem.

## Rule coverage

* `deld` — delete derived constraint
* `delc` — delete original clause
* `pol w` — weaken operation
-/

namespace VeriPB.Tests.Diverse

-- Delete derived constraint: derive a trivial constraint, delete it,
-- then derive the real contradiction. Exercises `deld` rule.
veripb_proof deld_test
  "p cnf 1 2
1 0
-1 0"
  "pseudo-Boolean proof version 3.0
f 2;
rup >= 0 : ~ ;
deld 3;
pol 1 2 +;
output NONE ;
conclusion UNSAT : 4;
end pseudo-Boolean proof;"

-- Delete original clause: remove an original clause from the database,
-- then prove UNSAT from the remaining clauses. Exercises `delc` rule.
veripb_proof delc_test
  "p cnf 2 4
1 0
2 0
-1 0
-2 0"
  "pseudo-Boolean proof version 3.0
f 4;
delc 2;
pol 1 3 +;
output NONE ;
conclusion UNSAT : 5;
end pseudo-Boolean proof;"

-- Weaken inline: K3 edge clauses + negations. First add three edge clauses
-- to get 2x1+2x2+2x3 >= 3, then weaken x3 (coeff 2 < degree 3) to get
-- 2x1+2x2 >= 1, then add 2*(~x1) and 2*(~x2) to derive 0 >= 1.
veripb_proof weaken_inline
  "p cnf 3 6
1 2 0
1 3 0
2 3 0
-1 0
-2 0
-3 0"
  "pseudo-Boolean proof version 3.0
f 6;
pol 1 2 + 3 + w x3 4 2 * + 5 2 * +;
output NONE ;
conclusion UNSAT : 7;
end pseudo-Boolean proof;"

end VeriPB.Tests.Diverse

/-!
## Normalization consistency tests

These verify that `normalizeConstr` (which at runtime uses the
HashMap-based `@[implemented_by]` fast path) produces the expected
results matching the slow fuel-based definition. This guards the
`@[implemented_by normalizeConstrFast]` trust.
-/

namespace VeriPB.Tests.Normalization

open Sat.PB in
private def termKey : Term → Nat × Bool
  | (_, .pos i) => (i, false)
  | (_, .neg i) => (i, true)

open Sat.PB in
private def termLt (a b : Term) : Bool :=
  let (ai, ap) := termKey a
  let (bi, bp) := termKey b
  ai < bi || (ai == bi && !ap && bp)

open Sat.PB in
private def sortTerms (ts : List Term) : List Term :=
  ts.mergeSort termLt

open Sat.PB in
private def normEq (c1 c2 : Constr) : Bool :=
  c1.degree == c2.degree && sortTerms c1.terms == sortTerms c2.terms

-- Test 1: No normalization needed
#guard normEq
  (VeriPB.normalizeConstr ⟨[(2, .pos 0), (3, .pos 1)], 3⟩)
  ⟨[(2, .pos 0), (3, .pos 1)], 3⟩

-- Test 2: Remove zero-coefficient term
#guard normEq
  (VeriPB.normalizeConstr ⟨[(0, .pos 0), (3, .pos 1)], 2⟩)
  ⟨[(3, .pos 1)], 2⟩

-- Test 3: Cancel complementary pair (5·x0 + 3·~x0 ≥ 4 → 2·x0 ≥ 1)
#guard normEq
  (VeriPB.normalizeConstr ⟨[(5, .pos 0), (3, .neg 0)], 4⟩)
  ⟨[(2, .pos 0)], 1⟩

-- Test 4: Merge like terms (2·x0 + 3·x0 ≥ 4 → 5·x0 ≥ 4)
#guard normEq
  (VeriPB.normalizeConstr ⟨[(2, .pos 0), (3, .pos 0)], 4⟩)
  ⟨[(5, .pos 0)], 4⟩

-- Test 5: Guard prevents cancel when min > degree
#guard normEq
  (VeriPB.normalizeConstr ⟨[(2, .pos 0), (3, .neg 0)], 1⟩)
  ⟨[(2, .pos 0), (3, .neg 0)], 1⟩

-- Test 6: Cancel produces all-zero terms → empty constraint
#guard normEq
  (VeriPB.normalizeConstr ⟨[(3, .pos 0), (3, .neg 0)], 5⟩)
  ⟨[], 2⟩

-- Test 7: Multiple variables with cancel + zero removal
#guard normEq
  (VeriPB.normalizeConstr
    ⟨[(2, .pos 0), (1, .neg 0), (3, .pos 1), (2, .neg 1)], 5⟩)
  ⟨[(1, .pos 0), (1, .pos 1)], 2⟩

-- Test 8: Large coefficients
#guard normEq
  (VeriPB.normalizeConstr ⟨[(100, .pos 0), (50, .neg 0)], 80⟩)
  ⟨[(50, .pos 0)], 30⟩

-- Test 9: All zeros after cancel → empty
#guard normEq
  (VeriPB.normalizeConstr ⟨[(4, .pos 0), (4, .neg 0)], 10⟩)
  ⟨[], 6⟩

-- Test 10: Multiple like terms to merge (1+2+3=6)
#guard normEq
  (VeriPB.normalizeConstr
    ⟨[(1, .pos 0), (2, .pos 0), (3, .pos 0)], 5⟩)
  ⟨[(6, .pos 0)], 5⟩

-- Test 11: Contradictory after normalization
#guard (VeriPB.normalizeConstr
  ⟨[(1, .pos 0), (1, .neg 0)], 3⟩).isContra

-- Test 12: Mixed cancel + merge + zero removal
#guard normEq
  (VeriPB.normalizeConstr
    ⟨[(2, .pos 0), (3, .neg 0), (1, .pos 0)], 4⟩)
  ⟨[], 1⟩

end VeriPB.Tests.Normalization
