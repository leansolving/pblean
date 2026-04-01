/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import VeriPB.Tactic.Sat.Reflect

/-!
# Reflection-based Checker Tests

Test the reflection-based checker (`checkProofBool` + `ofReduceBool`)
on a small OPB instance with VeriPB kernel proof.
-/

namespace VeriPB.Tests.Reflect

-- PHP(2,1): 2 vars, 3 constraints. Uses rup + pol.
veripb_reflect php21_reflect
  "VeriPB/Tactic/Sat/Tests/data/php21.opb"
  "VeriPB/Tactic/Sat/Tests/data/php21_kernel.pbp"

-- Red subproof test: pigeon-hole variant with redundance-based strengthening.
-- Uses red/dom with explicit subproof (proofgoal #1 and proofgoal 1).
-- Tests: red rule, substitution parsing, goal verification, auto-satisfaction.
-- From VeriPB test suite: redundance_explicit_subproof.
veripb_reflect red_subproof_reflect
  "VeriPB/Tactic/Sat/Tests/data/red_subproof.opb"
  "VeriPB/Tactic/Sat/Tests/data/red_subproof_kernel.pbp"

-- Red variable swap test: symmetric formula with x1↔x2 swap.
-- Tests: auto-satisfied coverage (all constraints map to each other under swap).
veripb_reflect red_swap_reflect
  "VeriPB/Tactic/Sat/Tests/data/red_swap.opb"
  "VeriPB/Tactic/Sat/Tests/data/red_swap_kernel.pbp"

-- Red with constant substitution (x1 → 0): all 4 constraints affected,
-- 3 have trivially-contra goal negates, 2 need real subproofs.
veripb_reflect red_const_reflect
  "VeriPB/Tactic/Sat/Tests/data/red_const.opb"
  "VeriPB/Tactic/Sat/Tests/data/red_const_kernel.pbp"

-- Red with negated literal substitution (x1 → ~x2, x2 → ~x1):
-- complementary swap where all constraints auto-satisfy.
veripb_reflect red_neglit_reflect
  "VeriPB/Tactic/Sat/Tests/data/red_neglit.opb"
  "VeriPB/Tactic/Sat/Tests/data/red_neglit_kernel.pbp"

-- Dom keyword (identical semantics to red, different keyword).
veripb_reflect dom_basic_reflect
  "VeriPB/Tactic/Sat/Tests/data/dom_basic.opb"
  "VeriPB/Tactic/Sat/Tests/data/dom_basic_kernel.pbp"

-- PHP(3,2): pigeonhole principle with symmetry-breaking via red rule.
-- Proof uses red to add x1≥1 (WLOG pigeon 1 goes to hole 1) with a cyclic
-- substitution (x1↔x3↔x5, x2↔x4↔x6), then derives contradiction via pol.
-- Elaborated from VeriPB test suite: redundance_explicit_subproof.
veripb_reflect php32_red_reflect
  "applications/php/php32.opb"
  "applications/php/php32_kernel.pbp"

end VeriPB.Tests.Reflect
