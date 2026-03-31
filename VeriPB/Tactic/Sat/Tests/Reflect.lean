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

end VeriPB.Tests.Reflect
