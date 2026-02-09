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

end VeriPB.Tests.Reflect
