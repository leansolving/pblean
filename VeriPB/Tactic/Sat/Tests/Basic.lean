/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import VeriPB.Tactic.Sat.FromVeriPB

/-!
# VeriPB Inline Tests

Kernel-verified tests using inline CNF and VeriPB proof strings.
Each `veripb_proof` invocation parses a CNF + kernel proof, constructs
a Lean proof term via the metaprogram, and registers a theorem with
zero sorry.
-/

namespace VeriPB.Tests

-- Trivial UNSAT: x AND NOT x. 1 variable, 2 clauses.
veripb_proof trivial_unsat
  "p cnf 1 2
1 0
-1 0"
  "pseudo-Boolean proof version 3.0
f 2;
rup >= 0 : ~ ;
pol 2 1 +;
output NONE ;
conclusion UNSAT : 4;
end pseudo-Boolean proof;"

-- Pigeonhole PHP(2,1): 2 pigeons, 1 hole.
veripb_proof php_2_1
  "p cnf 2 3
1 0
2 0
-1 -2 0"
  "pseudo-Boolean proof version 3.0
f 3;
rup >= 0 : ~ ;
rup 1 x1 1 x2 >= 2 : 1 2 ~;
pol 3 5 +;
output NONE ;
conclusion UNSAT : 6;
end pseudo-Boolean proof;"

-- Weakening test: x1 OR x2 OR x3 with all negated. Uses pol (addition) chain.
veripb_proof weaken_test
  "p cnf 3 4
1 2 3 0
-1 0
-2 0
-3 0"
  "pseudo-Boolean proof version 3.0
f 4;
pol 1 2 +;
pol 5 3 +;
pol 6 4 +;
output NONE ;
conclusion UNSAT : 7;
end pseudo-Boolean proof;"

-- Division/saturation test: 2 variables, 3 clauses.
veripb_proof div_sat_test
  "p cnf 2 3
1 2 0
-1 0
-2 0"
  "pseudo-Boolean proof version 3.0
f 3;
pol 2 3 +;
pol 1 4 +;
output NONE ;
conclusion UNSAT : 5;
end pseudo-Boolean proof;"

-- Tseitin on K3: 3 variables, 6 clauses. Uses both pol and rup steps.
veripb_proof tseitin_k3
  "p cnf 3 6
1 3 0
-1 -3 0
1 2 0
-1 -2 0
2 3 0
-2 -3 0"
  "pseudo-Boolean proof version 3.0
f 6;
rup >= 0 : ~ ;
pol 6 3 + 1 + s;
rup 1 ~x3 >= 1 : ~ 8 2;
rup 1 ~x2 >= 1 : ~ 8 4;
rup 1 ~x2 1 ~x3 >= 2 : 10 9 ~;
pol 5 11 +;
output NONE ;
conclusion UNSAT : 12;
end pseudo-Boolean proof;"

-- Pigeonhole PHP(3,2): 6 variables, 9 clauses. Solver-generated proof.
veripb_proof php_3_2
  "p cnf 6 9
1 2 0
3 4 0
5 6 0
-1 -3 0
-1 -5 0
-3 -5 0
-2 -4 0
-2 -6 0
-4 -6 0"
  "pseudo-Boolean proof version 3.0
f 9;
rup >= 0 : ~ ;
pol 6 3 + 2 + 8 + 7 + s;
rup 1 x1 >= 1 : ~ 11 1;
rup 1 ~x3 >= 1 : ~ 12 4;
rup 1 ~x5 >= 1 : ~ 12 5;
rup 1 x4 >= 1 : ~ 13 2;
rup 1 x6 >= 1 : ~ 14 3;
rup 1 x4 1 x6 >= 2 : 15 16 ~;
pol 9 17 +;
output NONE ;
conclusion UNSAT : 18;
end pseudo-Boolean proof;"

-- Pigeonhole PHP(4,3): 12 variables, 22 clauses. Largest inline test.
veripb_proof php_4_3
  "p cnf 12 22
1 2 3 0
4 5 6 0
7 8 9 0
10 11 12 0
-1 -4 0
-1 -7 0
-1 -10 0
-4 -7 0
-4 -10 0
-7 -10 0
-2 -5 0
-2 -8 0
-2 -11 0
-5 -8 0
-5 -11 0
-8 -11 0
-3 -6 0
-3 -9 0
-3 -12 0
-6 -9 0
-6 -12 0
-9 -12 0"
  "pseudo-Boolean proof version 3.0
f 22;
rup >= 0 : ~ ;
pol 10 4 + 3 + 15 + 14 + s;
pol 16 4 + 3 + 9 + 8 + s 2 + 24 + s 19 + 18 + s 17 + s;
pol 20 3 + 2 + 6 + 5 + s 1 + 25 + 16 + 15 + s 13 + s;
pol 11 2 + 1 + 25 + 9 + 7 + s 4 + 26 + 22 + 20 + s;
pol 6 3 + 27 + 1 + 25 + 14 + 11 + s;
pol 21 4 + 26 + 2 + 28 + 10 + 8 + s;
rup 1 x8 >= 1 : ~ 29 27 3;
rup 1 ~x2 >= 1 : ~ 30 12;
rup 1 x1 >= 1 : ~ 31 25 1;
rup 1 ~x4 >= 1 : ~ 32 5;
rup 1 ~x10 >= 1 : ~ 32 7;
rup 1 x6 >= 1 : ~ 33 28 2;
rup 1 x12 >= 1 : ~ 34 26 4;
rup 1 x6 1 x12 >= 2 : 35 36 ~;
pol 21 37 +;
output NONE ;
conclusion UNSAT : 38;
end pseudo-Boolean proof;"

-- Proof by contradiction (pbc) test: 2 variables, 3 clauses.
-- Derives x1 >= 1 via pbc, then combines with ¬x1 for contradiction.
veripb_proof pbc_simple
  "p cnf 2 3
1 2 0
-1 0
-2 0"
  "pseudo-Boolean proof version 3.0
f 3;
pbc 1 x1 >= 1 : subproof;
pol 1 4 + ;
pol 5 3 + ;
qed : 6;
pol 7 2 + ;
output NONE ;
conclusion UNSAT : 8;
end pseudo-Boolean proof;"

-- Pbc with RUP inside subproof: 2 variables, 4 clauses.
-- x1 OR x2, NOT x1 OR NOT x2, x1 OR NOT x2, NOT x1 OR x2. UNSAT.
-- Derives x1 >= 1 via pbc (using two RUPs inside), then contradicts.
veripb_proof pbc_with_rup
  "p cnf 2 4
1 2 0
-1 -2 0
1 -2 0
-1 2 0"
  "pseudo-Boolean proof version 3.0
f 4;
pbc 1 x1 >= 1 : subproof;
rup 1 x2 >= 1 : ~ 5 1 ;
rup 1 ~x2 >= 1 : ~ 5 3 ;
pol 6 7 + ;
qed : 8;
pol 9 2 + ;
pol 9 4 + ;
pol 10 11 + ;
output NONE ;
conclusion UNSAT : 12;
end pseudo-Boolean proof;"

-- Division test: explicitly uses `d` (ceiling division) in pol.
-- x1 + x2 >= 1, ¬x1, ¬x2. Division by 1 is trivial but exercises the code path.
-- After: add negations to derive contradiction.
veripb_proof div_explicit_test
  "p cnf 2 3
1 2 0
-1 0
-2 0"
  "pseudo-Boolean proof version 3.0
f 3;
pol 1 1 d 2 + 3 +;
output NONE ;
conclusion UNSAT : 4;
end pseudo-Boolean proof;"

-- Multiplication test: explicitly uses `* N` in pol.
-- x1 + x2 >= 1, ¬x1, ¬x2. Multiply first by 2, saturate, then add.
-- 2·x1 + 2·x2 >= 2, saturate → 2·x1 + 2·x2 >= 2
-- Add 2*(¬x1) and 2*(¬x2): complementary pairs cancel to 0 >= 2.
veripb_proof mul_explicit_test
  "p cnf 2 3
1 2 0
-1 0
-2 0"
  "pseudo-Boolean proof version 3.0
f 3;
pol 1 2 * 2 2 * + 3 2 * +;
output NONE ;
conclusion UNSAT : 4;
end pseudo-Boolean proof;"

-- Literal axiom test: uses literal axiom in pol derivation.
-- x1 >= 1 (unit clause), ~x1 >= 1 (unit clause).
-- Add literal axiom x1 (>= 0) to C1, giving 2·x1 >= 1.
-- Then add 2*(C2) = 2·~x1 >= 2. After cancel: 0 >= 1. Contradiction.
veripb_proof lit_axiom_test
  "p cnf 1 2
1 0
-1 0"
  "pseudo-Boolean proof version 3.0
f 2;
pol 1 x1 + 2 2 * +;
output NONE ;
conclusion UNSAT : 3;
end pseudo-Boolean proof;"

end VeriPB.Tests
