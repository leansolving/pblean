/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
-- Kernel + Tests
import VeriPBKernel

-- Applications (trusted encodings)
import VeriPB.Tactic.Sat.IndependentSet
import VeriPB.Tactic.Sat.Langford
import VeriPB.Tactic.Sat.Schur
import VeriPB.Tactic.Sat.VanDerWaerden
import VeriPB.Tactic.Sat.Ramsey
import VeriPB.Tactic.Sat.EquitableColoring

/-!
# VeriPB: Verified Pseudo-Boolean Proof Checking

This is the root import file for the VeriPB library, which provides
kernel-verified checking of VeriPB pseudo-Boolean proofs in Lean 4.
-/
