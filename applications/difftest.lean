/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import VeriPB.Tactic.Sat.Tests.Differential

/-!
Release-time differential test of the fast reflection checker against the
verified step function on every application proof (see
`VeriPB/Tactic/Sat/Tests/Differential.lean` for the harness). Run from the
project root after `lake build`:

    lake env lean applications/difftest.lean

The verified List-based pipeline is slow; the whole run takes a few minutes.
-/

open VeriPB.Tests.Differential in
#eval show IO Unit from do
  let cases : List (String × String) := [
    ("php", "php32"),
    ("binpack", "bp12_5"),
    ("eqcoloring", "k331_4"),
    ("langford", "langford5"), ("langford", "langford6"), ("langford", "langford9"),
    ("schur", "schur5"), ("schur", "schur14_3"),
    ("vdw", "vdw9"), ("vdw", "vdw35"),
    ("ramsey", "ramsey6"), ("ramsey", "ramsey9_34"),
    ("paley", "Paley_13"), ("paley", "Paley_17"), ("paley", "Paley_29"), ("paley", "Paley_37"),
    ("paley", "Paley_41"), ("paley", "Paley_53"), ("paley", "Paley_61"), ("paley", "Paley_73"),
    ("paley", "Paley_89"), ("paley", "Paley_97"), ("paley", "Paley_101")
  ]
  for (dir, n) in cases do
    let base := s!"applications/{dir}/{n}"
    runOne n (base ++ ".opb") (base ++ "_kernel.pbp") (fullEvery := 2000)
