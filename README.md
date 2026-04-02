# PBLean: VeriPB Proof Certificates for Lean 4

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0--rc1-blue?logo=data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAzMiAzMiI+PHRleHQgeD0iNCIgeT0iMjYiIGZvbnQtc2l6ZT0iMjgiIGZpbGw9IndoaXRlIj5MPC90ZXh0Pjwvc3ZnPg==)](https://lean-lang.org/)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

**PBLean** provides verified pseudo-Boolean proof checking in Lean 4. Reads [VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB) kernel-format proofs and produces Lean theorems, analogous to `Std.Tactic.BVDecide` (LRAT) but for pseudo-Boolean reasoning. VeriPB's kernel format is the fully-elaborated proof format produced by `veripb --elaborate`, in which every inference step is made explicit. Standalone Lean 4 project with no Mathlib dependency.

**Paper:** S. Szeider. *PBLean: Pseudo-Boolean Proof Certificates for Lean 4.* [arXiv:2602.08692](https://arxiv.org/abs/2602.08692), 2026.

## Architecture

Three-layer design mirroring LRAT:

| Layer | File | Description |
|-------|------|-------------|
| Kernel | `VeriPB/Tactic/Sat/PseudoBoolean.lean` | PB constraint types, evaluation, soundness lemmas |
| Metaprogram | `VeriPB/Tactic/Sat/FromVeriPB.lean` | Parser, checker, `Expr`-level proof construction |
| Reflection | `VeriPB/Tactic/Sat/Reflect.lean` | `checkProofBool` + `ofReduceBool` native evaluation |

Two verification paths are available. The **metaprogram path** (`veripb_proof`) builds kernel proof terms directly in `MetaM`. The **reflection path** (`veripb_reflect`) uses `native_decide` for better scalability at the cost of trusting the Lean compiler — the same trade-off as `bv_decide`. All application theorems use the reflection path.

## Supported VeriPB rules

`pol` (polynomial arithmetic), `rup` (reverse unit propagation), `pbc`/`subproof`/`qed` (proof by contradiction), `red`/`dom` (redundance and dominance-based strengthening), `deld`/`delc` (deletion), `sol`/`soli` (solution), `f` (formula size), `output`, `conclusion UNSAT/SAT/BOUNDS`.

## Application modules

Each module provides a trusted PB encoding, soundness theorems, and verified results for a combinatorial problem. The `applications/` directory contains the corresponding OPB encodings and VeriPB kernel proofs, loaded at elaboration time. Naming convention: `Paley_97.opb` (encoding) and `Paley_97_kernel.pbp` (kernel proof).

**Independent set** (`IndependentSet.lean`) — Independence number of Paley graphs for all primes p ≡ 1 (mod 4) from 13 to 101. (Paley(5) is omitted as α(K₅) = 1 is trivial.)
```lean
theorem paley13_alpha  : independenceNumber (paley 13)  3
theorem paley17_alpha  : independenceNumber (paley 17)  3
theorem paley29_alpha  : independenceNumber (paley 29)  4
theorem paley37_alpha  : independenceNumber (paley 37)  4
theorem paley41_alpha  : independenceNumber (paley 41)  5
theorem paley53_alpha  : independenceNumber (paley 53)  5
theorem paley61_alpha  : independenceNumber (paley 61)  5
theorem paley73_alpha  : independenceNumber (paley 73)  5
theorem paley89_alpha  : independenceNumber (paley 89)  5
theorem paley97_alpha  : independenceNumber (paley 97)  6
theorem paley101_alpha : independenceNumber (paley 101) 5
```

The data yields a formally verified non-monotonicity result: α(Paley(97)) = 6 > 5 = α(Paley(101)).
```lean
theorem paley_alpha_not_monotone :
    ∃ p q : Nat, p < q ∧ ∃ a b : Nat,
      independenceNumber (paley p) a ∧ independenceNumber (paley q) b ∧ a > b
```

**Langford pairing** (`Langford.lean`) — No Langford pairing of orders 6 and 9 exists.
```lean
-- Langford namespace
theorem langford6_impossible : ¬hasLangfordPairing 6
theorem langford9_impossible : ¬hasLangfordPairing 9
```

**Schur number** (`Schur.lean`) — S(2) = 4: {1,...,4} has a Schur-free 2-coloring but {1,...,5} does not. Generalized to k-coloring: S(3) = 13 verified via one-hot encoding.
```lean
-- Schur namespace
theorem schur_number_2 : schurNumber 4
theorem schur14_impossible : ¬hasKSchurFreeColoring 3 14
```

**Van der Waerden number** (`VanDerWaerden.lean`) — W(2,3) = 9: {1,...,8} has an AP-free 2-coloring but {1,...,9} does not. Generalized to k-term APs: W(2,4) = 35 verified.
```lean
-- VanDerWaerden namespace
theorem vdw_number_2_3 : vanDerWaerdenNumber 8
theorem vdw35_impossible : ¬hasKAPFreeColoring 4 35
```

**Ramsey number** (`Ramsey.lean`) — R(3,3) = 6: K₅ has a triangle-free 2-coloring but K₆ does not. Generalized to asymmetric R(s,t): R(3,4) ≤ 9 verified.
```lean
-- Ramsey namespace
theorem ramsey_3_3 : ramseyNumber 5
theorem ramsey9_34_impossible : ¬hasAsymRamseyFreeColoring 9 3 4
```

**Equitable coloring** (`EquitableColoring.lean`) — The equitable chromatic number of K_{3,3,1} is 5.
```lean
-- EquitableColoring namespace
theorem k331_eq_chromatic : equitableChromaticNumber k331 5
```

**Pigeonhole principle** (`Tests/Reflect.lean`, `applications/php/`) — PHP(3,2) is unsatisfiable. Exercises the `red` rule for symmetry breaking via a cyclic substitution witness.
```lean
theorem php32_red_reflect : formulaUnsat
```

**Bin packing** (`BinPacking.lean`) — 12 items of sizes [10,9,8,8,6,5,4,4,4,4,4,4] do not fit into 5 bins of capacity 14. The total size equals 5×14 = 70 (not refutable by weight alone); unsatisfiability follows from a rounding argument on the capacity constraints.
```lean
-- BinPacking namespace
theorem bp12_5_impossible : ¬hasPacking inst12_5
```

**Predicate convention:** Each predicate `fooNumber n` asserts that `n` is the largest value for which the feasibility condition holds. For example, `ramseyNumber 5` means K₅ admits a Ramsey-free 2-coloring but K₆ does not, hence R(3,3) = 6.

## Trust base

Standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) plus the Lean compiler (`Lean.trustCompiler`), the same trust model as `bv_decide` and `omega`.

## Building

Requires [elan](https://github.com/leanprover/elan). The `lean-toolchain` file pins the exact Lean version.

```
lake build                 # build everything (~7 min, mostly IndependentSet.lean)
lake build VeriPBKernel    # build kernel + tests only (~20 sec)
```

Full build time is dominated by `IndependentSet.lean` (~6 min), which verifies 11 Paley graph independence numbers via `native_decide`. The kernel-only build is fast.

## Benchmarks

`applications/benchmark.py` measures verification times for all showcase theorems.
```
python3 applications/benchmark.py           # Lean verification times
python3 applications/benchmark.py --full    # Also re-solve + re-elaborate
```
The `--full` mode requires [RoundingSat](https://gitlab.com/MIAOresearch/software/roundingsat) and [VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB) in PATH.

## References

- S. Szeider. *PBLean: Pseudo-Boolean Proof Certificates for Lean 4.* [arXiv:2602.08692](https://arxiv.org/abs/2602.08692), 2026.
- [VeriPB proof system](https://gitlab.com/MIAOresearch/software/VeriPB)
- B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström. *Certified Symmetry and Dominance Breaking for Combinatorial Optimisation.* AAAI 2022.
- [RoundingSat PB solver](https://gitlab.com/MIAOresearch/software/roundingsat)

## License

Apache 2.0. See [LICENSE](LICENSE).
