# PBLean: VeriPB Proof Certificates for Lean 4

[![Lean 4](https://img.shields.io/badge/Lean-4.30.0-blue?logo=data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAzMiAzMiI+PHRleHQgeD0iNCIgeT0iMjYiIGZvbnQtc2l6ZT0iMjgiIGZpbGw9IndoaXRlIj5MPC90ZXh0Pjwvc3ZnPg==)](https://lean-lang.org/)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

**PBLean** provides verified pseudo-Boolean proof checking in Lean 4. Reads [VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB) kernel-format proofs and produces Lean theorems, analogous to `Std.Tactic.BVDecide` (LRAT) but for pseudo-Boolean reasoning. VeriPB's kernel format is the fully-elaborated proof format produced by `veripb --elaborate`, in which every inference step is made explicit. Standalone Lean 4 project with no Mathlib dependency.

**Paper:** S. Szeider. *PBLean: Pseudo-Boolean Proof Certificates for Lean 4.* [arXiv:2602.08692](https://arxiv.org/abs/2602.08692), 2026.

## Architecture

Three-layer design mirroring LRAT:

| Layer | File | Description |
|-------|------|-------------|
| Kernel | `VeriPB/Tactic/Sat/PseudoBoolean.lean` | PB constraint types, evaluation, soundness lemmas |
| Metaprogram | `VeriPB/Tactic/Sat/FromVeriPB.lean` | Parser, normalization, `Expr`-level proof construction |
| Reflection | `VeriPB/Tactic/Sat/ReflectCheck.lean` | Verified checker definitions (pol, RUP, red coverage) |
| Reflection | `VeriPB/Tactic/Sat/ReflectFast.lean` | Runtime implementation of the checker (`@[implemented_by]`) |
| Reflection | `VeriPB/Tactic/Sat/Reflect.lean` | `checkProofBool`, soundness proof, `veripb_reflect`, `mkFormulaUnsatProof` |

Verification uses reflection: a Boolean checker with a proved soundness theorem, executed as compiled native code via `native_decide` (same trade-off as `bv_decide`). The verified checker is written over lists for provability; at runtime `@[implemented_by]` swaps in an array-based implementation that must be extensionally equal to it. That equality is tested, not proved: `Tests/Normalize.lean` and `Tests/FastConstr.lean` compare the runtime operations against verbatim copies of the verified definitions on random inputs, and `Tests/Differential.lean` (and `applications/difftest.lean` for the large proofs) runs both checkers side by side and requires identical constraint databases after every proof step.

Downstream projects that produce `formulaUnsat` theorems from their own encodings can call `VeriPB.Reflect.mkFormulaUnsatProof` to build the reflection bridge term instead of assembling it by hand.

## Supported VeriPB rules

`pol` (polynomial arithmetic, including `x w` weakening), `rup` (reverse unit propagation), `pbc`/`subproof`/`qed` (proof by contradiction), `red`/`dom` (redundance and dominance-based strengthening), `deld`/`delc` (deletion), `sol`/`soli` (solution), `f` (formula size), `output`, `conclusion UNSAT/SAT/BOUNDS`.

Known completeness gaps relative to VeriPB's checker (PBLean rejects, VeriPB accepts; never the other way round): input constraints are used as written rather than normalized, so RUP propagation over an input constraint with a repeated variable is weaker; `rup C` with an empty hint list propagates only over the negation of `C`, not over the whole database; a `pol` intermediate whose degree would become negative is truncated to 0 (VeriPB keeps the negative degree), which can make a later derivation from it weaker; and `rup` certifies the conflict by scaled addition of the hints (one complementary pair cancelled per hint) after locating the conflicting hint by propagation, which can miss a conflict that VeriPB's unit propagation finds when several weighted literals are propagated at once. Proofs elaborated by VeriPB from RoundingSat logs do not hit these cases.

## Application modules

Each module provides a trusted PB encoding and soundness theorems for a combinatorial problem. The `applications/` directory contains the corresponding OPB encodings and VeriPB kernel proofs, loaded at elaboration time. Naming convention: `Paley_97.opb` (encoding) and `Paley_97_kernel.pbp` (kernel proof).

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

Standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) plus, per theorem, one native-evaluation axiom (`_native.<command>.ax_<n>`, the same mechanism `native_decide` uses) asserting that the compiled checker run returned `true`.

## Building

Requires [elan](https://github.com/leanprover/elan). The `lean-toolchain` file pins the exact Lean version.

```
lake build                 # build everything (~40 sec)
lake build VeriPBKernel    # build kernel + tests only (~20 sec)
```

The checker modules are precompiled to native code (`precompileModules`, like `bv_decide`), so all certificate checks — including the 11 Paley graph independence numbers in `IndependentSet.lean` — run compiled rather than interpreted.

## Benchmarks

`applications/benchmark.py` measures end-to-end verification times (one `veripb_reflect` command per instance, in a fresh `lean` process) for all showcase theorems; `applications/timing.lean` times the checker alone.
```
python3 applications/benchmark.py           # Lean verification times
python3 applications/benchmark.py --full    # Also re-solve + re-elaborate
```
The `--full` mode requires [RoundingSat](https://gitlab.com/MIAOresearch/software/roundingsat) and [VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB) in PATH. Both scripts load the precompiled checker libraries; a plain `lake env lean` run does not, and then the checker executes in Lean's IR interpreter, about 20x slower.

Independence numbers of Paley graphs, v0.4.0 on an Apple M2 (Lean 4.30.0):

| p | proof lines | `checkProofBool` | of which parsing | `veripb_reflect` end-to-end |
|---|---|---|---|---|
| 53 | 1,848 | 28 ms | 8 ms | 0.97 s |
| 73 | 9,808 | 176 ms | 45 ms | 1.29 s |
| 89 | 36,795 | 787 ms | 174 ms | 2.06 s |
| 101 | 62,924 | 1.33 s | 0.29 s | 2.83 s |

The end-to-end time includes about 0.7 s of Lean startup and, for Paley(101), 0.6 s for compiling the auxiliary definition that `nativeEqTrue` evaluates (the constraint array as a Lean term). The native VeriPB checker verifies the Paley(101) proof in 0.23 s.

## References

- S. Szeider. *PBLean: Pseudo-Boolean Proof Certificates for Lean 4.* [arXiv:2602.08692](https://arxiv.org/abs/2602.08692), 2026.
- [VeriPB proof system](https://gitlab.com/MIAOresearch/software/VeriPB)
- B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström. *Certified Symmetry and Dominance Breaking for Combinatorial Optimisation.* AAAI 2022.
- [RoundingSat PB solver](https://gitlab.com/MIAOresearch/software/roundingsat)

## License

Apache 2.0. See [LICENSE](LICENSE).
