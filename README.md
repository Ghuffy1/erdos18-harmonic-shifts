# Harmonic dyadic shifts and short sums of factorial divisors

**Will Howe, Grant Huffman, Jensen Kohlmeyer, Liam Kruer**

Equal joint contributions to the mathematics and Lean formalization:
[@H0W4RD-dev](https://github.com/H0W4RD-dev),
[@Ghuffy1](https://github.com/Ghuffy1),
[@JENW1N](https://github.com/JENW1N),
[@lkruer](https://github.com/lkruer).

This repository contains a complete mathematical manuscript and Lean 4 proof
of the uniform bound

\[ h(n!)=O((\log n)^9). \]

Here h(N) is the maximum, over every integer 1<=R<=N, of the least number of
distinct positive divisors of N summing to R. The bound implies all three
original statements in [Erdős Problem 18](https://www.erdosproblems.com/18).
The proposed new contribution is the quantitative harmonic dyadic-shift
mixing step and its uniform factorial application. Earlier results for (a)
and (b), the divisor construction and transfer methods remain explicitly credited.

## Manuscript and exact theorems

- [Mathematical manuscript](paper/manuscript.pdf), Theorem 1 and Corollary 6.
- [Editable manuscript](paper/manuscript.md) and [bibliography](paper/references.bib).
- [Lean entry point](lean/Erdos18c.lean).
- [Original statements](lean/Erdos18c/OriginalStatement.lean):
  `Erdos18.erdos_18a`, `Erdos18.erdos_18b`, `Erdos18.erdos_18c`.
- [Unconditional quantitative bound](lean/Erdos18c/FinalBound.lean):
  `Erdos18c.ninthPowerBound`.
- [Attribution and source roles](ATTRIBUTION.md).

The three original definitions are reproduced from the pinned Formal
Conjectures sources, with equivalence proofs to the internal definitions.
Unproved upstream conjectures are not imported. All final targets report
only `propext`, `Classical.choice`, and `Quot.sound` as axiom dependencies.

## Reproduction

The toolchain is Lean 4.34.0; mathlib is pinned to
`5ed2965256430c3649e86755f9576b54eca72435`. The complete dependency lock is
`lean/lake-manifest.json`.

With the pinned Lean toolchain installed, the conventional commands are:

```sh
cd lean
lake exe cache get
lake build
lake env lean Erdos18c.lean
```

For a clean direct-compiler check against an existing installation of the
same dependencies, run from the repository root:

```sh
python scripts/verify_lean.py --all --fresh --dependency-project PATH_TO_DEPENDENCY_PROJECT --lean PATH_TO_LEAN_4_34
```

The command creates an empty local output directory and records every source
hash, command, exit code, diagnostic, and axiom audit in `verification/`.
Use the generated build directory for the additional import recheck:

```sh
python scripts/verify_lean.py Erdos18c --build-dir FRESH_OUTPUT_DIRECTORY --dependency-project PATH_TO_DEPENDENCY_PROJECT --lean PATH_TO_LEAN_4_34 --trust-zero
```

The local proof check is not a sponsor acceptance, an external expert review,
or a novelty/priority certificate. The source comparisons and their limits
are recorded in [the novelty report](docs/NOVELTY_REPORT.md). No prize or
particular award allocation is asserted.
