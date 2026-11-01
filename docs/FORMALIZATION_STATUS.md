# Full formalization and statement audit

The complete proof is present. `Erdos18c.ninthPowerBound` is unconditional;
it is no longer an assumed input. `Erdos18c.erdos_18_full` proves all three
conclusions. `OriginalStatement.lean` proves the exact original statements as
`Erdos18.erdos_18a`, `Erdos18.erdos_18b`, and `Erdos18.erdos_18c`.

## Exact target correspondence

The upstream reference is google-deepmind/formal-conjectures, commit
`a64e959c32c270df4dd0d96d2027481f15750534`. Source blobs:

- Problem 18: `b271cde9f99252c9430b2d99db12dfef70077da4`.
- Practical numbers: `5232acfb635006def7014d7863612d1f1eaaaefb`.
- AdditivelyComplete: `6b1bf6f167619ca16dbd97ac19a4c71eaa448e1b`.

The natural-number subset-sum, practicalH and IsPractical definitions are
reproduced in the original namespaces, with equivalence theorems to the
internal definitions. The upstream conjecture file is not imported. It
contains unfinished declarations, retained only as noncompiled evidence.

The bound covers every integer from 1 through n!, with distinct positive
divisors. Zero remainders, the inclusive endpoint, residue zero, exact positive
quotients, and the finite initial exceptions are handled. For (a), factorials
give an unbounded practical sequence. For (b), every real epsilon > 0 is covered.
For (c), a fixed exponent 10 absorbs the ninth-power bound's constant.

## Proof dependency chain

| Layer | Files and strongest output |
|---|---|
| Finite entropy and convolution | FiniteLaw, BinaryEntropy, FiniteConvolution, DyadicEntropy, DyadicConvolution, DyadicDilations |
| New mixing lemma | HarmonicMixing: support greater than half the cyclic group; two support elements cover every residue |
| Credited divisor digits | DivisorRepresentations, DivisorDigits, LinearDigitSupply, DigitInput |
| Positive local representatives | LocalRepresentatives, LocalBounds: common host 1004k; count <= 400000(log k)^5 eventually |
| Exact lifting | LiftingScale, LogPotential, IntegerLifting, LocalShortSums: exact positive integer representations in (6 binaryLength R)! with O((log binaryLength R)^7) distinct summands |
| Global bound | GlobalBounds, FinalBound: factorial radix plus logarithmic potential, yielding O((log n)^9) |
| Original statements | Target, OriginalStatement, Erdos18c: all three statements, no target hypothesis |

The formalization uses a convolution/involution-difference proof of the
harmonic lemma and potential functions for the two recursions. Constants
differ from the written proof; the theorem and all required cases agree.
The auxiliary EntropyEstimates module is also compiled and audited.

## Actual verification

`verification/clean-build.json` records the complete fresh-output build,
module order and completion. Per-module receipts record exact source hashes,
commands, compiler versions, exit codes, stdout/stderr, and output hashes.
The target axiom audits list only:

    propext, Classical.choice, Quot.sound

There are no admitted proof steps, custom axioms, unsafe declarations or
native_decide in the submitted Lean sources. Static checks are supplementary;
the transitive target audits establish that no extra axiom is used.

`verification/trust-zero-run.json`, when present with a successful receipt,
records the additional Lean `--trust=0` import recheck. That is the same Lean
implementation, not a second independently implemented kernel. See its actual
exit code rather than assuming that a requested check succeeded.

This is local proof verification. External mathematical review, sponsor
verification, priority and award adjudication remain separate.
