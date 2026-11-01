# Mathematical review and version boundary

The original complete argument is preserved in the nonpublic review archive as `source-manuscript.md`, SHA-256
`667b28b7dfd1eb4ae0df58bbf707a43978eb848b62b0e39785aed2523162dd6c`.
The earlier separate-context informal review is preserved in the nonpublic
review archive as `evidence/prior-independent-review.txt`; it found no gap in the ninth-power bound.

The final manuscript retains the core written proof, expands citations and
attribution, proves all three corollaries, and describes the full formalization.
The author list is exactly the one supplied by the user. No human verifier or
individual contribution role has been invented.

| Obligation | Final check |
|---|---|
| Uniform small-rate harmonic mixing | Finite entropy, dyadic projections, convolution contraction, support bound and two-sum covering proved in Lean |
| Uniform divisor digits at linear host | Prime-count estimate, blocks, incomplete prefixes and entropy supplied in Lean |
| Positive representatives, including residue zero | Positive digit smoothing and actual multiset witnesses proved in Lean |
| Exact integer lifting | Representative height, S<R, positive quotient, bit-length decrease and logarithmic potential proved in Lean |
| Distinctness and factorial host | Multiset carrying, divisibility reserve and host embedding proved in Lean |
| All targets through n! | Uniform remainder construction and exact factorial radix proved in Lean |
| Eventual ninth-power bound | Full potential induction, finite base cases and constant absorption proved in Lean |
| Original three statements | Exact definitions and quantifiers matched; all three unconditional theorems compiled |

The formal route implements the same mechanism using order-two translation
differences instead of an explicit conditional-probability space. It uses
logarithmic potentials in place of counting recursion stages. It does not
assume that the earlier (b) theorem implies (c), or that a fixed-parameter
mixing theorem is uniform as its parameter tends to zero.

No finite experiment stands in for an infinite assertion. The threshold and
constants are ineffective for practical computation here; numerical efficiency
is not claimed. The construction is mathematical and noncomputable, as allowed
by the original existential/eventual statements.

The source-level proof and Lean target now agree on the result. The novelty
review found no earlier matching complete solution in its documented search,
but global priority and independent expert acceptance are not certified.
