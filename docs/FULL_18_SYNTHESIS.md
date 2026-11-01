# Unified account of Erdős Problem 18

Authors of the new manuscript: Will Howe, Grant Huffman, Jensen Kohlmeyer,
Liam Kruer. Manuscript and formalization prepared 1 November 2026.

The new quantitative bound \(h(n!)\le A(\log n)^9\) is now fully proved in
Lean. It implies all three original statements; it is not obtained merely
by combining the statements of the previously known (a) and (b).

| Part | Conclusion | Prior credit and current proof |
|---|---|---|
| (a) | Infinitely many practical m have h(m)<(log log m)^C | Prior Price/GPT-5.6 Sol Pro and van Doorn/GPT-6 Astra Pro work is retained. The new factorial subsequence gives exponent 10, not a better general-sequence bound. |
| (b) | For every epsilon>0, h(n!)<n^epsilon eventually | Kohlmeyer-Kruer's earlier accepted result retains priority. The new bound also implies it. |
| (c) | h(n!)<(log n)^C eventually for fixed C>0 | New harmonic-shift argument and full formalization give exponent 10. Novelty is relative to the documented search. |

For (c), log n>A absorbs the constant. For (b), powers of log n are eventually
smaller than every n^epsilon. For (a), (n+1)!>=2^n implies
log(n+1)<=4 log log((n+1)!) eventually; these factorials are practical and unbounded.
Theorem 1 and Corollary 6 give the written proof; `FinalBound.lean` and
`OriginalStatement.lean` give unconditional Lean theorems.

## Collaboration-hub source used

The connected API retrieved the private [18(b) manuscript/source record](https://github.com/lkruer/collaboration-hub/tree/main/results/math/erdos/0018/jenwin-site-manuscript)
and [accepted-source record](https://github.com/lkruer/collaboration-hub/blob/main/results/math/erdos/0018/jkdesktop-part-b-accepted-source/README.md).
The full 735,691-byte source has SHA-256
`4d6ee89617415288e9f127beb3c0e0211c011f891889fcb43d0e16373bd14088`
and Git blob `22ad0e1cf8e87ced632e45bde82de7e6c117dd1c`.
The paper hash is
`f89f4f46b9535c5c990a29bf0ddf1eb305123429a3b89dfb508e95c8cc9b2d6a`.

The formalization adapts its representation operations, binary divisor blocks,
finite entropy infrastructure, factorial quotient estimates and potential
induction, with source-specific credit in code. These adapted components and
the new synthesis were compiled locally; the historical entire (b) file was
not replayed as a standalone project. No circular use of (c) occurs.

## References

- [Kohlmeyer-Kruer paper](https://jenwin.io/papers/erdos18b-factorial-divisors.pdf).
- [Accepted part-(b) result](https://conjectures.io/results/e93a2766-4c70-4564-b565-d0c556f35929).
- [van Doorn/GPT-6 Astra Pro manuscript](https://github.com/Woett/ChatGPT-s-note-on-Erdos18/blob/56b455ae6949b76f41292d35829034ebb8663241/Practical%20numbers%20and%20Egyptian%20fractions.tex).
- [Original problem](https://www.erdosproblems.com/18).

This document records the mathematical scope. It is not a JSP adjudication or
an award decision.
