# Authorship, AI assistance and prior work

The manuscript authors, in the supplied order, are **Will Howe, Grant Huffman,
Jensen Kohlmeyer and Liam Kruer**. The submitter records all four as equal joint
contributors to the new mathematics and the accompanying Lean formalization.
No institutional affiliation is asserted.

| Contributor | GitHub | New mathematics | Lean formalization |
|---|---|---|---|
| Will Howe | [@H0W4RD-dev](https://github.com/H0W4RD-dev) | Equal joint contribution | Equal joint contribution |
| Grant Huffman | [@Ghuffy1](https://github.com/Ghuffy1) | Equal joint contribution | Equal joint contribution |
| Jensen Kohlmeyer | [@JENW1N](https://github.com/JENW1N) | Equal joint contribution | Equal joint contribution |
| Liam Kruer | [@lkruer](https://github.com/lkruer) | Equal joint contribution | Equal joint contribution |

The submitting account is **Ghuffy1**. The handles were checked against the
team's collaboration-hub membership list; Will Howe's public profile also
identifies his name. The submitter supplied the equal-contribution attribution
on 1 November 2026. This is the authors' contribution statement, not independent
identity verification or a decision about award allocation. No personal award
claim is made on another contributor's behalf.

Codex assisted the new mathematical exploration, informal reviews, Lean
formalization and local checking. The full written proof received a separate-
context AI review; that is not represented as independent human peer review.

The new quantitative harmonic additive-shift estimate and its application
use earlier infrastructure. Jensen Kohlmeyer and Liam Kruer's *Short sums of
factorial divisors and Erdős Problem 18(b)* (16 September 2026) is credited for
divisor digits, positive lifting, factorial radix and related formal code.
The companion source was retrieved with SHA-256
`4d6ee89617415288e9f127beb3c0e0211c011f891889fcb43d0e16373bd14088`.
Adaptations are identified in the Lean modules; the earlier (b) theorem is
not being reclassified as a new discovery here.

Plasma AI's L63/L64/L66 records are credited for the overlapping quantitative
transfer criterion and relevant limitations. The general entropy literature
is cited in the manuscript. Prior part-(a) work by GPT-5.6 Sol Pro prompted
by Liam Price, and by Wouter van Doorn with GPT-6 Astra Pro, retains its credit.

In particular, the new proof of part (a) in this repository is a corollary of
the new factorial bound; it does not import the earlier part-(a) proof. The
[pinned van Doorn manuscript](https://github.com/Woett/ChatGPT-s-note-on-Erdos18/blob/56b455ae6949b76f41292d35829034ebb8663241/Practical%20numbers%20and%20Egyptian%20fractions.tex)
gives the earlier square-log-log result and credits Price's GPT-assisted work.
It also reports an Aristotle formalization. No first mathematical or first
formalization priority for part (a) is claimed here, and that earlier Lean code
is not used by this project. The original Price document was not separately
audited in this review.

Definitions and target types adapted from The Formal Conjectures Authors
(2026), commit `a64e959c32c270df4dd0d96d2027481f15750534`, are Apache-2.0;
the license is included. The three original source snapshots under `reference/`
are evidence and are not compiled. An overall redistribution license for new
work has not been assigned on the authors' behalf.
