# Novelty review for the proposed solution of Erdős 18(c)

Reviewed on 1 November 2026. This is a documented prior-art search, not a guarantee
that every unpublished or unindexed result has been found.

## Result being assessed

The manuscript claims the uniform bound \(h(n!)=O((\log n)^9)\), where each target
integer up to \(n!\) is a sum of distinct positive divisors. Its proposed new
ingredient is a harmonic random-shift lemma on \(\mathbb Z/2^k\mathbb Z\):
a law having lower-prefix entropy at least \(gL\log 2\) reaches support density
greater than one half after \(O(g^{-2}(\log k)^2)\) independently shifted copies.
The application uses \(g\asymp 1/\log k\). Two copies of that support cover the
group. The claimed novelty is this quantitative bridge and its factorial
application, not entropy, binary digits, or factorial lifting in general.

## Conclusion

No earlier complete proof of the polylogarithmic factorial conclusion was found.
No matching harmonic-shift lemma with the same hypotheses and uniform
small-\(g\) bound was found in the primary sources examined. The proposed result
therefore appears new relative to this search. Global novelty, priority,
authorship adjudication, and external mathematical acceptance remain unsettled.

The manuscript's main mathematical argument was separately checked in full in
the previous independent review. No gap was identified. The accompanying new
Lean development now proves the ninth-power bound and all three original
statements without extra axioms. This settles local proof checking; it does
not itself establish novelty, peer review or sponsor acceptance.

## Closest prior work and exact overlap

| Source | What was inspected | Relationship to this manuscript |
|---|---|---|
| Kohlmeyer–Kruer, *Short sums of factorial divisors and Erdős Problem 18(b)*, 16 September 2026 | Complete local manuscript; freshly downloaded PDF matched SHA-256 f89f4f46b9535c5c990a29bf0ddf1eb305123429a3b89dfb508e95c8cc9b2d6a. In particular Sections 2–6 and the statement expressly leaving (c) open. | Direct prior art. Supplies disjoint factorial-divisor digits and positive quotient/radix methods. Its fixed-parameter multiplicative mixing proves (b), not the uniform polylogarithm in (c). These methods must be credited. |
| Plasma AI L63, updated 14 October 2026 | Statement and complete linked proof | Direct prior art. Already gives a quantitative local-to-global criterion, including positive lifting, repetition removal and factorial radix. The required local representatives remain an unproved input there. No novelty is claimed for the general transfer mechanism. |
| Plasma AI L64, updated 14 October 2026 | Statement and complete linked proof | Its obstruction rules out a fixed positive entropy rate for a separated-digit family at the relevant factorial scale. It allows the vanishing rate and overlapping additive sums used here. |
| Plasma AI L66, updated 14 October 2026 | Statement and complete linked proof, including the loss in the displayed mixing witnesses | Supplies a vanishing-rate spread estimate and a conditional multiplicative route. Its polynomial quantitative mixing assumption is explicitly unproved. The present proof does not assume that statement or substitute a varying parameter into a fixed-parameter theorem. |
| Hughes, *Sums of distinct divisors of factorials*, arXiv:2609.10902v1 | Author record and HTML manuscript, especially theorem and final remarks | Gives an explicit (n/\log n)-scale upper bound, not the proposed polylogarithmic result. The factorial question is the same, but the greedy-gap mechanism differs. |
| Tao, *Sumset and inverse sumset theory for Shannon entropy*, arXiv:0906.4387v5 | Main Theorems 1.10–1.11, conditional-trial setting, and Appendix A entropy facts | Establishes general entropy/additive-combinatorial tools. The inverse theorem's quantitative dependence is poor and no harmonic powers-of-two mixing assertion was located. Standard chain rules and conditioning arguments are background, not new claims. This is not a proof that no corollary of the paper could yield a related statement. |
| Green–Manners–Tao, *Sumsets and entropy revisited*, arXiv:2306.13403v3; DOI 10.1002/rsa.21252 | Main statements and Proposition 1.4 with its proof under homomorphisms | Closely related use of entropy and fibers. It treats entropic doubling, Ruzsa distance and structural results, rather than this stated small-rate harmonic-shift covering estimate. No directly matching theorem was located. |
| Abbe–Li–Madiman, *Entropies of weighted sums in cyclic groups and an application to polar codes*, arXiv:1512.00135v4 | Main statements and Sections 3.1–3.3 on weighted sums and source polarization | Important related background that should not be omitted. Its optimized kernels over finite fields and sum/difference comparisons differ from a harmonic distribution of noninvertible dyadic multipliers on prime-power cyclic groups. No directly matching estimate was found. |
| Hochman, *On self-similar sets with overlaps and inverse theorems for entropy*, Annals of Mathematics 180 (2014), 773–822 | Published paper's definitions of components and Theorems 2.7–2.9, with the surrounding parameter discussion; not the entire 50-page proof | Close multiscale entropy background. The statements concern convolution growth and local uniform/atomic structure on the line, with parameter-dependent thresholds. They do not state the manuscript's explicit harmonic dyadic-shift estimate. This comparison is not a proof that the new lemma cannot be derived from a more general known result. |
| van Doorn and GPT-6 Astra Pro, *Practical numbers and Egyptian fractions*, commit 56b455ae6949b76f41292d35829034ebb8663241 | Complete TeX text; especially Theorem 1.1 and its proof, and the attribution to GPT-5.6 Sol Pro prompted by Liam Price | Earlier part-(a) work with h(m) bounded by a constant times (log log m)^2 on a suitable practical sequence, stronger there than this manuscript's corollary. The construction does not give the asserted bound for every large factorial. Credit is retained; no new priority for (a) is claimed. The original Price document was not separately audited. |
| OpenAI, *Almost-everywhere Fourier convergence in L log L*, September 2026, entropy-foundations section, Git blob 96d0dd847785759b2c8f3c9493960c429b7030e4 | Complete retrieved entropy-foundations section | Uses independent rows, conditioning contexts and entropy compression. Its hypotheses and conclusion concern noisy sums and phase alignment. The shared conditioning principles are standard; no factorial or harmonic-dyadic covering result was found in this section. Other sections were not exhaustively audited. |

## Public status and priority evidence

The original [problem page](https://www.erdosproblems.com/18) and
[proof-claim page](https://www.erdosproblems.com/forum/thread/18/proof-claims)
were retrieved directly on this date. Three listed claims address (a) or (b),
not (c). The [research index](https://erdosproblems.ai/wiki/research/erdos_18)
still describes (c) as open. Such labels are corroborating status evidence,
not proof that no prior solution exists.

The [Conjectures.io result](https://conjectures.io/results/e93a2766-4c70-4564-b565-d0c556f35929)
is an accepted and paid part-(b) record. It is not evidence that (c) was settled.
The original paper explicitly distinguishes the stronger question.

The private collaboration hub was also read through the connected GitHub API
on this date. The manuscript record includes the 18(b) PDF and Lean file; the
accepted-source record links the matched source and reports its accepted target
as `Erdos18.erdos_18b`. The full 735,691-byte source was subsequently retrieved
and matched to SHA-256
`4d6ee89617415288e9f127beb3c0e0211c011f891889fcb43d0e16373bd14088`.
The adapted representation, digit, entropy and transfer infrastructure was
compiled as part of the new proof. The entire historical (b) project was not
independently replayed. The three retrieved README files are preserved in the nonpublic review archive
under `evidence/hub/`. No hub content was written or published.

Searches of the public JSP repository for `JSP-000055` returned five PRs and
two issues at the earlier check on this date. The PRs concern finite examples,
the classical (h(n!)<n) bound, or incorrect problem mappings; none supplies a
complete (c) proof. [Scope issue 4923](https://github.com/TheJustinSunPrize/awards/issues/4923)
concerns the older (b) result. The retrieved comment does not adjudicate (c).

The final same-day repository check again returned five PRs and two issues;
their text still supplies no complete (c) proof. Exact-ID search evidence is
saved in the nonpublic review archive as `evidence/JSP-duplicate-search.json`. Follow-up public searches for
the exact harmonic/18(c) formulation and polylogarithmic factorial bounds
again located the credited conditional routes and prior weaker results,
without a matching earlier complete theorem. Search misses are not proofs of
absence, and the sponsor may identify further records during review.

Private local source caches were also searched for the exact harmonic-shift
phrases and `erdos_18c`; no matching cached document was returned in that
bounded search. A private cache is neither a complete literature database nor
independently verifiable public priority evidence.

## Search strategy and limits

Search families included exact problem labels and formulas, the new lemma's
description, factorial divisor representations, entropy in prime-power cyclic
groups, random dilations/powers of two, weighted sums, source polarization,
and additive entropy under homomorphisms. Exact-title and citation-following
searches were used to obtain the related primary papers rather than relying on
aggregator summaries. The separate query log preserves representative queries.

The review distinguishes reading a complete proof from inspecting selected
statements. It does not assert that all cited literature, every later citation,
non-English literature, or private correspondence was exhaustively reviewed.
An external expert could still identify an equivalent known lemma or a prior
application. That possibility must not be converted into either a certainty
of novelty or an invented prior-art objection.

## Recommended claim and attribution

A defensible submission description is: “A proposed proof of Erdős 18(c) via a
quantitative harmonic dyadic-shift entropy lemma, combined with credited
factorial-divisor digit and lifting methods.”

List Will Howe, Grant Huffman, Jensen Kohlmeyer and Liam Kruer as instructed.
Do not invent individual contribution roles. Retain Kohlmeyer–Kruer's earlier
part-(b) authorship and Plasma AI's author-recorded transfer/obstruction credits.
Disclose Codex assistance and the actual review/formalization status.

## Primary links

- [Kohlmeyer–Kruer](https://jenwin.io/papers/erdos18b-factorial-divisors.pdf)
- [L63 proof](https://erdosproblems.ai/wiki/theory/number_theory/L63_polylogarithmic_dyadic_representatives/_proof)
- [L64 proof](https://erdosproblems.ai/wiki/theory/number_theory/L64_factorial_digit_entropy/_proof)
- [L66 proof](https://erdosproblems.ai/wiki/theory/number_theory/L66_divisor_residue_spread/_proof)
- [Hughes](https://arxiv.org/abs/2609.10902)
- [Tao](https://arxiv.org/abs/0906.4387)
- [Green–Manners–Tao](https://arxiv.org/abs/2306.13403)
- [Abbe–Li–Madiman](https://arxiv.org/abs/1512.00135)
- [Hochman, published paper](https://annals.math.princeton.edu/wp-content/uploads/annals-v180-n2-p07-p.pdf)
- [van Doorn and GPT-6 Astra Pro, pinned TeX](https://github.com/Woett/ChatGPT-s-note-on-Erdos18/blob/56b455ae6949b76f41292d35829034ebb8663241/Practical%20numbers%20and%20Egyptian%20fractions.tex)
- [Private hub, 18(b) manuscript and Lean](https://github.com/lkruer/collaboration-hub/tree/main/results/math/erdos/0018/jenwin-site-manuscript)
- [OpenAI entropy foundations](https://github.com/openai/math/blob/main/preprints/Almost-everywhere-Fourier-convergence-in-L-log-L-September-23-2026/build/sections/03-entropy-foundations.tex)

