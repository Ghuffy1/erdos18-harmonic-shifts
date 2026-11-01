# Verification of the selected proof commit

Original proof repository: https://github.com/Ghuffy1/erdos18-harmonic-shifts

Selected proof commit: **`4b2ed2d07693602fa3b87fb5aa72fe16933f98af`**.

All 24 production Lean files in this commit match the exact bytes checked by
the complete fresh-output build. `PROOF_COMMIT.json` lists their SHA-256 hashes
and records the Git-blob comparison. The full build finished at
2026-11-01T19:30:58.437449+00:00. After the commit was created, the aggregate was checked
again with Lean `--trust=0`, finishing at 2026-11-01T19:34:36.302911+00:00 with exit code 0.

## Results

- The exact original targets `Erdos18.erdos_18a`, `Erdos18.erdos_18b` and
  `Erdos18.erdos_18c` are unconditional theorems.
- `Erdos18c.ninthPowerBound` proves the quantitative ninth-power logarithmic bound.
- Final transitive axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- No admitted step, custom axiom or native_decide replaces a proof step.
- The source references for the original definitions are byte-matched to the
  pinned upstream Git blobs. Unfinished upstream conjectures are not imported.
- The ten-page manuscript at this commit matches the visually checked PDF;
  all 340 formulas rendered without reported errors or overflow.

The compiler is Lean 4.34.0, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b.
mathlib is 5ed2965256430c3649e86755f9576b54eca72435. The full dependency lock is
committed. Existing dependencies were read-only during verification.
See the root README for commands and the accompanying module receipts for
complete stdout/stderr, source and output hashes and elapsed times.

The full clean build was performed before the Git commit; correspondence to
the selected commit was then checked byte for byte. The trust-zero command
was repeated after the commit, against unchanged committed source. This is
local Lean verification, not an independently implemented checker or an
external human review. It does not establish novelty, prize eligibility,
sponsor acceptance or payment.

The four authors are credited equally for the new mathematics and Lean
formalization, as instructed by the submitting author. Earlier part-(a)/(b)
priority and adapted methods are credited separately in ATTRIBUTION.md and
the manuscript. Identity and contribution adjudication remain external to
these mathematical checks.
