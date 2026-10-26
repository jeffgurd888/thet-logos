import ThetLogos.BlockedQuestions
import Mathlib.Data.Fin.VecNotation

/-!
# ThetLogos.MeasuredClockSpectrum — the measured clock spectrum (Tier T4 INPUT)

**Status: measured data, entered 2026-10-25. NO CLAIM.**

This module contains *data and one posted question* — no theorems, no
proofs, and no placeholder tactics. The data are the standard optical-clock frequency
ratios, copied as exact rationals from the published compilation:

H. S. Margolis, G. Panfilo, G. Petit, C. Oates, T. Ido, S. Bize, et al.
(CCL-CCTF Working Group on Frequency Standards), "The CIPM list
'Recommended values of standard frequencies': 2021 update",
Metrologia (2024), arXiv:2401.14537 — Appendix B, Table 11 (ratios
consistent with the 2021 recommended frequency values), with the
⁸⁷Sr/¹³³Cs entry formed from the same paper's recommended ⁸⁷Sr
frequency. Full provenance, row by row, is in the dossier
`whitepaper/measured-clock-spectrum-data-2026-10-25.md`.

Why this exists: the original Q1 (`blockedQ1_physicalClock`) asked for
a thermal triple whose modular frequency differences reproduce "an
observed clock spectrum", but quantified the spectrum existentially —
the prover could choose it, so the statement was a form, not a
question. `clockObs` below is the missing given: a measured spectrum,
fixed by the world's clock laboratories, not by us. `measuredClockQuestion`
is the repaired Q1′ instantiated on this data. It is a definition — the
question is POSTED here, not answered.
-/

namespace ThetLogos

/-- The measured clock spectrum: seven optical-clock frequency ratios
    as exact rationals (the published decimal values of the CIPM 2021
    compilation, Table 11). **Tier T4 INPUT — measured data, not
    derived and not proved.**

    Index legend (`ν` labels are the compilation's):
    - `0` : ν(¹⁷¹Yb) / ν(⁸⁷Sr)        = 1.207507039343337845
    - `1` : ν(²⁷Al⁺) / ν(⁸⁷Sr)        = 2.611701431781463019
    - `2` : ν(²⁷Al⁺) / ν(¹⁷¹Yb)       = 2.162887127516663705
    - `3` : ν(¹⁷¹Yb⁺ E3) / ν(⁸⁷Sr)    = 1.495991618544900552
    - `4` : ν(¹⁷¹Yb⁺ E2) / ν(⁸⁷Sr)    = 1.60371404597510300
    - `5` : ν(¹⁹⁹Hg⁺) / ν(⁸⁷Sr)       = 2.48055019571587754
    - `6` : ν(⁸⁷Sr) / ν(¹³³Cs)        = 429228004229872.99 / 9192631770
                                        ≈ 46692.61371163059107 -/
def clockObs : Fin 7 → ℚ :=
  ![1207507039343337845 / 1000000000000000000,
    2611701431781463019 / 1000000000000000000,
    2162887127516663705 / 1000000000000000000,
    1495991618544900552 / 1000000000000000000,
    1603714045975103000 / 1000000000000000000,
    2480550195715877540 / 1000000000000000000,
    42922800422987299 / 919263177000]

/-- The published standard uncertainties of `clockObs`, as positive
    rationals **on the same scale** (absolute, in ratio units) — the
    error bars ride along as data, not decoration. For indices `0`–`5`
    these are the compilation's parenthetical absolute uncertainties
    on the printed values. For index `6` only a fractional uncertainty
    is published (1.9×10⁻¹⁶, on the ⁸⁷Sr recommended frequency), so
    the stored entry is the exact product of the ratio with that
    fraction. -/
def clockObsErr : Fin 7 → ℚ :=
  ![16 / 1000000000000000000,
    39 / 1000000000000000000,
    24 / 1000000000000000000,
    68 / 1000000000000000000,
    130 / 1000000000000000000,
    260 / 1000000000000000000,
    (42922800422987299 / 919263177000) * (19 / 100000000000000000)]

/-- **The repaired Q1′, instantiated on the measured spectrum** — a
    definition (a posted question), **not** a theorem and **not**
    answered here.

    `measuredClockQuestion N ε` asks: does there exist a thermal
    triple — inverse temperature `β > 0` and a Dirac spectrum
    `lam : Fin N → ℝ` on an `N`-dimensional space — together with a
    nonzero global scale `c` and an assignment `f` of clock lines to
    pairs of levels, such that every *measured* ratio in `clockObs`
    is reproduced by a modular frequency difference
    `modularFreqDiff β lam i j = β (lam i ^ 2 - lam j ^ 2)` up to the
    scale `c` and within the tolerance `ε`?

    Differences from the original `blockedQ1_physicalClock`: the
    spectrum is *given* (it is `clockObs`, measured), `β` is required
    positive, and matching is up to the tolerance `ε` — a parameter,
    so the published error bars in `clockObsErr` can set it. The exact
    form `ε = 0` is expected to be **false** for measured data
    (differences of squares form a measure-zero set; real measurements
    land where they land). The tolerance form is the physical
    question. -/
noncomputable def measuredClockQuestion (N : ℕ) [NeZero N] (ε : ℝ) : Prop :=
  ∃ (β : ℝ) (lam : Fin N → ℝ) (c : ℝ) (f : Fin 7 → Fin N × Fin N),
    0 < β ∧ c ≠ 0 ∧
      ∀ m : Fin 7,
        |modularFreqDiff β lam (f m).1 (f m).2 - c * (clockObs m : ℝ)| ≤ ε

end ThetLogos
