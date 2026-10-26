# The Measured Clock Spectrum — the standard optical-clock ratio table, entered as data

**Date of entry:** 2026-10-25 (commissioned by Jeff Gurd: "the standard
optical-clock ratio table, entered as T4 input with its error bars riding
along").

## Status block

- **Tier: T4 INPUT.** Every number in this dossier is *measured data*,
  copied from the published compilation named below. Nothing here is
  derived, proved, or claimed by the thet-logos corpus.
- **NO CLAIM.** This data answers nothing by itself. It is the `obs` —
  the given, measured clock spectrum — whose absence made the original
  Q1 (`blockedQ1_physicalClock`) defective: there the spectrum was
  existentially quantified, so the prover could choose it. Entered here
  as fixed data, it is what the repaired question Q1′
  (`measuredClockQuestion` in `ThetLogos/MeasuredClockSpectrum.lean`)
  is asked *about*.
- **The uncertainties ride along as data, not decoration.** Each ratio
  is stored together with its published standard uncertainty, at the
  same scale, in `clockObsErr`. A fit that ignores the error bars is
  not a fit to this data.

## Source

H. S. Margolis, G. Panfilo, G. Petit, C. Oates, T. Ido, S. Bize, et al.
(analysis performed under the auspices of the **CCL-CCTF Working Group
on Frequency Standards, WGFS**), *"The CIPM list 'Recommended values of
standard frequencies': 2021 update"*, Metrologia (2024).
Read directly at: https://arxiv.org/html/2401.14537v1

The recommended values were approved by the CCTF at its 22nd meeting
(March 2021) and became active on 13 April 2022. The ratios below are
from **Appendix B, Table 11** of that paper — "Frequency ratios
consistent with the 2021 recommended frequency values, taking into
account the covariance of the output matrix" — except the Sr/Cs entry,
which is formed from the same paper's recommended ⁸⁷Sr frequency
(Table 9) divided by the exact SI caesium frequency (see its row).

Table 11 prints each ratio with a parenthetical *absolute* standard
uncertainty on its final digits and a *fractional* uncertainty; the two
agree. The uncertainties entered here are the absolute ones (same units
as the ratio itself), so value and error bar sit on one scale.

## The table (M = 7), as entered in `clockObs` / `clockObsErr`

| # | Ratio | Value (exact rational as entered) | ± absolute uncertainty (as entered) | Published fractional uncertainty | Provenance |
|---|-------|-----------------------------------|-------------------------------------|----------------------------------|------------|
| 0 | ν(¹⁷¹Yb) / ν(⁸⁷Sr) | 1207507039343337845 / 10¹⁸ = 1.207507039343337845 | 16 / 10¹⁸ = 1.6×10⁻¹⁷ | 1.3×10⁻¹⁷ | Table 11, row ν₈/ν₁₂, printed 1.207 507 039 343 337 845(16) |
| 1 | ν(²⁷Al⁺) / ν(⁸⁷Sr) | 2611701431781463019 / 10¹⁸ = 2.611701431781463019 | 39 / 10¹⁸ = 3.9×10⁻¹⁷ | 1.5×10⁻¹⁷ | Table 11, row ν₄/ν₁₂, printed 2.611 701 431 781 463 019(39) |
| 2 | ν(²⁷Al⁺) / ν(¹⁷¹Yb) | 2162887127516663705 / 10¹⁸ = 2.162887127516663705 | 24 / 10¹⁸ = 2.4×10⁻¹⁷ | 1.1×10⁻¹⁷ | Table 11, row ν₄/ν₈, printed 2.162 887 127 516 663 705(24) |
| 3 | ν(¹⁷¹Yb⁺ E3) / ν(⁸⁷Sr) | 1495991618544900552 / 10¹⁸ = 1.495991618544900552 | 68 / 10¹⁸ = 6.8×10⁻¹⁷ | 4.6×10⁻¹⁷ | Table 11, row ν₇/ν₁₂, printed 1.495 991 618 544 900 552(68) |
| 4 | ν(¹⁷¹Yb⁺ E2) / ν(⁸⁷Sr) | 1603714045975103000 / 10¹⁸ = 1.60371404597510300 | 130 / 10¹⁸ = 1.3×10⁻¹⁶ | 8.2×10⁻¹⁷ | Table 11, row ν₆/ν₁₂, printed 1.603 714 045 975 103 00(13) |
| 5 | ν(¹⁹⁹Hg⁺) / ν(⁸⁷Sr) | 2480550195715877540 / 10¹⁸ = 2.48055019571587754 | 260 / 10¹⁸ = 2.6×10⁻¹⁶ | 1.1×10⁻¹⁶ | Table 11, row ν₅/ν₁₂, printed 2.480 550 195 715 877 54(26) |
| 6 | ν(⁸⁷Sr) / ν(¹³³Cs) | 42922800422987299 / 919263177000 ≈ 46692.61371163059107 | (value) × 1.9×10⁻¹⁶ ≈ 8.87×10⁻¹² | 1.9×10⁻¹⁶ | ν(⁸⁷Sr) recommended frequency 429 228 004 229 872.99 Hz (Table 9 of the same paper) ÷ 9 192 631 770 Hz, the exact SI ¹³³Cs frequency |

Notes on the rows:

- Here ¹⁷¹Yb⁺(E3) is the ²S₁/₂(F=0)–⁴f¹³6s ²F₇/₂(F=3) octupole
  transition (ν₇), ¹⁷¹Yb⁺(E2) the ²S₁/₂(F=0)–5d ²D₃/₂(F=2) quadrupole
  transition (ν₆), ¹⁷¹Yb the neutral lattice-clock transition (ν₈),
  ⁸⁷Sr is ν₁₂, ²⁷Al⁺ is ν₄, ¹⁹⁹Hg⁺ is ν₅ — the compilation's labels.
- Row 6 is the one entry not printed as a ratio in Table 11 (that table
  links Cs only through the recommended frequencies). Its value is the
  exact quotient of the two published numbers shown; its uncertainty
  is the published *fractional* uncertainty of the ⁸⁷Sr recommended
  frequency (1.9×10⁻¹⁶), carried onto the ratio — in the Lean module
  the stored error is the exact product
  `(42922800422987299 / 919263177000) * (19 / 10¹⁷)`, flagged here so
  nobody mistakes it for a directly printed parenthetical.
- All uncertainties are standard uncertainties (1σ), as published.

## Disagreements found, and how they were resolved

1. **Yb/Sr, adjusted vs direct.** The most precise single direct
   measurement feeding the adjustment — Boulder Atomic Clock Optical
   Network (BACON) Collaboration, "Frequency ratio measurements at
   18-digit accuracy using an optical clock network," *Nature* 591,
   564–569 (2021); input datum q₁₀₂ in the compilation — reports
   ν(¹⁷¹Yb)/ν(⁸⁷Sr) = 1.207507039343337**8482**(82) (fractional
   uncertainty 6.8×10⁻¹⁸). The adjusted compilation value entered
   here is 1.207507039343337**845**(16). The central values differ by
   3.2×10⁻¹⁸, in the trailing digits, inside both uncertainties.
   Resolution: the compilation (least-squares adjusted, correlation-
   aware) value is entered, as commissioned; the direct value is
   recorded here, not silently dropped.
2. **Print precision.** A December
...[truncated 1735 chars]