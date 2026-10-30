/-
# ThetLogos.PlaneCrossingBeta7Close — B7-2b-v: the B7-2
close — `kappa7dep_eq`, probe-consistency stated, and
the B7-line close fences

**Fences, up front.** NO CLAIM. Parts of the Clay
Yang–Mills statement closed by this module: **0**.
Dials 0/4. This is the closing brick (B7-2b-v) of
B7-2 and of the B7 line's assembly work. It is thin
by design: it packages the landed total decomposition
`kappa7dep_total_decomposition`
(`ThetLogos.PlaneCrossingBeta7Fibers` § Total7, in
B7-1's exact variable context) as the single named
assembly identity `kappa7dep_eq`, by transport — the
fiber accounting is NOT re-proved here. It records
the probe-consistency sentence in bounded prose
(stated, not re-proved; see the closing section), and
it writes the B7-line close fences.

**Why a separate closing module.** The decomposition
lives in `PlaneCrossingBeta7Fibers`, which imports
`PlaneCrossingBeta7Assembly`; the assembly module
therefore cannot import the fibers module (an import
cycle), and the identity cannot be packaged there.
This module imports the fibers module (for the
decomposition) and the probe module (for the
certified verdict it names in prose) and closes the
line here.

**B7-line close fences, recorded here.** B7-2 is
COMPLETE: B7-2a (the seven channel excesses,
`PlaneCrossingBeta7Assembly`), B7-2b-i/ii/iii (the
fiber accounting, the ADJ/OPP counts evaluated
CONSTANT at `8` and `4` per primitive quad, and the
two B7-0 settlements), B7-2b-iv (the total
decomposition), and B7-2b-v (this module,
`kappa7dep_eq`). B7-0's claims-to-check are SETTLED,
both CONFIRMED in the predicted direction at
B7-2b-iii: the card-5 erasure claim
(`card_five_erasure_settlement`) and the card-6
family-split claim
(`card_six_family_split_settlement`). B7-PROBE's
certified outcome is **(ii)** (registry BR1-008,
`verdict_B7Probe`): every order-7 channel vanishes
on the joint kernel `K₆` at both seats; K-K7 did NOT
fire at either seat. **No sign is asserted for
`kappa7dep` or for any term of the identity**: the
β⁷ general sign is FRONTIER (B7-3 is not queued),
and the β⁷ decision at the seats passes to β⁸ —
β⁸ is not queued, and the regress has no internal
stop (as recorded on the face of `verdict_B7Probe`).
-/

import ThetLogos.PlaneCrossingBeta7Fibers
import ThetLogos.PlaneCrossingBeta7Probe

open MeasureTheory Finset

namespace ThetLogos

section Close7

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- **The order-7 assembly identity** (B7-2b-v, the
B7-2 headline, packaging
`kappa7dep_total_decomposition` by transport):
`κ₇^dep` is the order-6 dependent part dressed by
`4 + (colCount N − 4) B` (with
`B = 1 − e₁/d`), plus the order-5 and order-4
dressings displayed below, plus the seven B7-2a
channel excesses at `d⁻⁷` with weights `-1/24`
(`(4,1,1,1)`), `-1/12` (`(3,2,1,1)`, adjacent and
opposite parts together), `-1/48` (`(2,2,2,1)`),
`-1/2` (`(2,1,1,1,1,1)` on `C₆`), `-1/2`
(`(2,1,1,1,1,1)` on `Θ(2,2,2)`), `-1` (`Θ(1,3,3)`
book), plus the forced named residuals: the order-6
`C₆`/`Θ` channel excesses reappearing at
`2 e₁ d⁻⁷`, the theta 4-subset sum at
`e₁ (μ₂ − 2 e₁²) d⁻⁷`, its doubled companion
`theta4SubsetDoubledSum` at `(e₁²/2) d⁻⁷`,
`bookHexaEraseSum` at `e₁ d⁻⁷`, and
`book4SubsetSum` at `-2 e₁³ d⁻⁷`. Every coefficient
was read off the landed fiber accounting
(B7-2b-i/ii/iii) at B7-2b-iv; nothing is fitted and
nothing is re-proved here — the proof is the
decomposition itself. The statement sits in B7-1's
exact variable context (general `(G, ρ)`, no
irreducibility; `Even N`, `3 ≤ N`, continuity of
`g ↦ repMatrix ρ g`). FENCE: NO CLAIM; this is a
finite counting identity inside the corpus — parts
closed 0, dials 0/4; no sign is asserted. -/
theorem kappa7dep_eq (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    kappa7dep ρ μG u u'
      = (4 + (colCount N - 4) * (1 - e1 ρ μG / (d : ℝ)))
          * kappa6dep ρ μG u u'
        + (- (1 / 2) * ((1 - e1 ρ μG / (d : ℝ)) ^ 2 * (colCount N : ℝ) ^ 2
            - 7 * (1 - e1 ρ μG / (d : ℝ)) ^ 2 * (colCount N : ℝ)
            + 12 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
            + 6 * (1 - e1 ρ μG / (d : ℝ)) * (colCount N : ℝ)
            - 24 * (1 - e1 ρ μG / (d : ℝ))
            + (colCount N : ℝ)
            - (colCount N - 4) * (realMoment ρ μG 2 / (d : ℝ) ^ 2)
            + 12))
          * kappa5dep ρ μG u u'
        + ((1 / 6) * ((1 - e1 ρ μG / (d : ℝ)) ^ 3 * (colCount N : ℝ) ^ 3
            - 9 * (1 - e1 ρ μG / (d : ℝ)) ^ 3 * (colCount N : ℝ) ^ 2
            + 26 * (1 - e1 ρ μG / (d : ℝ)) ^ 3 * (colCount N : ℝ)
            - 24 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
            + 6 * (1 - e1 ρ μG / (d : ℝ)) ^ 2 * (colCount N : ℝ) ^ 2
            - 42 * (1 - e1 ρ μG / (d : ℝ)) ^ 2 * (colCount N : ℝ)
            + 72 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
            - 3 * (1 - e1 ρ μG / (d : ℝ)) * (colCount N : ℝ) ^ 2 * (realMoment ρ μG 2 / (d : ℝ) ^ 2)
            + 3 * (1 - e1 ρ μG / (d : ℝ)) * (colCount N : ℝ) ^ 2
            + 21 * (1 - e1 ρ μG / (d : ℝ)) * (colCount N : ℝ) * (realMoment ρ μG 2 / (d : ℝ) ^ 2)
            + 6 * (1 - e1 ρ μG / (d : ℝ)) * (colCount N : ℝ)
            - 36 * (1 - e1 ρ μG / (d : ℝ)) * (realMoment ρ μG 2 / (d : ℝ) ^ 2)
            - 72 * (1 - e1 ρ μG / (d : ℝ))
            - (colCount N : ℝ) * (realMoment ρ μG 3 / (d : ℝ) ^ 3)
            - 9 * (colCount N : ℝ) * (realMoment ρ μG 2 / (d : ℝ) ^ 2)
            + 10 * (colCount N : ℝ)
            + 4 * (realMoment ρ μG 3 / (d : ℝ) ^ 3)
            + 36 * (realMoment ρ μG 2 / (d : ℝ) ^ 2)
            + 24))
          * kappa4dep ρ μG u u'
        + ((d : ℝ)⁻¹) ^ 7
          * (- (1 / 24) * kappa7chan4111Excess ρ μG u u'
            - (1 / 12) * (kappa7chan3211AdjExcess ρ μG u u'
              + kappa7chan3211OppExcess ρ μG u u')
            - (1 / 48) * kappa7chan2221Excess ρ μG u u'
            - (1 / 2) * kappa7chan211111C6Excess ρ μG u u'
            - (1 / 2)
              * kappa7chan211111ThetaExcess ρ μG u u'
            - kappa7chanTheta133Excess ρ μG u u'
            + 2 * e1 ρ μG
              * (kappa6chanC6Excess ρ μG u u'
                + kappa6chanThetaExcess ρ μG u u')
            + e1 ρ μG * (realMoment ρ μG 2
                - 2 * (e1 ρ μG) ^ 2)
              * ∑ C ∈ thetaSupports,
              ∑ T ∈ Finset.powersetCard 4 C,
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            + ((e1 ρ μG) ^ 2 / 2)
              * theta4SubsetDoubledSum ρ μG u u'
            + e1 ρ μG * bookHexaEraseSum ρ μG u u'
            - 2 * (e1 ρ μG) ^ 3
              * book4SubsetSum ρ μG u u') :=
  kappa7dep_total_decomposition ρ μG hN hN3 hρcont u u'

#print axioms kappa7dep_eq

end Close7

/-! ## Probe-consistency, stated (not re-proved)

**The consistency sentence, in exactly these bounded
terms.** The identity `kappa7dep_eq` is consistent
with BR1-008's certified verdict (`verdict_B7Probe`,
outcome (ii)) by construction, in the following
sense and no stronger: (1) each dressing term of the
identity is a scalar multiple of `κ₆^dep`, `κ₅^dep`,
or `κ₄^dep`, and at either probe seat each dressing
vanishes on the joint kernel
`K₆ = ker κ₄^dep ∩ ker κ₅^dep ∩ ker κ₆^dep` — each
lower dependent form vanishes on the joint kernel by
its own landed definition chain, as the probe's
pre-registered procedure records; (2) the seven
channels of the identity vanish at both seats on
`K₆` by `verdict_B7Probe`; (3) the remaining terms
of the identity — the named residuals (the order-6
`C₆`/`Θ` channel excesses at `2 e₁ d⁻⁷`, the theta
4-subset sum at `e₁ (μ₂ − 2 e₁²) d⁻⁷` and its doubled
companion at `(e₁²/2) d⁻⁷`, `bookHexaEraseSum` at
`e₁ d⁻⁷`, and `book4SubsetSum` at `−2 e₁³ d⁻⁷`) —
are seat-data-free general `(G, ρ)` forms, and this
brick asserts NOTHING about their restrictions to
the seats. Accordingly this brick does NOT assert
that `κ₇^dep` vanishes on `K₆` at the seats, and it
asserts no β⁷ sign. The verdict is the probe's, the
identity is general; their conjunction — the
dressings and the seven channels pose no term that
contradicts outcome (ii), with the residuals' seat
behavior unasserted rather than claimed — is the
whole of the consistency recorded here. -/

/-! ## B7-line close

This module closes B7-2 and the B7 line's assembly
work. Landed state, recorded at full rank: B7-2 is
COMPLETE (`kappa7dep_eq` above, by transport from
B7-2b-iv's `kappa7dep_total_decomposition`, over
B7-2a's seven excesses and B7-2b-i/ii/iii's fiber
accounting). B7-0's claims-to-check are SETTLED,
both CONFIRMED in the predicted direction at
B7-2b-iii (card-5 erasure:
`card_five_erasure_settlement`; card-6 family split:
`card_six_family_split_settlement`). B7-PROBE's
certified outcome is (ii) (BR1-008): every order-7
channel vanishes on `K₆` at both seats, K-K7 did not
fire, and the β⁷ decision at the seats passes to β⁸.
FENCES: NO CLAIM; parts of the Clay Yang–Mills
statement closed by the B7 line: 0; dials 0/4; the
β⁷ general sign is FRONTIER (B7-3 not queued); β⁸ is
not queued; the 𝒜 ⪰ 0 core is untouched by this
identity in either direction, and the β line's
continuum content is untouched by this finite
identity. -/

end ThetLogos
