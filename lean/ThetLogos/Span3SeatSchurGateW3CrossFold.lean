/-
# W3 REMAINDER R2b: `hCrossFold` DISCHARGED — the folded cross identity

Brick R2b of the W3 remainder package (scoping dossier
`w3-remainder-scoping-2026-11-03.md` §2). GATE-0 item 6's
assembly (`gate4c_hyp6_of_named_inputs`,
`ThetLogos.Span3SeatSchurGateItem6`) consumes five
per-pair named inputs for GATE-4C hypothesis 6; this
module discharges the fourth, `hCrossFold`: the folded
cross identity consumed by item 6's P3
(`seatPairing_dressed_folded_nonneg_of_cross`) in its
`hCrossFold` hypothesis slot, verbatim:

`fiberAvgTop μG hN (fun z => (Real.exp
    (-(halfActionP ρ β z)) : ℂ) * (posGaugeAvg μG f) z
    * φ' (tauBot hN z))`
`= fiberAvgTop μG hN (fun z => (Real.exp
    (-(halfActionP ρ β z)) : ℂ)
    * (mirrorGaugeAvg μG f) z * φ' (tauBot hN z))`,

for every even `N`, every `β`, every strict-half
observable `f` and every layer function `φ'` — **no
hypotheses on either, and no `4 ≤ N`**: the identity is
a pure substitution, junk-safe in exactly the way the
dressed integrabilities are not (compare R1's
K-W3-HMARG-FORM lesson — those were integral
*identities between different integrals*; this one is
an equality of *integrands*, pointwise, before any
integration happens).

**The engine (one substitution, both cross
identities).** The two twirls coincide as functions,
`mirrorGaugeAvg μG f = posGaugeAvg μG f`, because the
mirror action IS the pos action precomposed with the
site reflection, pointwise at every strict-half link:

`gaugeMirrorPos g z' m = gaugePosFun (g ∘ reflSite) z' m`

— at a spatial link because reflection commutes with
spatial shifts (`reflSite_torusShift_of_ne`); at a
time link because reflection conjugates the time
shift to its inverse (`reflSite_torusShift_zero`) and
the mirror's defining double inversion cancels against
it. This is the mechanism the R2a falsity probe exposed
at its finite seats (probe report
`w3-r2a-hcross-probe-report-2026-11-03.md` §4, T2);
here it is proved at the corpus's general `(G, μG)`.
The pi Haar measure on gauge functions is invariant
under the reparametrization `g ↦ g ∘ reflSite`
(`measurePreserving_piCongrLeft` at the site
reflection's permutation), so the two Haar averages
agree. The folded weight never enters the argument:
both sides of `hCrossFold` carry the same factor
`(Real.exp (-(halfActionP ρ β z)) : ℂ)` at the same
point `z`, so the folded identity is the unfolded
twirl equality composed with a common multiplier —
the same engine also yields the unfolded `hCross`
(corollary below; R2a's brick proper, recorded here
only as the engine's immediate byproduct).
K-W3-CROSS does NOT fire, in either clause: no
counterexample exists at the consumed generality
because the identity is a theorem there.

**NO CLAIM** — parts of any official Millennium
statement closed by this module: 0. Dials: 0/4.
**The fence, on the face:** this discharges ONE of
item 6's five named inputs (the fourth). `hMarg`
stands consumed only in R1's re-pinned form (its
integrability side conditions are R6's wiring
question); the two dressed integrabilities stand at
the factor class (R2d+R3a); `hCross` is R2a's brick
(in flight in its own lane at the time of this
landing — the corollary below is the same engine,
not a second landing of it); `hInvFold` is discharged
(R2c). Hypothesis 6 is NOT discharged — its assembly
is R6, which fires separately under Jeff's 2026-11-03
decision (the factor-class entry). GATE-4C's frozen
statement is untouched; W3 (`seatSchurProductStepOpen`)
remains OPEN. This is a route fact only — not K-F2-2,
and nothing here certifies any pairing's sign. The
gate + W3 prove neither FACT nor clause (a);
`LayerKernelPos`, `𝒜 ⪰ 0`, and uniformity remain open.

This module is NOT in the root import list of the
library; it is verified by a targeted build.
-/

import ThetLogos.Span3SeatSchurGateItem6
import ThetLogos.PlaneCrossingSeparate
import ThetLogos.PlaneCrossingSymm
import ThetLogos.LatticeReflection

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Span3SeatSchurGateW3CrossFold

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## §1. The reflection reparametrization of gauge-function space -/

/-- The site reflection as a permutation of the torus
sites (it is an involution, `reflSite_involutive`). -/
def reflSiteEquiv : Equiv.Perm (Fin 4 → ZMod N) :=
  Function.Involutive.toPerm _ reflSite_involutive

/-- The reparametrization of gauge-function space by
precomposition with the site reflection, as a
measurable equivalence (the pi-congruence at the site
permutation). -/
def reflGaugeEquiv :
    ((Fin 4 → ZMod N) → G) ≃ᵐ ((Fin 4 → ZMod N) → G) :=
  MeasurableEquiv.piCongrLeft (fun _ => G) reflSiteEquiv

theorem reflSiteEquiv_symm_apply (x : Fin 4 → ZMod N) :
    reflSiteEquiv.symm x = reflSite x :=
  rfl

omit [Group G] [MeasurableInv G] [TopologicalSpace G]
  [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] in
theorem reflGaugeEquiv_apply (g : (Fin 4 → ZMod N) → G)
    (x : Fin 4 → ZMod N) :
    reflGaugeEquiv g x = g (reflSite x) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : (Fin 4 → ZMod N) => G)
    reflSiteEquiv g (reflSiteEquiv.symm x)
  rw [Equiv.apply_symm_apply, reflSiteEquiv_symm_apply] at h
  exact h

omit [Group G] [MeasurableInv G] [IsTopologicalGroup G] [BorelSpace G]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG] in
/-- The reflection reparametrization preserves the pi
Haar measure on gauge functions: the family is
constant, so the pi-congruence at a site permutation
is measure-preserving. -/
theorem measurePreserving_reflGaugeEquiv :
    MeasurePreserving (⇑(reflGaugeEquiv (G := G) (N := N)))
      (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)
      (Measure.pi fun _ : (Fin 4 → ZMod N) => μG) :=
  MeasureTheory.measurePreserving_piCongrLeft
    (fun _ : (Fin 4 → ZMod N) => μG) reflSiteEquiv

/-! ## §2. The pointwise substitution: mirror = pos, reflected -/

/-- **The probe's mechanism, proved.** The mirror
gauge action is the pos gauge action of the reflected
gauge function, pointwise at every strict-half link:
at a spatial link, reflection commutes with the shift
(`reflSite_torusShift_of_ne`), so both actions read
`g (reflSite x)` at the base and `g (reflSite (σμ x))`
at the tip; at a time link, the mirror transports to
the reflected link `((σ₀)⁻¹ (θ x), 0)` and inverts
twice, while reflection conjugates the time shift to
its inverse (`reflSite_torusShift_zero`), and the two
computations agree. -/
theorem gaugeMirrorPos_eq_gaugePosFun_refl
    (g : (Fin 4 → ZMod N) → G)
    (z' : ↥(posLinks (N := N)) → G)
    (m : ↥(posLinks (N := N))) :
    gaugeMirrorPos g z' m
      = gaugePosFun (g ∘ reflSite) z' m := by
  by_cases hμ : m.1.2 = 0
  · rw [gaugeMirrorPos_of_snd_eq_zero g z' hμ]
    have hr : reflLink m.1
        = ((torusShift N 0).symm (reflSite m.1.1), 0) := by
      unfold reflLink
      rw [ite_eq_left hμ]
    rw [hr]
    show (g ((torusShift N 0).symm (reflSite m.1.1)) * (z' m)⁻¹
          * (g (torusShift N 0
              ((torusShift N 0).symm (reflSite m.1.1))))⁻¹)⁻¹
        = (g ∘ reflSite) m.1.1 * z' m
          * ((g ∘ reflSite) (torusShift N m.1.2 m.1.1))⁻¹
    rw [Equiv.apply_symm_apply, hμ]
    simp only [Function.comp_apply]
    rw [reflSite_torusShift_zero]
    simp only [mul_inv_rev, inv_inv]
    rw [mul_assoc]
  · rw [gaugeMirrorPos_of_snd_ne_zero g z' hμ]
    have hr : reflLink m.1 = (reflSite m.1.1, m.1.2) := by
      unfold reflLink
      rw [ite_eq_right hμ]
    rw [hr]
    show g (reflSite m.1.1) * z' m
          * (g (torusShift N m.1.2 (reflSite m.1.1)))⁻¹
        = (g ∘ reflSite) m.1.1 * z' m
          * ((g ∘ reflSite) (torusShift N m.1.2 m.1.1))⁻¹
    simp only [Function.comp_apply]
    rw [reflSite_torusShift_of_ne hμ]

/-! ## §3. The twirls coincide -/

omit [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG] in
/-- **The two twirls are the same function.** The
mirror gauge average equals the pos gauge average for
every strict-half observable: pointwise the mirror
action is the pos action of the reflected gauge
function (§2), and the pi Haar measure on gauge
functions is invariant under that reflection
reparametrization (§1). No regularity on `f` is used —
the substitution is exact, hence junk-safe. -/
theorem mirrorGaugeAvg_eq_posGaugeAvg
    (f : (↥(posLinks (N := N)) → G) → ℂ) :
    mirrorGaugeAvg μG f = posGaugeAvg μG f := by
  funext z
  have hfun : ∀ g : (Fin 4 → ZMod N) → G,
      gaugeMirrorPos g z
        = gaugePosFun (⇑(reflGaugeEquiv (G := G) (N := N)) g) z := by
    intro g
    funext m
    rw [gaugeMirrorPos_eq_gaugePosFun_refl]
    congr 1
    funext x
    exact (reflGaugeEquiv_apply g x).symm
  show (∫ g : (Fin 4 → ZMod N) → G, f (gaugeMirrorPos g z)
      ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG))
    = ∫ g : (Fin 4 → ZMod N) → G, f (gaugePosFun g z)
      ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG)
  calc (∫ g : (Fin 4 → ZMod N) → G, f (gaugeMirrorPos g z)
        ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG))
      = ∫ g : (Fin 4 → ZMod N) → G,
          f (gaugePosFun (⇑(reflGaugeEquiv (G := G) (N := N)) g) z)
        ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG) :=
        integral_congr_ae (ae_of_all _ fun g => by
          show f (gaugeMirrorPos g z)
              = f (gaugePosFun (⇑(reflGaugeEquiv (G := G) (N := N)) g) z)
          rw [hfun g])
    _ = ∫ g : (Fin 4 → ZMod N) → G, f (gaugePosFun g z)
        ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG) :=
        (measurePreserving_reflGaugeEquiv μG).integral_comp
          (reflGaugeEquiv (G := G) (N := N)).measurableEmbedding
          (fun g : (Fin 4 → ZMod N) → G =>
            f (gaugePosFun g z))

/-! ## §4. The folded cross identity (headline) and its unfolded corollary -/

omit [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG] in
/-- **R2b — `hCrossFold` discharged.** The folded
cross identity, in exactly the form item 6's folded
pairing P3 (`seatPairing_dressed_folded_nonneg_of_cross`)
takes as its `hCrossFold` hypothesis and its assembly
P4 (`gate4c_hyp6_of_named_inputs`) consumes as the
fourth of its five per-pair named inputs: for every
even `N`, every `β`, every strict-half observable `f`
and every layer function `φ'`, with no hypotheses on
either,

`fiberAvgTop μG hN (fun z => (Real.exp
    (-(halfActionP ρ β z)) : ℂ) * (posGaugeAvg μG f) z
    * φ' (tauBot hN z))`
`= fiberAvgTop μG hN (fun z => (Real.exp
    (-(halfActionP ρ β z)) : ℂ)
    * (mirrorGaugeAvg μG f) z * φ' (tauBot hN z))`.

Both sides carry the folded weight at the same point,
so the identity is the twirl equality of §3 composed
with a common multiplier; P3's own prefix carries no
`4 ≤ N` on this input and none is needed here. -/
theorem fiberAvgTop_dressed_folded_cross_proved
    (hN : Even N) (β : ℝ)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (φ' : (LayerLink N → G) → ℂ) :
    fiberAvgTop μG hN
        (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
          * (posGaugeAvg μG f) z * φ' (tauBot hN z))
      = fiberAvgTop μG hN
        (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
          * (mirrorGaugeAvg μG f) z * φ' (tauBot hN z)) := by
  rw [mirrorGaugeAvg_eq_posGaugeAvg]

omit [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG] in
/-- **Corollary (the engine's unfolded byproduct).**
The unfolded cross identity `hCross`, in exactly the
form item 6's marginal pairing P2 takes as its
`hCross` hypothesis: the same twirl equality with no
folded weight. R2a's brick proper — recorded here
only because the engine of §2–§3 proves it verbatim;
its landing and ceremony are the parent's to
coordinate with the R2a lane. -/
theorem fiberAvgTop_dressed_marginal_cross_proved
    (hN : Even N)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (φ' : (LayerLink N → G) → ℂ) :
    fiberAvgTop μG hN
        (fun z => (posGaugeAvg μG f) z * φ' (tauBot hN z))
      = fiberAvgTop μG hN
        (fun z => (mirrorGaugeAvg μG f) z * φ' (tauBot hN z)) := by
  rw [mirrorGaugeAvg_eq_posGaugeAvg]

end Span3SeatSchurGateW3CrossFold

end ThetLogos
