import Mathlib.Tactic
import ThetLogos.WaveFamilyWeld
import ThetLogos.MaxwellQuadSpectrum

namespace ThetLogos

open scoped InnerProductSpace
open Finset

/-!
# ThetLogos.WaveModeIdentification - GR-PROP-2: the mode identification

**Working label only.** The module name
`WaveModeIdentification` and the line name GR-PROP are
working labels; Jeff names.

**Status: GR-PROP-2 landing brick, PARTIAL at the named
completeness seam (stated exactly below). NO CLAIM.
Dial 2 = 0 under every outcome of this line, including
total success. No gravity object is defined, constructed,
or asserted to exist.**

Governing texts: the GR-PROP-0 pin `WaveFamilyPost.lean`
(its registered names govern: `waveFamily`, `ModeFreq`,
`FreqShift`), GR-PROP-1 `WaveFamilyWeld.lean`
(`linkWaveFamily`, `maxwellOpCE`, `maxwellOpC_ofReal`,
`modeFreq_linkWaveFamily`), MAX-3
`MaxwellQuadSpectrum.lean` landed PARTIAL (its clauses
1, 2, 3, 5 discharged: `cosMode_eigen`, `sinMode_eigen`,
`transverse_eig_eq`, `hasEigenvalue_zero`, `clause1`;
clause 4, the spectral gap lower bound over the whole
spectrum, is OPEN), and the scoping memo
`routeb-general-scratch/scoping-gravity-vocabulary-2026-10-31.md`
sections 5-6.

## What is discharged here

1. **Identification, existence direction.** MAX-3's named
   Fourier modes - the transverse cosine and sine link
   modes `cosMode K A` / `sinMode K A` of the real
   operator `maxwellOp N`, and the longitudinal
   pure-gauge modes `gaugeAngle phi` - complexify, via
   GR-PROP-1's `modeVecC` embedding below, to modes of
   the complexified operator `maxwellOpCE N` in the pin's
   `ModeFreq` vocabulary, at their named frequencies, and
   are preserved by `linkWaveFamily` at those frequencies
   (the family acts on them by the named eigenphase).
2. **Frequency of mode k.** At spatial momentum
   `k : Fin 3 -> ZMod N` (extended momentum
   `Fin.cons 0 k`, transverse polarization `A`), the
   frequency of the cosine and sine modes is SUPPLIED and
   NAMED as `maxwellTransverseEig N k` - the M5
   eigenvalue `4 * sum_i sin^2 (pi * k_i / N)` in its
   registered form - never existentially quantified
   (K-GR-VAC discipline).
3. **The longitudinal sector is the stationary sector.**
   The pure-gauge (longitudinal) modes have frequency 0
   as modes of `maxwellOpCE N`, and the wave family fixes
   them exactly: `linkWaveFamily N t (gaugeModeC phi)
   = gaugeModeC phi` for every `t`. This is stated as
   finite eigenvalue arithmetic only (the phase at
   frequency 0 is `evolPhase 0 t = 1`); it is the finite
   shadow registered in the memo, printed as arithmetic,
   never as physics.

## The named completeness seam (PARTIAL, stated exactly)

The "exactly" direction of the identification - EVERY
mode of `maxwellOpCE N` is one of the named Fourier
modes above - is NOT discharged in this brick and is NOT
asserted anywhere in it. The landed MAX-3 clauses 1, 2,
3, 5 name and prove the Fourier modes and their
eigenvalues; they do not provide a completeness or
dimension count over the full constructed family (for
example cross-momentum linear independence of all the
constructed modes plus a dimension count of the link
space), which is what an exhaustion theorem would need.
This brick therefore lands PARTIAL at that seam: the
existence, frequency, preservation, and longitudinal
stationarity directions above, with completeness named
open. In particular, MAX-3's clause 4 (every eigenvalue
is 0 or at least the gap value) is NOT consumed, implied,
or assumed anywhere in this brick; no proof here reaches
for "no other eigenvalues exist".

## Fences (binding, from the pin and the memo)

- Frequencies are named/supplied only; no instance of
  `PoseObjBFreqShadow` is asserted anywhere in this
  brick (that decision is GR-PROP-3's).
- Mode/frequency language here is eigenvalue bookkeeping
  over a finite operator; no propagation-in-spacetime,
  dispersion-as-physics, bending, redshift, or gravity
  sentence may be drawn from it (K-GR-SMUG / K-GR-LAUNDER).
  The finite dispersion value `maxwellTransverseEig N k`
  is labeled finite wherever stated.
- Ceiling on the face: Dial 2 unmoved by anything in
  this brick; NO CLAIM.
-/

section ComplexifiedModes

variable {N : ℕ} [NeZero N]

/-- **The complexification embedding of a real link
angle.** A real link angle `theta : linkAngle N`, read
componentwise in `C` and transported to the Euclidean
link space by GR-PROP-1's `linkEquivC`. This is the seat
map under which MAX-3's real Fourier modes become modes
of the complexified operator `maxwellOpCE N`. -/
noncomputable def modeVecC (θ : linkAngle N) :
    EuclideanSpace ℂ (LayerLink N) :=
  (linkEquivC N).symm (fun ℓ => ((θ ℓ : ℂ)))

/-- **Read-back under the identification.** Reading a
complexified real angle back through `linkEquivC`
recovers the componentwise cast. -/
theorem equiv_modeVecC (θ : linkAngle N) :
    linkEquivC N (modeVecC θ) = fun ℓ => ((θ ℓ : ℂ)) :=
  LinearEquiv.apply_symm_apply _ _

/-- **Component form of the complexification embedding**:
at a link, the complexified angle is the real angle,
cast. -/
theorem modeVecC_apply (θ : linkAngle N) (ℓ : LayerLink N) :
    modeVecC θ ℓ = ((θ ℓ : ℂ)) := by
  calc modeVecC θ ℓ
      = linkEquivC N (modeVecC θ) ℓ :=
        (linkEquivC_apply _ _).symm
    _ = ((θ ℓ : ℂ)) := congrFun (equiv_modeVecC θ) ℓ

/-- **The complexification embedding preserves
nonvanishing**: a nonzero real angle complexifies to a
nonzero vector of the complexified link space. -/
theorem modeVecC_ne_zero {θ : linkAngle N} (hθ : θ ≠ 0) :
    modeVecC θ ≠ 0 := by
  intro h0
  apply hθ
  funext ℓ
  have hℓ : modeVecC θ ℓ = 0 := by
    rw [h0]
    rfl
  rw [modeVecC_apply] at hℓ
  exact Complex.ofReal_eq_zero.mp hℓ

/-- **Eigen-transport across the complexification.** If
a real link angle `theta` is an eigenvector of the real
operator `maxwellOp N` at the real eigenvalue `lam`,
then its complexification is an eigenvector of the
complexified operator `maxwellOpCE N` at the cast
eigenvalue `(lam : C)`. Proved by transporting through
`linkEquivC` and consuming GR-PROP-1's
`maxwellOpC_ofReal_apply` (the complexification extends
the real operator exactly) together with MAX-3's real
eigen-equation, supplied as the hypothesis. -/
theorem maxwellOpCE_modeVecC {θ : linkAngle N} {lam : ℝ}
    (h : maxwellOp N θ = lam • θ) :
    maxwellOpCE N (modeVecC θ) = ((lam : ℂ)) • modeVecC θ := by
  apply (linkEquivC N).injective
  rw [equiv_maxwellOpCE, equiv_modeVecC, map_smul,
    equiv_modeVecC]
  funext ℓ
  rw [maxwellOpC_ofReal_apply, h]
  simp [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]

/-- **A real mode is a complexified mode, in the pin's
`ModeFreq` vocabulary.** If `theta` is a nonzero real
eigenvector of `maxwellOp N` at `lam`, its
complexification is a `ModeFreq` mode of `maxwellOpCE N`
at the named frequency `(lam : C)`. The mode and the
frequency are supplied, never asserted to exist by this
statement. This single transport covers every real mode
MAX-3 names, including the clause-2 witness pairs. -/
theorem modeFreq_modeVecC {θ : linkAngle N} {lam : ℝ}
    (hθ : θ ≠ 0) (h : maxwellOp N θ = lam • θ) :
    ModeFreq (maxwellOpCE N) (modeVecC θ) ((lam : ℂ)) :=
  ⟨modeVecC_ne_zero hθ, maxwellOpCE_modeVecC h⟩

/-- **Phase action on a complexified real mode.** If the
complexification of `theta` is a mode of `maxwellOpCE N`
at the real frequency `lam` (cast to `C`), the link wave
family acts on it by the named eigenphase
`evolPhase lam t`, by GR-PROP-1's
`linkWaveFamily_apply_of_modeFreq`. The mode stays at
the same frequency; nothing is shifted. -/
theorem modeVecC_phase (t : ℝ) {θ : linkAngle N} {lam : ℝ}
    (hm : ModeFreq (maxwellOpCE N) (modeVecC θ) ((lam : ℂ))) :
    linkWaveFamily N t (modeVecC θ)
      = evolPhase lam t • modeVecC θ :=
  linkWaveFamily_apply_of_modeFreq t hm

end ComplexifiedModes

section FourierModesComplexified

variable {N : ℕ} [NeZero N]

/-- **The complexified cosine Fourier mode**: MAX-3's
real cosine link mode `cosMode K A` at momentum profile
`K` and polarization `A`, complexified by `modeVecC`. -/
noncomputable def cosModeC (K : Fin 4 → ZMod N)
    (A : Fin 4 → ℝ) : EuclideanSpace ℂ (LayerLink N) :=
  modeVecC (cosMode K A)

/-- **The complexified sine Fourier mode**: MAX-3's real
sine link mode `sinMode K A`, complexified. -/
noncomputable def sinModeC (K : Fin 4 → ZMod N)
    (A : Fin 4 → ℝ) : EuclideanSpace ℂ (LayerLink N) :=
  modeVecC (sinMode K A)

/-- **The complexified longitudinal (pure-gauge) mode**:
MAX-3's / MAX-2's real gauge angle `gaugeAngle phi` for
a site potential `phi`, complexified. The longitudinal
sector of this brick is exactly these modes. -/
noncomputable def gaugeModeC (φ : LayerSite N → ℝ) :
    EuclideanSpace ℂ (LayerLink N) :=
  modeVecC (gaugeAngle φ)

/-- **The cosine mode is an eigenvector of the
complexified operator**, at the cast of MAX-3's computed
transverse value `4 * sum_mu (modeSin K mu)^2`, whenever
the polarization is transverse (`K 0 = 0` and
`sum_nu A nu * modeSin K nu = 0`). Direct transport of
MAX-3's `cosMode_eigen`. FINITE statement. -/
theorem cosModeC_eigen (hN : 2 ≤ N) (K : Fin 4 → ZMod N)
    (A : Fin 4 → ℝ) (hK0 : K 0 = 0)
    (htrans : ∑ ν, A ν * modeSin K ν = 0) :
    maxwellOpCE N (cosModeC K A)
      = (((4 * ∑ μ, (modeSin K μ)^2 : ℝ) : ℂ))
        • cosModeC K A :=
  maxwellOpCE_modeVecC (cosMode_eigen hN K A hK0 htrans)

/-- **The sine mode is an eigenvector of the
complexified operator**, at the same transverse value,
under the same transversality condition. Direct
transport of MAX-3's `sinMode_eigen`. FINITE
statement. -/
theorem sinModeC_eigen (hN : 2 ≤ N) (K : Fin 4 → ZMod N)
    (A : Fin 4 → ℝ) (hK0 : K 0 = 0)
    (htrans : ∑ ν, A ν * modeSin K ν = 0) :
    maxwellOpCE N (sinModeC K A)
      = (((4 * ∑ μ, (modeSin K μ)^2 : ℝ) : ℂ))
        • sinModeC K A :=
  maxwellOpCE_modeVecC (sinMode_eigen hN K A hK0 htrans)

/-- **HEADLINE (frequency of mode k, cosine).** At
spatial momentum `k : Fin 3 -> ZMod N`, the complexified
cosine mode at the extended momentum `Fin.cons 0 k` and
any transverse polarization `A` is an eigenvector of
`maxwellOpCE N` at the NAMED frequency
`(maxwellTransverseEig N k : C)` - the M5 eigenvalue,
supplied and named, via MAX-3's `transverse_eig_eq`.
FINITE statement: the frequency is a property of the
chosen finite operator at spacing 1. -/
theorem cosModeC_eigen_spatial (hN : 2 ≤ N)
    (k : Fin 3 → ZMod N) (A : Fin 4 → ℝ)
    (htrans : ∑ ν, A ν
      * modeSin (Fin.cons (0 : ZMod N) k) ν = 0) :
    maxwellOpCE N (cosModeC (Fin.cons (0 : ZMod N) k) A)
      = ((maxwellTransverseEig N k : ℂ))
        • cosModeC (Fin.cons (0 : ZMod N) k) A := by
  have h := cosModeC_eigen hN (Fin.cons (0 : ZMod N) k) A
    (by rfl) htrans
  rwa [transverse_eig_eq] at h

/-- **HEADLINE (frequency of mode k, sine).** The sine
form of `cosModeC_eigen_spatial`: the complexified sine
mode at spatial momentum `k` carries the NAMED frequency
`(maxwellTransverseEig N k : C)`. FINITE statement. -/
theorem sinModeC_eigen_spatial (hN : 2 ≤ N)
    (k : Fin 3 → ZMod N) (A : Fin 4 → ℝ)
    (htrans : ∑ ν, A ν
      * modeSin (Fin.cons (0 : ZMod N) k) ν = 0) :
    maxwellOpCE N (sinModeC (Fin.cons (0 : ZMod N) k) A)
      = ((maxwellTransverseEig N k : ℂ))
        • sinModeC (Fin.cons (0 : ZMod N) k) A := by
  have h := sinModeC_eigen hN (Fin.cons (0 : ZMod N) k) A
    (by rfl) htrans
  rwa [transverse_eig_eq] at h

/-- **HEADLINE (the cosine mode is a `ModeFreq` mode at
its named frequency).** At spatial momentum `k`, a
nonzero complexified cosine mode with transverse
polarization `A` is a mode of `maxwellOpCE N` in the
pin's `ModeFreq` vocabulary at the SUPPLIED, NAMED
frequency `(maxwellTransverseEig N k : C)`. Nonvanishing
of the named mode is supplied as a hypothesis (it holds
for MAX-3's constructed polarizations, e.g. `modePol`,
by MAX-3's clause-1/clause-2 arguments); the frequency
is never existentially quantified. -/
theorem cosModeC_modeFreq_spatial (hN : 2 ≤ N)
    (k : Fin 3 → ZMod N) (A : Fin 4 → ℝ)
    (htrans : ∑ ν, A ν
      * modeSin (Fin.cons (0 : ZMod N) k) ν = 0)
    (hne : cosMode (Fin.cons (0 : ZMod N) k) A ≠ 0) :
    ModeFreq (maxwellOpCE N)
      (cosModeC (Fin.cons (0 : ZMod N) k) A)
      ((maxwellTransverseEig N k : ℂ)) :=
  ⟨modeVecC_ne_zero hne,
    cosModeC_eigen_spatial hN k A htrans⟩

/-- **HEADLINE (the sine mode is a `ModeFreq` mode at
its named frequency).** The sine form of
`cosModeC_modeFreq_spatial`. -/
theorem sinModeC_modeFreq_spatial (hN : 2 ≤ N)
    (k : Fin 3 → ZMod N) (A : Fin 4 → ℝ)
    (htrans : ∑ ν, A ν
      * modeSin (Fin.cons (0 : ZMod N) k) ν = 0)
    (hne : sinMode (Fin.cons (0 : ZMod N) k) A ≠ 0) :
    ModeFreq (maxwellOpCE N)
      (sinModeC (Fin.cons (0 : ZMod N) k) A)
      ((maxwellTransverseEig N k : ℂ)) :=
  ⟨modeVecC_ne_zero hne,
    sinModeC_eigen_spatial hN k A htrans⟩

/-- **Preservation under the wave family (cosine).** The
link wave family carries the named cosine mode at
momentum `k` to a mode of the same operator at the SAME
named frequency `(maxwellTransverseEig N k : C)`, by
GR-PROP-1's `modeFreq_linkWaveFamily`. No frequency is
shifted by the family. -/
theorem cosModeC_preserved_spatial (hN : 2 ≤ N) (t : ℝ)
    (k : Fin 3 → ZMod N) (A : Fin 4 → ℝ)
    (htrans : ∑ ν, A ν
      * modeSin (Fin.cons (0 : ZMod N) k) ν = 0)
    (hne : cosMode (Fin.cons (0 : ZMod N) k) A ≠ 0) :
    ModeFreq (maxwellOpCE N)
      (linkWaveFamily N t
        (cosModeC (Fin.cons (0 : ZMod N) k) A))
      ((maxwellTransverseEig N k : ℂ)) :=
  modeFreq_linkWaveFamily t
    (cosModeC_modeFreq_spatial hN k A htrans hne)

/-- **Preservation under the wave family (sine).** The
sine form of `cosModeC_preserved_spatial`. -/
theorem sinModeC_preserved_spatial (hN : 2 ≤ N) (t : ℝ)
    (k : Fin 3 → ZMod N) (A : Fin 4 → ℝ)
    (htrans : ∑ ν, A ν
      * modeSin (Fin.cons (0 : ZMod N) k) ν = 0)
    (hne : sinMode (Fin.cons (0 : ZMod N) k) A ≠ 0) :
    ModeFreq (maxwellOpCE N)
      (linkWaveFamily N t
        (sinModeC (Fin.cons (0 : ZMod N) k) A))
      ((maxwellTransverseEig N k : ℂ)) :=
  modeFreq_linkWaveFamily t
    (sinModeC_modeFreq_spatial hN k A htrans hne)

/-- **Phase action at the named frequency (cosine).**
On the named cosine mode at momentum `k`, the link wave
family acts by the eigenphase at its named frequency:
`linkWaveFamily N t (cosModeC ...) = evolPhase
(maxwellTransverseEig N k) t * cosModeC ...` (scalar
action). By GR-PROP-1's
`linkWaveFamily_apply_of_modeFreq`. -/
theorem cosModeC_phase_spatial (hN : 2 ≤ N) (t : ℝ)
    (k : Fin 3 → ZMod N) (A : Fin 4 → ℝ)
    (htrans : ∑ ν, A ν
      * modeSin (Fin.cons (0 : ZMod N) k) ν = 0)
    (hne : cosMode (Fin.cons (0 : ZMod N) k) A ≠ 0) :
    linkWaveFamily N t
        (cosModeC (Fin.cons (0 : ZMod N) k) A)
      = evolPhase (maxwellTransverseEig N k) t
        • cosModeC (Fin.cons (0 : ZMod N) k) A :=
  linkWaveFamily_apply_of_modeFreq t
    (cosModeC_modeFreq_spatial hN k A htrans hne)

/-- **Phase action at the named frequency (sine).** The
sine form of `cosModeC_phase_spatial`. -/
theorem sinModeC_phase_spatial (hN : 2 ≤ N) (t : ℝ)
    (k : Fin 3 → ZMod N) (A : Fin 4 → ℝ)
    (htrans : ∑ ν, A ν
      * modeSin (Fin.cons (0 : ZMod N) k) ν = 0)
    (hne : sinMode (Fin.cons (0 : ZMod N) k) A ≠ 0) :
    linkWaveFamily N t
        (sinModeC (Fin.cons (0 : ZMod N) k) A)
      = evolPhase (maxwellTransverseEig N k) t
        • sinModeC (Fin.cons (0 : ZMod N) k) A :=
  linkWaveFamily_apply_of_modeFreq t
    (sinModeC_modeFreq_spatial hN k A htrans hne)

/-- **Occurrence corollary.** At every spatial momentum
`k` and general Even `N`, the named frequency
`maxwellTransverseEig N k` DOES occur as the frequency
of a `ModeFreq` mode of `maxwellOpCE N`: MAX-3's
clause 1 (`clause1`, clauses 1/3/5 part) supplies a real
eigenvector at that eigenvalue, and `modeFreq_modeVecC`
complexifies it. This asserts occurrence of the named
frequencies only; it asserts NO completeness - it does
not say these are all the modes (the named seam on this
module's face). -/
theorem exists_modeFreqC_transverse (hN : Even N)
    (k : Fin 3 → ZMod N) :
    ∃ v : EuclideanSpace ℂ (LayerLink N),
      ModeFreq (maxwellOpCE N) v
        ((maxwellTransverseEig N k : ℂ)) := by
  obtain ⟨θ, hvec⟩ :=
    (clause1 hN k).1.exists_hasEigenvector
  exact ⟨modeVecC θ,
    modeFreq_modeVecC hvec.2 hvec.apply_eq_smul⟩

end FourierModesComplexified

section LongitudinalSector

variable {N : ℕ} [NeZero N]

/-- **The longitudinal modes sit at frequency 0
(eigen-equation).** For every site potential `phi`, the
complexified pure-gauge mode `gaugeModeC phi` is an
eigenvector of `maxwellOpCE N` at eigenvalue `0`:
transport of MAX-2's `maxwellOp_gaugeAngle` (the real
gauge modes are in the kernel of `maxwellOp N`; MAX-3's
clause-1 zero half, `hasEigenvalue_zero`, is the same
sector). FINITE arithmetic. -/
theorem gaugeModeC_eigen_zero (φ : LayerSite N → ℝ) :
    maxwellOpCE N (gaugeModeC φ)
      = (0 : ℂ) • gaugeModeC φ := by
  have h : maxwellOp N (gaugeAngle φ)
      = (0 : ℝ) • gaugeAngle φ := by
    rw [maxwellOp_gaugeAngle, zero_smul]
  have h2 := maxwellOpCE_modeVecC h
  have hcast : (((0 : ℝ) : ℂ)) = (0 : ℂ) := Complex.ofReal_zero
  rw [hcast] at h2
  exact h2

/-- **The longitudinal modes are `ModeFreq` modes at
frequency 0.** A nonzero complexified pure-gauge mode
is a mode of `maxwellOpCE N` in the pin's `ModeFreq`
vocabulary at the NAMED frequency `0`. Nonvanishing of
the named gauge mode is supplied as a hypothesis
(MAX-3's `hasEigenvalue_zero` exhibits a nonzero one). -/
theorem gaugeModeC_modeFreq_zero (φ : LayerSite N → ℝ)
    (hne : gaugeAngle φ ≠ 0) :
    ModeFreq (maxwellOpCE N) (gaugeModeC φ) (0 : ℂ) :=
  ⟨modeVecC_ne_zero hne, gaugeModeC_eigen_zero φ⟩

/-- **HEADLINE (the longitudinal sector is the family's
stationary sector).** For every time `t` and every site
potential `phi`, the link wave family FIXES the
complexified pure-gauge mode exactly:
`linkWaveFamily N t (gaugeModeC phi) = gaugeModeC phi`.
The proof is the phase action at frequency 0:
`evolPhase 0 t = 1`. Stated as finite eigenvalue
arithmetic only - the longitudinal sector is the
stationary sector of the family in exactly this
arithmetic sense, and in no other sense asserted here. -/
theorem gaugeModeC_stationary (t : ℝ)
    (φ : LayerSite N → ℝ) :
    linkWaveFamily N t (gaugeModeC φ) = gaugeModeC φ := by
  have hmem : gaugeModeC φ
      ∈ Module.End.eigenspace (maxwellOpCE N) (0 : ℂ) :=
    Module.End.mem_eigenspace_iff.mpr
      (gaugeModeC_eigen_zero φ)
  have h := linkWaveFamily_apply_mem_eigenspace (N := N)
    t hmem
  have hp : evolPhase ((0 : ℂ).re) t = 1 := by
    simp [evolPhase]
  rw [hp, one_smul] at h
  exact h

end LongitudinalSector

/-! ## Axiom audit

Headlines checked on exactly
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms maxwellOpCE_modeVecC
#print axioms cosModeC_eigen_spatial
#print axioms sinModeC_eigen_spatial
#print axioms cosModeC_modeFreq_spatial
#print axioms sinModeC_modeFreq_spatial
#print axioms cosModeC_preserved_spatial
#print axioms cosModeC_phase_spatial
#print axioms exists_modeFreqC_transverse
#print axioms gaugeModeC_eigen_zero
#print axioms gaugeModeC_modeFreq_zero
#print axioms gaugeModeC_stationary

end ThetLogos
