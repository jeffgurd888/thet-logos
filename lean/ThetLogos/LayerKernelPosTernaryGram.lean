/-
# Brick TM-3 — Gram assembly + the ternary seat headline
(Ternary Magnetism chain, brick 4; TM-0 gate PASSED, TM-1/TM-2 shipped)

Commission: Jeff's TM chain commission (2026-11-05, "do it"), executing
TM-3 from the priced menu in
`~/workspace/your_files/ternary-magnetism-scoping-2026-11-05.md` (§7,
with §2.3 Step 5), fired after TM-2 integrated and shipped (census
13,589 strict / 507 modules).

**Scope — exactly this brick.**  The Gram assembly of TM-2's closed
form at the ZMod 3 character seat and the headline

  `layerKernelPos_ternary_seat : LayerKernelPos seatμ₃ seatρ₃ β`
  at `N = 2` for all `β ≥ 0`,

mirroring the binary seat's `layerKernelPos_seat`
(`LayerKernelPosSeatProbe.lean`): the `LayerKernelPos` pairing is a
positive scalar times `∑_ε w_ε ‖W_ε‖²` over the divergence-free
patterns, with `W_ε = ∑_u A_ε(u) F(u)` the pattern observation and
`w_ε ≥ 0` for `β ≥ 0` (`patternWeight₃_nonneg`, banked in TM-2 for
exactly this).  Gauge invariance is never consumed.

**NOT in this brick** (later bricks, fired separately): TM-4 (the
FACT-analog decision at the ternary seat — the gate already shows
the excess `K(1,1) − a₃²⁴ > 0`, T2).

**Kill armed: K-TM-SEAT** — a negative pairing witness at the seat
would mean the ternary seat's `LayerKernelPos` is *false*; priced
in, in the K-LKP-AB pattern: the kill is a result at full rank, and
the seat's claim shrinks to whatever survives.

NO CLAIM; dials 0/4.  Magnetism grade (scoping §2.2): ternary
magnetism in the clock/Potts sense only.
-/

import ThetLogos.LayerKernelPos
import ThetLogos.LayerKernelPosTernaryFilter

open MeasureTheory Finset
open scoped ENNReal

namespace ThetLogos

/-- The pattern observation at the ternary seat:
`W_ε = ∑_u A_ε(u) · F(u)` — the Gram vector of the assembly
(the ternary analog of the binary seat's `Z_S`). -/
noncomputable def patternObs₃ (ε : LayerColumn 2 → ZMod 3)
    (F : (LayerLink 2 → Multiplicative (ZMod 3)) → ℂ) : ℂ :=
  ∑ u, patternConfig₃ ε u * F u

/-- The conjugate of a pattern observation separates as the sum of
the conjugated summands: `conj(W_ε) = ∑_u conj(F u) · conj(A_ε(u))`. -/
theorem star_patternObs₃ (ε : LayerColumn 2 → ZMod 3)
    (F : (LayerLink 2 → Multiplicative (ZMod 3)) → ℂ) :
    (starRingEnd ℂ) (patternObs₃ ε F)
      = ∑ u, (starRingEnd ℂ) (F u) * star (patternConfig₃ ε u) := by
  rw [patternObs₃, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_mul, starRingEnd_apply, starRingEnd_apply]
  exact mul_comm _ _

/-- The `LayerKernelPos` pairing at the ternary seat, as a scaled
double sum over configurations (the finite-seat integral
`seatIntegralPi₃` applied twice). -/
theorem ternary_pairing_sum (β : ℝ)
    (F : (LayerLink 2 → Multiplicative (ZMod 3)) → ℂ) :
    (∫ u, ∫ u', (starRingEnd ℂ) (F u)
        * layerKernel seatμ₃ seatρ₃ β u u' * F u'
        ∂(Measure.pi fun _ : LayerLink 2 => seatμ₃)
        ∂(Measure.pi fun _ : LayerLink 2 => seatμ₃))
      = ((Fintype.card (LayerLink 2 → Multiplicative (ZMod 3))
          : ℝ)⁻¹)
        • ∑ u, (((Fintype.card (LayerLink 2
            → Multiplicative (ZMod 3)) : ℝ)⁻¹)
          • ∑ u', (starRingEnd ℂ) (F u)
              * layerKernel seatμ₃ seatρ₃ β u u' * F u') := by
  rw [seatIntegralPi₃]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  exact seatIntegralPi₃ _

/-- **Term factorization.**  One pairing summand under the closed
form: the kernel's pattern sum distributes into per-pattern Gram
terms `w_ε · (conj(F u) · conj(A_ε(u))) · (A_ε(u') · F u')`. -/
theorem ternary_gram_term (β : ℝ)
    (F : (LayerLink 2 → Multiplicative (ZMod 3)) → ℂ)
    (u u' : LayerLink 2 → Multiplicative (ZMod 3)) :
    (starRingEnd ℂ) (F u)
        * layerKernel seatμ₃ seatρ₃ β u u' * F u'
      = ∑ ε ∈ Finset.univ.filter patternSurvives₃,
          ((patternWeight₃ ε β : ℂ))
          * ((starRingEnd ℂ) (F u) * star (patternConfig₃ ε u))
          * (patternConfig₃ ε u' * F u') := by
  rw [layerKernel_ternary_closed]
  unfold layerKernel_ternary
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ε _ => ?_
  ring

/-- The triple-sum swap over configurations and surviving patterns
(the `hswap` step of the binary assembly, at the pattern filter). -/
theorem ternary_gram_swap
    (g : (LayerLink 2 → Multiplicative (ZMod 3))
      → (LayerLink 2 → Multiplicative (ZMod 3))
      → (LayerColumn 2 → ZMod 3) → ℂ) :
    (∑ u, ∑ u', ∑ ε ∈ Finset.univ.filter patternSurvives₃, g u u' ε)
      = ∑ ε ∈ Finset.univ.filter patternSurvives₃,
          ∑ u, ∑ u', g u u' ε := by
  calc (∑ u, ∑ u', ∑ ε ∈ Finset.univ.filter patternSurvives₃,
        g u u' ε)
      = ∑ u, ∑ ε ∈ Finset.univ.filter patternSurvives₃,
          ∑ u', g u u' ε :=
        Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ ε ∈ Finset.univ.filter patternSurvives₃,
          ∑ u, ∑ u', g u u' ε :=
        Finset.sum_comm

/-- **Pattern factorization.**  A pattern's double sum separates
into the weight times the Gram product `conj(W_ε) · W_ε`. -/
theorem ternary_gram_factor (β : ℝ)
    (F : (LayerLink 2 → Multiplicative (ZMod 3)) → ℂ)
    (ε : LayerColumn 2 → ZMod 3) :
    (∑ u, ∑ u',
        ((patternWeight₃ ε β : ℂ))
          * ((starRingEnd ℂ) (F u) * star (patternConfig₃ ε u))
          * (patternConfig₃ ε u' * F u'))
      = ((patternWeight₃ ε β : ℂ))
          * ((starRingEnd ℂ) (patternObs₃ ε F)
            * patternObs₃ ε F) := by
  calc (∑ u, ∑ u',
        ((patternWeight₃ ε β : ℂ))
          * ((starRingEnd ℂ) (F u) * star (patternConfig₃ ε u))
          * (patternConfig₃ ε u' * F u'))
      = ∑ u, (((patternWeight₃ ε β : ℂ))
            * ((starRingEnd ℂ) (F u) * star (patternConfig₃ ε u)))
          * (∑ u', patternConfig₃ ε u' * F u') := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
    _ = ((patternWeight₃ ε β : ℂ))
          * ((∑ u, (starRingEnd ℂ) (F u)
              * star (patternConfig₃ ε u))
            * (∑ u', patternConfig₃ ε u' * F u')) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, mul_assoc]
    _ = ((patternWeight₃ ε β : ℂ))
          * ((starRingEnd ℂ) (patternObs₃ ε F)
            * patternObs₃ ε F) := by
        rw [star_patternObs₃, patternObs₃]

/-- A pattern's Gram product as a nonnegative real cast:
`w_ε · (conj(W_ε) · W_ε) = ↑(w_ε · ‖W_ε‖²)`. -/
theorem ternary_gram_weight_normSq (β : ℝ)
    (F : (LayerLink 2 → Multiplicative (ZMod 3)) → ℂ)
    (ε : LayerColumn 2 → ZMod 3) :
    ((patternWeight₃ ε β : ℂ))
        * ((starRingEnd ℂ) (patternObs₃ ε F) * patternObs₃ ε F)
      = ((patternWeight₃ ε β * ‖patternObs₃ ε F‖ ^ 2 : ℝ) : ℂ) := by
  have hcc : (starRingEnd ℂ) (patternObs₃ ε F) * patternObs₃ ε F
      = ((‖patternObs₃ ε F‖ ^ 2 : ℝ) : ℂ) :=
    (mul_comm _ _).trans
      ((RCLike.mul_conj _).trans (Complex.ofReal_pow _ _).symm)
  rw [hcc, ← Complex.ofReal_mul]

/-- **The ternary pairing in Gram form.**  The `LayerKernelPos`
pairing at the ternary seat is a positive scalar times
`∑_ε w_ε ‖W_ε‖²` over the divergence-free patterns, as a real cast. -/
theorem ternary_pairing_gram (β : ℝ)
    (F : (LayerLink 2 → Multiplicative (ZMod 3)) → ℂ) :
    (∫ u, ∫ u', (starRingEnd ℂ) (F u)
        * layerKernel seatμ₃ seatρ₃ β u u' * F u'
        ∂(Measure.pi fun _ : LayerLink 2 => seatμ₃)
        ∂(Measure.pi fun _ : LayerLink 2 => seatμ₃))
      = (((Fintype.card (LayerLink 2 → Multiplicative (ZMod 3))
            : ℝ)⁻¹
          * ((Fintype.card (LayerLink 2 → Multiplicative (ZMod 3))
              : ℝ)⁻¹
            * ∑ ε ∈ Finset.univ.filter patternSurvives₃,
                patternWeight₃ ε β * ‖patternObs₃ ε F‖ ^ 2)
          : ℝ) : ℂ) := by
  calc (∫ u, ∫ u', (starRingEnd ℂ) (F u)
        * layerKernel seatμ₃ seatρ₃ β u u' * F u'
        ∂(Measure.pi fun _ : LayerLink 2 => seatμ₃)
        ∂(Measure.pi fun _ : LayerLink 2 => seatμ₃))
      = ((Fintype.card (LayerLink 2 → Multiplicative (ZMod 3))
            : ℝ)⁻¹)
          • ∑ u, (((Fintype.card (LayerLink 2
              → Multiplicative (ZMod 3)) : ℝ)⁻¹)
            • ∑ u', (starRingEnd ℂ) (F u)
                * layerKernel seatμ₃ seatρ₃ β u u' * F u') :=
        ternary_pairing_sum β F
    _ = (((Fintype.card (LayerLink 2 → Multiplicative (ZMod 3))
              : ℝ)⁻¹ : ℂ))
          * ((((Fintype.card (LayerLink 2
              → Multiplicative (ZMod 3)) : ℝ)⁻¹ : ℂ))
            * ∑ u, ∑ u', (starRingEnd ℂ) (F u)
                * layerKernel seatμ₃ seatρ₃ β u u' * F u') := by
        have e1 : ∀ x : ℂ,
            ((Fintype.card (LayerLink 2 → Multiplicative (ZMod 3))
              : ℝ)⁻¹) • x
            = (((Fintype.card (LayerLink 2
                → Multiplicative (ZMod 3)) : ℝ)⁻¹ : ℂ)) * x := by
          intro x
          rw [Complex.real_smul, Complex.ofReal_inv]
        rw [e1]
        congr 1
        rw [← Finset.smul_sum, e1]
    _ = (((Fintype.card (LayerLink 2 → Multiplicative (ZMod 3))
              : ℝ)⁻¹ : ℂ))
          * ((((Fintype.card (LayerLink 2
              → Multiplicative (ZMod 3)) : ℝ)⁻¹ : ℂ))
            * ∑ ε ∈ Finset.univ.filter patternSurvives₃,
                ((patternWeight₃ ε β : ℂ))
                  * ((starRingEnd ℂ) (patternObs₃ ε F)
                    * patternObs₃ ε F)) := by
        congr 1
        congr 1
        rw [Finset.sum_congr rfl fun u _ =>
          Finset.sum_congr rfl fun u' _ => ternary_gram_term β F u u',
          ternary_gram_swap]
        refine Finset.sum_congr rfl fun ε _ => ?_
        exact ternary_gram_factor β F ε
    _ = (((Fintype.card (LayerLink 2 → Multiplicative (ZMod 3))
            : ℝ)⁻¹
          * ((Fintype.card (LayerLink 2 → Multiplicative (ZMod 3))
              : ℝ)⁻¹
            * ∑ ε ∈ Finset.univ.filter patternSurvives₃,
                patternWeight₃ ε β * ‖patternObs₃ ε F‖ ^ 2)
          : ℝ) : ℂ) := by
        have hper : ∀ ε ∈ Finset.univ.filter patternSurvives₃,
            ((patternWeight₃ ε β : ℂ))
              * ((starRingEnd ℂ) (patternObs₃ ε F)
                * patternObs₃ ε F)
            = ((patternWeight₃ ε β * ‖patternObs₃ ε F‖ ^ 2
                : ℝ) : ℂ) :=
          fun ε _ => ternary_gram_weight_normSq β F ε
        rw [Finset.sum_congr rfl hper, ← Complex.ofReal_inv,
          ← Complex.ofReal_sum, ← Complex.ofReal_mul,
          ← Complex.ofReal_mul]

/-- **TM-3 headline — PSD at the ternary seat; K-TM-SEAT does not
fire.**  At the ZMod 3 character seat, `LayerKernelPos` holds for
all `β ≥ 0`: with TM-2's closed form, the pairing is (a positive
scalar times) a sum over divergence-free patterns of nonnegative
weights `w_ε = a₃^(24−|supp ε|) b₃^|supp ε|` times `‖W_ε‖²` — a
Gram sum.  Gauge invariance is not consumed.  This is a seat
result: it proves `LayerKernelPos` at this one finite seat, not in
general. -/
theorem layerKernelPos_ternary_seat {β : ℝ} (hβ : 0 ≤ β) :
    LayerKernelPos (N := 2) seatμ₃ seatρ₃ β := by
  intro F _hF
  rw [ternary_pairing_gram, Complex.ofReal_re]
  have hMnn : (0 : ℝ)
      ≤ ((Fintype.card (LayerLink 2 → Multiplicative (ZMod 3))
        : ℝ))⁻¹ :=
    inv_nonneg.mpr (by positivity)
  refine mul_nonneg hMnn (mul_nonneg hMnn ?_)
  refine Finset.sum_nonneg fun ε _ => ?_
  exact mul_nonneg (patternWeight₃_nonneg ε hβ)
    (pow_nonneg (norm_nonneg _) _)

end ThetLogos
