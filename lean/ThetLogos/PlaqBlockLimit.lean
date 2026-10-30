/-
# ThetLogos.PlaqBlockLimit — Brick A2-2e (RE-SCOPED):
approximant convergence and the closing statement of the
A2-2 line (Route B)

**Fences, up front.** NO CLAIM. Parts of the Clay
Yang–Mills statement closed by this module: **0**. Dials
**0/4**, unmoved. Route B scope on the face: one-plaquette
mechanism + leading square only — this brick is **NOT**
`𝒜 ⪰ 0`, **NOT** clause (a), and the block is not a factor
of `layerKernel`. The literal quotient form R1 is CERTIFIED
DEAD (probe BR1-005) and is not touched.

## The re-scope, on the face (read first)

This brick is **not** the A2-2 scoping's original A2-2e.
The original A2-2e (`scoping-a2-2-telescoping-2026-10-29`
§4) was the limit passage `K → ∞` landing (T) and (P) for
`f_β` at general `(G, ρ)` as the factor theorem; it
consumes uniform-in-`K` stage statements. A2-2d landed
PARTIAL (dossier `whitepaper/a22d-landing-2026-10-30.md`):
(T)/(P) exist at `K = 0`, the contracted form at `K = 1`,
PSD at `K = 0` only, and uniform-in-`K` is blocked by the
two seams named below. The substitution executed here is
the scoping's own stop, verbatim in substance: *"if the
limit passage fails on uniformity, the polynomial-stage
landing stands as A2-2's result, labeled PARTIAL at full
rank, and the all-β headline is not claimed. There is no
fallback wording under which a polynomial-stage result is
reported as the factor theorem."* What this module lands
is exactly what the landed scope supports:

1. **Approximant convergence (the analytic content).**
   The order-`K` approximant block `PlaqBlockApprox` and
   kernel `PlaqKernelApprox` of A2-2d converge, as
   `K → ∞`, to the true block `PlaqBlock` and kernel
   `PlaqKernel` of A2-2a — for the RAW objects (the
   definitions, built from `f_β = columnKernel` and its
   polynomial approximants `colApprox`), pointwise in the
   configurations/section data, at general `(G, ρ)`. The
   proof is the uniform bound `|Re tr ρ| ≤ d` on the group
   (hence `wordDensity ∈ [0, 2]`, §1), the resulting
   `K`-independent dominator `exp (2|β|)` per column
   factor (§2), and dominated convergence for the corner
   integrals in the tree's integral-continuity pattern
   (`tendsto_integral_of_dominated_convergence`, as in
   `LorentzContinuity`) (§§3–4). Convergence of
   definitions needs **no irreducibility and no twirls**:
   the only hypothesis on the face is the corpus's
   standing continuity hypothesis
   `hρcont : Continuous fun g => repMatrix ρ g`, used for
   measurability of the integrands. This convergence is
   exactly the input any future completion (post-TW-1,
   post-J-pattern) will consume.
2. **The transfer disposition: NON-TRANSFER, recorded in
   prose — no transfer corollary is landed.** PSD is a
   closed condition under pointwise limits, but that
   closedness has nothing to act on here: PSD is owned
   only at `K = 0`, and the `K = 0` approximant is not the
   sequence whose limit is taken in any useful sense —
   `(P)` at `K = 0` is a statement about the `K = 0`
   objects, not a limit statement, and it neither needs
   nor receives a transfer. `(T)`/`(P)` at general `K` do
   **NOT** transfer: they do not exist (uniform-in-`K` is
   blocked at the seams). The `K = 1` contracted form
   (`plaqBlockApprox_one`) does **NOT** become a statement
   about `f_β`: it is an identity about the order-`1`
   approximant, and the convergence of §4 passes the
   *objects* to their limits, not polynomial-stage
   *identities* proved by order-`≤ 2` contractions. A
   non-transfer record outranks a decorative corollary;
   none is landed.

## The closing statement of the A2-2 line (verbatim in substance)

A2-2's result is the polynomial-stage PARTIAL: A2-2a
registration; probe PASS with R1 dead; A2-2b reductions +
class invariance; A2-2c contractions at orders ≤ 2 total;
A2-2d (T)/(P) at `K = 0`, contracted form at `K = 1`, PSD
at `K = 0` — supplemented by this brick's approximant
convergence of the raw block/kernel. The all-β
factor-theorem headline — (T)/(P) for `f_β` at general
`(G, ρ)` — is **NOT CLAIMED**. The blockers are
SEAM A2-2c-HIGHER-ORDERS (triple twirls — TW-1's brick)
and SEAM A2-2d-J-PATTERNS (J-invariance collapse —
unpriced). A2-3 remains unpriced.

## The seams (all named, none edited away)

- **SEAM A2-2c-HIGHER-ORDERS** (inherited, binding):
  total degree `≥ 3` needs triple-and-higher twirls — not
  owned (TW-1's brick in the GD line). Consequence: no
  uniform-in-`K` (T)/(P); the convergence landed here is
  convergence of the raw definitions only and does not
  manufacture stage statements at any `K ≥ 1`. K-A2
  remains armed at every untested order.
- **SEAM A2-2d-J-PATTERNS** (inherited): the
  non-alternating character sign patterns of the `K = 1`
  cycle integral need entry-level J-invariance collapse
  (`C · J · Cᵀ = J`) around the whole cycle — not owned,
  unpriced. Consequence: the closed form of
  `plaqCycleIntegral`, PSD of `Ψ₁` at `K = 1`, and (T) at
  `K = 1` in factorized form remain open, and the `K = 1`
  contracted form stays an approximant statement (see the
  non-transfer record above).
-/

import ThetLogos.PlaqBlockAssembly

namespace ThetLogos

open Finset MeasureTheory Filter Topology

section WordDensityBounds

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- **The uniform bound**: `|Re tr ρ (w)| ≤ d` for every
`w` — the real part of the character is bounded by the
norm of the character (`norm_charFn_le`). This is the
bound the pack names; everything in §2 is downstream of
it. -/
theorem abs_re_trace_repMatrix_le (w : G) :
    |(Matrix.trace (repMatrix ρ w)).re| ≤ (d : ℝ) :=
  le_trans (Complex.abs_re_le_norm _) (norm_charFn_le ρ w)

/-- `wordDensity ρ w ≥ 0`: `Re tr ρ (w) ≤ d`. (The `d = 0`
case is definitional: the trace over `Fin 0` is `0` and
division by `0` is `0`, so the density is `1`.) -/
theorem wordDensity_nonneg (w : G) : 0 ≤ wordDensity ρ w := by
  unfold wordDensity
  have h1 : (Matrix.trace (repMatrix ρ w)).re ≤ (d : ℝ) :=
    re_trace_le_of_mem_unitaryGroup (repMatrix_mem ρ w)
  by_cases hd : (d : ℝ) = 0
  · have hd0 : d = 0 := by exact_mod_cast hd
    subst hd0
    simp
  · have hdpos : (0 : ℝ) < d :=
      lt_of_le_of_ne (Nat.cast_nonneg d) (Ne.symm hd)
    rw [sub_nonneg, div_le_one hdpos]
    exact h1

/-- `wordDensity ρ w ≤ 2`: `-d ≤ Re tr ρ (w)`. -/
theorem wordDensity_le_two (w : G) : wordDensity ρ w ≤ 2 := by
  unfold wordDensity
  have h2 : -(d : ℝ) ≤ (Matrix.trace (repMatrix ρ w)).re :=
    neg_re_trace_le_of_mem_unitaryGroup (repMatrix_mem ρ w)
  by_cases hd : (d : ℝ) = 0
  · have hd0 : d = 0 := by exact_mod_cast hd
    subst hd0
    simp
  · have hdpos : (0 : ℝ) < d :=
      lt_of_le_of_ne (Nat.cast_nonneg d) (Ne.symm hd)
    have h3 : (-1 : ℝ)
        ≤ (Matrix.trace (repMatrix ρ w)).re / (d : ℝ) := by
      rw [le_div_iff₀ hdpos]
      calc (-1 : ℝ) * (d : ℝ) = -(d : ℝ) := by ring
        _ ≤ (Matrix.trace (repMatrix ρ w)).re := h2
    linarith

/-- `|wordDensity ρ w| ≤ 2`, from the two-sided bound. -/
theorem abs_wordDensity_le_two (w : G) :
    |wordDensity ρ w| ≤ 2 :=
  abs_le.mpr ⟨by linarith [wordDensity_nonneg ρ w],
    wordDensity_le_two ρ w⟩

end WordDensityBounds

section ColApproxConvergence

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The exponential series of the majorant, as a `HasSum`:
`∑' k, (2|β|)ᵏ / k! = exp (2|β|)`. -/
theorem hasSum_pow_div_factorial (x : ℝ) :
    HasSum (fun k : ℕ => x ^ k / (Nat.factorial k : ℝ))
      (Real.exp x) := by
  have hsumm : Summable (fun k : ℕ => x ^ k / (Nat.factorial k : ℝ)) :=
    Summable.of_norm_bounded (Real.summable_pow_div_factorial |x|)
      (fun k => by
        have hk : |(Nat.factorial k : ℝ)| = (Nat.factorial k : ℝ) :=
          abs_of_nonneg (Nat.cast_nonneg _)
        rw [Real.norm_eq_abs, abs_div, abs_pow, hk])
  have hexp : Real.exp x
      = ∑' k : ℕ, x ^ k / (Nat.factorial k : ℝ) := by
    rw [Real.exp_eq_exp_ℝ]
    exact congr_fun NormedSpace.exp_eq_tsum_div x
  rw [hexp]
  exact hsumm.hasSum

/-- **The dominator bound for one column factor**:
`|colApprox ρ β K a b u u'| ≤ exp (2|β|)`, uniformly in
`K` and in all the data — each series term is bounded by
the majorant term `(2|β|)ᵏ / k!` because
`wordDensity ∈ [0, 2]`, and the finite partial sum is
bounded by the majorant's full sum. -/
theorem abs_colApprox_le (β : ℝ) (K : ℕ) (a b u u' : G) :
    |colApprox ρ β K a b u u'| ≤ Real.exp (2 * |β|) := by
  set w := a * u' * b⁻¹ * u⁻¹ with hw
  have hw0 : 0 ≤ wordDensity ρ w := wordDensity_nonneg ρ w
  have hw2 : wordDensity ρ w ≤ 2 := wordDensity_le_two ρ w
  have hterm : ∀ k : ℕ,
      |(-β) ^ k / (Nat.factorial k : ℝ) * (wordDensity ρ w) ^ k|
        ≤ (2 * |β|) ^ k / (Nat.factorial k : ℝ) := by
    intro k
    have hk : (0 : ℝ) < (Nat.factorial k : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos k)
    rw [abs_mul, abs_div, abs_pow, abs_neg, abs_pow,
      abs_of_nonneg hw0, abs_of_pos hk]
    have h1 : (wordDensity ρ w) ^ k ≤ 2 ^ k :=
      pow_le_pow_left₀ hw0 hw2 k
    have h2 : |β| ^ k * (wordDensity ρ w) ^ k ≤ (2 * |β|) ^ k := by
      rw [mul_pow]
      calc |β| ^ k * (wordDensity ρ w) ^ k
          ≤ |β| ^ k * 2 ^ k :=
            mul_le_mul_of_nonneg_left h1 (pow_nonneg (abs_nonneg β) k)
        _ = 2 ^ k * |β| ^ k := mul_comm _ _
    calc |β| ^ k / (Nat.factorial k : ℝ) * (wordDensity ρ w) ^ k
        = |β| ^ k * (wordDensity ρ w) ^ k
            / (Nat.factorial k : ℝ) := by ring
      _ ≤ (2 * |β|) ^ k / (Nat.factorial k : ℝ) :=
          div_le_div_of_nonneg_right h2 (le_of_lt hk)
  calc |colApprox ρ β K a b u u'|
      = |∑ k ∈ Finset.range (K + 1), (-β) ^ k
          / (Nat.factorial k : ℝ) * (wordDensity ρ w) ^ k| := rfl
    _ ≤ ∑ k ∈ Finset.range (K + 1),
          (2 * |β|) ^ k / (Nat.factorial k : ℝ) :=
        le_trans (Finset.abs_sum_le_sum_abs _ _)
          (Finset.sum_le_sum fun k _ => hterm k)
    _ ≤ ∑' k : ℕ, (2 * |β|) ^ k / (Nat.factorial k : ℝ) :=
        (Real.summable_pow_div_factorial _).sum_le_tsum
          (Finset.range (K + 1)) (fun k _ => by positivity)
    _ = Real.exp (2 * |β|) := (hasSum_pow_div_factorial _).tsum_eq

/-- **Pointwise convergence of one column factor**: the
order-`K` approximant `colApprox` tends to the true factor
`columnKernel ρ β a b u u' = exp (-β · wordDensity)` as
`K → ∞` — the Taylor partial sums of the exponential, at
the column word. No hypothesis on `ρ` or `d`. -/
theorem colApprox_tendsto (β : ℝ) (a b u u' : G) :
    Tendsto (fun K => colApprox ρ β K a b u u') atTop
      (𝓝 (columnKernel ρ β a b u u')) := by
  set w := a * u' * b⁻¹ * u⁻¹ with hw
  have hterm : ∀ k : ℕ,
      ((-β) * wordDensity ρ w) ^ k / (Nat.factorial k : ℝ)
        = (-β) ^ k / (Nat.factorial k : ℝ)
          * (wordDensity ρ w) ^ k := by
    intro k
    calc ((-β) * wordDensity ρ w) ^ k / (Nat.factorial k : ℝ)
        = ((-β) ^ k * (wordDensity ρ w) ^ k)
            / (Nat.factorial k : ℝ) :=
          congrArg (· / (Nat.factorial k : ℝ)) (mul_pow _ _ _)
      _ = (-β) ^ k / (Nat.factorial k : ℝ)
            * (wordDensity ρ w) ^ k :=
          (div_mul_eq_mul_div _ _ _).symm
  have hHas : HasSum
      (fun k : ℕ => (-β) ^ k / (Nat.factorial k : ℝ)
        * (wordDensity ρ w) ^ k)
      (Real.exp ((-β) * wordDensity ρ w)) := by
    have hsumm : Summable
        (fun k : ℕ => (-β) ^ k / (Nat.factorial k : ℝ)
          * (wordDensity ρ w) ^ k) :=
      (hasSum_pow_div_factorial ((-β) * wordDensity ρ w)).summable.congr
        (fun k => hterm k)
    have htsum : (∑' k : ℕ, (-β) ^ k / (Nat.factorial k : ℝ)
          * (wordDensity ρ w) ^ k)
        = Real.exp ((-β) * wordDensity ρ w) := by
      calc (∑' k : ℕ, (-β) ^ k / (Nat.factorial k : ℝ)
            * (wordDensity ρ w) ^ k)
          = ∑' k : ℕ, ((-β) * wordDensity ρ w) ^ k
              / (Nat.factorial k : ℝ) :=
            tsum_congr (fun k => (hterm k).symm)
        _ = Real.exp ((-β) * wordDensity ρ w) :=
            (hasSum_pow_div_factorial _).tsum_eq
    exact htsum ▸ hsumm.hasSum
  have hlim : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n,
        (-β) ^ k / (Nat.factorial k : ℝ) * (wordDensity ρ w) ^ k)
      atTop (𝓝 (Real.exp ((-β) * wordDensity ρ w))) :=
    hHas.tendsto_sum_nat
  have hcomp : Tendsto
      (fun K : ℕ => ∑ k ∈ Finset.range (K + 1),
        (-β) ^ k / (Nat.factorial k : ℝ) * (wordDensity ρ w) ^ k)
      atTop (𝓝 (Real.exp ((-β) * wordDensity ρ w))) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have hfun : (fun K => colApprox ρ β K a b u u')
      = (fun K : ℕ => ∑ k ∈ Finset.range (K + 1),
          (-β) ^ k / (Nat.factorial k : ℝ)
            * (wordDensity ρ w) ^ k) := rfl
  rw [hfun]
  have hck : columnKernel ρ β a b u u'
      = Real.exp ((-β) * wordDensity ρ w) := by
    unfold columnKernel
    congr 1
    ring
  rw [hck]
  exact hcomp

end ColApproxConvergence

section BlockLimit

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **The limit integrand**: the product over the four
edges of the true column factors `columnKernel`, cast to
`ℂ` — `plaqApproxIntegrand` with `colApprox` replaced by
its limit. Its corner integral is `PlaqBlock`, cast to
`ℂ` (`integral_plaqBlockIntegrand` below). -/
noncomputable def plaqBlockIntegrand (P : PlaqDatum N) (β : ℝ)
    (u u' : LayerLink N → G) (a : Fin 4 → G) : ℂ :=
  ∏ e : Fin 4, ((columnKernel ρ β (a (plaqCornerA e))
      (a (plaqCornerB e)) (u (plaqEdgeOf P e))
      (u' (plaqEdgeOf P e)) : ℝ) : ℂ)

/-- `wordDensity ρ` is measurable (for a continuous
representation): it is `1 - (Re χ)/d` with `χ` measurable. -/
theorem measurable_wordDensity
    (hρcont : Continuous fun g => repMatrix ρ g) :
    Measurable (wordDensity ρ) := by
  have hfun : wordDensity ρ
      = fun w => 1 - (charFn ρ w).re / (d : ℝ) := rfl
  rw [hfun]
  exact measurable_const.sub
    ((Complex.continuous_re.measurable.comp
      (measurable_charFn ρ hρcont)).div_const _)

/-- A plaquette word is continuous in the corner tuple. -/
theorem continuous_plaqWord (P : PlaqDatum N)
    (u u' : LayerLink N → G) (e : Fin 4) :
    Continuous fun a : Fin 4 → G => plaqWord P u u' a e := by
  unfold plaqWord
  exact (((continuous_apply (plaqCornerA e)).mul
    continuous_const).mul
    (continuous_apply (plaqCornerB e)).inv).mul continuous_const

/-- The column word inside `colApprox` at edge `e` is the
plaquette word: the approximant factor at edge `e` is the
exponential series in `wordDensity` of `plaqWord`. -/
theorem colApprox_edge_eq (P : PlaqDatum N) (K : ℕ) (β : ℝ)
    (u u' : LayerLink N → G) (e : Fin 4) (a : Fin 4 → G) :
    colApprox ρ β K (a (plaqCornerA e)) (a (plaqCornerB e))
        (u (plaqEdgeOf P e)) (u' (plaqEdgeOf P e))
      = ∑ k ∈ Finset.range (K + 1), (-β) ^ k
          / (Nat.factorial k : ℝ)
          * (wordDensity ρ (plaqWord P u u' a e)) ^ k := rfl

/-- The approximant factor at edge `e`, cast to `ℂ`, is
measurable in the corner tuple. -/
theorem measurable_colApprox_factor
    (hρcont : Continuous fun g => repMatrix ρ g) (P : PlaqDatum N)
    (K : ℕ) (β : ℝ) (u u' : LayerLink N → G) (e : Fin 4) :
    Measurable fun a : Fin 4 → G =>
      ((colApprox ρ β K (a (plaqCornerA e)) (a (plaqCornerB e))
        (u (plaqEdgeOf P e)) (u' (plaqEdgeOf P e)) : ℝ) : ℂ) := by
  have hwd : Measurable fun a : Fin 4 → G =>
      wordDensity ρ (plaqWord P u u' a e) :=
    (measurable_wordDensity ρ hρcont).comp
      (continuous_plaqWord P u u' e).measurable
  have hfun : (fun a : Fin 4 → G =>
        ((colApprox ρ β K (a (plaqCornerA e)) (a (plaqCornerB e))
          (u (plaqEdgeOf P e)) (u' (plaqEdgeOf P e)) : ℝ) : ℂ))
      = fun a => ∑ k ∈ Finset.range (K + 1),
          (((-β) ^ k / (Nat.factorial k : ℝ)
            * (wordDensity ρ (plaqWord P u u' a e)) ^ k : ℝ) : ℂ) := by
    funext a
    rw [colApprox_edge_eq, Complex.ofReal_sum]
  rw [hfun]
  exact Finset.measurable_sum _ fun k _ =>
    Complex.continuous_ofReal.measurable.comp
      (measurable_const.mul (hwd.pow_const k))

/-- The approximant integrand is measurable in the corner
tuple (a finite product of measurable factors). -/
theorem measurable_plaqApproxIntegrand
    (hρcont : Continuous fun g => repMatrix ρ g) (P : PlaqDatum N)
    (K : ℕ) (β : ℝ) (u u' : LayerLink N → G) :
    Measurable (plaqApproxIntegrand ρ P K β u u') :=
  Finset.measurable_prod _ fun e _ =>
    measurable_colApprox_factor ρ hρcont P K β u u' e

/-- **The dominator**: the approximant integrand is bounded
by `exp (2|β|)⁴`, uniformly in `K`, in the configurations,
and in the corner tuple — four column factors, each under
the §2 bound. This constant is the dominated-convergence
bound of §4. -/
theorem norm_plaqApproxIntegrand_le (P : PlaqDatum N) (K : ℕ)
    (β : ℝ) (u u' : LayerLink N → G) (a : Fin 4 → G) :
    ‖plaqApproxIntegrand ρ P K β u u' a‖
      ≤ (Real.exp (2 * |β|)) ^ 4 := by
  unfold plaqApproxIntegrand
  calc ‖∏ e : Fin 4, ((colApprox ρ β K (a (plaqCornerA e))
          (a (plaqCornerB e)) (u (plaqEdgeOf P e))
          (u' (plaqEdgeOf P e)) : ℝ) : ℂ)‖
      ≤ ∏ e : Fin 4, ‖((colApprox ρ β K (a (plaqCornerA e))
          (a (plaqCornerB e)) (u (plaqEdgeOf P e))
          (u' (plaqEdgeOf P e)) : ℝ) : ℂ)‖ := norm_prod_le _ _
    _ ≤ ∏ _e : Fin 4, Real.exp (2 * |β|) := by
        gcongr with e _
        rw [Complex.norm_real]
        exact abs_colApprox_le ρ β K _ _ _ _
    _ = (Real.exp (2 * |β|)) ^ 4 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Pointwise convergence of the integrands**: for every
fixed corner tuple, the approximant integrand tends to the
limit integrand as `K → ∞` — a finite product of the §2
one-factor convergences, cast to `ℂ`. -/
theorem tendsto_plaqApproxIntegrand (P : PlaqDatum N) (β : ℝ)
    (u u' : LayerLink N → G) (a : Fin 4 → G) :
    Tendsto (fun K => plaqApproxIntegrand ρ P K β u u' a) atTop
      (𝓝 (plaqBlockIntegrand ρ P β u u' a)) := by
  unfold plaqApproxIntegrand plaqBlockIntegrand
  apply tendsto_finsetProd Finset.univ
  intro e _
  exact (Complex.continuous_ofReal.tendsto _).comp
    (colApprox_tendsto ρ β _ _ _ _)

/-- **The limit integral is the true block**: the corner
integral of the limit integrand is `PlaqBlock`, cast to
`ℂ` — the fourfold product of `Fin.prod_univ_four` is
`PlaqBlock`'s four-factor product (bottom, right, top,
left), and the cast commutes with the integral. -/
theorem integral_plaqBlockIntegrand (P : PlaqDatum N) (β : ℝ)
    (u u' : LayerLink N → G) :
    ∫ a : Fin 4 → G, plaqBlockIntegrand ρ P β u u' a
        ∂(Measure.pi fun _ : Fin 4 => μG)
      = ((PlaqBlock μG ρ P β u u' : ℝ) : ℂ) := by
  have hA0 : plaqCornerA 0 = 0 := rfl
  have hA1 : plaqCornerA 1 = 1 := rfl
  have hA2 : plaqCornerA 2 = 2 := rfl
  have hA3 : plaqCornerA 3 = 0 := rfl
  have hB0 : plaqCornerB 0 = 1 := rfl
  have hB1 : plaqCornerB 1 = 3 := rfl
  have hB2 : plaqCornerB 2 = 3 := rfl
  have hB3 : plaqCornerB 3 = 2 := rfl
  have hpt : ∀ a : Fin 4 → G, plaqBlockIntegrand ρ P β u u' a
      = ((columnKernel ρ β (a 0) (a 1) (u (plaqEdgeB P))
            (u' (plaqEdgeB P)) *
          columnKernel ρ β (a 1) (a 3) (u (plaqEdgeR P))
            (u' (plaqEdgeR P)) *
          columnKernel ρ β (a 2) (a 3) (u (plaqEdgeT P))
            (u' (plaqEdgeT P)) *
          columnKernel ρ β (a 0) (a 2) (u (plaqEdgeL P))
            (u' (plaqEdgeL P)) : ℝ) : ℂ) := by
    intro a
    unfold plaqBlockIntegrand
    rw [Fin.prod_univ_four, hA0, hB0, hA1, hB1, hA2, hB2, hA3, hB3,
      plaqEdgeOf_zero, plaqEdgeOf_one, plaqEdgeOf_two,
      plaqEdgeOf_three, Complex.ofReal_mul, Complex.ofReal_mul,
      Complex.ofReal_mul]
  calc ∫ a : Fin 4 → G, plaqBlockIntegrand ρ P β u u' a
          ∂(Measure.pi fun _ : Fin 4 => μG)
      = ∫ a : Fin 4 → G,
          ((columnKernel ρ β (a 0) (a 1) (u (plaqEdgeB P))
              (u' (plaqEdgeB P)) *
            columnKernel ρ β (a 1) (a 3) (u (plaqEdgeR P))
              (u' (plaqEdgeR P)) *
            columnKernel ρ β (a 2) (a 3) (u (plaqEdgeT P))
              (u' (plaqEdgeT P)) *
            columnKernel ρ β (a 0) (a 2) (u (plaqEdgeL P))
              (u' (plaqEdgeL P)) : ℝ) : ℂ)
          ∂(Measure.pi fun _ : Fin 4 => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ((∫ a : Fin 4 → G,
          columnKernel ρ β (a 0) (a 1) (u (plaqEdgeB P))
              (u' (plaqEdgeB P)) *
            columnKernel ρ β (a 1) (a 3) (u (plaqEdgeR P))
              (u' (plaqEdgeR P)) *
            columnKernel ρ β (a 2) (a 3) (u (plaqEdgeT P))
              (u' (plaqEdgeT P)) *
            columnKernel ρ β (a 0) (a 2) (u (plaqEdgeL P))
              (u' (plaqEdgeL P))
          ∂(Measure.pi fun _ : Fin 4 => μG) : ℝ) : ℂ) :=
        integral_ofReal
    _ = ((PlaqBlock μG ρ P β u u' : ℝ) : ℂ) := rfl

/-! ## §4. The limit passage for the raw objects

Dominated convergence, in the tree's integral-continuity
pattern: measurability of every approximant integrand,
the constant dominator `exp (2|β|)⁴` (integrable against
the probability `Measure.pi`), the dominator bound at
every `K`, and pointwise convergence of the integrands.
The conclusion is convergence of the RAW block/kernel —
no stage proposition (T)/(P) is stated or implied by it
(see the header's non-transfer record). -/

/-- **A2-2e headline — approximant convergence of the
block**: the order-`K` approximant block converges to the
true block as `K → ∞`, at general `(G, ρ)`, pointwise in
the configurations `(u, u')`. Hypotheses on the face:
the standing continuity of `ρ` (measurability only). No
irreducibility, no `d` hypothesis, no twirl. -/
theorem plaqBlockApprox_tendsto
    (hρcont : Continuous fun g => repMatrix ρ g) (P : PlaqDatum N)
    (β : ℝ) (u u' : LayerLink N → G) :
    Tendsto (fun K => PlaqBlockApprox μG ρ P K β u u') atTop
      (𝓝 ((PlaqBlock μG ρ P β u u' : ℝ) : ℂ)) := by
  have hbound_int : Integrable
      (fun _ : Fin 4 → G => (Real.exp (2 * |β|)) ^ 4)
      (Measure.pi fun _ : Fin 4 => μG) := integrable_const _
  have hDCT := tendsto_integral_of_dominated_convergence
    (bound := fun _ : Fin 4 → G => (Real.exp (2 * |β|)) ^ 4)
    (fun K => (measurable_plaqApproxIntegrand ρ hρcont P K β
      u u').aestronglyMeasurable)
    hbound_int
    (fun K => Filter.Eventually.of_forall fun a =>
      norm_plaqApproxIntegrand_le ρ P K β u u' a)
    (Filter.Eventually.of_forall fun a =>
      tendsto_plaqApproxIntegrand ρ P β u u' a)
  rw [integral_plaqBlockIntegrand μG ρ P β u u'] at hDCT
  exact hDCT

/-- **Approximant convergence of the kernel**: the
order-`K` approximant kernel `Ψ_K` converges to the true
kernel `Ψ` as `K → ∞`, pointwise in the section data
`(x, y)` — the block convergence read on the section
configurations, by the definitions of `PlaqKernelApprox`
and `PlaqKernel`. Same hypotheses on the face. -/
theorem plaqKernelApprox_tendsto
    (hρcont : Continuous fun g => repMatrix ρ g) (P : PlaqDatum N)
    (β : ℝ) (x y : G) :
    Tendsto (fun K => PlaqKernelApprox μG ρ P K β x y) atTop
      (𝓝 ((PlaqKernel μG ρ P β x y : ℝ) : ℂ)) :=
  plaqBlockApprox_tendsto μG ρ hρcont P β (plaqSection P x)
    (plaqSection P y)

end BlockLimit

end ThetLogos
