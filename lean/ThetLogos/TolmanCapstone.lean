import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import ThetLogos.TolmanContinuum

namespace ThetLogos

open Filter Topology MeasureTheory

/-!
# ThetLogos.TolmanCapstone — the Tolman continuum-limit capstone (WORKING LABEL)

Lane brick, commissioned by Zero 2026-11-16 ("build it") on the WP3
scope (`~/workspace/your_files/wp3-continuum-toy-seat-scope-2026-11-16.md`
§2.1, §4). Naming is a working label — final naming is Zero's.

**The gap this closes.** `TolmanContinuum` proves the characterization
of refinement-limit equilibria (samples of a continuum pair, finite
equilibria at every level) by the slope identity, both directions. Its
own ledger record names the missing piece: *"no existing equilibrium
is shown to approximate a continuum one."* The refinement-limit notion
quantifies over samples of the answer; this module proves the
sequential form: **independently given** finite equilibria `xₙ` at
level `n` for the sampled weights `tolmanSample a n` — arbitrary finite
data, not samples of any continuum function — that converge on grids
to a continuous `x` force the slope identity for `x` at one global
`λ`; and conversely every continuum equilibrium arises this way (its
own samples). The two notions — limit of finite equilibria and
refinement-limit equilibrium — coincide, and both are the slope
identity.

**Charter fences (on the face).** NO CLAIM. A toy seat: an equilibrium
characterization on `[0, 1]`, not a field theory, not a continuum
limit of the lattice seats, **not Yang-Mills progress**, and not a
gravity statement. Dials 0/4. This module closes no milestone by itself — rulings close
milestones. M-U4 ruling history: closed on the circle letter by Zero's
ruling of 2026-11-16 (11:19 EST), cleared by Zero the same day
(13:14 EST), and **closed on intent by Zero's ruling of 2026-11-17
(00:48 EST) on this module as its basis** — the non-degenerate Tolman
correspondence the WP3 audit priced (S–M). The close is intent-grade:
Dial 3 stays 0, no continuum limit of the theory's own dynamics is
claimed, the circle seat's limit keeps its PARTIAL grade, and the
AQFT continuum route stays FRONTIER. The weight `a` is a bare
positive weight at every level and in the limit (**K-TOL-PROXY**
armed: no statement names or treats it as a metric, a metric
component, or a redshift factor; the §5 joint insertion of the m-q3
scope is not built here).

**Kill register.**
- **K-CONT-CIRC** — armed, does not fire: the finite equilibria are
  arbitrary (`IsTolmanEquilibrium (tolmanSample a n) (xₙ n)` is a
  hypothesis on independent data); no `xₙ` is constructed from `x` or
  from the identity. The answer occurs only in the conclusion. (The
  converse direction uses the continuum pair's own samples — that is
  what "arises as a limit" means; the non-trivial direction is the
  forward one.)
- **K-CONT-DEGEN** — does not fire: no parameter collapses. `a` is
  fixed throughout, no coupling is sent anywhere, and the limit
  object satisfies the *same* identity in the *same* `λ`-form as the
  finite seats.
- **K-CONT-NAME** — does not fire: the continuum side is the slope
  identity on `[0, 1]`, a proved characterization with named
  witnesses and non-witnesses in `TolmanContinuum`.
- **K-MQ3-PROXY** — acknowledged: this is not the m-q3 scope's §1
  event and not Dial-3 motion.
-/

/-- **Convergence on grids** (the pinned sequential form, WP3 §2.1):
a sequence of finite configurations `xseq n : Fin (n + 1) → ℝ`
converges on grids to the continuum function `x` when, for every
`t ∈ [0, 1]` and every choice of grid points `tolmanGrid n (i n)`
converging to `t`, the values `xseq n (i n)` converge to `x t`.
Tier T1 (definition). -/
def TolmanGridConverges (xseq : ∀ n : ℕ, Fin (n + 1) → ℝ) (x : ℝ → ℝ) :
    Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : ∀ n : ℕ, Fin (n + 1),
    Tendsto (fun n => tolmanGrid n (i n)) atTop (𝓝 t) →
      Tendsto (fun n => xseq n (i n)) atTop (𝓝 (x t))

/-- **Sequential limit of finite equilibria** (WP3 §2.1): `x` is the
grid-limit of the sequence `xseq` of finite configurations, each of
which is a finite Tolman equilibrium at its level for the sampled
weights `tolmanSample a n`. The `xseq n` are arbitrary finite data —
**not** assumed to be samples of `x` or of any continuum function
(K-CONT-CIRC's fence is this definition's reading). Tier T1
(definition). -/
def IsSequentialTolmanLimit (a x : ℝ → ℝ)
    (xseq : ∀ n : ℕ, Fin (n + 1) → ℝ) : Prop :=
  (∀ n : ℕ, IsTolmanEquilibrium (tolmanSample a n) (xseq n)) ∧
    TolmanGridConverges xseq x

/-- **Every point of `[0, 1]` is within `1 / (n + 1)` of a level-`n`
grid point** — the per-level form of grid density the sequential
argument consumes (the landed `tolmanGrid_eventually_close` gives a
point at *some* level; the sequence construction needs one at *every*
level). Tier T1. -/
theorem exists_tolmanGrid_close {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    ∃ i : Fin (n + 1), |t - tolmanGrid n i| ≤ 1 / ((n : ℝ) + 1) := by
  obtain ⟨ht0, ht1⟩ := ht
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  set m := ⌊t * ((n : ℝ) + 1)⌋₊ with hm
  have hy0 : 0 ≤ t * ((n : ℝ) + 1) := mul_nonneg ht0 hnpos.le
  have hmfloor : (m : ℝ) ≤ t * ((n : ℝ) + 1) := Nat.floor_le hy0
  have hmlt : t * ((n : ℝ) + 1) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmle : m ≤ n + 1 := by
    have h1 : t * ((n : ℝ) + 1) ≤ (n : ℝ) + 1 :=
      calc t * ((n : ℝ) + 1) ≤ 1 * ((n : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right ht1 hnpos.le
        _ = (n : ℝ) + 1 := one_mul _
    have h2 : (m : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      rw [hcast]
      exact le_trans hmfloor h1
    exact_mod_cast h2
  by_cases hmn : m ≤ n
  · refine ⟨⟨m, by omega⟩, ?_⟩
    have hgrid : tolmanGrid n ⟨m, by omega⟩ = (m : ℝ) / ((n : ℝ) + 1) := by
      simp only [tolmanGrid, hcast]
    rw [hgrid]
    have hdiv : t - (m : ℝ) / ((n : ℝ) + 1)
        = (t * ((n : ℝ) + 1) - m) / ((n : ℝ) + 1) := by
      rw [eq_div_iff (ne_of_gt hnpos), sub_mul]
      congr 1
      exact div_mul_cancel₀ _ (ne_of_gt hnpos)
    rw [hdiv, abs_div, abs_of_pos hnpos]
    have hnum0 : 0 ≤ t * ((n : ℝ) + 1) - m := by linarith
    have hnum1 : t * ((n : ℝ) + 1) - m ≤ 1 := by linarith
    rw [abs_of_nonneg hnum0]
    refine (div_le_iff₀ hnpos).mpr ?_
    have hone : (1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = 1 :=
      one_div_mul_cancel (ne_of_gt hnpos)
    linarith
  · have hm' : m = n + 1 := by omega
    have ht_eq : t = 1 := by
      have hge : (n : ℝ) + 1 ≤ t * ((n : ℝ) + 1) := by
        have h2 : (m : ℝ) ≤ t * ((n : ℝ) + 1) := hmfloor
        rw [hm'] at h2
        rwa [hcast] at h2
      have hle : t * ((n : ℝ) + 1) ≤ 1 * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right ht1 hnpos.le
      have heq : t * ((n : ℝ) + 1) = (n : ℝ) + 1 :=
        le_antisymm (by linarith) hge
      have heq2 : t * ((n : ℝ) + 1) = 1 * ((n : ℝ) + 1) := by
        rw [one_mul]; exact heq
      exact mul_right_cancel₀ (ne_of_gt hnpos) heq2
    refine ⟨⟨n, by omega⟩, ?_⟩
    have hgrid : tolmanGrid n ⟨n, by omega⟩ = (n : ℝ) / ((n : ℝ) + 1) := by
      simp only [tolmanGrid, hcast]
    rw [hgrid, ht_eq]
    have hval : (1 : ℝ) - (n : ℝ) / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) := by
      field_simp
      ring
    rw [hval, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))]

/-- **Grid points converge to every point of `[0, 1]` along a
sequence:** there is a choice of level-`n` grid points converging to
`t`. From `exists_tolmanGrid_close` by choice, then squeezing with
`1 / (n + 1) → 0`. Tier T1. -/
theorem exists_grid_seq_tendsto {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ i : ∀ n : ℕ, Fin (n + 1),
      Tendsto (fun n => tolmanGrid n (i n)) atTop (𝓝 t) := by
  choose i hi using fun n => exists_tolmanGrid_close ht n
  refine ⟨i, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero_norm' (a := fun n : ℕ => 1 / ((n : ℝ) + 1)) ?_ ?_
  · exact Filter.Eventually.of_forall (fun n => by
      rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, Real.dist_eq,
        abs_sub_comm]
      exact hi n)
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- **The slope is continuous at interior occupations:** `occSlope`
is `log (1 − ·) − log ·`, continuous wherever both arguments are
positive. Tier T1. -/
theorem continuousAt_occSlope {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    ContinuousAt occSlope y := by
  have hlog1 : ContinuousAt (fun t : ℝ => Real.log (1 - t)) y := by
    apply ContinuousAt.log
    · exact continuousAt_const.sub continuousAt_id
    · exact ne_of_gt (by linarith : (0 : ℝ) < 1 - y)
  have hlog2 : ContinuousAt (fun t : ℝ => Real.log t) y :=
    ContinuousAt.log continuousAt_id (ne_of_gt h0)
  exact hlog1.sub hlog2

/-- **Continuity transports along grid sequences:** a function
continuous on `[0, 1]` composed with a sequence of domain points
converging to `t ∈ [0, 1]` converges to its value at `t`. Tier T1. -/
theorem tendsto_comp_continuousOn_Icc {f : ℝ → ℝ} {g : ℕ → ℝ} {t : ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hgI : ∀ n : ℕ, g n ∈ Set.Icc (0 : ℝ) 1)
    (hg : Tendsto g atTop (𝓝 t)) :
    Tendsto (fun n => f (g n)) atTop (𝓝 (f t)) := by
  have hwithin : Tendsto g atTop (𝓝[Set.Icc (0 : ℝ) 1] t) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hg, Filter.Eventually.of_forall hgI⟩
  exact Tendsto.comp
    (show Tendsto f (𝓝[Set.Icc (0 : ℝ) 1] t) (𝓝 (f t)) from hf t ht)
    hwithin

/-- **Per-level witnesses exist:** a sequence of finite equilibria at
the sampled weights carries a sequence of slope witnesses `lam n`,
one per level, by the landed finite characterization
(`tolman_characterization`). Tier T1. -/
theorem exists_seq_lambda {a : ℝ → ℝ}
    {xseq : ∀ n : ℕ, Fin (n + 1) → ℝ}
    (ha0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < a t)
    (heq : ∀ n : ℕ, IsTolmanEquilibrium (tolmanSample a n) (xseq n)) :
    ∃ lam : ℕ → ℝ, ∀ (n : ℕ) (i : Fin (n + 1)),
      occSlope (xseq n i) = lam n * tolmanSample a n i := by
  have hpos : ∀ n : ℕ, ∀ i : Fin (n + 1), 0 < tolmanSample a n i :=
    fun n i => ha0 _ tolmanGrid_mem_Icc
  have key : ∀ n : ℕ, ∃ lam : ℝ, ∀ i : Fin (n + 1),
      occSlope (xseq n i) = lam * tolmanSample a n i := by
    intro n
    exact ((tolman_characterization (a := tolmanSample a n)
      (x₀ := xseq n) (hpos n)).mp (heq n)).2
  choose lam hlam using key
  exact ⟨lam, hlam⟩

/-- **The λ-collapse over sequences:** the per-level witnesses are
all forced at the shared grid point `0` — `lam n = occSlope (xseq n 0)
 / a 0` — and grid convergence at `t = 0` then gives
`lam n → occSlope (x 0) / a 0`. The landed λ-collapse engine
(`slope_eq_on_grid_of_refinementLimit`) re-run over sequences
instead of samples. Tier T1. -/
theorem seq_lambda_tendsto {a x : ℝ → ℝ}
    {xseq : ∀ n : ℕ, Fin (n + 1) → ℝ} {lam : ℕ → ℝ}
    (ha0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < a t)
    (hx01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < x t ∧ x t < 1)
    (hlam : ∀ (n : ℕ) (i : Fin (n + 1)),
      occSlope (xseq n i) = lam n * tolmanSample a n i)
    (hconv : TolmanGridConverges xseq x) :
    Tendsto lam atTop (𝓝 (occSlope (x 0) / a 0)) := by
  have h00 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have ha00 : (0 : ℝ) < a 0 := ha0 0 h00
  have hlam_eq : ∀ n : ℕ, lam n = occSlope (xseq n 0) / a 0 := by
    intro n
    have h := hlam n 0
    simp only [tolmanSample, tolmanGrid_zero] at h
    rw [eq_div_iff (ne_of_gt ha00)]
    exact h.symm
  have hx0 : Tendsto (fun n => xseq n (0 : Fin (n + 1))) atTop
      (𝓝 (x 0)) := by
    apply hconv 0 h00 (fun _ => 0)
    have hfun : (fun n => tolmanGrid n ((fun _ => (0 : Fin (n + 1))) n))
        = (fun _ => (0 : ℝ)) :=
      funext (fun n => tolmanGrid_zero)
    rw [hfun]
    exact tendsto_const_nhds
  have hocc : Tendsto (fun n => occSlope (xseq n (0 : Fin (n + 1))))
      atTop (𝓝 (occSlope (x 0))) :=
    ((continuousAt_occSlope (hx01 0 h00).1 (hx01 0 h00).2).tendsto).comp hx0
  have hdiv := hocc.div_const (a 0)
  have hfun : lam = (fun n => occSlope (xseq n (0 : Fin (n + 1))) / a 0) :=
    funext hlam_eq
  rw [hfun]
  exact hdiv

/-- **Brick 1 headline — the forward direction (approximation):**
independently given finite equilibria converging on grids to a
continuous interior `x` force the slope identity for `x` at one
global `λ = occSlope (x 0) / a 0`. At each `t`, the finite slope
identity at level-`n` grid points converging to `t` passes to the
limit by continuity of `occSlope ∘ x` and of `a`. Tier T1. -/
theorem slope_identity_of_seq_limit {a x : ℝ → ℝ}
    {xseq : ∀ n : ℕ, Fin (n + 1) → ℝ}
    (ha : ContinuousOn a (Set.Icc 0 1))
    (ha0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < a t)
    (hx : ContinuousOn x (Set.Icc 0 1))
    (hx01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < x t ∧ x t < 1)
    (hseq : IsSequentialTolmanLimit a x xseq) :
    ∃ lam : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, occSlope (x t) = lam * a t := by
  obtain ⟨heq, hconv⟩ := hseq
  obtain ⟨lam, hlam⟩ := exists_seq_lambda ha0 heq
  refine ⟨occSlope (x 0) / a 0, fun t ht => ?_⟩
  obtain ⟨i, hi⟩ := exists_grid_seq_tendsto ht
  have hlim_lam : Tendsto lam atTop (𝓝 (occSlope (x 0) / a 0)) :=
    seq_lambda_tendsto ha0 hx01 hlam hconv
  have hlim_a : Tendsto (fun n => a (tolmanGrid n (i n))) atTop
      (𝓝 (a t)) :=
    tendsto_comp_continuousOn_Icc ha ht (fun n => tolmanGrid_mem_Icc) hi
  have hlim_prod : Tendsto (fun n => lam n * a (tolmanGrid n (i n)))
      atTop (𝓝 (occSlope (x 0) / a 0 * a t)) := hlim_lam.mul hlim_a
  have hlim_occ : Tendsto (fun n => occSlope (xseq n (i n))) atTop
      (𝓝 (occSlope (x t))) :=
    ((continuousAt_occSlope (hx01 t ht).1 (hx01 t ht).2).tendsto).comp
      (hconv t ht i hi)
  have heqseq : (fun n => occSlope (xseq n (i n)))
      = (fun n => lam n * a (tolmanGrid n (i n))) :=
    funext (fun n => hlam n (i n))
  rw [heqseq] at hlim_occ
  exact tendsto_nhds_unique hlim_occ hlim_prod

/-- **Sequential limits are exactly the refinement-limit
equilibria:** the forward direction is Brick 1's headline plus the
landed characterization's converse; the backward direction takes the
continuum pair's own samples — finite equilibria at every level by
definition of `IsRefinementLimitEquilibrium` — which converge on
grids by continuity of `x`. Tier T1. -/
theorem seq_limit_iff_refinement_limit {a x : ℝ → ℝ}
    (ha : ContinuousOn a (Set.Icc 0 1))
    (ha0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < a t)
    (hx : ContinuousOn x (Set.Icc 0 1))
    (hx01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < x t ∧ x t < 1) :
    (∃ xseq : ∀ n : ℕ, Fin (n + 1) → ℝ,
      IsSequentialTolmanLimit a x xseq) ↔
      IsRefinementLimitEquilibrium a x := by
  constructor
  · rintro ⟨xseq, hseq⟩
    obtain ⟨lam, hlam⟩ := slope_identity_of_seq_limit ha ha0 hx hx01 hseq
    exact (tolman_continuum_characterization hx ha hx01 ha0).mpr
      ⟨lam, hlam⟩
  · intro h
    refine ⟨tolmanSample x, h, fun t ht i hi => ?_⟩
    show Tendsto (fun n => x (tolmanGrid n (i n))) atTop (𝓝 (x t))
    exact tendsto_comp_continuousOn_Icc hx ht
      (fun n => tolmanGrid_mem_Icc) hi

/-- **The capstone headline — the three notions coincide:**
being a limit of independently given finite equilibria, being a
refinement-limit equilibrium, and satisfying the slope identity at
one global `λ` are one and the same at this seat. The second
equivalence is the landed `tolman_continuum_characterization`,
cited; the first is this module's capstone. Tier T1. -/
theorem tolman_capstone_coincidence {a x : ℝ → ℝ}
    (ha : ContinuousOn a (Set.Icc 0 1))
    (ha0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < a t)
    (hx : ContinuousOn x (Set.Icc 0 1))
    (hx01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < x t ∧ x t < 1) :
    (∃ xseq : ∀ n : ℕ, Fin (n + 1) → ℝ,
      IsSequentialTolmanLimit a x xseq) ↔
      ∃ lam : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, occSlope (x t) = lam * a t :=
  (seq_limit_iff_refinement_limit ha ha0 hx hx01).trans
    (tolman_continuum_characterization hx ha hx01 ha0)

/-- **The capstone in the pin's a.e. form:** a sequential limit of
finite equilibria satisfies the slope identity almost everywhere on
`[0, 1]` at one global `λ` — the everywhere identity of the
coincidence headline, restricted to the a.e. quantifier via the
landed `tolman_continuum_slope_ae`. Tier T1. -/
theorem tolman_capstone_slope_ae {a x : ℝ → ℝ}
    (ha : ContinuousOn a (Set.Icc 0 1))
    (ha0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < a t)
    (hx : ContinuousOn x (Set.Icc 0 1))
    (hx01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < x t ∧ x t < 1)
    (hseq : ∃ xseq : ∀ n : ℕ, Fin (n + 1) → ℝ,
      IsSequentialTolmanLimit a x xseq) :
    ∃ lam : ℝ, ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      occSlope (x t) = lam * a t :=
  tolman_continuum_slope_ae hx ha hx01 ha0
    ((seq_limit_iff_refinement_limit ha ha0 hx hx01).mp hseq)

/-- **Sequential non-vacuity:** the constant pair `a ≡ 1`,
`x ≡ 1/4` is a sequential limit of finite equilibria (its own
samples, via the landed continuum witness
`tolman_continuum_witness`). The sequential notion is inhabited,
with the named non-witness of `TolmanContinuum` standing on the
other side (K-TOL-VAC's discipline). Tier T1. -/
theorem tolman_seq_limit_witness :
    ∃ xseq : ∀ n : ℕ, Fin (n + 1) → ℝ,
      IsSequentialTolmanLimit (fun _ => (1 : ℝ)) (fun _ => (1 / 4 : ℝ))
        xseq :=
  (seq_limit_iff_refinement_limit continuousOn_const
    (fun _ _ => one_pos) continuousOn_const
    (fun _ _ => ⟨by show (0 : ℝ) < 1 / 4; norm_num,
      by show (1 / 4 : ℝ) < 1; norm_num⟩)).mpr
    tolman_continuum_witness

end ThetLogos
