import Mathlib.Tactic
import ThetLogos.OGPin

namespace ThetLogos

/-!
# ThetLogos.OGExhibit — OG-1, the unity-datum exhibit (bench position 18)

**Commission:** Zero's tap 2026-11-08 18:15 EST (QUEUE.md position
18), on the pricing of `og-scope-2026-11-08.md` §5. Dependency:
OG-0 (the pin, `ThetLogos.OGPin`) landed in-lane. This module
proves theorems OF the frozen F1–F3 forms pinned there — or
reports the failure as the result, in the pin's own terms.

## Face declarations (read before anything below)

- **PRE-REGISTERED DIAL-INELIGIBLE.** Dial 2 = 0 before this
  exhibit, 0 after it, and 0 on every outcome recorded here.
  **NO CLAIM.** Everything below is finite mathematics about a
  DECLARED datum (Register A): the unity datum, its declared
  response *read* `ogRead`, and the fences around both. The read
  is a read throughout — never a response law, never a gravity
  object, never an identity, never Dial evidence (K-OG-PROXY /
  K-OG-SHADOW stand armed over any such presentation).
- **F1's disposition is PARTIAL, and the partiality is faced
  here, not smoothed.** The characterization conjunct (iff) is
  proved at the frozen form's exact hypotheses
  (`og_unity_characterization`). The frozen conjunction
  `OGUnityForm` as a whole is **FALSE as pinned**:
  `og_unity_form_selfloop_counterexample` proves its negation
  at the explicit diagonal weight on `Fin 2`. The frozen
  live-edge hypothesis `∃ i j, w i j ≠ 0` admits a diagonal-only
  weight — every live entry a self-loop — where every field is
  constant on the support and the read is identically zero, so
  the non-vacuity conjunct cannot hold there. Non-vacuity is
  proved under the genuine live-edge reading — an off-diagonal
  live edge, `i ≠ j` with `w i j ≠ 0`, which is what "live edge"
  means in the scoping's own target (i)+(ii) joined form —
  as `og_unity_nonvacuity`, with its two directions assembled
  as `og_reads_differ_equal_totals` and
  `og_reads_equal_distinct_profiles`. **The pin is not edited
  by this bench.** The narrowing of the frozen hypothesis (an
  off-diagonal live edge) is flagged for Zero's ruling at
  integration, in the W-2′ pattern.
- **Kill dispositions on this brick.** K-OG-FIAT does **not**
  fire: the characterization is DERIVED from the TE seat's
  landed equality case (`teDirichlet_eq_zero_iff`, TE-T4),
  never postulated. K-OG-VAC does **not** fire: at every
  genuine (off-diagonal) live edge the read provably differs
  across named states — the witnesses do not collapse; the
  defect recorded above sits in the frozen hypothesis, not in
  the exhibit. K-OG-TOLMAN does **not** fire: F3 is proved at
  exactly the fence's content and claims no more
  (`og_equilibrium_fence`). K-OG-SHADOW / K-OG-PROXY /
  K-OG-DIAL: nothing in this module routes, names, or presents
  the read as anything but a read on a declared datum.
- **F2 lands in full, F3 lands in full**: `og_factorization_fence`
  is a theorem OF the frozen type `OGFactorizationForm`, and
  `og_equilibrium_fence` is a theorem OF the frozen type
  `OGEquilibriumForm`.

## Target map (scoping §5, OG-1)

- (i) non-vacuity, both directions: `og_unity_nonvacuity`
  (a nonconstant-on-support field with nonzero read);
  `og_reads_differ_equal_totals` (equal charge totals — both
  zero by TE-T3 — and provably different reads);
  `og_reads_equal_distinct_profiles` (a constant shift changes
  the profile and not the read).
- (ii) characterization (iff), derived: `og_unity_characterization`,
  and at the datum level `ogRead_eq_zero_iff_isEquilibrium`.
- (iii) the factorization fence: `og_factorization_fence`.
- (iv) the equilibrium closed form: `og_equilibrium_fence`.
- The frozen form's corner: `og_unity_form_selfloop_counterexample`.
- Datum-level non-vacuity: `og_datum_exists_nonzero_read`.
-/

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- **OG-1, target (ii) — the characterization, at the frozen
form's exact hypotheses.** This is the first conjunct of the
frozen `OGUnityForm`, proved as stated in the pin (symmetric,
nonnegative, at least one live entry in the pin's literal sense):
the declared read vanishes exactly on the fields constant on the
weight's support. DERIVED — it is the TE seat's landed equality
case `teDirichlet_eq_zero_iff` (TE-T4) transported onto the
frozen form, not a postulate (K-OG-FIAT does not fire). -/
theorem og_unity_characterization (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (_hlive : ∃ i j, w i j ≠ 0) (θ : V → ℝ) :
    teDirichlet w θ = 0 ↔ ∀ i j, w i j ≠ 0 → θ i = θ j :=
  teDirichlet_eq_zero_iff w hw hw0 θ

/-- **OG-1, target (i) — non-vacuity at a genuine live edge.**
At an OFF-DIAGONAL live edge (`i ≠ j`, `w i j ≠ 0`) there is a
field not constant on the support whose read is nonzero: the
indicator of `i`. This is the non-vacuity content of the frozen
F1 form under the genuine live-edge reading; the frozen form's
literal hypothesis also admits diagonal-only weights, where the
content is false — see `og_unity_form_selfloop_counterexample`.
The witnesses here do not collapse (K-OG-VAC does not fire). -/
theorem og_unity_nonvacuity (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    {i j : V} (hij : i ≠ j) (hwij : w i j ≠ 0) :
    ∃ θ : V → ℝ, (¬ ∀ a b, w a b ≠ 0 → θ a = θ b) ∧
      teDirichlet w θ ≠ 0 := by
  refine ⟨fun k => if k = i then 1 else 0, ?_, ?_⟩
  · intro hcon
    have h2 : (if i = i then (1 : ℝ) else 0) =
        (if j = i then (1 : ℝ) else 0) :=
      hcon i j hwij
    rw [if_pos rfl, if_neg hij.symm] at h2
    exact one_ne_zero h2
  · intro hzero
    have hcon : ∀ a b, w a b ≠ 0 →
        (fun k => if k = i then (1 : ℝ) else 0) a =
          (fun k => if k = i then (1 : ℝ) else 0) b :=
      (teDirichlet_eq_zero_iff w hw hw0 _).mp hzero
    have h2 : (if i = i then (1 : ℝ) else 0) =
        (if j = i then (1 : ℝ) else 0) :=
      hcon i j hwij
    rw [if_pos rfl, if_neg hij.symm] at h2
    exact one_ne_zero h2

/-- **The frozen F1 conjunction is FALSE as pinned — the
self-loop corner, faced.** At the diagonal weight on `Fin 2`
(every live entry a self-loop: `w i j = 1` iff `i = j`, else
`0`), the frozen form's three hypotheses all hold, its iff
conjunct holds — and its non-vacuity conjunct fails: every
field is constant on the support (the only constrained pairs
are `(i, i)`), so no field is nonconstant-on-support, whatever
its read. Hence `¬ OGUnityForm` at this weight. This is a
defect of the frozen hypothesis (it counts a self-loop as a
live edge), recorded as a proved refutation of the conjunction
at the corner — NOT a vacuity of the exhibit: at every genuine
edge the read separates states (`og_unity_nonvacuity`). The
pin stands unedited; the narrowing is Zero's ruling to make
at integration. -/
theorem og_unity_form_selfloop_counterexample :
    ¬ OGUnityForm (V := Fin 2)
      (fun i j => if i = j then (1 : ℝ) else 0) := by
  intro hform
  have hsymm : ∀ i j : Fin 2,
      (if i = j then (1 : ℝ) else 0) = (if j = i then (1 : ℝ) else 0) := by
    intro i j
    by_cases h : i = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh : j = i => h hh.symm)]
  have hnonneg : ∀ i j : Fin 2,
      0 ≤ (if i = j then (1 : ℝ) else 0) := by
    intro i j
    split <;> norm_num
  have hlive : ∃ i j : Fin 2,
      (if i = j then (1 : ℝ) else 0) ≠ 0 :=
    ⟨0, 0, by simp⟩
  obtain ⟨_hiff, θ, hnc, _hne⟩ := hform hsymm hnonneg hlive
  exact hnc (fun i j hij => by
    have hij' : (if i = j then (1 : ℝ) else 0) ≠ 0 := hij
    have hEq : i = j := by
      by_contra hne
      rw [if_neg hne] at hij'
      exact hij' rfl
    rw [hEq])

/-- **OG-1, target (i), direction 1 — equal totals, different
reads.** At a genuine live edge there are two named states
whose total separated charges are EQUAL (both are zero, by the
seat's conservation law TE-T3, `teCharge_sum_eq_zero`) and
whose declared reads are provably DIFFERENT (the zero field
reads 0; the non-vacuity witness does not). The read lives in
the distribution, never in the total (K-OG-SUM) — this is that
fence, exhibited. -/
theorem og_reads_differ_equal_totals (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    {i j : V} (hij : i ≠ j) (hwij : w i j ≠ 0) :
    ∃ θ₁ θ₂ : V → ℝ,
      (∑ a, teCharge w θ₁ a) = (∑ a, teCharge w θ₂ a) ∧
        teDirichlet w θ₁ ≠ teDirichlet w θ₂ := by
  obtain ⟨θ₂, -, hne⟩ := og_unity_nonvacuity w hw hw0 hij hwij
  refine ⟨fun _ => 0, θ₂, ?_, ?_⟩
  · rw [teCharge_sum_eq_zero w hw, teCharge_sum_eq_zero w hw]
  · have h0 : teDirichlet w (fun _ => 0) = 0 := by
      simp [teDirichlet]
    rw [h0]
    exact hne.symm

/-- **The read is invariant under constant shifts of the field.**
`teDirichlet w (θ + c) = teDirichlet w θ`: the pairing is
metered by gradient energy (TE-T4, `teDirichlet_eq`), and a
constant shift changes no gradient difference. The engine of
target (i)'s second direction. -/
theorem teDirichlet_add_const (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (θ : V → ℝ) (c : ℝ) :
    teDirichlet w (fun i => θ i + c) = teDirichlet w θ := by
  rw [teDirichlet_eq w hw (fun i => θ i + c), teDirichlet_eq w hw θ]
  have hE : teGradEnergy w (fun i => θ i + c) = teGradEnergy w θ := by
    show (∑ i, ∑ j, w i j * ((θ i + c) - (θ j + c)) ^ 2) =
      ∑ i, ∑ j, w i j * (θ i - θ j) ^ 2
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hd : (θ i + c) - (θ j + c) = θ i - θ j := by ring
    rw [hd]
  rw [hE]

/-- **OG-1, target (i), direction 2 — different profiles, equal
reads.** For any nonzero constant `c`, the shifted field
`θ + c` is a DIFFERENT profile from `θ` (they differ at every
site) with the SAME declared read. Named states, different
profiles, equal reads — the second direction of the scoping's
non-vacuity target (i). -/
theorem og_reads_equal_distinct_profiles (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (θ : V → ℝ) {c : ℝ} (hc : c ≠ 0) :
    (fun i => θ i + c) ≠ θ ∧
      teDirichlet w (fun i => θ i + c) = teDirichlet w θ := by
  refine ⟨?_, teDirichlet_add_const w hw θ c⟩
  intro hfun
  obtain ⟨i₀⟩ := (inferInstance : Nonempty V)
  have h2 : θ i₀ + c = θ i₀ := congrFun hfun i₀
  have hc0 : c = 0 := by linarith
  exact hc hc0

/-- **OG-1, target (iii) — the factorization fence, OF the
frozen type, in full.** A theorem of the frozen
`OGFactorizationForm` type: for every ordered-pair
factorization of the datum's own field, `θ = φ + ψ`, constancy
of one side `φ` on the weight's support collapses the read's
`θ`-dependence to the other side alone,
`teDirichlet w θ = teDirichlet w ψ`. Proof: the read is minus
half the gradient energy (TE-T4); on every live edge `φ` has
zero difference, so `θ`'s gradient differences equal `ψ`'s
edge by edge, and off the support the weight kills both terms.
The fence holds — the direction the scoping did not own in
advance; it fires no kill either way. -/
theorem og_factorization_fence (w : V → V → ℝ) (θ : V → ℝ) :
    OGFactorizationForm w θ := by
  intro hw _hw0 φ ψ hθ hφ
  have hE : teGradEnergy w ψ = teGradEnergy w θ := by
    show (∑ i, ∑ j, w i j * (ψ i - ψ j) ^ 2) =
      ∑ i, ∑ j, w i j * (θ i - θ j) ^ 2
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : w i j = 0
    · rw [hij, zero_mul, zero_mul]
    · have hφij : φ i = φ j := hφ i j hij
      have hd : θ i - θ j = ψ i - ψ j := by
        have e : θ i = φ i + ψ i := by rw [hθ, Pi.add_apply]
        have e' : θ j = φ j + ψ j := by rw [hθ, Pi.add_apply]
        rw [e, e', hφij]; ring
      rw [hd]
  rw [teDirichlet_eq w hw θ, teDirichlet_eq w hw ψ, hE]

/-- **OG-1, target (iv) — the equilibrium fence, OF the frozen
type, in full.** A theorem of the frozen `OGEquilibriumForm`
type: at equilibrium every datum's declared read is zero, and
its thermal content is constant-field on the support — the
Tolman rigidity restated over the declared datum, claiming
exactly the fence's content and no more (K-OG-TOLMAN does not
fire). The read vanishes by the characterization
(`teDirichlet_eq_zero_iff`); the constancy is the pinned
equilibrium predicate itself. -/
theorem og_equilibrium_fence : OGEquilibriumForm (V := V) := by
  intro D hD
  refine ⟨?_, hD⟩
  exact (teDirichlet_eq_zero_iff D.w D.w_symm D.w_nonneg D.θ).mpr hD

/-- **The datum-level characterization (targets (ii)+(iv)
joint).** For a datum `D` of the pinned unity form,
`ogRead D = 0 ↔ D.IsEquilibrium`: the declared read vanishes
exactly at equilibrium. Derived from the TE seat's landed
equality case at the datum's own structure fields — the
exhibit's headline, stated over the declared datum itself. -/
theorem ogRead_eq_zero_iff_isEquilibrium (D : OGDatum V) :
    ogRead D = 0 ↔ D.IsEquilibrium := by
  constructor
  · intro h
    exact (teDirichlet_eq_zero_iff D.w D.w_symm D.w_nonneg D.θ).mp h
  · intro h
    exact (teDirichlet_eq_zero_iff D.w D.w_symm D.w_nonneg D.θ).mpr h

/-- **Datum-level non-vacuity.** Over any seat with two
distinct sites there EXISTS a datum of the pinned unity form
that is not at equilibrium and whose declared read is
nonzero: the complete-graph weight (0 on the diagonal, 1 off
it) with the indicator field of one site. The exhibit is not
vacuous at the datum level either — the unity form has
non-equilibrium inhabitants with live reads. -/
theorem og_datum_exists_nonzero_read {i₀ j₀ : V} (h : i₀ ≠ j₀) :
    ∃ D : OGDatum V, ¬ D.IsEquilibrium ∧ ogRead D ≠ 0 := by
  let w : V → V → ℝ := fun a b => if a = b then 0 else 1
  let θ : V → ℝ := fun k => if k = i₀ then 1 else 0
  have hw0 : ∀ a b, 0 ≤ w a b := by
    intro a b
    show 0 ≤ (if a = b then (0 : ℝ) else 1)
    split <;> norm_num
  have hws : ∀ a b, w a b = w b a := by
    intro a b
    show (if a = b then (0 : ℝ) else 1) = (if b = a then (0 : ℝ) else 1)
    by_cases hab : a = b
    · rw [if_pos hab, if_pos hab.symm]
    · rw [if_neg hab, if_neg (fun hh : b = a => hab hh.symm)]
  have hwij : w i₀ j₀ ≠ 0 := by
    show (if i₀ = j₀ then (0 : ℝ) else 1) ≠ 0
    rw [if_neg h]
    norm_num
  have hθ : θ i₀ ≠ θ j₀ := by
    show (if i₀ = i₀ then (1 : ℝ) else 0) ≠
      (if j₀ = i₀ then (1 : ℝ) else 0)
    rw [if_pos rfl, if_neg (fun hh : j₀ = i₀ => h hh.symm)]
    norm_num
  refine ⟨⟨w, hw0, hws, θ⟩, ?_, ?_⟩
  · intro hEq
    exact hθ (hEq i₀ j₀ hwij)
  · intro hread
    have hread' : teDirichlet w θ = 0 := hread
    have hcon := (teDirichlet_eq_zero_iff w hws hw0 θ).mp hread'
    exact hθ (hcon i₀ j₀ hwij)

end ThetLogos
