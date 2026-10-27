import ThetLogos.SMHiggsBreaking

/-!
# ThetLogos.PhotonUniqueMassless — the photon is the unique massless
gauge direction of the finite assembly (field-side exactness)

**Status: T1 theorems about a T2-input model. NO CLAIM beyond the
assembled sector.**

Origin: Jeff Gurd's coinage "the one photon theory" (2026-10-26),
scoped 2026-10-27 (`one-photon-object-scoping`). The sharpened
question (reading R3′): *within the finite assembly, is the photon
provably the **only** massless gauge direction?* The generator side
was already T1 (`higgs_stabilizer_is_Q`: the VEV stabilizer is
exactly span(Q)); the photon direction was known massless
(`higgs_photon_direction_massless`). What was un-owned is the
field-side exactness proved here: the zero set of the Higgs mass
form `higgsMassQuad` is **exactly** the photon line — no second
massless direction hides anywhere in the assembled sector.

**The hypothesis correction, on the face.** The scoping priced the
statement under `v ≠ 0` and `(g, g′) ≠ (0, 0)`. The derivation
shows that hypothesis set is exactly right for the **neutral**
sector (`higgsMassQuad_neutral_eq_zero_iff`, landed as priced) but
NOT for the full four-field form: at `g = 0` the charged directions
`(W1, W2, 0, 0)` are massless for every `W1, W2`
(`higgsMassQuad_charged_massless_of_g_eq_zero`) — physically
correct (g = 0 switches off the SU(2) coupling, so the W's get no
mass from this form), but a genuine second massless sector. The
full uniqueness therefore carries the hypothesis the source's
algebra demands, `g ≠ 0` (`photonLine_eq_zero_iff`,
`photon_unique_massless_direction`). This is reported as a verdict
change on the scoping's hypothesis set, not silently absorbed:
under the priced hypotheses read literally over all four fields,
uniqueness is FALSE, and the counterexample is a theorem below.

**Scope fence (K3, on the face).** Everything here is inside the
assembled electroweak sector of `SMHiggsBreaking`. The couplings
`g, g′` and the VEV `v` remain T2 inputs (matched, not derived);
the statement is classical; it asserts nothing about nature's full
gauge content, no dark sector, no continuum. This is a **photon**
object. It is not a gravity object, and Dial 2 is unaffected by it.
-/

namespace ThetLogos

/-- T1: the exact zero set of the Higgs mass form, under `v ≠ 0`
alone. The mass form vanishes iff each of its two sum-of-squares
sectors vanishes: the charged sector contributes the conditions
`g * W1 = 0` and `g * W2 = 0` (NOT `W1 = 0` outright — at `g = 0`
the charged fields decouple from the form), and the neutral sector
contributes `g * W3 = g' * B`. This is the field-side exactness the
generator-side theorems did not state. -/
theorem higgsMassQuad_eq_zero_iff {g g' v : ℝ} (hv : v ≠ 0)
    (W1 W2 W3 B : ℝ) :
    higgsMassQuad g g' v W1 W2 W3 B = 0 ↔
      g * W1 = 0 ∧ g * W2 = 0 ∧ g * W3 = g' * B := by
  rw [higgsMassQuad_eq]
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv
  have hA : 0 ≤ g ^ 2 * v ^ 2 * (W1 ^ 2 + W2 ^ 2) / 8 := by positivity
  have hC : 0 ≤ v ^ 2 * (g * W3 - g' * B) ^ 2 / 8 := by positivity
  constructor
  · intro h
    have hsum := (add_eq_zero_iff_of_nonneg hA hC).mp h
    have hA0 : g ^ 2 * v ^ 2 * (W1 ^ 2 + W2 ^ 2) = 0 := by
      have := hsum.1
      linarith
    have hC0 : v ^ 2 * (g * W3 - g' * B) ^ 2 = 0 := by
      have := hsum.2
      linarith
    have hneut : g * W3 = g' * B := by
      have h1 : (g * W3 - g' * B) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hC0 with h2 | h2
        · exact absurd h2 hv2
        · exact h2
      have h2 : g * W3 - g' * B = 0 := pow_eq_zero_iff (by norm_num) |>.mp h1
      linarith
    have hchg : g * W1 = 0 ∧ g * W2 = 0 := by
      rcases mul_eq_zero.mp hA0 with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · have hg : g = 0 := pow_eq_zero_iff (by norm_num) |>.mp h2
          exact ⟨by rw [hg]; ring, by rw [hg]; ring⟩
        · exact absurd h2 hv2
      · have hW : W1 ^ 2 + W2 ^ 2 = 0 := h1
        have hW1 : W1 = 0 := by
          have h1' : W1 ^ 2 = 0 := by
            have hs1 : 0 ≤ W1 ^ 2 := sq_nonneg W1
            have hs2 : 0 ≤ W2 ^ 2 := sq_nonneg W2
            linarith
          exact pow_eq_zero_iff (by norm_num) |>.mp h1'
        have hW2 : W2 = 0 := by
          have h2' : W2 ^ 2 = 0 := by
            have hs1 : 0 ≤ W1 ^ 2 := sq_nonneg W1
            have hs2 : 0 ≤ W2 ^ 2 := sq_nonneg W2
            linarith
          exact pow_eq_zero_iff (by norm_num) |>.mp h2'
        exact ⟨by rw [hW1]; ring, by rw [hW2]; ring⟩
    exact ⟨hchg.1, hchg.2, hneut⟩
  · rintro ⟨h1, h2, h3⟩
    have hA0 : g ^ 2 * v ^ 2 * (W1 ^ 2 + W2 ^ 2) / 8 = 0 := by
      rcases mul_eq_zero.mp h1 with hg | hW1
      · rw [hg]; ring
      · rcases mul_eq_zero.mp h2 with hg | hW2
        · rw [hg]; ring
        · rw [hW1, hW2]; ring
    have hC0 : v ^ 2 * (g * W3 - g' * B) ^ 2 / 8 = 0 := by
      have : g * W3 - g' * B = 0 := by linarith
      rw [this]; ring
    rw [hA0, hC0]; ring

/-- T1: the neutral sector, under exactly the hypotheses the
scoping priced (`v ≠ 0`, `(g, g′) ≠ (0, 0)`): with the charged
fields off, the mass form vanishes iff `(W3, B)` lies on the
photon line `(W3, B) ∝ (g′, g)`. Landed as priced. -/
theorem higgsMassQuad_neutral_eq_zero_iff {g g' v : ℝ} (hv : v ≠ 0)
    (hgg' : g ≠ 0 ∨ g' ≠ 0) (W3 B : ℝ) :
    higgsMassQuad g g' v 0 0 W3 B = 0 ↔
      ∃ t : ℝ, W3 = t * g' ∧ B = t * g := by
  rw [higgsMassQuad_eq_zero_iff hv]
  simp only [mul_zero, true_and]
  constructor
  · intro h
    rcases hgg' with hg | hg'
    · refine ⟨B / g, ?_, by field_simp⟩
      rw [div_mul_eq_mul_div, eq_div_iff hg]
      linear_combination h
    · refine ⟨W3 / g', by field_simp, ?_⟩
      rw [div_mul_eq_mul_div, eq_div_iff hg']
      linear_combination -h
  · rintro ⟨t, rfl, rfl⟩
    ring

/-- T1: the full four-field exactness, under the hypotheses the
source's algebra demands (`v ≠ 0`, `g ≠ 0`): the mass form
vanishes **exactly** on the photon line — charged fields zero and
`(W3, B) ∝ (g′, g)` — and nowhere else. -/
theorem photonLine_eq_zero_iff {g g' v : ℝ} (hv : v ≠ 0) (hg : g ≠ 0)
    (W1 W2 W3 B : ℝ) :
    higgsMassQuad g g' v W1 W2 W3 B = 0 ↔
      W1 = 0 ∧ W2 = 0 ∧ ∃ t : ℝ, W3 = t * g' ∧ B = t * g := by
  rw [higgsMassQuad_eq_zero_iff hv]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hW1 : W1 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hg
      · exact h
    have hW2 : W2 = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hg
      · exact h
    refine ⟨hW1, hW2, B / g, ?_, by field_simp⟩
    rw [div_mul_eq_mul_div, eq_div_iff hg]
    linear_combination h3
  · rintro ⟨rfl, rfl, t, rfl, rfl⟩
    exact ⟨by ring, by ring, by ring⟩

/-- T1 (packaging corollary): inside the assembled sector, under
`v ≠ 0` and `g ≠ 0`, the photon is the **unique** massless gauge
direction: every field direction annihilated by the mass form lies
on the photon line, and the line is attained (a nonzero direction
on it is massless — the content of
`higgs_photon_direction_massless`, recovered). Together with the
generator-side `higgs_stabilizer_is_Q`, this closes reading R3′ of
the one-photon question inside the assembly. Scope fence: the
assembled sector only; `g, g′, v` are T2 inputs; classical only;
no claim about nature's full gauge content. -/
theorem photon_unique_massless_direction {g g' v : ℝ} (hv : v ≠ 0)
    (hg : g ≠ 0) :
    (∀ W1 W2 W3 B : ℝ, higgsMassQuad g g' v W1 W2 W3 B = 0 →
      W1 = 0 ∧ W2 = 0 ∧ ∃ t : ℝ, W3 = t * g' ∧ B = t * g) ∧
    (∃ t : ℝ, t ≠ 0 ∧
      higgsMassQuad g g' v 0 0 (t * g') (t * g) = 0) := by
  constructor
  · intro W1 W2 W3 B h
    exact (photonLine_eq_zero_iff hv hg W1 W2 W3 B).mp h
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [photonLine_eq_zero_iff hv hg]
    exact ⟨rfl, rfl, 1, by ring, by ring⟩

/-- T1 (the K1 counterexample content, kept as a theorem so the
correction is checkable, not anecdotal): at `g = 0` the charged
directions are ALL massless — `higgsMassQuad 0 g' v W1 W2 0 0 = 0`
for every `W1, W2`. Hence the scoping's priced hypothesis
`(g, g′) ≠ (0, 0)`, read over the full four-field form, does NOT
give uniqueness: the W¹ direction at `(g, g′, v) = (0, 1, 1)` is a
massless direction off the photon line. Physically honest: `g = 0`
switches off the SU(2) coupling entirely. -/
theorem higgsMassQuad_charged_massless_of_g_eq_zero (g' v W1 W2 : ℝ) :
    higgsMassQuad 0 g' v W1 W2 0 0 = 0 := by
  rw [higgsMassQuad_eq]
  ring

/-- T1: at `v = 0` (unbroken phase) the mass form vanishes
identically — every direction is massless. The `v ≠ 0` hypothesis
in every exactness statement above is load-bearing, not
decoration. -/
theorem higgsMassQuad_v_eq_zero (g g' W1 W2 W3 B : ℝ) :
    higgsMassQuad g g' 0 W1 W2 W3 B = 0 := by
  rw [higgsMassQuad_eq]
  ring

end ThetLogos
