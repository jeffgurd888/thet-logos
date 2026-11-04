import Mathlib.Tactic
import ThetLogos.BridgeCompletion

/-!
# ThetLogos.ThermalChargePoisson — discrete Poisson on the bridge seat (T1)

HONESTY LEDGER (read before citing):

- Everything in this file is **T1 finite linear algebra** on the
  `BridgeLaplacian` seat: a finite vertex type `V`, a symmetric real
  weight function `w : V → V → ℝ`, and the operator
  `laplacianOp w F i = ∑ j, w i j * (F i - F j)`. Zero sorrys, no new
  axioms (headline theorems checked against the standard three:
  `propext`, `Classical.choice`, `Quot.sound`).
- THE THEOREM. This is the corpus's first electrostatics theorem, the
  finite statics of "charge separation creates structure" in the only
  form the finite level supports — **determination, not
  self-organization**: a charge distribution `g` on the vertices
  determines a potential `f` with `L f = g`, provided the compatibility
  condition `∑ i, g i = 0` holds; the potential is unique up to an
  additive constant, and its edge field (`dropVec f`, hence the Ohm
  flow `flowVec w f`) is unique on the nose. Charges + a fixed
  operator determine a potential and its field. Nothing here builds
  itself, and no dynamics is stated or implied.
- THE COMPATIBILITY CONDITION IS IN THE STATEMENT, NOT A RESCUE.
  The bare ∀-form — a potential exists for ARBITRARY `g` — is FALSE:
  a constant nonzero charge admits no potential, because
  `∑ i, (L F) i = 0` for every `F` (`sum_laplacianOp_eq_zero`) while
  `∑ i, g i ≠ 0`. That false form is the pre-registered kill
  **K-TCS-POIS**; it is not attempted anywhere in this file. The
  headline is therefore an *iff*: a potential exists **iff** the total
  charge vanishes (`exists_potential_iff_sum_eq_zero`).
- CONNECTIVITY, IN THE SEAT'S OWN LANDED FORM. The kernel of `L` is
  the constants via `BridgeLaplacian`'s energy route, whose
  all-support form is `eq_const_of_energy_eq_zero`: the hypotheses
  carried throughout are symmetry (`w i j = w j i`), nonnegativity
  (`0 ≤ w i j`), and strict positivity off the diagonal
  (`i ≠ j → 0 < w i j`). That positivity *is* the connectedness of
  the weighted graph at this seat — every pair of vertices conducts.
  No weaker connectivity notion is stated or needed.
- EXISTENCE ROUTE. `L` preserves the mean-zero subspace
  (`LinearMap.ker chargeSum`, by the current law), and its
  restriction to that subspace is injective: a mean-zero potential
  killed by `L` is constant (energy route) and a mean-zero constant
  is zero. A finite-dimensional injective endomorphism is surjective
  (`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`), and
  surjectivity onto the mean-zero subspace *is* Poisson existence.
  Equivalently, `LinearMap.range (lapLinFun w) = LinearMap.ker
  chargeSum` (`range_lapLinFun_eq_ker_chargeSum`).
- SEP FENCES, STANDING (Jeff's SEP-0 ruling, 2026-10-31). No operator
  acting on a thermal density matrix separates charge by its own
  action; nothing in this file claims one does. There is **no charge
  operator and no electromagnetic field object** at this seat: `g` is
  a real-valued function on vertices (data), `f` a real-valued
  function (the determined potential), `dropVec f` its edge
  differences. The word "charge" is the dossier's vocabulary for the
  input function; β appears nowhere — β is data elsewhere in the
  corpus and moves nothing here. This brick is T2 of the
  thermal-charge-separation scoping dossier (2026-11-04); the
  assertion's equivalence and division components are NOT addressed
  here and appear only as this fence.
- NOT CLAIMED: continuum Poisson/Maxwell theory, self-organization,
  any physical system. Finite graph statics only. NO CLAIM; dials 0/4.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. The total-charge functional and the mean-zero subspace -/

/-- The total-charge functional: `chargeSum F = ∑ i, F i`. Its kernel
is the mean-zero (compatibility) subspace of the Poisson problem. -/
def chargeSum : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun F := ∑ i, F i
  map_add' F G := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c F := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]

omit [DecidableEq V] in
theorem chargeSum_apply (F : V → ℝ) : chargeSum F = ∑ i, F i := rfl

/-- `lapLinFun` (BridgeCompletion's packaging of `laplacianOp` as a
linear map) applies as `laplacianOp`. -/
theorem lapLinFun_apply (w : V → V → ℝ) (F : V → ℝ) :
    lapLinFun w F = laplacianOp w F := rfl

omit [DecidableEq V] in
theorem mem_ker_chargeSum_iff (F : V → ℝ) :
    F ∈ LinearMap.ker chargeSum ↔ ∑ i, F i = 0 := by
  rw [LinearMap.mem_ker, chargeSum_apply]

/-! ## §2. `L` preserves the mean-zero subspace; the restriction -/

/-- The image of the Laplacian lies in the kernel of `chargeSum`:
the current law `sum_laplacianOp_eq_zero` in kernel form. It holds
for every `F`, mean-zero or not. -/
theorem lapLinFun_mapsTo_ker_chargeSum (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (F : V → ℝ) :
    lapLinFun w F ∈ LinearMap.ker chargeSum := by
  rw [mem_ker_chargeSum_iff, lapLinFun_apply]
  exact sum_laplacianOp_eq_zero w hw F

/-- The Laplacian restricted to the mean-zero subspace, as an
endomorphism of it: codomain restriction to the kernel of
`chargeSum`, precomposed with the subtype inclusion. -/
noncomputable def lapRestrict (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i) :
    (LinearMap.ker (chargeSum : (V → ℝ) →ₗ[ℝ] ℝ)) →ₗ[ℝ]
      (LinearMap.ker (chargeSum : (V → ℝ) →ₗ[ℝ] ℝ)) :=
  ((lapLinFun w).codRestrict
    (LinearMap.ker (chargeSum : (V → ℝ) →ₗ[ℝ] ℝ))
    (fun F => lapLinFun_mapsTo_ker_chargeSum w hw F)) ∘ₗ
    (LinearMap.ker (chargeSum : (V → ℝ) →ₗ[ℝ] ℝ)).subtype

theorem lapRestrict_coe (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (F : LinearMap.ker chargeSum) :
    (lapRestrict w hw F : V → ℝ) = laplacianOp w (F : V → ℝ) := rfl

/-! ## §3. The kernel of `L` is the constants (energy route) -/

/-- If `L F = 0` then `F` is constant: the kernel characterization
consumed from `BridgeLaplacian.eq_const_of_energy_eq_zero` — zero
energy forces constancy on the (fully conducting) support. -/
theorem eq_const_of_laplacianOp_eq_zero (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (F : V → ℝ)
    (hF : laplacianOp w F = 0) : ∀ i j, F i = F j := by
  apply eq_const_of_energy_eq_zero w hw hw0 hpos F
  rw [hF]
  simp

/-! ## §4. The restriction is injective -/

/-- A mean-zero element of the kernel of the restriction is zero:
constant (by §3) and mean-zero, and a mean-zero constant on a
nonempty vertex set vanishes. -/
theorem eq_zero_of_lapRestrict_eq_zero [Nonempty V] (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (F : LinearMap.ker chargeSum)
    (hF : lapRestrict w hw F = 0) : F = 0 := by
  obtain ⟨a⟩ := (inferInstance : Nonempty V)
  have hL : laplacianOp w (F : V → ℝ) = 0 := by
    have h := congrArg Subtype.val hF
    rw [lapRestrict_coe] at h
    exact h
  have hconst : ∀ i j, (F : V → ℝ) i = (F : V → ℝ) j :=
    eq_const_of_laplacianOp_eq_zero w hw hw0 hpos _ hL
  have hsum : ∑ i, (F : V → ℝ) i = 0 := by
    have h2 : (F : V → ℝ) ∈ LinearMap.ker chargeSum := F.2
    rwa [mem_ker_chargeSum_iff] at h2
  have hsum' : ∑ i, (F : V → ℝ) i
      = (Fintype.card V : ℝ) * (F : V → ℝ) a := by
    rw [Finset.sum_congr rfl (fun i _ => hconst i a), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  rw [hsum] at hsum'
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := V)).ne'
  have hFa : (F : V → ℝ) a = 0 := by
    rcases mul_eq_zero.mp hsum'.symm with h | h
    · exact absurd h hcard
    · exact h
  apply Subtype.ext
  funext i
  show (F : V → ℝ) i = (0 : V → ℝ) i
  rw [hconst i a, hFa, Pi.zero_apply]

/-- The restriction of `L` to the mean-zero subspace is injective. -/
theorem lapRestrict_injective [Nonempty V] (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) :
    Function.Injective (lapRestrict w hw) := by
  intro F G hFG
  have hsub : lapRestrict w hw (F - G) = 0 := by
    rw [map_sub, hFG, sub_self]
  have h0 := eq_zero_of_lapRestrict_eq_zero w hw hw0 hpos (F - G) hsub
  exact sub_eq_zero.mp h0

/-! ## §5. Existence: the discrete Poisson theorem -/

/-- **Existence.** Every mean-zero charge distribution admits a
potential: `∑ i, g i = 0 → ∃ f, L f = g`. Surjectivity of the
restriction (§4 + finite dimensionality) at the element `g`. -/
theorem exists_potential_of_sum_eq_zero (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g : V → ℝ)
    (hg : ∑ i, g i = 0) : ∃ f, laplacianOp w f = g := by
  rcases isEmpty_or_nonempty V with hE | hNE
  · have := hE
    exact ⟨0, funext fun i => (IsEmpty.false i).elim⟩
  · have := hNE
    have hinj := lapRestrict_injective w hw hw0 hpos
    have hsurj : Function.Surjective (lapRestrict w hw) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj
    obtain ⟨F, hF⟩ := hsurj ⟨g, by
      rw [LinearMap.mem_ker, chargeSum_apply]; exact hg⟩
    refine ⟨(F : V → ℝ), ?_⟩
    have h := congrArg Subtype.val hF
    rw [lapRestrict_coe] at h
    exact h

/-- **Range = compatibility.** The range of the Laplacian is exactly
the mean-zero subspace: every value of `L` has total zero, and every
total-zero function is a value of `L`. -/
theorem range_lapLinFun_eq_ker_chargeSum (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) :
    LinearMap.range (lapLinFun w) = LinearMap.ker chargeSum := by
  apply le_antisymm
  · rintro g ⟨f, rfl⟩
    rw [LinearMap.mem_ker, chargeSum_apply, lapLinFun_apply]
    exact sum_laplacianOp_eq_zero w hw f
  · intro g hg
    rw [mem_ker_chargeSum_iff] at hg
    obtain ⟨f, hf⟩ := exists_potential_of_sum_eq_zero w hw hw0 hpos g hg
    exact ⟨f, by rw [lapLinFun_apply]; exact hf⟩

/-- **The discrete Poisson theorem (iff form).** A potential for `g`
exists if and only if the total charge vanishes. The (⇒) direction
is the current law; the (⇐) direction is §5 existence. The bare
∀-form without the condition is false (K-TCS-POIS) and is not
stated. -/
theorem exists_potential_iff_sum_eq_zero (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g : V → ℝ) :
    (∃ f, laplacianOp w f = g) ↔ ∑ i, g i = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    exact sum_laplacianOp_eq_zero w hw f
  · exact exists_potential_of_sum_eq_zero w hw hw0 hpos g

/-! ## §6. Uniqueness modulo constants; the field is unique -/

/-- **Uniqueness modulo constants.** Two potentials for the same
charge differ by an additive constant: their difference is killed
by `L`, hence constant by §3. -/
theorem exists_add_const_of_laplacianOp_eq (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (f f' : V → ℝ)
    (h : laplacianOp w f = laplacianOp w f') :
    ∃ c : ℝ, ∀ i, f' i = f i + c := by
  have hD : ∀ i j, (f' - f) i = (f' - f) j :=
    eq_const_of_laplacianOp_eq_zero w hw hw0 hpos _
      (by rw [laplacianOp_sub, h, sub_self])
  rcases isEmpty_or_nonempty V with hE | hNE
  · have := hE
    exact ⟨0, fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨a⟩ := hNE
    refine ⟨(f' - f) a, fun i => ?_⟩
    have hi := hD i a
    simp only [Pi.sub_apply] at hi
    show f' i = f i + (f' a - f a)
    linarith

/-- **The edge field is unique on the nose.** Two potentials for the
same charge have the same drop (coboundary) — the additive constant
cancels in every edge difference. -/
theorem dropVec_eq_of_laplacianOp_eq (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (f f' : V → ℝ)
    (h : laplacianOp w f = laplacianOp w f') :
    dropVec f' = dropVec f := by
  obtain ⟨c, hc⟩ := exists_add_const_of_laplacianOp_eq w hw hw0 hpos f f' h
  funext i j
  rw [dropVec_apply, dropVec_apply, hc i, hc j]
  ring

/-- **The Ohm flow is unique on the nose.** Two potentials for the
same charge drive the same current field. -/
theorem flowVec_eq_of_laplacianOp_eq (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (f f' : V → ℝ)
    (h : laplacianOp w f = laplacianOp w f') :
    flowVec w f' = flowVec w f := by
  obtain ⟨c, hc⟩ := exists_add_const_of_laplacianOp_eq w hw hw0 hpos f f' h
  funext i j
  rw [flowVec_apply, flowVec_apply, hc i, hc j]
  ring

/-- **Pinned uniqueness.** Two potentials for the same charge that
agree at one vertex agree everywhere: pinning one value kills the
constant freedom. -/
theorem potential_eq_of_laplacianOp_eq_of_apply_eq (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (f f' : V → ℝ)
    (h : laplacianOp w f = laplacianOp w f') {a : V}
    (ha : f' a = f a) : f' = f := by
  obtain ⟨c, hc⟩ := exists_add_const_of_laplacianOp_eq w hw hw0 hpos f f' h
  have hc0 : c = 0 := by
    have h1 := hc a
    rw [ha] at h1
    linarith
  funext i
  rw [hc i, hc0, add_zero]

/-- **Normalization freedom.** A potential for `g` can be chosen with
any prescribed value at any prescribed vertex: shift the §5
potential by a constant, which `L` kills (`laplacianOp_const`). -/
theorem exists_potential_with_value (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g : V → ℝ)
    (hg : ∑ i, g i = 0) (a : V) (v : ℝ) :
    ∃ f, laplacianOp w f = g ∧ f a = v := by
  obtain ⟨f, hf⟩ := exists_potential_of_sum_eq_zero w hw hw0 hpos g hg
  refine ⟨fun i => f i + (v - f a), ?_, by
    show f a + (v - f a) = v; ring⟩
  have hfun : (fun i => f i + (v - f a)) = f + (fun _ => v - f a) := rfl
  rw [hfun, laplacianOp_add, laplacianOp_const, add_zero]
  exact hf

/-- **The discrete Poisson package.** For a mean-zero charge `g`:
a potential exists, it is unique up to an additive constant, and
its edge field is unique outright. -/
theorem discrete_poisson (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g : V → ℝ)
    (hg : ∑ i, g i = 0) :
    ∃ f, laplacianOp w f = g ∧
      (∀ f', laplacianOp w f' = g → ∃ c : ℝ, ∀ i, f' i = f i + c) ∧
      (∀ f', laplacianOp w f' = g → dropVec f' = dropVec f) := by
  obtain ⟨f, hf⟩ := exists_potential_of_sum_eq_zero w hw hw0 hpos g hg
  refine ⟨f, hf, ?_, ?_⟩
  · intro f' hf'
    exact exists_add_const_of_laplacianOp_eq w hw hw0 hpos f f'
      (by rw [hf, hf'])
  · intro f' hf'
    exact dropVec_eq_of_laplacianOp_eq w hw hw0 hpos f f'
      (by rw [hf, hf'])

end ThetLogos
