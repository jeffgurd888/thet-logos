import ThetLogos.GramDominance

/-
# ThetLogos.SepDoubledQuad - GD-2: Sep at the doubled quad,
twirl-free (SINGLE-LANE brick on the A >= 0 core chain)

**The fork (pack GD-2, governing memo
`scoping-gram-dominance-2026-10-29.md` sections 2 and 4.2).**
Order 5's only channel network is the doubled quad: a
primitive quad `C` with one column `P in C` doubled, type
(2,1,1,1), its moment `doubledQuadReMoment C P`
(`PlaneCrossingBeta5`). Sep-weak at order 5 asks: does the
doubled column's second copy separate to the opposite
network, giving `M = (positive scalar) * RN * star RN` in
diagonal form, as PW-5c-i's reindexing swap gave for every
multiplicity-free pattern (`quadCharMoment_eq_rowNetwork_mul`)?
WIN: the copies separate. KILL: a same-side copy forces a
cross term `RN1 * star RN2`, `RN1 != RN2` - Sep-weak is
FALSE at the first multiplicity. STALL: the expansion
technology resists - PARTIAL at the named seam, the fork
never forced.

**Outcome of this brick: PARTIAL, at the seam named
below.** No twirl is evaluated anywhere in this module
(twirl-free means twirl-free). What is landed:

1. `SepWeak2111`: Sep-weak at order 5, stated in GD-0's
   vocabulary for exactly this network type (per primitive
   quad `C`, per doubled column `P in C`). Registered,
   NOT asserted. Its diagonal nonnegativity consequence is
   proved (`sepWeak2111_diag_nonneg`): Sep-weak would force
   every doubled moment's diagonal to be nonnegative, so
   the kill criterion is a single certified negative
   diagonal value - none is exhibited here.
2. The full pattern (subset) expansion of the doubled
   moment, `doubledQuadReMoment_eq_sum_doubledCharMoment`:
   the doubled moment is `2^{-(|C|+1)}` times the real part
   of the sum of the 32 doubled character moments
   `doubledCharMoment C P t eps` over patterns `t subset C`
   and the second copy's side `eps : Bool`. This is the
   R1-ready expansion, proved by the telescope's subset
   technology (the multiset form of
   `quadReMoment_eq_sum_quadCharMoment`).
3. The copy-side split of that expansion
   (`doubledSum_eq_same_add_opp`): the 32 terms divide
   into the OPPOSITE-copies terms (the first copy of `P`
   plain and the second conjugated, or vice versa) and the
   SAME-SIDE terms (both copies plain, or both
   conjugated). At a primitive quad each family has
   exactly 16 terms (`sameSide_count_primitive`,
   `oppSide_count_primitive`). The same-side terms carry
   the doubled column's character SQUARED on one side:
   `doubledCharMoment_sq_plain` exhibits the factor
   `chi_P^2`, `doubledCharMoment_sq_conj` the factor
   `star(chi_P)^2`, inside the moment's integrand.
4. The conjugation pairing survives doubling
   (`doubledCharMoment_compl`): complementary patterns
   with flipped second-copy side are conjugate on the
   diagonal, the doubled form of `quadCharMoment_compl`.

**The named seam (why the fork is not forced here).**
PW-5c-i's split runs through the R1 entry expansion: each
site of the ordered quad carries exactly TWO incident
entry factors, and the owned pair evaluations
(`integral_entryFac_mul`) split each site integral into a
row value times a column value. At the doubled column's
two sites, the doubled network carries THREE incident
entry factors - the neighbouring column's factor and BOTH
copies of the doubled column's factor. Splitting either
sub-sum of item 3 into `RN * star RN` therefore requires
evaluating a triple site integral, the degree-(2,1) triple
twirl of TW-1, which no module in the tree owns (the same
seam B5-1/B5-2 name for the beta5 sign). Per this brick's
discipline, that is the stall seam: no twirl is evaluated,
no cross term is exhibited, and the same-side family's
presence (16 of 32 terms, squared factors exhibited) is
recorded as the precise obstruction locus - it is NOT
dressed as a kill, because a sum of same-side terms is
not yet a proved unavoidable `RN1 * star RN2` cross term
in the contracted network.

**Registration against GD-0.** Sep-weak at order 5 is
OPEN after this brick: neither proved (WIN) nor refuted
(KILL). It does NOT prove GD-global at 5 (GD-1's cone
question), does not touch GD-strong / GD-kernel / GD-cmp
as registered in `ThetLogos.GramDominance`, and does not
touch the A >= 0 core claim, which is not a brick.

**Fences.** NO CLAIM. Parts of the Clay Yang-Mills
statement closed by this module: 0. Dials: 0/4.
Scope: the (2,1,1,1) network type at order 5 only; the
all-orders Sep-weak statement is NOT claimed.
-/

open MeasureTheory Finset

namespace ThetLogos

section SepDoubledQuad

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-! ## Sep-weak at order 5, registered in GD-0's vocabulary -/

/-- **Sep-weak at order 5 for the (2,1,1,1) network**
(registered target; asserted nowhere). For every
primitive quad `C` and every doubled column `P in C`
there are a positive real scalar and a row network
`RN` (a complex-valued function of the diagonal link
configuration) with the doubled moment in diagonal
form `M = scalar * RN * star RN`, i.e.
`doubledQuadReMoment C P u u = scalar * ||RN u||^2`.
This is memo section 2.2's Sep-weak scoped to exactly
the first multiplicity; no other network type and no
other order is stated. -/
def SepWeak2111 : Prop :=
  ∀ (C : Finset (LayerColumn N)), C ∈ primitiveQuads →
    ∀ P ∈ C, ∃ (c : ℝ) (RN : (LayerLink N → G) → ℂ),
    0 < c ∧ ∀ u : LayerLink N → G,
      doubledQuadReMoment ρ μG C P u u = c * ‖RN u‖ ^ 2

/-- **The kill criterion Sep-weak carries.** If
Sep-weak at order 5 held, every doubled moment's
diagonal would be nonnegative. Hence one certified
negative value `doubledQuadReMoment C P u u < 0` at a
primitive quad would refute `SepWeak2111` - the seat
evaluation form of the pack's KILL fork. (No such value
is exhibited in this module.) -/
theorem sepWeak2111_diag_nonneg (hSep : SepWeak2111 (N := N) ρ μG)
    {C : Finset (LayerColumn N)} (hC : C ∈ primitiveQuads)
    {P : LayerColumn N} (hP : P ∈ C) (u : LayerLink N → G) :
    0 ≤ doubledQuadReMoment ρ μG C P u u := by
  obtain ⟨c, RN, hc, hRN⟩ := hSep C hC P hP
  rw [hRN u]
  exact mul_nonneg hc.le (sq_nonneg _)

/-! ## The doubled character moments -/

/-- **The doubled character moment** of a quad support
`C`, doubled column `P`, pattern `t subset C`, and the
second copy's side `eps`: the stratum integral of the
pattern integrand of `quadCharMoment C t` times ONE
MORE character factor of the doubled column - plain
(`eps = true`) or conjugated (`eps = false`). The
first copy of `P` is the one inside the pattern
integrand (plain iff `P in t`); `eps` is the second
copy. Summed over all `(t, eps)` these are the atoms
of the doubled moment's subset expansion, exactly as
`quadCharMoment`'s patterns are the atoms of
`quadReMoment`. -/
noncomputable def doubledCharMoment (C : Finset (LayerColumn N))
    (P : LayerColumn N) (t : Finset (LayerColumn N)) (eps : Bool)
    (u u' : LayerLink N → G) : ℂ :=
  ∫ α, (∏ Q ∈ t, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))
      * (∏ Q ∈ C \ t, star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)))
      * cond eps (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
          (star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)))
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- The pointwise integrand of a doubled character
moment, named for the proofs below. -/
noncomputable def doubledCharIntegrand (C : Finset (LayerColumn N))
    (P : LayerColumn N) (t : Finset (LayerColumn N)) (eps : Bool)
    (u u' : LayerLink N → G) (α : LayerSite N → G) : ℂ :=
  (∏ Q ∈ t, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))
    * (∏ Q ∈ C \ t, star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)))
    * cond eps (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
        (star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)))

theorem doubledCharMoment_def (C : Finset (LayerColumn N))
    (P : LayerColumn N) (t : Finset (LayerColumn N)) (eps : Bool)
    (u u' : LayerLink N → G) :
    doubledCharMoment ρ μG C P t eps u u'
      = ∫ α, doubledCharIntegrand ρ C P t eps u u' α
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
  rfl

/-! ## Measurability and integrability of the doubled integrand -/

private theorem measurable_charFn_colWord'
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P : LayerColumn N) :
    Measurable (fun α : LayerSite N → G =>
      charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)) :=
  (measurable_charFn ρ hρcont).comp (measurable_colWord u u' P.1 P.2.1 P.2.2)

private theorem measurable_doubledCharIntegrand
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (C : Finset (LayerColumn N)) (P : LayerColumn N)
    (t : Finset (LayerColumn N)) (eps : Bool)
    (u u' : LayerLink N → G) :
    Measurable (doubledCharIntegrand ρ C P t eps u u') := by
  have h1 : Measurable (fun α : LayerSite N → G =>
      ∏ Q ∈ t, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)) :=
    Finset.measurable_prod _ fun Q _ =>
      measurable_charFn_colWord' ρ hρcont u u' Q
  have h2 : Measurable (fun α : LayerSite N → G =>
      ∏ Q ∈ C \ t, star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))) :=
    Finset.measurable_prod _ fun Q _ =>
      continuous_star.measurable.comp (measurable_charFn_colWord' ρ hρcont u u' Q)
  have h3 : Measurable (fun α : LayerSite N → G =>
      cond eps (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
        (star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)))) := by
    cases eps
    · exact continuous_star.measurable.comp
        (measurable_charFn_colWord' ρ hρcont u u' P)
    · exact measurable_charFn_colWord' ρ hρcont u u' P
  exact (h1.mul h2).mul h3

private theorem integrable_doubledCharIntegrand
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (C : Finset (LayerColumn N)) (P : LayerColumn N)
    (t : Finset (LayerColumn N)) (ht : t ⊆ C) (eps : Bool)
    (u u' : LayerLink N → G) :
    Integrable (doubledCharIntegrand ρ C P t eps u u')
      (Measure.pi fun _ : LayerSite N => μG) := by
  refine Integrable.of_bound
    (measurable_doubledCharIntegrand ρ hρcont C P t eps u u').aestronglyMeasurable
    ((d : ℝ) ^ (C.card + 1)) (Filter.Eventually.of_forall fun α => ?_)
  have hnorm1 : ‖∏ Q ∈ t, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)‖
      ≤ (d : ℝ) ^ t.card := by
    calc ‖∏ Q ∈ t, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)‖
        ≤ ∏ Q ∈ t, ‖charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)‖ :=
          Finset.norm_prod_le t _
      _ ≤ ∏ _Q ∈ t, (d : ℝ) :=
          Finset.prod_le_prod₀ (fun Q _ => norm_nonneg _)
            (fun Q _ => norm_charFn_le ρ _)
      _ = (d : ℝ) ^ t.card := by rw [Finset.prod_const]
  have hnorm2 : ‖∏ Q ∈ C \ t,
        star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))‖
      ≤ (d : ℝ) ^ (C \ t).card := by
    calc ‖∏ Q ∈ C \ t, star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))‖
        ≤ ∏ Q ∈ C \ t, ‖star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))‖ :=
          Finset.norm_prod_le (C \ t) _
      _ ≤ ∏ _Q ∈ C \ t, (d : ℝ) :=
          Finset.prod_le_prod₀ (fun Q _ => by rw [norm_star]; exact norm_nonneg _)
            (fun Q _ => by rw [norm_star]; exact norm_charFn_le ρ _)
      _ = (d : ℝ) ^ (C \ t).card := by rw [Finset.prod_const]
  have hnorm3 : ‖cond eps (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
        (star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)))‖ ≤ (d : ℝ) := by
    cases eps
    · simpa using norm_charFn_le ρ (colWord u u' P.1 P.2.1 P.2.2 α)
    · exact norm_charFn_le ρ _
  have hcard : t.card + (C \ t).card = C.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr ht]
    exact Nat.add_sub_cancel' (Finset.card_le_card ht)
  calc ‖doubledCharIntegrand ρ C P t eps u u' α‖
      = ‖(∏ Q ∈ t, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))
          * (∏ Q ∈ C \ t, star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)))
          * cond eps (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
            (star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)))‖ := rfl
    _ = ‖∏ Q ∈ t, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)‖
          * ‖∏ Q ∈ C \ t, star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))‖
          * ‖cond eps (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
            (star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)))‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ (d : ℝ) ^ t.card * (d : ℝ) ^ (C \ t).card * (d : ℝ) :=
        mul_le_mul (mul_le_mul hnorm1 hnorm2
          (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg d) _))
          hnorm3 (norm_nonneg _)
          (mul_nonneg (pow_nonneg (Nat.cast_nonneg d) _)
            (pow_nonneg (Nat.cast_nonneg d) _))
    _ = (d : ℝ) ^ (C.card + 1) := by
        rw [← pow_add, hcard, pow_succ]

/-! ## Conjugation pairing for the doubled moments -/

/-- **Conjugation pairing, doubled form.** The doubled
moment of the complementary pattern with the second
copy's side flipped is the conjugate of the doubled
moment: the integrand at `(C \ t, !eps)` is pointwise
the conjugate of the integrand at `(t, eps)`, since
`C \ (C \ t) = t` and conjugation exchanges the plain
and conjugated factors, second copy included. The
doubled form of `quadCharMoment_compl`. -/
theorem doubledCharMoment_compl {C t : Finset (LayerColumn N)}
    (ht : t ⊆ C) (P : LayerColumn N) (eps : Bool)
    (u u' : LayerLink N → G) :
    doubledCharMoment ρ μG C P (C \ t) (!eps) u u'
      = star (doubledCharMoment ρ μG C P t eps u u') := by
  classical
  have hsd : C \ (C \ t) = t := by
    ext x
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hxC, hx⟩
      by_contra hxt
      exact hx ⟨hxC, hxt⟩
    · intro hxt
      exact ⟨ht hxt, fun h => h.2 hxt⟩
  have hpt : ∀ α : LayerSite N → G,
      doubledCharIntegrand ρ C P (C \ t) (!eps) u u' α
        = star (doubledCharIntegrand ρ C P t eps u u' α) := by
    intro α
    have hcond : cond (!eps) (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
          (star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)))
        = star (cond eps (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
            (star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)))) := by
      cases eps <;> simp
    show (∏ Q ∈ C \ t, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))
          * (∏ Q ∈ C \ (C \ t), star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)))
          * cond (!eps) _ _
        = star ((∏ Q ∈ t, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))
          * (∏ Q ∈ C \ t, star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)))
          * cond eps _ _)
    rw [hsd, hcond]
    simp only [star_mul, star_prod, star_star]
    ring
  have hstar : star (∫ α, doubledCharIntegrand ρ C P t eps u u' α
          ∂(Measure.pi fun _ : LayerSite N => μG))
      = ∫ α, star (doubledCharIntegrand ρ C P t eps u u' α)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
    simpa only [starRingEnd_apply] using
      (integral_conj (μ := (Measure.pi fun _ : LayerSite N => μG))
        (f := doubledCharIntegrand ρ C P t eps u u')).symm
  calc doubledCharMoment ρ μG C P (C \ t) (!eps) u u'
      = ∫ α, doubledCharIntegrand ρ C P (C \ t) (!eps) u u' α
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        doubledCharMoment_def ρ μG C P (C \ t) (!eps) u u'
    _ = ∫ α, star (doubledCharIntegrand ρ C P t eps u u' α)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = star (∫ α, doubledCharIntegrand ρ C P t eps u u' α
          ∂(Measure.pi fun _ : LayerSite N => μG)) := hstar.symm
    _ = star (doubledCharMoment ρ μG C P t eps u u') :=
        congrArg star (doubledCharMoment_def ρ μG C P t eps u u').symm

/-! ## The subset expansion of the doubled moment -/

/-- One real character value as a complex number is the
average of the character and its conjugate (the
telescope's `ofReal_colRe_eq`, restated for the doubled
integrand). -/
private theorem ofReal_colRe_eq' (u u' : LayerLink N → G) (Q : LayerColumn N)
    (α : LayerSite N → G) :
    ((colRe ρ u u' Q α : ℝ) : ℂ)
      = (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)
        + star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))) * (2 : ℂ)⁻¹ := by
  have havg : ∀ z : ℂ, ((z.re : ℂ)) = (z + star z) * (2 : ℂ)⁻¹ := by
    intro z
    rw [show ((z.re : ℂ)) = (z + (starRingEnd ℂ) z) / 2 from
        RCLike.re_eq_add_conj z, div_eq_mul_inv, starRingEnd_apply]
  calc ((colRe ρ u u' Q α : ℝ) : ℂ)
      = ((charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)).re : ℂ) := rfl
    _ = (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)
          + star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))) * (2 : ℂ)⁻¹ :=
        havg _

/-- The pointwise subset expansion of the doubled
integrand, as a complex identity: the product of the
quad's real characters times the doubled column's real
character is `2^{-(|C|+1)}` times the sum of the doubled
integrands over all patterns and second-copy sides. -/
private theorem prod_colRe_mul_colRe_eq (C : Finset (LayerColumn N))
    (P : LayerColumn N) (u u' : LayerLink N → G) (α : LayerSite N → G) :
    (((∏ Q ∈ C, colRe ρ u u' Q α) * colRe ρ u u' P α : ℝ) : ℂ)
      = ((2 : ℂ)⁻¹) ^ (C.card + 1) * ∑ t ∈ C.powerset, ∑ eps : Bool,
          doubledCharIntegrand ρ C P t eps u u' α := by
  have hfac : ∀ Q ∈ C, ((colRe ρ u u' Q α : ℝ) : ℂ)
      = (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)
        + star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))) * (2 : ℂ)⁻¹ :=
    fun Q _ => ofReal_colRe_eq' ρ u u' Q α
  have hP : ((colRe ρ u u' P α : ℝ) : ℂ)
      = (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)
        + star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))) * (2 : ℂ)⁻¹ :=
    ofReal_colRe_eq' ρ u u' P α
  have hsumP : (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)
        + star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)))
      = ∑ eps : Bool, cond eps (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
          (star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))) := by
    rw [Fintype.sum_bool]
    simp [add_comm]
  have hsum_eq : (∑ t ∈ C.powerset, ∑ eps : Bool,
        doubledCharIntegrand ρ C P t eps u u' α)
      = ∑ t ∈ C.powerset, ∑ eps : Bool,
        (∏ Q ∈ t, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))
          * (∏ Q ∈ C \ t, star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)))
          * cond eps (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
            (star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))) :=
    Finset.sum_congr rfl fun t _ =>
      Finset.sum_congr rfl fun eps _ => rfl
  rw [Complex.ofReal_mul, Complex.ofReal_prod,
    Finset.prod_congr rfl hfac, hP, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_add, hsumP, hsum_eq, ← Finset.sum_mul_sum, pow_succ]
  ring

/-- **The subset expansion of the doubled moment
(GD-2's landed expansion).** For `P in C`, the doubled
`(2,1,1,1)` moment is `2^{-(|C|+1)}` times the real part
of the sum of the doubled character moments over all
patterns `t subset C` and both second-copy sides - the
multiset form of the telescope's stage-one contraction
formula, with `2^{|C|+1} = 32` terms at a primitive
quad (`|C| = 4`). No site integral is evaluated: this
is the expansion the R1 entry technology would consume,
stated before any split. -/
theorem doubledQuadReMoment_eq_sum_doubledCharMoment
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (C : Finset (LayerColumn N)) (P : LayerColumn N) (hPC : P ∈ C)
    (u : LayerLink N → G) :
    doubledQuadReMoment ρ μG C P u u
      = ((2 : ℝ)⁻¹) ^ (C.card + 1)
          * (∑ t ∈ C.powerset, ∑ eps : Bool,
              doubledCharMoment ρ μG C P t eps u u).re := by
  have hcast : ((doubledQuadReMoment ρ μG C P u u : ℝ) : ℂ)
      = ((2 : ℂ)⁻¹) ^ (C.card + 1)
          * ∑ t ∈ C.powerset, ∑ eps : Bool,
              doubledCharMoment ρ μG C P t eps u u := by
    have h1 : ((doubledQuadReMoment ρ μG C P u u : ℝ) : ℂ)
        = ∫ α, (((∏ Q ∈ C, colRe ρ u u Q α) * colRe ρ u u P α : ℝ) : ℂ)
            ∂(Measure.pi fun _ : LayerSite N => μG) := by
      have hofr : (∫ α, (((∏ Q ∈ C, colRe ρ u u Q α)
              * colRe ρ u u P α : ℝ) : ℂ)
            ∂(Measure.pi fun _ : LayerSite N => μG))
          = ((∫ α, (∏ Q ∈ C, colRe ρ u u Q α) * colRe ρ u u P α
              ∂(Measure.pi fun _ : LayerSite N => μG) : ℝ) : ℂ) :=
        integral_ofReal
      rw [hofr, doubledQuadReMoment_eq_mul ρ μG hPC u u]
    have hsum : (∫ α, ∑ t ∈ C.powerset, ∑ eps : Bool,
          doubledCharIntegrand ρ C P t eps u u α
            ∂(Measure.pi fun _ : LayerSite N => μG))
        = ∑ t ∈ C.powerset, ∑ eps : Bool,
            doubledCharMoment ρ μG C P t eps u u := by
      rw [MeasureTheory.integral_finsetSum C.powerset (fun t ht =>
        integrable_finset_sum Finset.univ (fun eps _ =>
          integrable_doubledCharIntegrand ρ μG hρcont C P t
            (Finset.mem_powerset.mp ht) eps u u))]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [MeasureTheory.integral_finsetSum Finset.univ (fun eps _ =>
        integrable_doubledCharIntegrand ρ μG hρcont C P t
          (Finset.mem_powerset.mp ht) eps u u)]
      exact Finset.sum_congr rfl fun eps _ =>
        (doubledCharMoment_def ρ μG C P t eps u u).symm
    calc ((doubledQuadReMoment ρ μG C P u u : ℝ) : ℂ)
        = ∫ α, ((2 : ℂ)⁻¹) ^ (C.card + 1)
            * ∑ t ∈ C.powerset, ∑ eps : Bool,
              doubledCharIntegrand ρ C P t eps u u α
            ∂(Measure.pi fun _ : LayerSite N => μG) := by
          rw [h1]
          exact integral_congr_ae (Filter.Eventually.of_forall fun α =>
            prod_colRe_mul_colRe_eq ρ C P u u α)
      _ = ((2 : ℂ)⁻¹) ^ (C.card + 1)
            * ∫ α, ∑ t ∈ C.powerset, ∑ eps : Bool,
                doubledCharIntegrand ρ C P t eps u u α
              ∂(Measure.pi fun _ : LayerSite N => μG) :=
          integral_const_mul _ _
      _ = ((2 : ℂ)⁻¹) ^ (C.card + 1)
            * ∑ t ∈ C.powerset, ∑ eps : Bool,
                doubledCharMoment ρ μG C P t eps u u := by
          rw [hsum]
  have hre := congrArg Complex.re hcast
  rw [Complex.ofReal_re] at hre
  have hsc : (((2 : ℂ)⁻¹) ^ (C.card + 1)
        * ∑ t ∈ C.powerset, ∑ eps : Bool,
            doubledCharMoment ρ μG C P t eps u u).re
      = ((2 : ℝ)⁻¹) ^ (C.card + 1)
        * (∑ t ∈ C.powerset, ∑ eps : Bool,
            doubledCharMoment ρ μG C P t eps u u).re := by
    have hc : ((2 : ℂ)⁻¹) ^ (C.card + 1)
        = ((((2 : ℝ)⁻¹) ^ (C.card + 1) : ℝ) : ℂ) := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_inv,
        ← Complex.ofReal_pow]
    rw [hc]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_mul, sub_zero]
  rw [hsc] at hre
  exact hre

/-! ## The copy-side split of the expansion -/

/-- **Same side vs opposite sides, for the doubled
column's two copies.** In the term `(t, eps)` of the
expansion, the first copy of `P` is plain iff
`P in t` and conjugated iff `P notin t`; the second
copy is plain iff `eps = true`. The copies are on the
SAME side iff `eps = decide (P in t)`: both plain
(`P in t`, `eps = true`) or both conjugated
(`P notin t`, `eps = false`). Otherwise they are on
opposite sides. This is the fork of memo section 2.2,
read off the expansion's indices. -/
def sameSide2111 (P : LayerColumn N) (t : Finset (LayerColumn N))
    (eps : Bool) : Prop :=
  eps = decide (P ∈ t)

theorem sameSide2111_iff (P : LayerColumn N) (t : Finset (LayerColumn N))
    (eps : Bool) :
    sameSide2111 P t eps
      ↔ (P ∈ t ∧ eps = true) ∨ (P ∉ t ∧ eps = false) := by
  unfold sameSide2111
  cases eps <;> by_cases h : P ∈ t <;> simp [h]

/-- The **same-side sub-sum** of the doubled expansion:
the terms whose two copies of the doubled column land
on the same side. -/
noncomputable def doubledSameSum (C : Finset (LayerColumn N))
    (P : LayerColumn N) (u : LayerLink N → G) : ℂ :=
  ∑ t ∈ C.powerset, ∑ eps : Bool,
    if eps = decide (P ∈ t) then doubledCharMoment ρ μG C P t eps u u else 0

/-- The **opposite-copies sub-sum** of the doubled
expansion: the terms whose two copies of the doubled
column land on opposite sides. -/
noncomputable def doubledOppSum (C : Finset (LayerColumn N))
    (P : LayerColumn N) (u : LayerLink N → G) : ℂ :=
  ∑ t ∈ C.powerset, ∑ eps : Bool,
    if eps = decide (P ∈ t) then 0 else doubledCharMoment ρ μG C P t eps u u

/-- **The copy-side split.** The full doubled sum of
the expansion theorem is the opposite-copies sub-sum
plus the same-side sub-sum, term by term. This is the
partial split this brick lands: the expansion separates
cleanly into the two families of the fork, and the
same-side family is the obstruction locus - converting
either family into a single `RN * star RN` is exactly
what the named seam (the triple site integral at the
doubled column's sites) blocks. -/
theorem doubledSum_eq_opp_add_same (C : Finset (LayerColumn N))
    (P : LayerColumn N) (u : LayerLink N → G) :
    (∑ t ∈ C.powerset, ∑ eps : Bool, doubledCharMoment ρ μG C P t eps u u)
      = doubledOppSum ρ μG C P u + doubledSameSum ρ μG C P u := by
  rw [doubledOppSum, doubledSameSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun eps _ => ?_
  by_cases h : eps = decide (P ∈ t) <;> simp [h]

/-- **Counting the same-side family.** Among the
`2^{|C|+1}` index pairs `(t, eps)` of the expansion,
exactly `2^{|C|}` are same-side: the side condition
forces `eps` from `t`, leaving the pattern free. -/
theorem sameSide_count (C : Finset (LayerColumn N)) (P : LayerColumn N) :
    ((C.powerset ×ˢ Finset.univ).filter
      (fun p : Finset (LayerColumn N) × Bool =>
        p.2 = decide (P ∈ p.1))).card = 2 ^ C.card := by
  rw [Finset.card_filter, Finset.sum_product]
  have hinner : ∀ t : Finset (LayerColumn N),
      (∑ eps ∈ (Finset.univ : Finset Bool),
        if eps = decide (P ∈ t) then (1 : ℕ) else 0) = 1 := by
    intro t
    rw [Finset.sum_eq_single (decide (P ∈ t))]
    · simp
    · intro b _ hb
      exact if_neg hb
    · simp
  rw [Finset.sum_congr rfl (fun t _ => hinner t)]
  simp [Finset.card_powerset]

/-- **Counting the opposite-copies family.** The
remaining index pairs are also exactly `2^{|C|}`:
the two families of the fork are equinumerous. -/
theorem oppSide_count (C : Finset (LayerColumn N)) (P : LayerColumn N) :
    ((C.powerset ×ˢ Finset.univ).filter
      (fun p : Finset (LayerColumn N) × Bool =>
        ¬ p.2 = decide (P ∈ p.1))).card = 2 ^ C.card := by
  have htot : ((C.powerset ×ˢ Finset.univ).filter
        (fun p : Finset (LayerColumn N) × Bool =>
          p.2 = decide (P ∈ p.1))).card
      + ((C.powerset ×ˢ Finset.univ).filter
        (fun p : Finset (LayerColumn N) × Bool =>
          ¬ p.2 = decide (P ∈ p.1))).card
      = (C.powerset ×ˢ Finset.univ).card :=
    Finset.card_filter_add_card_filter_not _
  rw [sameSide_count C P, Finset.card_product, Finset.card_powerset,
    Finset.card_univ, Fintype.card_bool, ← pow_succ] at htot
  rw [pow_succ] at htot
  omega

/-- At a primitive quad (`|C| = 4`) the same-side
family has exactly **16** of the expansion's 32 terms. -/
theorem sameSide_count_primitive {C : Finset (LayerColumn N)}
    (hC : C ∈ primitiveQuads) (P : LayerColumn N) :
    ((C.powerset ×ˢ Finset.univ).filter
      (fun p : Finset (LayerColumn N) × Bool =>
        p.2 = decide (P ∈ p.1))).card = 16 := by
  have hcard : C.card = 4 := by
    rw [primitiveQuads, Finset.mem_filter] at hC
    exact hC.2.1
  calc ((C.powerset ×ˢ Finset.univ).filter
        (fun p : Finset (LayerColumn N) × Bool =>
          p.2 = decide (P ∈ p.1))).card
      = 2 ^ C.card := sameSide_count C P
    _ = 16 := by norm_num [hcard]

/-- At a primitive quad (`|C| = 4`) the
opposite-copies family has exactly **16** of the
expansion's 32 terms. -/
theorem oppSide_count_primitive {C : Finset (LayerColumn N)}
    (hC : C ∈ primitiveQuads) (P : LayerColumn N) :
    ((C.powerset ×ˢ Finset.univ).filter
      (fun p : Finset (LayerColumn N) × Bool =>
        ¬ p.2 = decide (P ∈ p.1))).card = 16 := by
  have hcard : C.card = 4 := by
    rw [primitiveQuads, Finset.mem_filter] at hC
    exact hC.2.1
  calc ((C.powerset ×ˢ Finset.univ).filter
        (fun p : Finset (LayerColumn N) × Bool =>
          ¬ p.2 = decide (P ∈ p.1))).card
      = 2 ^ C.card := oppSide_count C P
    _ = 16 := by norm_num [hcard]

/-! ## The same-side terms carry the character squared -/

/-- **Same-side, plain: the squared factor exhibited.**
For a same-side term with both copies plain
(`P in t`, `eps = true`), the doubled moment's
integrand is the pattern integrand with the doubled
column's character appearing TWICE on the plain side:
`chi_P^2` times the remaining pattern factors. In the
R1 entry expansion this is the factor whose two copies
would have to be split by a site integral at `P`'s
sites - the triple site integral of the seam. -/
theorem doubledCharMoment_sq_plain {C t : Finset (LayerColumn N)}
    {P : LayerColumn N} (hPt : P ∈ t) (u u' : LayerLink N → G) :
    doubledCharMoment ρ μG C P t true u u'
      = ∫ α, (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)) ^ 2
          * (∏ Q ∈ t.erase P, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))
          * (∏ Q ∈ C \ t, star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)))
        ∂(Measure.pi fun _ : LayerSite N => μG) := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
  show (∏ Q ∈ t, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))
        * (∏ Q ∈ C \ t, star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)))
        * cond true (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
          (star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)))
      = (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)) ^ 2
        * (∏ Q ∈ t.erase P, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))
        * (∏ Q ∈ C \ t, star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)))
  rw [Bool.cond_true, ← Finset.mul_prod_erase t
    (fun Q => charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)) hPt]
  ring

/-- **Same-side, conjugated: the squared factor
exhibited.** For a same-side term with both copies
conjugated (`P notin t`, `eps = false`), the doubled
moment's integrand carries `star(chi_P)^2` on the
conjugated side, times the remaining pattern factors. -/
theorem doubledCharMoment_sq_conj {C t : Finset (LayerColumn N)}
    {P : LayerColumn N} (hPC : P ∈ C) (hPt : P ∉ t)
    (u u' : LayerLink N → G) :
    doubledCharMoment ρ μG C P t false u u'
      = ∫ α, (star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))) ^ 2
          * (∏ Q ∈ t, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))
          * (∏ Q ∈ (C \ t).erase P,
              star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)))
        ∂(Measure.pi fun _ : LayerSite N => μG) := by
  have hPCt : P ∈ C \ t := Finset.mem_sdiff.mpr ⟨hPC, hPt⟩
  refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
  show (∏ Q ∈ t, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))
        * (∏ Q ∈ C \ t, star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)))
        * cond false (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))
          (star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)))
      = (star (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α))) ^ 2
        * (∏ Q ∈ t, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))
        * (∏ Q ∈ (C \ t).erase P,
            star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)))
  rw [Bool.cond_false, ← Finset.mul_prod_erase (C \ t)
    (fun Q => star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))) hPCt]
  ring

/-! ## The composed headline: expansion, split -/

/-- **GD-2 headline (PARTIAL at the named seam).** The
doubled `(2,1,1,1)` moment, in the copy-side split form
this brick lands: at any support `C` with `P in C`,

  `doubledQuadReMoment C P u u`
    `= 2^{-(|C|+1)} * Re (opposite-copies sum + same-side sum)`,

the two sub-sums of `doubledSum_eq_opp_add_same`, each
carrying `2^{|C|}` of the `2^{|C|+1}` expansion terms
(16 of 32 at a primitive quad). Neither sub-sum is
factored here: factoring either one into a single
`RN * star RN` through the R1 entry expansion requires
the triple site integral at the doubled column's two
sites (three incident entry factors: the neighbour's
and both copies'), the degree-(2,1) triple twirl owned
by no module in the tree - TW-1's object. Per the
brick's discipline no twirl is evaluated, so the fork
is NOT forced: Sep-weak at order 5 remains OPEN, the
same-side family (with its exhibited `chi_P^2` /
`star(chi_P)^2` factors) is the named obstruction
locus, and this is a PARTIAL, not a kill. -/
theorem doubledQuadReMoment_eq_opp_add_same
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (C : Finset (LayerColumn N)) (P : LayerColumn N) (hPC : P ∈ C)
    (u : LayerLink N → G) :
    doubledQuadReMoment ρ μG C P u u
      = ((2 : ℝ)⁻¹) ^ (C.card + 1)
          * (doubledOppSum ρ μG C P u + doubledSameSum ρ μG C P u).re := by
  rw [doubledQuadReMoment_eq_sum_doubledCharMoment ρ μG hρcont C P hPC u,
    doubledSum_eq_opp_add_same ρ μG C P u]

end SepDoubledQuad

#print axioms sepWeak2111_diag_nonneg
#print axioms doubledCharMoment_compl
#print axioms doubledQuadReMoment_eq_sum_doubledCharMoment
#print axioms doubledSum_eq_opp_add_same
#print axioms doubledQuadReMoment_eq_opp_add_same
#print axioms sameSide_count_primitive
#print axioms oppSide_count_primitive
#print axioms doubledCharMoment_sq_plain
#print axioms doubledCharMoment_sq_conj

end ThetLogos
