/-
# Brick TM-2 — pattern filter + closed form at `N = 2`
(Ternary Magnetism chain, brick 3; TM-0 gate PASSED, TM-1 shipped)

Commission: Jeff's TM chain commission (2026-11-05, "do it"), executing
TM-2 from the priced menu in
`~/workspace/your_files/ternary-magnetism-scoping-2026-11-05.md` (§7,
with §2.3 Steps 3–5 and the accident registry §2.5), fired after TM-1
integrated and shipped (census 13,573 strict / 506 modules).

**Scope — exactly this brick.**  The pattern machinery of the ZMod 3
character seat at the priced torus side `N = 2`:

* **Step 0 (ACC-TM-5 hygiene).**  The column ↔ layer-link
  correspondence `layerLinkOf` isolated as a proved bijection, in the
  fiberwise form the pattern arguments use — the binary engine read
  link values through it without isolating it.
* The **pattern type** `LayerColumn 2 → ZMod 3` (a branch per column:
  `0` = the constant term `a₃`, `1` = `b₃·χ(word)`, `2` = `b₃·χ̄(word)`),
  the **site exponent** `patternDiv₃ ε c` — the `ZMod 3` signed
  divergence of the pattern field (base contributions minus head
  contributions) — and its ℕ-valued exponent shadow `patternExp₃`,
  tied together by the divisibility bridge.
* The **stratum monomial lemma**: a pattern's stratum character
  collects fiberwise into site character powers of the divergence.
* The **mod-3 signed-divergence filter** (`stratum_average₃`, the
  `stratum_average` analog): the stratum average of a pattern's
  monomial is `1` iff the pattern is divergence-free at every site,
  else `0`.  A pattern survives iff `σ ∘ ε` is a divergence-free
  signed flow (a cycle flow over `ZMod 3`).
* The **pattern expansion** of the seat Boltzmann weight and the
  **closed form** `layerKernel_ternary`:
  `layerKernel seatμ₃ seatρ₃ β u u' = Σ_{ε : E(ε) ≡ 0} w_ε ·
  A_ε(u') · conj(A_ε(u))` with `w_ε = a₃^{24−|supp ε|} b₃^{|supp ε|}`.

**NOT in this brick** (later bricks, fired separately): TM-3 (the
Gram assembly + `layerKernelPos_ternary_seat` headline), TM-4 (the
FACT-analog decision — the gate already shows the excess
`K(1,1) − a₃²⁴ > 0`, T2).

**Kills armed.**  **K-TM-FILTER** — a pattern the filter keeps whose
stratum average is not `1`, or one it kills whose average is not `0`
(the filter identity false in the corpus's geometry, including via
the step-0 correspondence).  **K-TM-CLOSED** — closed-form mismatch
against TM-0's numbers at any probed `(β, u, u')` (gate ground truth:
closed form vs direct stratum sums ≤ `1.1e-16` on 8 pairs × 5 β;
filter verified exhaustively in exponent space; survivors at support
≤ 3 exactly 25 — the empty pattern and the 24 go/return equal-branch
pairs).

**The `N = 1` quarantine, cited in its LICENSE form** (TM-0 gate
report §5, refining ACC-TM-2): nothing at `N = 1` is wrong with the
filter or the closed form *as column-formula objects* — the closed
form there is internally exact and positivity is exhaustive.  What
is missing at `N = 1` is the **license**: the column decomposition
of `layerAction` (`Even N` in the landed tree, `2 ≤ N` in R1's
chain) that identifies the column formula with `layerKernel` at
all.  It is a license failure, not a closed-form failure.  This
brick lives at `N = 2`, where the license holds.

NO CLAIM; dials 0/4.  Magnetism grade (scoping §2.2): ternary
magnetism in the clock/Potts sense only.
-/

import ThetLogos.LayerKernelPosTernarySeat

open MeasureTheory Finset
open scoped ENNReal

namespace ThetLogos

/-! ## Step 0 (ACC-TM-5): the column ↔ layer-link correspondence -/

/-- **Step 0 — the `layerLinkOf` correspondence.**  The map sending a
column `(c, ν)` to its layer link is a bijection
`LayerColumn 2 ≃ LayerLink 2`: a column *is* a layer link, read
through its base site and direction.  Isolated as a proved lemma
(ACC-TM-5) rather than left as ambient practice — the fiberwise
pattern arguments below read configuration values through exactly
this map (`configChar₃ P u = seatChar₃ (u (layerLinkOf …))`). -/
theorem layerLinkOf_bijective :
    Function.Bijective
      (fun P : LayerColumn 2 => layerLinkOf P.1 P.2.1 P.2.2) := by
  constructor
  · intro P Q h
    have hval : (P.1.1, P.2.1) = (Q.1.1, Q.2.1) :=
      congrArg Subtype.val h
    rw [Prod.mk.injEq] at hval
    exact Prod.ext (Subtype.ext hval.1) (Subtype.ext hval.2)
  · intro ℓ
    exact ⟨(⟨ℓ.1.1, ℓ.2.1⟩, ⟨ℓ.1.2, ℓ.2.2⟩), Subtype.ext rfl⟩

/-- The correspondence in fiberwise (product) form: a product over
layer links is the product over columns of the pulled-back values. -/
theorem prod_layerLinkOf (f : LayerLink 2 → ℂ) :
    ∏ ℓ : LayerLink 2, f ℓ
      = ∏ P : LayerColumn 2, f (layerLinkOf P.1 P.2.1 P.2.2) :=
  (Fintype.prod_bijective _ layerLinkOf_bijective
    (fun P : LayerColumn 2 => f (layerLinkOf P.1 P.2.1 P.2.2)) f
    (fun _ => rfl)).symm

/-! ## Character power algebra at the seat -/

/-- The character squared is its conjugate: `χ(g)² = χ̄(g)` (the
ternary seat's branch `2` *is* the conjugate branch — ACC-TM-4's
load-bearing symmetry, in power form). -/
theorem seatChar₃_sq (g : Multiplicative (ZMod 3)) :
    (seatChar₃ g) ^ 2 = star (seatChar₃ g) := by
  rcases seatChar₃_cases g with h | h | h
  · rw [h]
    simp
  · rw [h, zetaC3_star]
  · rw [h]
    have h4 : (zetaC3 ^ 2) ^ 2 = zetaC3 := by
      calc (zetaC3 ^ 2) ^ 2 = zetaC3 ^ 3 * zetaC3 := by ring
        _ = zetaC3 := by rw [zetaC3_cube, one_mul]
    have hstar : star (zetaC3 ^ 2) = zetaC3 := by
      calc star (zetaC3 ^ 2) = (star zetaC3) ^ 2 := by rw [star_pow]
        _ = (zetaC3 ^ 2) ^ 2 := by rw [zetaC3_star]
        _ = zetaC3 := h4
    rw [h4, hstar]

/-- Inverse powers of the character are conjugate-branch powers:
`(χ(g)⁻¹)^k = χ(g)^((−k̂).val)` for `k̂ : ZMod 3` — the head-site
bookkeeping of the monomial lemma, where a column's head
contribution carries the *negated* branch. -/
theorem seatChar₃_inv_pow (g : Multiplicative (ZMod 3)) (k : ZMod 3) :
    ((seatChar₃ g)⁻¹) ^ k.val = (seatChar₃ g) ^ (-k).val := by
  rcases zmod3_cases k with hk | hk | hk
  · have e1 : k.val = 0 := by rw [hk]; rfl
    have e2 : (-k).val = 0 := by rw [hk]; rfl
    rw [e1, e2, pow_zero, pow_zero]
  · have e1 : k.val = 1 := by rw [hk]; rfl
    have e2 : (-k).val = 2 := by
      have : -k = 2 := by rw [hk]; decide
      rw [this]; rfl
    rw [e1, e2, pow_one, seatChar₃_sq, seatChar₃_star, seatChar₃_inv]
  · have e1 : k.val = 2 := by rw [hk]; rfl
    have e2 : (-k).val = 1 := by
      have : -k = 1 := by rw [hk]; decide
      rw [this]; rfl
    rw [e1, e2, pow_one]
    have h2 : ((seatChar₃ g)⁻¹) ^ 2 = ((seatChar₃ g) ^ 2)⁻¹ := by
      rw [inv_pow]
    rw [h2, seatChar₃_sq, seatChar₃_star, seatChar₃_inv, inv_inv]

/-! ## Patterns and the signed divergence -/

/-- The **site exponent** of a pattern `ε : LayerColumn 2 → ZMod 3`
at a site `c`: the `ZMod 3` **signed divergence** of the pattern
field — the branches of columns based at `c`, minus the branches of
columns whose head is `c` (each column an edge base → head; at the
binary seat the sign was invisible mod 2). -/
noncomputable def patternDiv₃ (ε : LayerColumn 2 → ZMod 3)
    (c : LayerSite 2) : ZMod 3 :=
  (∑ P ∈ Finset.univ.filter (fun P : LayerColumn 2 => P.1 = c), ε P)
    - ∑ P ∈ Finset.univ.filter
        (fun P : LayerColumn 2 => layerShift P.2.1 P.2.2 P.1 = c), ε P

/-- A pattern **survives** the stratum average iff its signed
divergence vanishes at every site — iff the signed pattern field is
a divergence-free flow (a cycle flow over `ZMod 3`). -/
noncomputable def patternSurvives₃ (ε : LayerColumn 2 → ZMod 3) : Prop :=
  ∀ c, patternDiv₃ ε c = 0

/-- Survival of a pattern is decidable. -/
noncomputable instance (ε : LayerColumn 2 → ZMod 3) :
    Decidable (patternSurvives₃ ε) :=
  Fintype.decidableForallFintype

/-- The ℕ-valued exponent shadow of the divergence: base branches
counted by their `ZMod 3` values, head branches by the values of
their *negations* — the exponent of `χ(α c)` in the pattern's
stratum monomial, before mod-3 reduction. -/
noncomputable def patternExp₃ (ε : LayerColumn 2 → ZMod 3)
    (c : LayerSite 2) : ℕ :=
  (∑ P ∈ Finset.univ.filter (fun P : LayerColumn 2 => P.1 = c),
      (ε P).val)
    + ∑ P ∈ Finset.univ.filter
        (fun P : LayerColumn 2 => layerShift P.2.1 P.2.2 P.1 = c),
        (-(ε P)).val

/-- **The divisibility bridge.**  The pattern survives at a site
iff `3` divides the ℕ exponent there: the exponent shadow casts
back to the divergence in `ZMod 3`. -/
theorem patternDiv₃_eq_zero_iff (ε : LayerColumn 2 → ZMod 3)
    (c : LayerSite 2) :
    patternDiv₃ ε c = 0 ↔ 3 ∣ patternExp₃ ε c := by
  have hcast : ((patternExp₃ ε c : ℕ) : ZMod 3) = patternDiv₃ ε c := by
    unfold patternExp₃ patternDiv₃
    rw [Nat.cast_add, Nat.cast_sum, Nat.cast_sum, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    exact congrArg₂ _
      (Finset.sum_congr rfl fun P _ => ZMod.natCast_zmod_val (ε P))
      (Finset.sum_congr rfl fun P _ => ZMod.natCast_zmod_val (-(ε P)))
  rw [← hcast]
  exact ZMod.natCast_eq_zero_iff _ _

/-- The empty (zero) pattern survives: its divergence is zero
everywhere. -/
theorem patternSurvives₃_zero :
    patternSurvives₃ (0 : LayerColumn 2 → ZMod 3) := by
  intro c
  simp [patternDiv₃]

/-- A single nonzero-branch column never survives: at its base site
the divergence is the branch itself (its head differs from its
base, `layerShift_ne`, and every other column carries branch `0`).
The singleton case of the filter — the gate's support-≤ 3 census
begins here. -/
theorem pattern_not_survives_singleton (P₀ : LayerColumn 2)
    (k : ZMod 3) (hk : k ≠ 0) :
    ¬ patternSurvives₃ (Function.update (0 : LayerColumn 2 → ZMod 3)
      P₀ k) := by
  intro h
  have hdiv := h P₀.1
  have hne : layerShift P₀.2.1 P₀.2.2 P₀.1 ≠ P₀.1 :=
    layerShift_ne P₀.2.1 P₀.2.2 P₀.1
  have hbase : (∑ P ∈ Finset.univ.filter
        (fun P : LayerColumn 2 => P.1 = P₀.1),
        Function.update (0 : LayerColumn 2 → ZMod 3) P₀ k P) = k := by
    rw [Finset.sum_eq_single P₀]
    · rw [Function.update_self]
    · intro P _ hneP
      simp only [Function.update_of_ne hneP, Pi.zero_apply]
    · intro hP
      rw [Finset.mem_filter] at hP
      exact absurd ⟨Finset.mem_univ P₀, rfl⟩ hP
  have hhead : (∑ P ∈ Finset.univ.filter
        (fun P : LayerColumn 2 => layerShift P.2.1 P.2.2 P.1 = P₀.1),
        Function.update (0 : LayerColumn 2 → ZMod 3) P₀ k P) = 0 := by
    apply Finset.sum_eq_zero
    intro P hP
    rw [Finset.mem_filter] at hP
    have hneP : P ≠ P₀ := by
      rintro rfl
      exact hne hP.2
    simp only [Function.update_of_ne hneP, Pi.zero_apply]
  rw [patternDiv₃, hbase, hhead, sub_zero] at hdiv
  exact hk hdiv

/-! ## The stratum monomial and the mod-3 filter -/

/-- The pattern's stratum monomial in per-column form: the product
over columns of the stratum character raised to the column's
branch. -/
noncomputable def stratumMonoAux₃ (ε : LayerColumn 2 → ZMod 3)
    (α : LayerSite 2 → Multiplicative (ZMod 3)) : ℂ :=
  ∏ P : LayerColumn 2, (stratumChar₃ P α) ^ (ε P).val

/-- The pattern's stratum monomial in collected (site) form: the
product over sites of the site character raised to the site
exponent. -/
noncomputable def stratumMono₃ (ε : LayerColumn 2 → ZMod 3)
    (α : LayerSite 2 → Multiplicative (ZMod 3)) : ℂ :=
  ∏ c : LayerSite 2, (seatChar₃ (α c)) ^ patternExp₃ ε c

/-- **The stratum monomial lemma.**  The per-column monomial
collects fiberwise into site powers: base fibers contribute their
branch values, head fibers the values of their negated branches
(`seatChar₃_inv_pow`) — the signed divergence is exactly the
exponent bookkeeping of the stratum character. -/
theorem stratumMonoAux₃_eq (ε : LayerColumn 2 → ZMod 3)
    (α : LayerSite 2 → Multiplicative (ZMod 3)) :
    stratumMonoAux₃ ε α = stratumMono₃ ε α := by
  classical
  have hcol : ∀ P : LayerColumn 2,
      (stratumChar₃ P α) ^ (ε P).val
        = (seatChar₃ (α P.1)) ^ (ε P).val
          * (seatChar₃ (α (layerShift P.2.1 P.2.2 P.1)))
              ^ (-(ε P)).val := by
    intro P
    unfold stratumChar₃
    rw [mul_pow, seatChar₃_inv_pow]
  have hR : stratumMono₃ ε α
      = ∏ c : LayerSite 2, ((seatChar₃ (α c)) ^
            (∑ P ∈ Finset.univ.filter (fun P : LayerColumn 2 => P.1 = c),
              (ε P).val)
          * (seatChar₃ (α c)) ^
            (∑ P ∈ Finset.univ.filter (fun P : LayerColumn 2 =>
                layerShift P.2.1 P.2.2 P.1 = c), (-(ε P)).val)) := by
    unfold stratumMono₃ patternExp₃
    exact Finset.prod_congr rfl fun c _ => pow_add _ _ _
  rw [stratumMonoAux₃, Finset.prod_congr rfl fun P _ => hcol P,
    Finset.prod_mul_distrib, hR, Finset.prod_mul_distrib]
  congr 1
  · rw [← Finset.prod_fiberwise_of_maps_to
      (g := fun P : LayerColumn 2 => P.1) (fun P _ => Finset.mem_univ _)]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun P hP => by
      rw [Finset.mem_filter] at hP
      rw [hP.2]
  · rw [← Finset.prod_fiberwise_of_maps_to
      (g := fun P : LayerColumn 2 => layerShift P.2.1 P.2.2 P.1)
      (fun P _ => Finset.mem_univ _)]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun P hP => by
      rw [Finset.mem_filter] at hP
      rw [hP.2]

/-- **The mod-3 signed-divergence filter** (the `stratum_average`
analog; **K-TM-FILTER guard**).  The shared-stratum average of a
pattern's monomial is `1` when the pattern is divergence-free at
every site and `0` otherwise: at each site,
`∑_g χ(g)^{E} = 3` if `3 ∣ E` and `0` if not
(`seatChar₃_pow_sum`), and `3^8 = 6561` cancels the seat factor. -/
theorem stratum_average₃ (ε : LayerColumn 2 → ZMod 3) :
    (6561 : ℂ)⁻¹ * ∑ α : LayerSite 2 → Multiplicative (ZMod 3),
        stratumMono₃ ε α
      = if patternSurvives₃ ε then 1 else 0 := by
  classical
  have hsum : (∑ α : LayerSite 2 → Multiplicative (ZMod 3),
        stratumMono₃ ε α)
      = ∏ c : LayerSite 2, ∑ g : Multiplicative (ZMod 3),
          (seatChar₃ g) ^ patternExp₃ ε c := by
    have hpi : Fintype.piFinset
        (fun _ : LayerSite 2 =>
          (Finset.univ : Finset (Multiplicative (ZMod 3))))
        = Finset.univ := by
      ext α
      simp
    calc (∑ α : LayerSite 2 → Multiplicative (ZMod 3),
          stratumMono₃ ε α)
        = ∑ α : LayerSite 2 → Multiplicative (ZMod 3),
            ∏ c : LayerSite 2, (seatChar₃ (α c)) ^ patternExp₃ ε c :=
          Finset.sum_congr rfl fun α _ => rfl
      _ = ∏ c : LayerSite 2, ∑ g : Multiplicative (ZMod 3),
            (seatChar₃ g) ^ patternExp₃ ε c := by
          rw [Finset.prod_univ_sum, hpi]
  rw [hsum, Finset.prod_congr rfl fun c _ => seatChar₃_pow_sum _]
  split_ifs with hsurv
  · have hprod : ∏ c : LayerSite 2,
        (if 3 ∣ patternExp₃ ε c then (3 : ℂ) else 0)
        = ∏ _c : LayerSite 2, (3 : ℂ) := by
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [ite_eq_left ((patternDiv₃_eq_zero_iff ε c).mp (hsurv c))]
    rw [hprod, Finset.prod_const, Finset.card_univ, layerSite_card]
    norm_num
  · obtain ⟨c₀, hc₀⟩ := not_forall.mp hsurv
    have hzero : ∏ c : LayerSite 2,
        (if 3 ∣ patternExp₃ ε c then (3 : ℂ) else 0) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ c₀) ?_
      exact ite_eq_right ((patternDiv₃_eq_zero_iff ε c₀).not.mp hc₀)
    rw [hzero, mul_zero]

/-! ## Pattern weights and configuration characters -/

/-- The support of a pattern: the columns carrying a nonzero
branch. -/
noncomputable def patternSupp₃ (ε : LayerColumn 2 → ZMod 3) :
    Finset (LayerColumn 2) :=
  Finset.univ.filter (fun P => ε P ≠ 0)

/-- The pattern weight `w_ε = a₃^{24−|supp ε|} b₃^{|supp ε|}` (the
closed form's scalar; nonnegative for `β ≥ 0` — the Gram assembly
of TM-3 consumes exactly this). -/
noncomputable def patternWeight₃ (ε : LayerColumn 2 → ZMod 3)
    (β : ℝ) : ℝ :=
  (seatA₃ β) ^ (24 - (patternSupp₃ ε).card)
    * (seatB₃ β) ^ (patternSupp₃ ε).card

/-- Pattern weights are nonnegative for `β ≥ 0` (both split
coefficients are, TM-1). -/
theorem patternWeight₃_nonneg (ε : LayerColumn 2 → ZMod 3)
    {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ patternWeight₃ ε β :=
  mul_nonneg (pow_nonneg (seatA₃_nonneg β) _)
    (pow_nonneg (seatB₃_nonneg hβ) _)

/-- The pattern's configuration character
`A_ε(u) = ∏_P χ(u (layerLinkOf P))^{ε_P}` — the link values read
through the step-0 correspondence. -/
noncomputable def patternConfig₃ (ε : LayerColumn 2 → ZMod 3)
    (u : LayerLink 2 → Multiplicative (ZMod 3)) : ℂ :=
  ∏ P : LayerColumn 2, (configChar₃ P u) ^ (ε P).val

/-- The conjugate of a configuration character is the product of
the inverse link characters: `conj(A_ε(u))` collects the
`(configChar₃ P u)⁻¹` powers (via `seatChar₃_star` /
`seatChar₃_inv`). -/
theorem star_patternConfig₃ (ε : LayerColumn 2 → ZMod 3)
    (u : LayerLink 2 → Multiplicative (ZMod 3)) :
    star (patternConfig₃ ε u)
      = ∏ P : LayerColumn 2,
          ((configChar₃ P u)⁻¹) ^ (ε P).val := by
  unfold patternConfig₃ configChar₃
  rw [star_prod]
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [star_pow, seatChar₃_star, seatChar₃_inv]

/-! ## The pattern expansion and the closed form -/

/-- The branch factor of one column at branch `k : ZMod 3`:
the constant coefficient times the character power — `a₃` at
`k = 0`, `b₃·χ(word)^k` at `k ≠ 0` (with `χ² = χ̄` the `k = 2`
branch, by `seatChar₃_sq`). -/
noncomputable def branchFactor₃ (k : ZMod 3) (β : ℝ)
    (P : LayerColumn 2) (α : LayerSite 2 → Multiplicative (ZMod 3))
    (u u' : LayerLink 2 → Multiplicative (ZMod 3)) : ℂ :=
  (if k = 0 then (seatA₃ β : ℂ) else (seatB₃ β : ℂ))
    * (seatChar₃ (colWord u u' P.1 P.2.1 P.2.2 α)) ^ k.val

/-- The three-term split as a sum over the three branches:
`exp(−β·dens) = ∑_{k : ZMod 3} branchFactor₃ k` — the `k = 2` term
is `b₃·χ̄(word)` by `seatChar₃_sq`, recovering TM-1's split. -/
theorem exp_colDensC₃_eq_sum₃ (β : ℝ) (P : LayerColumn 2)
    (α : LayerSite 2 → Multiplicative (ZMod 3))
    (u u' : LayerLink 2 → Multiplicative (ZMod 3)) :
    ((Real.exp (-β * colDensC seatρ₃ u u' P α) : ℂ))
      = ∑ k : ZMod 3, branchFactor₃ k β P α u u' := by
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by
    decide
  rw [huniv, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have h0 : branchFactor₃ 0 β P α u u' = (seatA₃ β : ℂ) := by
    simp [branchFactor₃]
  have h1 : branchFactor₃ 1 β P α u u'
      = (seatB₃ β : ℂ)
        * seatChar₃ (colWord u u' P.1 P.2.1 P.2.2 α) := by
    have e1 : (1 : ZMod 3).val = 1 := rfl
    simp only [branchFactor₃, e1,
      ite_eq_right (show (1 : ZMod 3) ≠ 0 by decide),
      pow_one]
  have h2 : branchFactor₃ 2 β P α u u'
      = (seatB₃ β : ℂ)
        * star (seatChar₃ (colWord u u' P.1 P.2.1 P.2.2 α)) := by
    have e2 : (2 : ZMod 3).val = 2 := rfl
    simp only [branchFactor₃, e2,
      ite_eq_right (show (2 : ZMod 3) ≠ 0 by decide)]
    rw [seatChar₃_sq]
  rw [h0, h1, h2, exp_colDensC₃, add_assoc]

/-- The seat Boltzmann weight of a layer action, column by column,
in branch-sum form:
`exp(−action) = ∏_P ∑_k branchFactor₃ k`. -/
theorem exp_neg_layerAction₃ (β : ℝ)
    (α : LayerSite 2 → Multiplicative (ZMod 3))
    (u u' : LayerLink 2 → Multiplicative (ZMod 3)) :
    ((Real.exp (-(layerAction seatρ₃ β α u u')) : ℂ))
      = ∏ P : LayerColumn 2, ∑ k : ZMod 3,
          branchFactor₃ k β P α u u' := by
  have h1 : layerAction seatρ₃ β α u u'
      = β * ∑ P : LayerColumn 2, colDensC seatρ₃ u u' P α := by
    rw [layerAction_eq, layerDensSum_eq_sum_columns seatρ₃
      (by decide) α u u']
  rw [h1]
  have h3 : -(β * ∑ P : LayerColumn 2, colDensC seatρ₃ u u' P α)
      = ∑ P : LayerColumn 2, (-β * colDensC seatρ₃ u u' P α) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun P _ => ?_
    ring
  rw [h3, Real.exp_sum, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun P _ => ?_
  exact exp_colDensC₃_eq_sum₃ β P α u u'

/-- The coefficient product of a pattern: the product of the branch
coefficients over all columns is the pattern weight
(`a₃` off the support, `b₃` on it). -/
theorem prod_branchCoeff₃ (ε : LayerColumn 2 → ZMod 3) (β : ℝ) :
    ∏ P : LayerColumn 2,
        (if ε P = 0 then (seatA₃ β : ℂ) else (seatB₃ β : ℂ))
      = (patternWeight₃ ε β : ℂ) := by
  have hsplit : ∏ P : LayerColumn 2,
        (if ε P = 0 then (seatA₃ β : ℂ) else (seatB₃ β : ℂ))
      = (∏ P ∈ Finset.univ.filter (fun P => ε P ≠ 0), (seatB₃ β : ℂ))
        * ∏ P ∈ Finset.univ.filter (fun P => ¬ ε P ≠ 0),
            (seatA₃ β : ℂ) := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun P => ε P ≠ 0)]
    congr 1
    · exact Finset.prod_congr rfl fun P hP => by
        rw [Finset.mem_filter] at hP
        rw [ite_eq_right hP.2]
    · exact Finset.prod_congr rfl fun P hP => by
        rw [Finset.mem_filter] at hP
        rw [ite_eq_left (not_not.mp hP.2)]
  rw [hsplit, Finset.prod_const, Finset.prod_const]
  have hcard : (Finset.univ.filter (fun P : LayerColumn 2 =>
        ¬ ε P ≠ 0)).card = 24 - (patternSupp₃ ε).card := by
    have h := Finset.card_filter_add_card_filter_not
      (p := fun P : LayerColumn 2 => ε P ≠ 0) (s := Finset.univ)
    rw [Finset.card_univ, layerColumn_card] at h
    have hsupp : (patternSupp₃ ε).card
        = (Finset.univ.filter (fun P : LayerColumn 2 => ε P ≠ 0)).card :=
      rfl
    omega
  rw [hcard]
  unfold patternWeight₃ patternSupp₃
  push_cast
  ring

/-- **Pattern term factorization.**  A pattern's branch-factor
product splits as weight × stratum monomial × configuration
characters:
`∏_P branchFactor₃ (ε P) = w_ε · stratumMono(ε, α) · (A_ε(u') ·
conj(A_ε(u)))`. -/
theorem prod_branchFactor₃ (ε : LayerColumn 2 → ZMod 3) (β : ℝ)
    (α : LayerSite 2 → Multiplicative (ZMod 3))
    (u u' : LayerLink 2 → Multiplicative (ZMod 3)) :
    ∏ P : LayerColumn 2, branchFactor₃ (ε P) β P α u u'
      = (patternWeight₃ ε β : ℂ) * stratumMonoAux₃ ε α
        * (patternConfig₃ ε u' * star (patternConfig₃ ε u)) := by
  classical
  have hfac : ∀ P : LayerColumn 2,
      branchFactor₃ (ε P) β P α u u'
        = (if ε P = 0 then (seatA₃ β : ℂ) else (seatB₃ β : ℂ))
          * ((stratumChar₃ P α) ^ (ε P).val
            * ((configChar₃ P u') ^ (ε P).val
              * ((configChar₃ P u)⁻¹) ^ (ε P).val)) := by
    intro P
    unfold branchFactor₃
    rw [colChar₃_factor, mul_pow, mul_pow]
  rw [Finset.prod_congr rfl fun P _ => hfac P,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, prod_branchCoeff₃,
    ← star_patternConfig₃]
  unfold stratumMonoAux₃ patternConfig₃
  ring

/-- **The closed form of the ternary seat kernel:**
`Σ_{ε : E(ε) ≡ 0} w_ε · A_ε(u') · conj(A_ε(u))` — the sum over
divergence-free patterns of the pattern weight times the
configuration characters (scoping §2.3 Step 5). -/
noncomputable def layerKernel_ternary (β : ℝ)
    (u u' : LayerLink 2 → Multiplicative (ZMod 3)) : ℂ :=
  ∑ ε ∈ Finset.univ.filter patternSurvives₃,
    (patternWeight₃ ε β : ℂ)
      * (patternConfig₃ ε u' * star (patternConfig₃ ε u))

/-- **The ternary seat kernel in closed form** (**K-TM-CLOSED
guard**: against TM-0's numbers — closed form vs direct stratum
sums ≤ `1.1e-16`).  Expand the Boltzmann product over patterns,
factor each pattern term, swap the finite sums, and apply the
mod-3 filter (`stratum_average₃`). -/
theorem layerKernel_ternary_closed (β : ℝ)
    (u u' : LayerLink 2 → Multiplicative (ZMod 3)) :
    layerKernel seatμ₃ seatρ₃ β u u' = layerKernel_ternary β u u' := by
  classical
  have hexpand : ∀ α : LayerSite 2 → Multiplicative (ZMod 3),
      ∏ P : LayerColumn 2, ∑ k : ZMod 3, branchFactor₃ k β P α u u'
        = ∑ ε : LayerColumn 2 → ZMod 3,
            ∏ P : LayerColumn 2, branchFactor₃ (ε P) β P α u u' := by
    intro α
    rw [Finset.prod_univ_sum]
    rw [Fintype.piFinset_univ]
  calc layerKernel seatμ₃ seatρ₃ β u u'
      = (∫ α : LayerSite 2 → Multiplicative (ZMod 3),
          ((Real.exp (-(layerAction seatρ₃ β α u u')) : ℂ))
          ∂(Measure.pi fun _ : LayerSite 2 => seatμ₃)) := rfl
    _ = (Fintype.card (LayerSite 2 → Multiplicative (ZMod 3)) : ℝ)⁻¹
          • ∑ α : LayerSite 2 → Multiplicative (ZMod 3),
            ((Real.exp (-(layerAction seatρ₃ β α u u')) : ℂ)) :=
        seatIntegralPi₃ _
    _ = (6561 : ℂ)⁻¹
          * ∑ α : LayerSite 2 → Multiplicative (ZMod 3),
            ((Real.exp (-(layerAction seatρ₃ β α u u')) : ℂ)) := by
        rw [show ((Fintype.card
              (LayerSite 2 → Multiplicative (ZMod 3)) : ℝ)⁻¹)
            = (6561 : ℝ)⁻¹ by rw [ternary_stratum_card]; norm_num,
          Complex.real_smul]
        congr 1
        rw [Complex.ofReal_inv]
        norm_num
    _ = (6561 : ℂ)⁻¹
          * ∑ ε : LayerColumn 2 → ZMod 3,
            (patternWeight₃ ε β : ℂ)
              * (patternConfig₃ ε u' * star (patternConfig₃ ε u))
              * ∑ α : LayerSite 2 → Multiplicative (ZMod 3),
                stratumMono₃ ε α := by
        rw [Finset.sum_congr rfl fun α _ =>
          exp_neg_layerAction₃ β α u u',
          Finset.sum_congr rfl fun α _ => hexpand α, Finset.sum_comm]
        refine congrArg _ (Finset.sum_congr rfl fun ε _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [prod_branchFactor₃, stratumMonoAux₃_eq]
        ring
    _ = ∑ ε : LayerColumn 2 → ZMod 3,
          (patternWeight₃ ε β : ℂ)
            * (patternConfig₃ ε u' * star (patternConfig₃ ε u))
            * (if patternSurvives₃ ε then 1 else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ε _ => ?_
        calc (6561 : ℂ)⁻¹
              * ((patternWeight₃ ε β : ℂ)
                * (patternConfig₃ ε u' * star (patternConfig₃ ε u))
                * ∑ α : LayerSite 2 → Multiplicative (ZMod 3),
                  stratumMono₃ ε α)
            = (patternWeight₃ ε β : ℂ)
                * (patternConfig₃ ε u' * star (patternConfig₃ ε u))
                * ((6561 : ℂ)⁻¹
                    * ∑ α : LayerSite 2 → Multiplicative (ZMod 3),
                      stratumMono₃ ε α) := by ring
          _ = (patternWeight₃ ε β : ℂ)
                * (patternConfig₃ ε u' * star (patternConfig₃ ε u))
                * (if patternSurvives₃ ε then 1 else 0) := by
              rw [stratum_average₃]
    _ = layerKernel_ternary β u u' := by
        unfold layerKernel_ternary
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun ε _ => ?_
        split_ifs with hε
        · rw [mul_one]
        · rw [mul_zero]

end ThetLogos
