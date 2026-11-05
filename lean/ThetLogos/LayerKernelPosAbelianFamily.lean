/-
# Brick R1 — `LayerKernelPos` at the abelian seat family (all `N`)

Commission: Jeff's tap on the Stage 3c re-scope's priced menu
(2026-11-05, re-scope §5 R1; contract:
`~/workspace/your_files/pitch4-stage3c-rescope-2026-11-05.md`).
Price band **M** (scoping estimate 15–35 strict).  Single-lane
𝒜 ⪰ 0 core-chain work; integration is the parent's.

## What this brick proves

`layerKernelPos_abelian_family`: at the seat of LK-P0 —
`G = Multiplicative (ZMod 2)`, `ρ = seatρ` the sign representation,
`μ = seatμ` the uniform probability measure — `LayerKernelPos`
holds for **every** `N` (with `NeZero N`) and every `β ≥ 0`,
generalizing `layerKernelPos_seat` (the `N = 2` case, LK-P0)
along its own proof shape: the parity filter over the stratum,
the closed form

  `𝒜 = Σ_{S even} a^(L−|S|) b^|S| · Φ_S(u) Φ_S(u')`,

(`L = Fintype.card (LayerColumn N) = 3N³` kept symbolic,
`a = (1 + e^{−2β})/2`, `b = (1 − e^{−2β})/2`), and the pairing
exhibited as `Σ w_S ‖Z_S‖²` with `w_S ≥ 0` for `β ≥ 0`.  No
`hρcont` hypothesis is consumed (the seat's continuity is the
discrete one, as in LK-P0).

## The one genuine case split (read before the proofs)

The corpus's column decomposition of the layer action
(`layerDensSum_eq_sum_columns`) routes through
`plaquette_layerConfig`, whose `Even N` hypothesis is spent in
exactly one place: `layerConfig_up`, where it is used only to
obtain `2 ≤ N` (for `(1 : ZMod N).val = 1`).  The word identity
therefore holds for **every `N ≥ 2`**, and §1 below re-proves
the three-link chain (`layerConfig_up` → `plaquette_layerConfig`
→ column sum) at `2 ≤ N` in this module's own names — no landed
file is edited.

At `N = 1` the word identity is **false**, not merely unproved:
`(x 0).val = 1` is impossible in `ZMod 1`, the "up" read of
`layerConfig` never fires, and the column formula genuinely
diverges from the kernel (the T2 gate computes both sides:
kernel `= 1`, column formula `= ∏_c (a + b·t_c)`).  But at
`N = 1` every plaquette word of the layer configuration is a
commutator `α c · u ℓ · (α c)⁻¹ · (u ℓ)⁻¹`, whose seat sign is
`+1`; hence every density is `0`, the action is `0`, and the
kernel is the constant `1` — `LayerKernelPos` holds at `N = 1`
by the same separation as the `β = 0` case (§3 below).  The
early T2 gate verified the closed form against directly
computed kernel values at `N = 4` and `N = 3` (and at `N = 2`
against five independent engines plus the LK-P0 landmark)
before this proof was written; no mismatch was found, so
**K-LKP-AB does not fire** and no negative pairing witness
exists at any probed `N` (K-LKP-SEAT does not fire).

## Honesty

This is qualitative-core content at one seat family.  It does
**not** claim the margin floor or any uniform gap — at this
very seat family the floor is **false** (re-scope §3.6: the
margins are `B′(β)^(link count)`, exponentially small in `N`).
It advances no continuum statement and moves no dial.
**NO CLAIM; dials 0/4.**
-/

import ThetLogos.LayerKernelPosSeatProbe

open MeasureTheory Finset
open scoped ENNReal

namespace ThetLogos

/-! ## §1 — The word identity at `2 ≤ N` (the `Even N` hypothesis
of the landed chain is only ever spent as `2 ≤ N`, in
`layerConfig_up`) -/

/-- The layer configuration one time step above a spatial link
of the layer reads the second boundary datum — for every
`N ≥ 2`.  (The landed `layerConfig_up` assumes `Even N` but
spends it only through `two_le_of_even`, to evaluate
`(1 : ZMod N).val = 1`.) -/
theorem layerConfig_up_fam {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableInv G] [TopologicalSpace G] [IsTopologicalGroup G]
    [BorelSpace G] [SecondCountableTopology G]
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) (α : LayerSite N → G)
    (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4)
    (hν : ν ≠ 0) :
    layerConfig α u u' (torusShift N 0 c.1, ν)
      = u' (layerLinkOf c ν hν) := by
  have hy0 : torusShift N 0 c.1 0 = 1 := by
    rw [torusShift_apply_coord, Pi.single_eq_same, layerSite_zero c,
      add_zero]
  have hy0val : (torusShift N 0 c.1 0).val = 1 := by
    rw [hy0, ← Nat.cast_one]
    exact ZMod.val_natCast_of_lt (by omega)
  have h1 : ¬ (torusShift N 0 c.1, ν).2 = (0 : Fin 4) := hν
  have h2 : ¬ ((torusShift N 0 c.1, ν).1 0).val = 0 := by
    show ¬ (torusShift N 0 c.1 0).val = 0
    rw [hy0val]
    exact Nat.one_ne_zero
  have h3 : ((torusShift N 0 c.1, ν).1 0).val = 1 := hy0val
  unfold layerConfig
  rw [dite_eq_right h1, dite_eq_right h2, dite_eq_left h3]
  congr 1
  apply Subtype.ext
  show ((torusShift N 0).symm (torusShift N 0 c.1), ν) = (c.1, ν)
  rw [Equiv.symm_apply_apply]

/-- **The one-layer word at `2 ≤ N`**: the plaquette of the
layer configuration at a layer site is Brick β1's word
`α c · u' ℓ · (α (σ_ν c))⁻¹ · (u ℓ)⁻¹`. -/
theorem plaquette_layerConfig_fam {G : Type*} [Group G]
    [MeasurableSpace G] [MeasurableInv G] [TopologicalSpace G]
    [IsTopologicalGroup G] [BorelSpace G]
    [SecondCountableTopology G]
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) (α : LayerSite N → G)
    (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4)
    (hν : ν ≠ 0) :
    plaquette (torusShift N) (layerConfig α u u') c.1 0 ν
      = α c * u' (layerLinkOf c ν hν) * (α (layerShift ν hν c))⁻¹
        * (u (layerLinkOf c ν hν))⁻¹ := by
  unfold plaquette
  rw [layerConfig_time, layerConfig_up_fam hN, layerConfig_time_shift,
    layerConfig_spatial]

/-- The column word, at the level of densities, at `2 ≤ N`. -/
theorem plaquetteDensity_layerConfig_word_fam {G : Type*} [Group G]
    [MeasurableSpace G] [MeasurableInv G] [TopologicalSpace G]
    [IsTopologicalGroup G] [BorelSpace G]
    [SecondCountableTopology G] {d : ℕ}
    (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) (α : LayerSite N → G)
    (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4)
    (hν : ν ≠ 0) :
    plaquetteDensity (torusShift N) ρ (layerConfig α u u') c.1 0 ν
      = wordDensity ρ (α c * u' (layerLinkOf c ν hν)
          * (α (layerShift ν hν c))⁻¹ * (u (layerLinkOf c ν hν))⁻¹) := by
  unfold plaquetteDensity wordDensity
  rw [plaquette_layerConfig_fam hN]

/-- The layer density sum is the sum over columns, at `2 ≤ N`. -/
theorem layerDensSum_eq_sum_columns_fam {G : Type*} [Group G]
    [MeasurableSpace G] [MeasurableInv G] [TopologicalSpace G]
    [IsTopologicalGroup G] [BorelSpace G]
    [SecondCountableTopology G] {d : ℕ}
    (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) (α : LayerSite N → G)
    (u u' : LayerLink N → G) :
    layerDensSum ρ α u u'
      = ∑ P : LayerColumn N, colDensC ρ u u' P α := by
  have hIoi : (Finset.univ.filter (fun ν : Fin 4 => ν ≠ 0))
      = Finset.Ioi (0 : Fin 4) := by
    ext ν
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ioi]
    exact Fin.pos_iff_ne_zero.symm
  have step : ∀ c : LayerSite N,
      (∑ ν ∈ Finset.Ioi (0 : Fin 4),
        plaquetteDensity (torusShift N) ρ (layerConfig α u u') c.1 0 ν)
      = ∑ ν : {ν : Fin 4 // ν ≠ 0}, colDens ρ u u' c ν.1 ν.2 α := by
    intro c
    refine Finset.sum_bij
      (fun ν hν => (⟨ν, Fin.pos_iff_ne_zero.mp (Finset.mem_Ioi.mp hν)⟩ :
        {ν : Fin 4 // ν ≠ 0})) ?_ ?_ ?_ ?_
    · intro ν _
      exact Finset.mem_univ _
    · intro ν₁ _ ν₂ _ hij
      exact Subtype.ext_iff.mp hij
    · intro P _
      exact ⟨P.1, Finset.mem_Ioi.mpr (Fin.pos_iff_ne_zero.mpr P.2),
        Subtype.ext rfl⟩
    · intro ν hν
      exact plaquetteDensity_layerConfig_word_fam ρ hN α u u' c ν
        (Fin.pos_iff_ne_zero.mp (Finset.mem_Ioi.mp hν))
  show (∑ c : LayerSite N, ∑ ν ∈ Finset.Ioi (0 : Fin 4),
        plaquetteDensity (torusShift N) ρ (layerConfig α u u') c.1 0 ν)
      = ∑ P : LayerColumn N, colDens ρ u u' P.1 P.2.1 P.2.2 α
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun c _ => step c

/-! ## §2 — The seat engine at general `N`

LK-P0's engine, lifted verbatim in shape from `LayerColumn 2`
to `LayerColumn N`: the sign factorization, the multiplicity,
the parity filter (with the stratum factor kept symbolic as the
stratum configuration count), the expansion over even families,
the closed form, and the Gram assembly.  The group-level seat
data (`seatμ`, `seatρ`, `seatSign` and its algebra,
`seatIntegralPi`, `charFn_seat`) is imported from LK-P0
unchanged — none of it mentions `N`. -/

section FamilyEngine

variable {N : ℕ} [NeZero N]

/-- The sign of a column word at general `N`. -/
def famColSign (P : LayerColumn N)
    (α : LayerSite N → Multiplicative (ZMod 2))
    (u u' : LayerLink N → Multiplicative (ZMod 2)) : ℝ :=
  seatSign (colWord u u' P.1 P.2.1 P.2.2 α)

/-- The stratum part of a column sign: the two `α`-factors. -/
def famStratumSign (P : LayerColumn N)
    (α : LayerSite N → Multiplicative (ZMod 2)) : ℝ :=
  seatSign (α P.1) * seatSign (α (layerShift P.2.1 P.2.2 P.1))

/-- The layer-configuration part of a column sign. -/
def famConfigSign (P : LayerColumn N)
    (u : LayerLink N → Multiplicative (ZMod 2)) : ℝ :=
  seatSign (u (layerLinkOf P.1 P.2.1 P.2.2))

/-- The configuration character of a column family. -/
def famConfigProd (S : Finset (LayerColumn N))
    (u : LayerLink N → Multiplicative (ZMod 2)) : ℝ :=
  ∏ P ∈ S, famConfigSign P u

/-- The multiplicity of a site `c` in a column family `S`: how
many columns of `S` are based at `c`, plus how many are based
at a site shifted to `c`.  This is the exponent of `χ(α c)` in
the family's stratum character. -/
noncomputable def famColMult (S : Finset (LayerColumn N))
    (c : LayerSite N) : ℕ :=
  (S.filter (fun P => P.1 = c)).card
    + (S.filter (fun P => layerShift P.2.1 P.2.2 P.1 = c)).card

/-- A column family is **even** when every site has even
multiplicity. -/
noncomputable def famEven (S : Finset (LayerColumn N)) : Prop :=
  ∀ c, famColMult S c % 2 = 0

/-- Evenness of a finite column family is decidable. -/
noncomputable instance (S : Finset (LayerColumn N)) :
    Decidable (famEven S) :=
  Fintype.decidableForallFintype

/-- **Sign factorization.**  The column sign splits as the
stratum sign times the two configuration signs. -/
theorem fam_colSign_factor (P : LayerColumn N)
    (α : LayerSite N → Multiplicative (ZMod 2))
    (u u' : LayerLink N → Multiplicative (ZMod 2)) :
    famColSign P α u u'
      = famStratumSign P α * (famConfigSign P u' * famConfigSign P u) := by
  unfold famColSign famStratumSign famConfigSign colWord
  simp only [seatSign_mul, seatSign_inv]
  ring

/-- The seat column density is `1 − χ(word) ∈ {0, 2}`. -/
theorem fam_colDensC_seat (u u' : LayerLink N → Multiplicative (ZMod 2))
    (P : LayerColumn N) (α : LayerSite N → Multiplicative (ZMod 2)) :
    colDensC seatρ u u' P α
      = 1 - seatSign (colWord u u' P.1 P.2.1 P.2.2 α) := by
  rw [colDensC, colDens_eq, charFn_seat]
  simp

/-- The Boltzmann factor of one seat column:
`exp (−β · dens) = a(β) + b(β) · χ(word)`. -/
theorem fam_exp_colDensC (β : ℝ) (P : LayerColumn N)
    (α : LayerSite N → Multiplicative (ZMod 2))
    (u u' : LayerLink N → Multiplicative (ZMod 2)) :
    Real.exp (-β * colDensC seatρ u u' P α)
      = (1 + Real.exp (-2 * β)) / 2
        + (1 - Real.exp (-2 * β)) / 2 * famColSign P α u u' := by
  rw [fam_colDensC_seat]
  unfold famColSign
  rcases seatSign_eq (colWord u u' P.1 P.2.1 P.2.2 α) with h | h
  · rw [h]
    simp only [sub_self, mul_zero, Real.exp_zero]
    ring
  · rw [h]
    have harg : -β * (1 - (-1 : ℝ)) = -2 * β := by ring
    rw [harg]
    ring

/-- The family's stratum character as a character monomial in
the site values: `∏_{P ∈ S} famStratumSign P α
= ∏_c χ(α c)^{mult_S(c)}` (fiberwise over base sites and over
shifted sites). -/
theorem fam_stratumSign_prod (S : Finset (LayerColumn N))
    (α : LayerSite N → Multiplicative (ZMod 2)) :
    ∏ P ∈ S, famStratumSign P α
      = ∏ c : LayerSite N, seatSign (α c) ^ famColMult S c := by
  have hsplit : ∏ c : LayerSite N, seatSign (α c) ^ famColMult S c
      = (∏ c : LayerSite N,
          seatSign (α c) ^ (S.filter (fun P => P.1 = c)).card)
        * ∏ c : LayerSite N, seatSign (α c)
            ^ (S.filter (fun P => layerShift P.2.1 P.2.2 P.1 = c)).card := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun c _ => ?_
    simp only [famColMult, pow_add]
  rw [hsplit]
  unfold famStratumSign
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [← Finset.prod_fiberwise_of_maps_to' (s := S) (t := Finset.univ)
      (g := fun P : LayerColumn N => P.1)
      (f := fun c => seatSign (α c)) (fun P _ => Finset.mem_univ _)]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [Finset.prod_const]
  · rw [← Finset.prod_fiberwise_of_maps_to' (s := S) (t := Finset.univ)
      (g := fun P : LayerColumn N => layerShift P.2.1 P.2.2 P.1)
      (f := fun c => seatSign (α c)) (fun P _ => Finset.mem_univ _)]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [Finset.prod_const]

/-- **The parity filter at general `N`.**  The shared-stratum
average of a column family's stratum character is `1` when the
family is even and `0` otherwise: at each site,
`∑_g χ(g)^{mult}` is `2` for even multiplicity and `0` for odd,
and the `2^(#sites)` cancels the seat factor (the stratum
configuration count, kept symbolic). -/
theorem fam_stratum_average (S : Finset (LayerColumn N)) :
    ((Fintype.card (LayerSite N → Multiplicative (ZMod 2)) : ℝ))⁻¹
        * ∑ α : LayerSite N → Multiplicative (ZMod 2),
          ∏ P ∈ S, famStratumSign P α
      = if famEven S then 1 else 0 := by
  have hsum : (∑ α : LayerSite N → Multiplicative (ZMod 2),
        ∏ P ∈ S, famStratumSign P α)
      = ∏ c : LayerSite N, ∑ g : Multiplicative (ZMod 2),
          seatSign g ^ famColMult S c := by
    have hpi : Fintype.piFinset
        (fun _ : LayerSite N =>
          (Finset.univ : Finset (Multiplicative (ZMod 2))))
        = Finset.univ := by
      ext α
      simp
    calc (∑ α : LayerSite N → Multiplicative (ZMod 2),
          ∏ P ∈ S, famStratumSign P α)
        = ∑ α : LayerSite N → Multiplicative (ZMod 2),
            ∏ c : LayerSite N, seatSign (α c) ^ famColMult S c :=
          Finset.sum_congr rfl fun α _ => fam_stratumSign_prod S α
      _ = ∏ c : LayerSite N, ∑ g : Multiplicative (ZMod 2),
            seatSign g ^ famColMult S c := by
          rw [Finset.prod_univ_sum, hpi]
  rw [hsum]
  have hinner : ∀ c : LayerSite N,
      (∑ g : Multiplicative (ZMod 2), seatSign g ^ famColMult S c)
        = if famColMult S c % 2 = 0 then 2 else 0 := by
    intro c
    split_ifs with hev
    · calc (∑ g : Multiplicative (ZMod 2), seatSign g ^ famColMult S c)
          = ∑ g : Multiplicative (ZMod 2), (1 : ℝ) := by
            refine Finset.sum_congr rfl fun g _ => ?_
            rcases seatSign_eq g with h | h
            · rw [h, one_pow]
            · rw [h]
              exact Even.neg_one_pow (Nat.even_iff.mpr hev)
        _ = 2 := by
            rw [Finset.sum_const, Finset.card_univ, seat_card]
            simp
    · have hodd : famColMult S c % 2 = 1 := by
        have := Nat.mod_lt (famColMult S c) (show 0 < 2 by norm_num)
        omega
      calc (∑ g : Multiplicative (ZMod 2), seatSign g ^ famColMult S c)
          = ∑ g : Multiplicative (ZMod 2), seatSign g := by
            refine Finset.sum_congr rfl fun g _ => ?_
            rcases seatSign_eq g with h | h
            · rw [h, one_pow]
            · rw [h]
              exact Odd.neg_one_pow (Nat.odd_iff.mpr hodd)
        _ = 0 := sum_seatSign
  rw [Finset.prod_congr rfl fun c _ => hinner c]
  have hcard : (Fintype.card (LayerSite N → Multiplicative (ZMod 2)) : ℝ)
      = (2 : ℝ) ^ Fintype.card (LayerSite N) := by
    rw [Fintype.card_fun, seat_card, Nat.cast_pow, Nat.cast_ofNat]
  split_ifs with hsev
  · have hprod : ∏ c : LayerSite N,
        (if famColMult S c % 2 = 0 then (2 : ℝ) else 0)
        = ∏ c : LayerSite N, (2 : ℝ) := by
      refine Finset.prod_congr rfl fun c _ => ?_
      split_ifs with hc
      · rfl
      · exact absurd (hsev c) hc
    have hX : (Fintype.card (LayerSite N → Multiplicative (ZMod 2)) : ℝ)
        ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
        (Fintype.card_pos_iff.mpr ⟨fun _ => 1⟩))
    rw [hprod, Finset.prod_const, Finset.card_univ, ← hcard]
    exact inv_mul_cancel₀ hX
  · obtain ⟨c₀, hc₀⟩ := not_forall.mp hsev
    have hzero : ∏ c : LayerSite N,
        (if famColMult S c % 2 = 0 then (2 : ℝ) else 0) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ c₀) ?_
      exact ite_eq_right hc₀
    rw [hzero, mul_zero]

/-- The seat Boltzmann weight of a layer action, column by
column: `exp (−action) = ∏_P (a + b · famColSign P)`. -/
theorem fam_exp_neg_layerAction (hN : 2 ≤ N) (β : ℝ)
    (α : LayerSite N → Multiplicative (ZMod 2))
    (u u' : LayerLink N → Multiplicative (ZMod 2)) :
    (Real.exp (-(layerAction seatρ β α u u')) : ℂ)
      = ((∏ P : LayerColumn N, ((1 + Real.exp (-2 * β)) / 2
          + (1 - Real.exp (-2 * β)) / 2 * famColSign P α u u') : ℝ)
          : ℂ) := by
  have h1 : layerAction seatρ β α u u'
      = β * ∑ P : LayerColumn N, colDensC seatρ u u' P α := by
    rw [layerAction_eq, layerDensSum_eq_sum_columns_fam seatρ hN α u u']
  rw [h1]
  have h2 : Real.exp (-(β * ∑ P : LayerColumn N,
        colDensC seatρ u u' P α))
      = ∏ P : LayerColumn N, ((1 + Real.exp (-2 * β)) / 2
          + (1 - Real.exp (-2 * β)) / 2 * famColSign P α u u') := by
    have h3 : -(β * ∑ P : LayerColumn N, colDensC seatρ u u' P α)
        = ∑ P : LayerColumn N, (-β * colDensC seatρ u u' P α) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun P _ => ?_
      ring
    rw [h3, Real.exp_sum]
    refine Finset.prod_congr rfl fun P _ => ?_
    exact fam_exp_colDensC β P α u u'
  rw [h2]

/-- **Expansion over even families.**  The stratum sum of the
seat Boltzmann weight, scaled by the seat factor, is the sum
over even column families of
`a^(L−|S|) b^|S| Φ_S(u) Φ_S(u')`: expand the product over
columns (`Finset.prod_add`), swap the finite sums, and apply
the parity filter (`fam_stratum_average`). -/
theorem fam_kernel_expand (β : ℝ)
    (u u' : LayerLink N → Multiplicative (ZMod 2)) :
    ((Fintype.card (LayerSite N → Multiplicative (ZMod 2)) : ℝ))⁻¹
        * ∑ α : LayerSite N → Multiplicative (ZMod 2),
          ∏ P : LayerColumn N, ((1 + Real.exp (-2 * β)) / 2
            + (1 - Real.exp (-2 * β)) / 2 * famColSign P α u u')
      = ∑ S ∈ Finset.univ.filter famEven,
          ((1 + Real.exp (-2 * β)) / 2)
              ^ (Fintype.card (LayerColumn N) - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card
            * famConfigProd S u * famConfigProd S u' := by
  set a := (1 + Real.exp (-2 * β)) / 2 with ha
  set b := (1 - Real.exp (-2 * β)) / 2 with hb
  have hexp : ∀ α : LayerSite N → Multiplicative (ZMod 2),
      ∏ P : LayerColumn N, (a + b * famColSign P α u u')
        = ∑ S ∈ Finset.univ.powerset,
            a ^ (Fintype.card (LayerColumn N) - S.card) * b ^ S.card
              * (∏ P ∈ S, famStratumSign P α)
              * famConfigProd S u * famConfigProd S u' := by
    intro α
    calc ∏ P : LayerColumn N, (a + b * famColSign P α u u')
        = ∏ P : LayerColumn N, (b * famColSign P α u u' + a) :=
          Finset.prod_congr rfl fun P _ => add_comm _ _
      _ = ∑ S ∈ Finset.univ.powerset,
            (∏ P ∈ S, b * famColSign P α u u')
              * ∏ P ∈ Finset.univ \ S, a := Finset.prod_add _ _ _
      _ = ∑ S ∈ Finset.univ.powerset,
            a ^ (Fintype.card (LayerColumn N) - S.card) * b ^ S.card
              * (∏ P ∈ S, famStratumSign P α)
              * famConfigProd S u * famConfigProd S u' := by
          refine Finset.sum_congr rfl fun S _ => ?_
          have hsign : ∏ P ∈ S, b * famColSign P α u u'
              = b ^ S.card * ((∏ P ∈ S, famStratumSign P α)
                  * (famConfigProd S u' * famConfigProd S u)) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
            congr 1
            calc ∏ P ∈ S, famColSign P α u u'
                = ∏ P ∈ S, (famStratumSign P α
                    * (famConfigSign P u' * famConfigSign P u)) :=
                  Finset.prod_congr rfl fun P _ =>
                    fam_colSign_factor P α u u'
              _ = (∏ P ∈ S, famStratumSign P α)
                    * ((∏ P ∈ S, famConfigSign P u')
                      * ∏ P ∈ S, famConfigSign P u) := by
                  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
              _ = (∏ P ∈ S, famStratumSign P α)
                    * (famConfigProd S u' * famConfigProd S u) := rfl
          have hpow : ∏ P ∈ Finset.univ \ S, a
              = a ^ (Fintype.card (LayerColumn N) - S.card) := by
            rw [Finset.prod_const, Finset.card_sdiff, Finset.inter_univ,
              Finset.card_univ]
          rw [hsign, hpow]
          ring
  calc ((Fintype.card (LayerSite N → Multiplicative (ZMod 2)) : ℝ))⁻¹
        * ∑ α : LayerSite N → Multiplicative (ZMod 2),
          ∏ P : LayerColumn N, (a + b * famColSign P α u u')
      = ((Fintype.card (LayerSite N → Multiplicative (ZMod 2)) : ℝ))⁻¹
          * ∑ S ∈ Finset.univ.powerset,
            ∑ α : LayerSite N → Multiplicative (ZMod 2),
              a ^ (Fintype.card (LayerColumn N) - S.card) * b ^ S.card
                * (∏ P ∈ S, famStratumSign P α)
                * famConfigProd S u * famConfigProd S u' := by
        rw [Finset.sum_congr rfl fun α _ => hexp α, Finset.sum_comm]
    _ = ∑ S ∈ Finset.univ.powerset,
          a ^ (Fintype.card (LayerColumn N) - S.card) * b ^ S.card
            * famConfigProd S u * famConfigProd S u'
            * (((Fintype.card (LayerSite N → Multiplicative (ZMod 2))
                : ℝ))⁻¹
              * ∑ α : LayerSite N → Multiplicative (ZMod 2),
                ∏ P ∈ S, famStratumSign P α) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        have hnorm : ∀ α : LayerSite N → Multiplicative (ZMod 2),
            a ^ (Fintype.card (LayerColumn N) - S.card) * b ^ S.card
                * (∏ P ∈ S, famStratumSign P α)
                * famConfigProd S u * famConfigProd S u'
              = (a ^ (Fintype.card (LayerColumn N) - S.card) * b ^ S.card
                  * famConfigProd S u * famConfigProd S u')
                * ∏ P ∈ S, famStratumSign P α := fun α => by ring
        rw [Finset.sum_congr rfl fun α _ => hnorm α, ← Finset.mul_sum]
        ring
    _ = ∑ S ∈ Finset.univ.powerset,
          a ^ (Fintype.card (LayerColumn N) - S.card) * b ^ S.card
            * famConfigProd S u * famConfigProd S u'
            * (if famEven S then 1 else 0) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [fam_stratum_average]
    _ = ∑ S ∈ Finset.univ.filter famEven,
          a ^ (Fintype.card (LayerColumn N) - S.card) * b ^ S.card
            * famConfigProd S u * famConfigProd S u' := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun S _ => ?_
        split_ifs with hS
        · rw [mul_one]
        · rw [mul_zero]

/-- **The closed form of the seat kernel at general `N ≥ 2`.**
The layer kernel is the cast of a real sum over even column
families. -/
theorem layerKernel_abelian (hN : 2 ≤ N) (β : ℝ)
    (u u' : LayerLink N → Multiplicative (ZMod 2)) :
    layerKernel seatμ seatρ β u u'
      = ((∑ S ∈ Finset.univ.filter famEven,
          ((1 + Real.exp (-2 * β)) / 2)
              ^ (Fintype.card (LayerColumn N) - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card
            * famConfigProd S u * famConfigProd S u' : ℝ) : ℂ) := by
  have h1 : layerKernel seatμ seatρ β u u'
      = (∫ α : LayerSite N → Multiplicative (ZMod 2),
          (Real.exp (-(layerAction seatρ β α u u')) : ℂ)
          ∂(Measure.pi fun _ : LayerSite N => seatμ)) := rfl
  rw [h1, seatIntegralPi,
    Finset.sum_congr rfl fun α _ => fam_exp_neg_layerAction hN β α u u',
    ← Complex.ofReal_sum, Complex.real_smul, ← Complex.ofReal_mul,
    fam_kernel_expand]

/-- **PSD at the seat family for `N ≥ 2`.**  With the closed
form of `layerKernel_abelian`, the pairing is (a positive
scalar times) a sum over even column families of nonnegative
weights `a^(L−|S|) b^(|S|)` (both `a, b ≥ 0` when `β ≥ 0`)
times `‖Z_S‖²`, where
`Z_S = ∑_u Φ_S(u) F(u)` — a Gram sum.  Gauge invariance is not
consumed. -/
theorem layerKernelPos_abelian_ge (hN : 2 ≤ N) {β : ℝ} (hβ : 0 ≤ β) :
    LayerKernelPos (N := N) seatμ seatρ β := by
  classical
  intro F _hF
  have ha0 : 0 ≤ (1 + Real.exp (-2 * β)) / 2 := by
    have h := Real.exp_pos (-2 * β)
    linarith
  have hb0 : 0 ≤ (1 - Real.exp (-2 * β)) / 2 := by
    have h : Real.exp (-2 * β) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    linarith
  have hP1 : (∫ u, ∫ u', (starRingEnd ℂ) (F u)
        * layerKernel seatμ seatρ β u u' * F u'
        ∂(Measure.pi fun _ : LayerLink N => seatμ)
        ∂(Measure.pi fun _ : LayerLink N => seatμ))
      = ((Fintype.card (LayerLink N → Multiplicative (ZMod 2))
          : ℝ)⁻¹)
        • ∑ u, (((Fintype.card (LayerLink N
            → Multiplicative (ZMod 2)) : ℝ)⁻¹)
          • ∑ u', (starRingEnd ℂ) (F u)
              * layerKernel seatμ seatρ β u u' * F u') := by
    rw [seatIntegralPi]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    exact seatIntegralPi _
  have hterm : ∀ u u' : LayerLink N → Multiplicative (ZMod 2),
      (starRingEnd ℂ) (F u)
        * ((∑ S ∈ Finset.univ.filter famEven,
            ((1 + Real.exp (-2 * β)) / 2)
                ^ (Fintype.card (LayerColumn N) - S.card)
              * ((1 - Real.exp (-2 * β)) / 2) ^ S.card
              * famConfigProd S u * famConfigProd S u' : ℝ) : ℂ) * F u'
      = ∑ S ∈ Finset.univ.filter famEven,
          ((((1 + Real.exp (-2 * β)) / 2)
                ^ (Fintype.card (LayerColumn N) - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card : ℝ) : ℂ)
          * ((starRingEnd ℂ) (F u)
            * ((famConfigProd S u : ℝ) : ℂ))
          * (((famConfigProd S u' : ℝ) : ℂ) * F u') := by
    intro u u'
    rw [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun S _ => ?_
    push_cast
    ring
  have hswap : ∀ g : (LayerLink N → Multiplicative (ZMod 2))
      → (LayerLink N → Multiplicative (ZMod 2))
      → Finset (LayerColumn N) → ℂ,
      (∑ u, ∑ u', ∑ S ∈ Finset.univ.filter famEven, g u u' S)
        = ∑ S ∈ Finset.univ.filter famEven, ∑ u, ∑ u', g u u' S := by
    intro g
    calc (∑ u, ∑ u', ∑ S ∈ Finset.univ.filter famEven, g u u' S)
        = ∑ u, ∑ S ∈ Finset.univ.filter famEven, ∑ u', g u u' S :=
          Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = ∑ S ∈ Finset.univ.filter famEven, ∑ u, ∑ u', g u u' S :=
          Finset.sum_comm
  have hfac : ∀ S : Finset (LayerColumn N),
      (∑ u, ∑ u',
          ((((1 + Real.exp (-2 * β)) / 2)
                ^ (Fintype.card (LayerColumn N) - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card : ℝ) : ℂ)
          * ((starRingEnd ℂ) (F u)
            * ((famConfigProd S u : ℝ) : ℂ))
          * (((famConfigProd S u' : ℝ) : ℂ) * F u'))
        = ((((1 + Real.exp (-2 * β)) / 2)
              ^ (Fintype.card (LayerColumn N) - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card : ℝ) : ℂ)
          * ((∑ u, (starRingEnd ℂ) (F u)
              * ((famConfigProd S u : ℝ) : ℂ))
            * (∑ u', ((famConfigProd S u' : ℝ) : ℂ) * F u')) := by
    intro S
    calc (∑ u, ∑ u',
          ((((1 + Real.exp (-2 * β)) / 2)
                ^ (Fintype.card (LayerColumn N) - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card : ℝ) : ℂ)
          * ((starRingEnd ℂ) (F u)
            * ((famConfigProd S u : ℝ) : ℂ))
          * (((famConfigProd S u' : ℝ) : ℂ) * F u'))
        = ∑ u, ((((1 + Real.exp (-2 * β)) / 2)
              ^ (Fintype.card (LayerColumn N) - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card : ℝ) : ℂ)
            * ((starRingEnd ℂ) (F u)
              * ((famConfigProd S u : ℝ) : ℂ))
            * (∑ u', ((famConfigProd S u' : ℝ) : ℂ) * F u') := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [← Finset.mul_sum]
      _ = ((((1 + Real.exp (-2 * β)) / 2)
              ^ (Fintype.card (LayerColumn N) - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card : ℝ) : ℂ)
          * ((∑ u, (starRingEnd ℂ) (F u)
              * ((famConfigProd S u : ℝ) : ℂ))
            * (∑ u', ((famConfigProd S u' : ℝ) : ℂ) * F u')) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, mul_assoc]
  have hZ : ∀ S : Finset (LayerColumn N),
      (∑ u, (starRingEnd ℂ) (F u) * ((famConfigProd S u : ℝ) : ℂ))
        = (starRingEnd ℂ)
          (∑ u, ((famConfigProd S u : ℝ) : ℂ) * F u) := by
    intro S
    rw [map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    exact mul_comm _ _
  have hKrw : ∀ u u' : LayerLink N → Multiplicative (ZMod 2),
      (starRingEnd ℂ) (F u) * layerKernel seatμ seatρ β u u' * F u'
        = (starRingEnd ℂ) (F u)
          * ((∑ S ∈ Finset.univ.filter famEven,
              ((1 + Real.exp (-2 * β)) / 2)
                  ^ (Fintype.card (LayerColumn N) - S.card)
                * ((1 - Real.exp (-2 * β)) / 2) ^ S.card
                * famConfigProd S u * famConfigProd S u' : ℝ) : ℂ)
          * F u' := by
    intro u u'
    rw [layerKernel_abelian hN]
  have hP : (∫ u, ∫ u', (starRingEnd ℂ) (F u)
        * layerKernel seatμ seatρ β u u' * F u'
        ∂(Measure.pi fun _ : LayerLink N => seatμ)
        ∂(Measure.pi fun _ : LayerLink N => seatμ))
      = (((Fintype.card (LayerLink N → Multiplicative (ZMod 2))
            : ℝ)⁻¹
          * ((Fintype.card (LayerLink N → Multiplicative (ZMod 2))
              : ℝ)⁻¹
            * ∑ S ∈ Finset.univ.filter famEven,
                ((1 + Real.exp (-2 * β)) / 2)
                    ^ (Fintype.card (LayerColumn N) - S.card)
                  * ((1 - Real.exp (-2 * β)) / 2) ^ S.card
                  * ‖∑ u, ((famConfigProd S u : ℝ) : ℂ) * F u‖ ^ 2)
          : ℝ) : ℂ) := by
    calc (∫ u, ∫ u', (starRingEnd ℂ) (F u)
          * layerKernel seatμ seatρ β u u' * F u'
          ∂(Measure.pi fun _ : LayerLink N => seatμ)
          ∂(Measure.pi fun _ : LayerLink N => seatμ))
        = ((Fintype.card (LayerLink N → Multiplicative (ZMod 2))
            : ℝ)⁻¹)
          • ∑ u, (((Fintype.card (LayerLink N
              → Multiplicative (ZMod 2)) : ℝ)⁻¹)
            • ∑ u', (starRingEnd ℂ) (F u)
                * layerKernel seatμ seatρ β u u' * F u') := hP1
      _ = (((Fintype.card (LayerLink N → Multiplicative (ZMod 2))
              : ℝ)⁻¹ : ℂ))
          * ((((Fintype.card (LayerLink N
              → Multiplicative (ZMod 2)) : ℝ)⁻¹ : ℂ))
            * ∑ u, ∑ u', (starRingEnd ℂ) (F u)
                * layerKernel seatμ seatρ β u u' * F u') := by
          have e1 : ∀ x : ℂ,
              ((Fintype.card (LayerLink N → Multiplicative (ZMod 2))
                : ℝ)⁻¹) • x
              = (((Fintype.card (LayerLink N
                  → Multiplicative (ZMod 2)) : ℝ)⁻¹ : ℂ)) * x := by
            intro x
            rw [Complex.real_smul, Complex.ofReal_inv]
          rw [e1]
          congr 1
          rw [← Finset.smul_sum, e1]
      _ = (((Fintype.card (LayerLink N → Multiplicative (ZMod 2))
              : ℝ)⁻¹ : ℂ))
          * ((((Fintype.card (LayerLink N
              → Multiplicative (ZMod 2)) : ℝ)⁻¹ : ℂ))
            * ∑ S ∈ Finset.univ.filter famEven,
                ((((1 + Real.exp (-2 * β)) / 2)
                    ^ (Fintype.card (LayerColumn N) - S.card)
                  * ((1 - Real.exp (-2 * β)) / 2) ^ S.card : ℝ)
                  : ℂ)
                * ((starRingEnd ℂ)
                    (∑ u, ((famConfigProd S u : ℝ) : ℂ) * F u)
                  * (∑ u, ((famConfigProd S u : ℝ) : ℂ) * F u))) := by
          congr 1
          congr 1
          rw [Finset.sum_congr rfl fun u _ =>
            Finset.sum_congr rfl fun u' _ => hKrw u u']
          rw [Finset.sum_congr rfl fun u _ =>
            Finset.sum_congr rfl fun u' _ => hterm u u', hswap]
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [hfac, hZ]
      _ = (((Fintype.card (LayerLink N → Multiplicative (ZMod 2))
            : ℝ)⁻¹
          * ((Fintype.card (LayerLink N → Multiplicative (ZMod 2))
              : ℝ)⁻¹
            * ∑ S ∈ Finset.univ.filter famEven,
                ((1 + Real.exp (-2 * β)) / 2)
                    ^ (Fintype.card (LayerColumn N) - S.card)
                  * ((1 - Real.exp (-2 * β)) / 2) ^ S.card
                  * ‖∑ u, ((famConfigProd S u : ℝ) : ℂ) * F u‖ ^ 2)
          : ℝ) : ℂ) := by
          have hper : ∀ S ∈ Finset.univ.filter famEven,
              ((((1 + Real.exp (-2 * β)) / 2)
                    ^ (Fintype.card (LayerColumn N) - S.card)
                  * ((1 - Real.exp (-2 * β)) / 2) ^ S.card : ℝ)
                  : ℂ)
                * ((starRingEnd ℂ)
                    (∑ u, ((famConfigProd S u : ℝ) : ℂ) * F u)
                  * (∑ u, ((famConfigProd S u : ℝ) : ℂ) * F u))
              = ((((1 + Real.exp (-2 * β)) / 2)
                    ^ (Fintype.card (LayerColumn N) - S.card)
                    * ((1 - Real.exp (-2 * β)) / 2) ^ S.card
                    * ‖∑ u, ((famConfigProd S u : ℝ) : ℂ) * F u‖ ^ 2
                  : ℝ) : ℂ) := by
            intro S _
            have hcc : (starRingEnd ℂ)
                  (∑ u, ((famConfigProd S u : ℝ) : ℂ) * F u)
                * (∑ u, ((famConfigProd S u : ℝ) : ℂ) * F u)
              = ((‖∑ u, ((famConfigProd S u : ℝ) : ℂ) * F u‖ ^ 2
                  : ℝ) : ℂ) :=
              (mul_comm _ _).trans
                ((RCLike.mul_conj _).trans (Complex.ofReal_pow _ _).symm)
            rw [hcc, ← Complex.ofReal_mul]
          rw [Finset.sum_congr rfl hper, ← Complex.ofReal_inv,
            ← Complex.ofReal_sum, ← Complex.ofReal_mul,
            ← Complex.ofReal_mul]
  rw [hP, Complex.ofReal_re]
  have hMnn : (0 : ℝ)
      ≤ ((Fintype.card (LayerLink N → Multiplicative (ZMod 2))
        : ℝ))⁻¹ :=
    inv_nonneg.mpr (by positivity)
  refine mul_nonneg hMnn (mul_nonneg hMnn ?_)
  refine Finset.sum_nonneg fun S _ => ?_
  refine mul_nonneg (mul_nonneg (pow_nonneg ha0 _) (pow_nonneg hb0 _)) ?_
  exact pow_nonneg (norm_nonneg _) _

end FamilyEngine

/-! ## §3 — The degenerate case `N = 1`

At `N = 1` the time direction has a single value, so the "up"
read of `layerConfig` never fires and every plaquette word of
the layer configuration is a commutator
`α c · u ℓ · (α c)⁻¹ · (u ℓ)⁻¹` (the two spatial reads are the
same link; the two stratum reads are the same site).  Its seat
sign is `+1`, every plaquette density is `0`, the layer action
vanishes identically, and the kernel is the constant `1`. -/

/-- At `N = 1` every torus shift is the identity (`1 = 0` in
`ZMod 1`). -/
theorem torusShift_eq_self_one (μ : Fin 4) (x : Fin 4 → ZMod 1) :
    torusShift 1 μ x = x := by
  funext j
  rw [torusShift_apply_coord]
  have h1 : (1 : ZMod 1) = 0 := by decide
  by_cases hj : j = μ
  · subst hj
    rw [Pi.single_eq_same, h1, zero_add]
  · rw [Pi.single_eq_of_ne hj, zero_add]

/-- At `N = 1` every layer shift is the identity. -/
theorem layerShift_eq_self_one (ν : Fin 4) (hν : ν ≠ 0)
    (c : LayerSite 1) : layerShift ν hν c = c := by
  apply Subtype.ext
  show torusShift 1 ν c.1 = c.1
  exact torusShift_eq_self_one ν c.1

/-- The layer configuration one time step above a spatial link
at `N = 1`: the shifted base is the base itself, so this is the
spatial read (the `u'` branch of `layerConfig` is unreachable
at `N = 1`). -/
theorem layerConfig_up_one
    (α : LayerSite 1 → Multiplicative (ZMod 2))
    (u u' : LayerLink 1 → Multiplicative (ZMod 2)) (c : LayerSite 1)
    (ν : Fin 4) (hν : ν ≠ 0) :
    layerConfig α u u' (torusShift 1 0 c.1, ν)
      = u (layerLinkOf c ν hν) := by
  rw [torusShift_eq_self_one]
  exact layerConfig_spatial α u u' c ν hν

/-- At `N = 1` every plaquette word of the layer configuration
has seat sign `+1`: it is the commutator
`α c · u ℓ · (α c)⁻¹ · (u ℓ)⁻¹`, and the sign is a homomorphism
into the commutative group `(ℝ, *)` with inversion invisible. -/
theorem plaquette_seatSign_one
    (α : LayerSite 1 → Multiplicative (ZMod 2))
    (u u' : LayerLink 1 → Multiplicative (ZMod 2)) (c : LayerSite 1)
    (ν : Fin 4) (hν : ν ≠ 0) :
    seatSign (plaquette (torusShift 1) (layerConfig α u u') c.1 0 ν)
      = 1 := by
  unfold plaquette
  rw [layerConfig_time α u u' c, layerConfig_up_one α u u' c ν hν,
    layerConfig_time_shift α u u' ν hν c, layerShift_eq_self_one ν hν c,
    layerConfig_spatial α u u' c ν hν]
  simp only [seatSign_mul, seatSign_inv]
  -- The sign identity `x * y * x * y = 1` for `x * x = y * y = 1`,
  -- proved on abstract reals: `nlinarith`/`ring` over the dependent
  -- atoms themselves rebuilds them with a metavariable proof
  -- argument inside `layerLinkOf`, so the arithmetic is factored
  -- out here.  (The rewrites above are given fully explicit
  -- arguments: `hν` occurs only on their right-hand sides, and a
  -- bare `rw` leaves it as an unsolved side goal whose proof
  -- metavariable then contaminates the main goal.)
  have key : ∀ x y : ℝ, x * x = 1 → y * y = 1 → x * y * x * y = 1 := by
    intro x y hx hy
    have e : x * y * x * y = (x * x) * (y * y) := by ring
    rw [e, hx, hy, mul_one]
  exact key _ _ (seatSign_sq _) (seatSign_sq _)

/-- Every plaquette density of the layer configuration at
`N = 1` vanishes at the seat. -/
theorem plaquetteDensity_layerConfig_one
    (α : LayerSite 1 → Multiplicative (ZMod 2))
    (u u' : LayerLink 1 → Multiplicative (ZMod 2)) (c : LayerSite 1)
    (ν : Fin 4) (hν : ν ≠ 0) :
    plaquetteDensity (torusShift 1) seatρ (layerConfig α u u') c.1 0 ν
      = 0 := by
  have hwd : plaquetteDensity (torusShift 1) seatρ
        (layerConfig α u u') c.1 0 ν
      = wordDensity seatρ
          (plaquette (torusShift 1) (layerConfig α u u') c.1 0 ν) := rfl
  have htr : Matrix.trace (repMatrix seatρ
        (plaquette (torusShift 1) (layerConfig α u u') c.1 0 ν))
      = (seatSign (plaquette (torusShift 1) (layerConfig α u u')
          c.1 0 ν) : ℂ) :=
    charFn_seat _
  rw [hwd]
  unfold wordDensity
  rw [htr, plaquette_seatSign_one α u u' c ν hν]
  simp

/-- At `N = 1` the seat kernel is the constant `1`: the layer
action vanishes identically, since every plaquette density
does. -/
theorem layerKernel_one (β : ℝ)
    (u u' : LayerLink 1 → Multiplicative (ZMod 2)) :
    layerKernel seatμ seatρ β u u' = 1 := by
  have hact : ∀ α : LayerSite 1 → Multiplicative (ZMod 2),
      layerAction seatρ β α u u' = 0 := by
    intro α
    have hsum : (∑ c : LayerSite 1, ∑ ν ∈ Finset.Ioi (0 : Fin 4),
        plaquetteDensity (torusShift 1) seatρ (layerConfig α u u')
          c.1 0 ν) = 0 := by
      refine Finset.sum_eq_zero fun c _ => ?_
      refine Finset.sum_eq_zero fun ν hν => ?_
      exact plaquetteDensity_layerConfig_one α u u' c ν
        (Fin.pos_iff_ne_zero.mp (Finset.mem_Ioi.mp hν))
    show β * (∑ c : LayerSite 1, ∑ ν ∈ Finset.Ioi (0 : Fin 4),
        plaquetteDensity (torusShift 1) seatρ (layerConfig α u u')
          c.1 0 ν) = 0
    rw [hsum, mul_zero]
  have h2 : (∫ α : LayerSite 1 → Multiplicative (ZMod 2),
        (Real.exp (-(layerAction seatρ β α u u')) : ℂ)
        ∂(Measure.pi fun _ : LayerSite 1 => seatμ))
      = ∫ _α : LayerSite 1 → Multiplicative (ZMod 2), (1 : ℂ)
          ∂(Measure.pi fun _ : LayerSite 1 => seatμ) := by
    refine integral_congr_ae (ae_of_all _ fun α => ?_)
    show (Real.exp (-(layerAction seatρ β α u u')) : ℂ) = 1
    rw [hact α]
    simp
  show layerKernel seatμ seatρ β u u' = 1
  rw [show layerKernel seatμ seatρ β u u'
      = ∫ α : LayerSite 1 → Multiplicative (ZMod 2),
          (Real.exp (-(layerAction seatρ β α u u')) : ℂ)
          ∂(Measure.pi fun _ : LayerSite 1 => seatμ) from rfl, h2]
  simp [integral_const]

/-- `LayerKernelPos` at `N = 1`: the kernel is the constant
`1`, the pairing separates, and its real part is a norm square
(the `β = 0` argument at the degenerate seat). -/
theorem layerKernelPos_one {β : ℝ} (_hβ : 0 ≤ β) :
    LayerKernelPos (N := 1) seatμ seatρ β := by
  intro F _hF
  have step1 : (∫ u, ∫ u', (starRingEnd ℂ) (F u)
        * layerKernel seatμ seatρ β u u' * F u'
        ∂(Measure.pi fun _ : LayerLink 1 => seatμ)
        ∂(Measure.pi fun _ : LayerLink 1 => seatμ))
      = (∫ u, (starRingEnd ℂ) (F u)
          * (∫ u', F u' ∂(Measure.pi fun _ : LayerLink 1 => seatμ))
          ∂(Measure.pi fun _ : LayerLink 1 => seatμ)) := by
    apply integral_congr_ae (ae_of_all _ _)
    intro u
    have hinner : (∫ u', (starRingEnd ℂ) (F u)
          * layerKernel seatμ seatρ β u u' * F u'
          ∂(Measure.pi fun _ : LayerLink 1 => seatμ))
        = ∫ u', (starRingEnd ℂ) (F u) * F u'
            ∂(Measure.pi fun _ : LayerLink 1 => seatμ) := by
      apply integral_congr_ae (ae_of_all _ _)
      intro u'
      rw [layerKernel_one β u u', mul_one]
    rw [hinner, integral_const_mul]
  rw [step1, integral_mul_const]
  have hconj : (∫ u, (starRingEnd ℂ) (F u)
        ∂(Measure.pi fun _ : LayerLink 1 => seatμ))
      = (starRingEnd ℂ) (∫ u, F u
        ∂(Measure.pi fun _ : LayerLink 1 => seatμ)) :=
    integral_conj
  rw [hconj]
  have hJ : ((starRingEnd ℂ) (∫ u, F u
          ∂(Measure.pi fun _ : LayerLink 1 => seatμ))
        * (∫ u, F u ∂(Measure.pi fun _ : LayerLink 1 => seatμ)))
      = ((‖∫ u, F u ∂(Measure.pi fun _ : LayerLink 1 => seatμ)‖
          : ℂ)) ^ 2 :=
    (mul_comm _ _).trans (RCLike.mul_conj _)
  rw [hJ, ← Complex.ofReal_pow, Complex.ofReal_re]
  positivity

/-! ## §4 — The headline: the whole abelian seat family -/

/-- **R1 — `LayerKernelPos` at the abelian seat family.**
At `(Multiplicative (ZMod 2), seatρ, seatμ)`, `LayerKernelPos`
holds for **every** `N` and every `β ≥ 0`: for `N ≥ 2` by the
parity filter, the closed form, and the Gram assembly
(`layerKernelPos_abelian_ge`); at the degenerate `N = 1` by
the constant kernel (`layerKernelPos_one`).  Qualitative core
only: no margin floor is claimed (the floor is false at this
seat family), and no dial moves. -/
theorem layerKernelPos_abelian_family {N : ℕ} [NeZero N] {β : ℝ}
    (hβ : 0 ≤ β) :
    LayerKernelPos (N := N) seatμ seatρ β := by
  have hN : 1 ≤ N := Nat.pos_of_ne_zero (NeZero.ne N)
  rcases (by omega : N = 1 ∨ 2 ≤ N) with h1 | h2
  · subst h1
    exact layerKernelPos_one hβ
  · exact layerKernelPos_abelian_ge h2 hβ

end ThetLogos
