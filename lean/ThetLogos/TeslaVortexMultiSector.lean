import Mathlib.Tactic
import ThetLogos.TeslaVortexSeparation
import ThetLogos.FluxClassification

open Filter Topology
open ThetLogos.TeslaVortexSeparation ThetLogos.FluxClassification

namespace ThetLogos.TeslaVortexMultiSector

/-!
# ThetLogos.TeslaVortexMultiSector — Tesla Vortex Modular Dynamics,
# Rung 2: multi-sector separation and ground-sector selection

STATUS: STANDS WHOLE (T1), landed 2026-10-22 (parent-verified:
in-tree build green, axiom check standard-only). Commissioned by
Jeff 2026-10-22 ("both tvmd and Stokes"). Charter:
`whitepaper/tesla-vortex-modular-dynamics-rung2-scoping-2026-10-22.md`.
Rung 1 (two sectors) is `ThetLogos.TeslaVortexSeparation`, landed
2026-10-22, dossier
`whitepaper/tesla-vortex-modular-dynamics-rung1-2026-10-22.md`.

## The idea, at the tier it can carry

Rung 2 generalizes Rung 1's first link only: a Gibbs state over a
finite nonempty family of sectors, with INPUT energies `E : ι → ℝ`
and INPUT charges `q : ι → ℝ`, populates the sectors unequally, and
the normalized thermal expectation of the charge — the *separation*
`S(β) = (Σᵢ qᵢ e^{−βEᵢ}) / (Σᵢ e^{−βEᵢ})` — is a weighted average of
the input charges. As `β → ∞` the zero-temperature state selects the
ground sectors alone: `S(β)` tends to the flat average of the
charges over the sectors of least energy. Rung 1's saturation is the
two-sector shadow of this selection. Thermodynamics converts an
energy splitting into a population separation; it does not create
the splitting, and it does not create the charges.

## Fences (on the face, per the charter)

- **K-TV1:** `q` and the energies `E` are INPUTS. No charge values
  are derived; nothing in this module models a nucleus or an atom.
- **K-TV2:** Links 2–3 of Jeff's chain (separation creating the
  nuclear charge; electrons trapped in magnetic suspension) are NOT
  modeled. They stand as Jeff's T5 picture, with the standing NO-GOs
  the record holds.
- **K-TV3:** "Tesla Vortex" is Jeff's coinage for his electric heat
  gauge vortex — not Tesla's devices, not 3-6-9 numerology.
- **K-TV4:** Monotonicity of the separation in `β` is a TWO-SECTOR
  theorem (Rung 1). It is NOT claimed for `N` sectors in this module,
  and no `N`-sector counterexample is claimed either — the property
  is simply not on this rung's face.

## Status line

NO CLAIM beyond the finite identities proved below and the one
limit (ground-sector selection, §3).

## Contents

- §0: the multi-sector separation `sepN` (T2 definition), the ground
  energy `minEnergy`, the ground sectors `groundSectors`, and the
  maximal input charge `maxAbsCharge`.
- §1 (Target T1): the denominator is positive at every `β`, and the
  separation is a weighted average of the input charges:
  `|sepN q E β| ≤ maxAbsCharge q` at EVERY real `β` (the bound comes
  free at all `β`, not only `β ≥ 0`).
- §2 (Target T2): infinite temperature — `sepN q E 0` is the flat
  average `(Σᵢ qᵢ) / (card ι)`.
- §3 (Target T3, the headline): ground-sector selection — as
  `β → ∞`, `sepN q E β` tends to the average of the charges over the
  ground sectors alone.
- §4 (Target T4): two-sector recovery — at `ι = Fin 2` with charges
  `(+q, −q)`, `sepN` is exactly Rung 1's `thermalSeparation`.
- §5 (Target T5): the flux hook at `N` sectors, over `Fin n` where
  FluxClassification's general form lives: at `β > 0`, the modular
  flux at the `N`-sector Gibbs state's `K = diagModularK w` vanishes
  iff `D` has no entries across distinct energy sectors.
-/

variable {ι : Type*} [Fintype ι] [Nonempty ι]

-- ============================================================================
-- §0. The multi-sector separation, ground data, and the charge bound data
-- ============================================================================

/-- **Multi-sector separation** (Tier T2 — definition): for a finite
nonempty family of sectors indexed by `ι`, INPUT energies
`E : ι → ℝ` and INPUT charges `q : ι → ℝ` (fence K-TV1: `q` and `E`
are inputs, no charge values are derived), and inverse temperature
`β`, the separation is the normalized thermal expectation of the
charge observable under the Gibbs weights `e^{−βEᵢ}`:

    `S(β) = (Σᵢ qᵢ · e^{−βEᵢ}) / (Σᵢ e^{−βEᵢ})`. -/
noncomputable def sepN (q E : ι → ℝ) (β : ℝ) : ℝ :=
  (∑ i, q i * Real.exp (-(β * E i))) / (∑ i, Real.exp (-(β * E i)))

/-- **Ground energy** (Tier T2 — definition): the least of the input
energies, `minEnergy E = minᵢ Eᵢ`, taken as the minimum of the finite
image of `E`. -/
noncomputable def minEnergy (E : ι → ℝ) : ℝ :=
  (Finset.univ.image E).min' (Finset.univ_nonempty.image E)

/-- The ground energy is attained and bounds every sector energy
from below (Tier T1 — proved): `minEnergy E ≤ E i` for all `i`. -/
theorem minEnergy_le (E : ι → ℝ) (i : ι) : minEnergy E ≤ E i :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem E (Finset.mem_univ i))

/-- Some sector attains the ground energy (Tier T1 — proved). -/
theorem exists_eq_minEnergy (E : ι → ℝ) : ∃ i, E i = minEnergy E := by
  have h := Finset.min'_mem (Finset.univ.image E) (Finset.univ_nonempty.image E)
  rcases Finset.mem_image.mp h with ⟨i, -, hi⟩
  exact ⟨i, hi⟩

/-- **Ground sectors** (Tier T2 — definition): the sectors of least
input energy, `{i | E i = minEnergy E}`. -/
noncomputable def groundSectors (E : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => E i = minEnergy E)

/-- Membership in the ground sectors is energy equality with the
ground energy (Tier T1 — proved). -/
theorem mem_groundSectors {E : ι → ℝ} {i : ι} :
    i ∈ groundSectors E ↔ E i = minEnergy E := by
  simp [groundSectors]

/-- The ground sectors are nonempty (Tier T1 — proved): the
zero-temperature average of §3 is over a nonempty finite set, so its
denominator `(groundSectors E).card` is positive. -/
theorem groundSectors_nonempty (E : ι → ℝ) : (groundSectors E).Nonempty := by
  obtain ⟨i, hi⟩ := exists_eq_minEnergy E
  exact ⟨i, mem_groundSectors.mpr hi⟩

/-- **Maximal input charge** (Tier T2 — definition): the largest of
the absolute input charges, `maxAbsCharge q = maxᵢ |qᵢ|`, taken as
the maximum of the finite image of `|q ∘ ·|`. -/
noncomputable def maxAbsCharge (q : ι → ℝ) : ℝ :=
  (Finset.univ.image (fun i => |q i|)).max' (Finset.univ_nonempty.image _)

/-- Every input charge is bounded by the maximal one (Tier T1 —
proved): `|q i| ≤ maxAbsCharge q` for all `i`. -/
theorem abs_charge_le_maxAbsCharge (q : ι → ℝ) (i : ι) :
    |q i| ≤ maxAbsCharge q := by
  have h : (fun i => |q i|) i ∈ Finset.univ.image (fun i => |q i|) :=
    Finset.mem_image_of_mem _ (Finset.mem_univ i)
  exact Finset.le_max' _ _ h

/-- The maximal input charge is nonnegative (Tier T1 — proved). -/
theorem maxAbsCharge_nonneg (q : ι → ℝ) : 0 ≤ maxAbsCharge q := by
  obtain ⟨i₀, -⟩ := Finset.univ_nonempty (α := ι)
  exact le_trans (abs_nonneg _) (abs_charge_le_maxAbsCharge q i₀)

-- ============================================================================
-- §1. Well-definedness and the weighted-average bound (Target T1)
-- ============================================================================

/-- **TARGET T1, well-definedness** (Tier T1 — proved): the Gibbs
denominator is a sum of positive exponentials over a nonempty index
type, hence positive at EVERY real `β`:

    `0 < Σᵢ e^{−βEᵢ}`. -/
theorem sepN_denominator_pos (E : ι → ℝ) (β : ℝ) :
    0 < ∑ i, Real.exp (-(β * E i)) :=
  Finset.sum_pos (fun i _ => Real.exp_pos (-(β * E i))) Finset.univ_nonempty

/-- **TARGET T1, the bound** (Tier T1 — proved): the separation is a
weighted average of the input charges, so it lies inside their
range at EVERY real `β` (the charter asked for `β ≥ 0`; the bound
comes free at all `β`, since the Gibbs weights are positive at
every `β`):

    `|sepN q E β| ≤ maxᵢ |qᵢ|`. -/
theorem sepN_abs_le (q E : ι → ℝ) (β : ℝ) :
    |sepN q E β| ≤ maxAbsCharge q := by
  have hden : (0 : ℝ) < ∑ i, Real.exp (-(β * E i)) := sepN_denominator_pos E β
  rw [sepN, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  calc |∑ i, q i * Real.exp (-(β * E i))|
      ≤ ∑ i, |q i * Real.exp (-(β * E i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, maxAbsCharge q * Real.exp (-(β * E i)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (abs_charge_le_maxAbsCharge q i)
          (le_of_lt (Real.exp_pos _))
    _ = maxAbsCharge q * ∑ i, Real.exp (-(β * E i)) := by
        rw [Finset.mul_sum]

-- ============================================================================
-- §2. Infinite temperature (Target T2)
-- ============================================================================

/-- **TARGET T2 — infinite temperature** (Tier T1 — proved): at
`β = 0` every Gibbs weight is `1`, so the separation is the flat
average of the input charges:

    `sepN q E 0 = (Σᵢ qᵢ) / (card ι)`. -/
theorem sepN_zero_beta (q E : ι → ℝ) :
    sepN q E 0 = (∑ i, q i) / (Fintype.card ι : ℝ) := by
  unfold sepN
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

-- ============================================================================
-- §3. Ground-sector selection (Target T3)
-- ============================================================================

/-- **The shifted form** (Tier T1 — proved): factoring the ground
sector's Gibbs weight `e^{−β·minEnergy}` out of numerator and
denominator (it cancels, being positive), the separation is a ratio
of *relative* weights `e^{−β(Eᵢ − minEnergy)}`:

    `sepN q E β = (Σᵢ qᵢ e^{−β(Eᵢ − m)}) / (Σᵢ e^{−β(Eᵢ − m)})`,

where `m = minEnergy E`. Every relative weight lies in `(0, 1]`,
equals `1` exactly on the ground sectors, and dies as `β → ∞` off
them — the form in which the §3 limit is read off. -/
theorem sepN_eq_shifted (q E : ι → ℝ) (β : ℝ) :
    sepN q E β
      = (∑ i, q i * Real.exp (-(β * (E i - minEnergy E))))
        / (∑ i, Real.exp (-(β * (E i - minEnergy E)))) := by
  have hfactor : ∀ i : ι, Real.exp (-(β * E i))
      = Real.exp (-(β * minEnergy E)) * Real.exp (-(β * (E i - minEnergy E))) := by
    intro i
    rw [← Real.exp_add]
    congr 1
    ring
  have hne : Real.exp (-(β * minEnergy E)) ≠ 0 := Real.exp_ne_zero _
  have hnum : (∑ i, q i * Real.exp (-(β * E i)))
      = Real.exp (-(β * minEnergy E))
        * ∑ i, q i * Real.exp (-(β * (E i - minEnergy E))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hfactor i]
    ring
  have hden : (∑ i, Real.exp (-(β * E i)))
      = Real.exp (-(β * minEnergy E))
        * ∑ i, Real.exp (-(β * (E i - minEnergy E))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hfactor i]
  rw [sepN, hnum, hden, mul_div_mul_left _ _ hne]

/-- **TARGET T3 — ground-sector selection** (Tier T1 — proved): as
`β → ∞`, the separation tends to the flat average of the charges
over the ground sectors alone:

    `sepN q E β ⟶ (Σ_{i ∈ ground} qᵢ) / (card ground)`.

Proof: in the shifted form of `sepN_eq_shifted`, each relative
weight `e^{−β(Eᵢ − m)}` is constantly `1` on the ground sectors
(`Eᵢ = m`) and tends to `0` off them (`Eᵢ − m > 0`, via
`Real.tendsto_exp_neg_atTop_nhds_zero`); the finite sums pass to
their termwise limits, and the ground sectors are nonempty, so the
limiting denominator `(card ground : ℝ)` is nonzero. The
zero-temperature state selects the ground sectors; every excited
sector's weight dies. Rung 1's saturation is the two-sector shadow
of this selection. Fence K-TV1 stands: the selected sectors are
the INPUT energies' minimizers; no charge is derived. -/
theorem tendsto_sepN_atTop (q E : ι → ℝ) :
    Tendsto (fun β => sepN q E β) atTop
      (𝓝 ((∑ i ∈ groundSectors E, q i) / ((groundSectors E).card : ℝ))) := by
  classical
  -- Termwise limits, numerator: `q i` on the ground sectors, `0` off them.
  have htermN : ∀ i : ι, Tendsto (fun β => q i * Real.exp (-(β * (E i - minEnergy E))))
      atTop (𝓝 (if E i = minEnergy E then q i else 0)) := by
    intro i
    by_cases hi : E i = minEnergy E
    · have hfun : (fun β => q i * Real.exp (-(β * (E i - minEnergy E))))
          = fun _ => q i := by
        funext β
        rw [hi, sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
      rw [ite_eq_left hi, hfun]
      exact tendsto_const_nhds
    · have hd : (0 : ℝ) < E i - minEnergy E := by
        have hle := minEnergy_le E i
        exact sub_pos.mpr (lt_of_le_of_ne hle (fun h => hi h.symm))
      have ht : Tendsto (fun β : ℝ => Real.exp (-(β * (E i - minEnergy E))))
          atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp ((tendsto_id).atTop_mul_const hd)
      rw [ite_eq_right hi]
      simpa using ht.const_mul (q i)
  -- Termwise limits, denominator: `1` on the ground sectors, `0` off them.
  have htermD : ∀ i : ι, Tendsto (fun β => Real.exp (-(β * (E i - minEnergy E))))
      atTop (𝓝 (if E i = minEnergy E then (1 : ℝ) else 0)) := by
    intro i
    by_cases hi : E i = minEnergy E
    · have hfun : (fun β => Real.exp (-(β * (E i - minEnergy E))))
          = fun _ => (1 : ℝ) := by
        funext β
        rw [hi, sub_self, mul_zero, neg_zero, Real.exp_zero]
      rw [ite_eq_left hi, hfun]
      exact tendsto_const_nhds
    · have hd : (0 : ℝ) < E i - minEnergy E := by
        have hle := minEnergy_le E i
        exact sub_pos.mpr (lt_of_le_of_ne hle (fun h => hi h.symm))
      rw [ite_eq_right hi]
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp ((tendsto_id).atTop_mul_const hd)
  have hN := tendsto_finsetSum Finset.univ (fun i _ => htermN i)
  have hD := tendsto_finsetSum Finset.univ (fun i _ => htermD i)
  -- The limiting sums collapse to sums over the ground sectors.
  have hsumN : (∑ i, if E i = minEnergy E then q i else 0)
      = ∑ i ∈ groundSectors E, q i := by
    show (∑ i, if E i = minEnergy E then q i else 0)
      = ∑ i ∈ Finset.univ.filter (fun i => E i = minEnergy E), q i
    rw [Finset.sum_filter]
  have hsumD : (∑ i, if E i = minEnergy E then (1 : ℝ) else 0)
      = ((groundSectors E).card : ℝ) := by
    have e : (∑ i ∈ groundSectors E, (1 : ℝ)) = ((groundSectors E).card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [← e]
    show (∑ i, if E i = minEnergy E then (1 : ℝ) else 0)
      = ∑ i ∈ Finset.univ.filter (fun i => E i = minEnergy E), (1 : ℝ)
    rw [Finset.sum_filter]
  rw [hsumN] at hN
  rw [hsumD] at hD
  have hcard : ((groundSectors E).card : ℝ) ≠ 0 := by
    have hpos : 0 < (groundSectors E).card :=
      Finset.card_pos.mpr (groundSectors_nonempty E)
    exact_mod_cast ne_of_gt hpos
  have hdiv := hN.div hD hcard
  have hfun : (fun β => sepN q E β)
      = (fun β => (∑ i, q i * Real.exp (-(β * (E i - minEnergy E))))
          / (∑ i, Real.exp (-(β * (E i - minEnergy E))))) :=
    funext fun β => sepN_eq_shifted q E β
  rw [hfun]
  exact hdiv

-- ============================================================================
-- §4. Two-sector recovery (Target T4)
-- ============================================================================

/-- **TARGET T4 — two-sector recovery** (Tier T1 — proved): at
`ι = Fin 2` with the charge assignment `(+q, −q)` (sector `0`
carries `+q`, sector `1` carries `−q`), the multi-sector separation
is exactly Rung 1's two-sector `thermalSeparation q E β` — proved
from Rung 1's exact formula `thermalSeparation_eq_exp_formula`.
The generalization welds back onto the brick it generalizes. -/
theorem sepN_fin_two_eq_thermalSeparation (q : ℝ) (E : Fin 2 → ℝ) (β : ℝ) :
    sepN (fun i : Fin 2 => if i = 0 then q else -q) E β
      = thermalSeparation q E β := by
  have hc0 : (fun i : Fin 2 => if i = 0 then q else -q) 0 = q := by simp
  have hc1 : (fun i : Fin 2 => if i = 0 then q else -q) 1 = -q := by simp
  unfold sepN
  rw [Fin.sum_univ_two, Fin.sum_univ_two, hc0, hc1,
    thermalSeparation_eq_exp_formula]
  congr 1
  ring

-- ============================================================================
-- §5. The flux hook at N sectors (Target T5)
-- ============================================================================

/-- At positive `β`, the `N`-sector Gibbs weights over `Fin n`
separate the sectors exactly when the energies do (Tier T1 —
proved): `e^{−βEᵢ} = e^{−βEⱼ} ⟺ Eᵢ = Eⱼ`. -/
theorem gibbsWeight_eq_iff {n : ℕ} (E : Fin n → ℝ) {β : ℝ} (hβ : 0 < β)
    (i j : Fin n) :
    Real.exp (-(β * E i)) = Real.exp (-(β * E j)) ↔ E i = E j := by
  constructor
  · intro h
    have harg : -(β * E i) = -(β * E j) := Real.exp_strictMono.injective h
    have h2 : β * E i = β * E j := neg_inj.mp harg
    exact mul_left_cancel₀ (ne_of_gt hβ) h2
  · intro h
    rw [h]

/-- **TARGET T5 — the flux hook at N sectors** (Tier T1 — proved,
via FluxClassification's general form
`classification_diagModularK_of_pos`): let `wⱼ = e^{−βEⱼ}` be the
`N`-sector Gibbs weights over `Fin n` and `K = diagModularK w` their
modular Hamiltonian. At `β > 0`, the modular flux
`φ = i[K, D]` vanishes iff `D` has no entries across distinct
*energy* sectors:

    `φ = 0 ⟺ ∀ i j, E i ≠ E j → D i j = 0`.

At positive `β` the Gibbs weights separate the sectors exactly when
the energies do (`gibbsWeight_eq_iff`), so the weight-level sectors
of the classification are the energy level sets. Fence K-TV1
stands: the sectors are the INPUT energies' level sets; no charge
is derived. -/
theorem gibbs_flux_eq_zero_iff_sectors {n : ℕ} (E : Fin n → ℝ) (β : ℝ)
    (hβ : 0 < β) (D : Matrix (Fin n) (Fin n) ℂ) :
    modularFlux (diagModularK (fun j => Real.exp (-(β * E j)))) D = 0
      ↔ ∀ i j, E i ≠ E j → D i j = 0 := by
  rw [classification_diagModularK_of_pos _ (fun j => Real.exp_pos _) D]
  constructor
  · intro h i j hij
    exact h i j (fun hw_eq => hij ((gibbsWeight_eq_iff E hβ i j).mp hw_eq))
  · intro h i j hij
    exact h i j (fun hE_eq => hij ((gibbsWeight_eq_iff E hβ i j).mpr hE_eq))

/-- **TARGET T5, witness form** (Tier T1 — proved, via
FluxClassification): at `β > 0`, a Dirac operator with a nonzero
cross-sector entry `D i j ≠ 0` between distinct energy sectors has
nonzero modular flux at the `N`-sector Gibbs state's `K`: coupling
distinct energy sectors switches the flux on. -/
theorem gibbs_flux_ne_zero_of_cross_entry {n : ℕ} (E : Fin n → ℝ) (β : ℝ)
    (hβ : 0 < β) (D : Matrix (Fin n) (Fin n) ℂ) {i j : Fin n}
    (hE : E i ≠ E j) (hD : D i j ≠ 0) :
    modularFlux (diagModularK (fun k => Real.exp (-(β * E k)))) D ≠ 0 := by
  apply flux_diagModularK_ne_zero_of_entry _ _ _ hD
  simp only [Real.log_exp]
  intro hcon
  apply hE
  have h1 : β * E i = β * E j := neg_inj.mp hcon
  exact mul_left_cancel₀ (ne_of_gt hβ) h1

-- Axiom check (headlines): expect exactly [propext, Classical.choice, Quot.sound].
#print axioms sepN_denominator_pos
#print axioms sepN_abs_le
#print axioms sepN_zero_beta
#print axioms tendsto_sepN_atTop
#print axioms sepN_fin_two_eq_thermalSeparation
#print axioms gibbs_flux_eq_zero_iff_sectors
#print axioms gibbs_flux_ne_zero_of_cross_entry

end ThetLogos.TeslaVortexMultiSector
