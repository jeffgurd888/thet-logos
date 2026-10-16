import ThetLogos.BosonicSecondQuant

/-!
# Bosonic Γ(U) (Rung 10, Task 3) — permanent-minor definition; PARTIAL

The fermionic Γ of Rung 9 was built from **determinant** minors
(`SecondQuantGamma.minorDet`): for fermions each mode is occupied at
most once, so a sector is a *subset* and its lift is a compound matrix
of minors. For bosons a sector is an occupation *configuration*
`c : Config d` (a multiset of modes, repetitions allowed), and the
correct analog of a minor is a **permanent**: enumerate the `tot c`
occupied positions of `c` and of `c'` (repetitions included) and take
the permanent of the matrix of one-particle entries between the two
enumerations, normalized by `√(∏ (c i)!) √(∏ (c' i)!)`.

This file defines that lift and proves what the definition gives
directly:

- `gammaBos_apply_basis` — the kernel formula on basis vectors;
- `gammaBos_sector` — Γ(M) preserves every total-occupation sector;
- `gammaBos_vacuum` — Γ(M) fixes the vacuum.

**What is NOT proved here, priced exactly (hence PARTIAL):**

1. `Γ(1) = 1` and the diagonal action `Γ(diag λ) e_c = (∏ λᵢ^{c i}) e_c`
   both reduce, for this kernel, to the **fiber-permanent counting
   lemma**: the permanent of the fiber-indicator matrix
   `a b ↦ (if enum a = enum b then 1 else 0)` equals `∏ i, (c i)!`
   (it counts the permutations preserving each mode's fiber). This is
   a finite but genuine counting argument about `Matrix.permanent`
   over repeated indices; it is not in Mathlib.
2. Multiplicativity `Γ(M)Γ(N) = Γ(MN)` and unitarity need a
   **permanent Cauchy–Binet identity for repeated indices**: expanding
   `per (M N)` over intermediate index functions and grouping by their
   multiset image, with the `1/∏ c'!` weights matching exactly. This
   is the bosonic analog of Rung 9's rectangular Cauchy–Binet
   campaign (which had to be proved from scratch for determinants);
   the permanent version, with multiplicities, is a separate campaign
   of comparable size.

Labels: finite modes `Fin d`, dense domain `Dom d`, free bosonic
theory scaffolding — not interacting Yang–Mills, not a Millennium
claim.
-/

namespace ThetLogos

open scoped InnerProductSpace
open scoped Matrix

/-! ## 1. Configurations of a fixed total count -/

/-- The finite set of occupation configurations with total count `n`,
built from coordinate functions into `Fin (n + 1)` (a finite type). -/
noncomputable def configsOfTot (d n : ℕ) : Finset (Config d) :=
  (Finset.univ.filter (fun g : Fin d → Fin (n + 1) => ∑ i, (g i).val = n)).image
    (fun g => Finsupp.equivFunOnFinite.symm (fun i => (g i).val))

/-- Membership in `configsOfTot` is exactly `tot c = n` (T1). -/
theorem mem_configsOfTot (d n : ℕ) (c : Config d) :
    c ∈ configsOfTot d n ↔ tot c = n := by
  constructor
  · intro h
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp h
    rw [Finset.mem_filter] at hg
    have htot : tot (Finsupp.equivFunOnFinite.symm (fun i => (g i).val))
        = ∑ i, (g i).val :=
      Finset.sum_congr rfl
        (fun i _ => congrFun (Finsupp.coe_equivFunOnFinite_symm _) i)
    rw [htot]
    exact hg.2
  · intro h
    apply Finset.mem_image.mpr
    have hle : ∀ i, c i ≤ n := by
      intro i
      have h1 : c i ≤ tot c :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (c j)) (Finset.mem_univ i)
      omega
    refine ⟨fun i => ⟨c i, Nat.lt_succ_of_le (hle i)⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · exact h
    · ext i
      exact congrFun (Finsupp.coe_equivFunOnFinite_symm _) i

/-! ## 2. The permanent-minor kernel -/

/-- The sorted enumeration of the occupied positions of `c`: position
`k` (of `tot c` positions) holds the mode sitting there, with
repetitions. Defined from `Finsupp.toMultiset` — no choices beyond the
canonical sort. -/
noncomputable def configEnum (d : ℕ) (c : Config d) (k : Fin (tot c)) : Fin d :=
  ((Finsupp.toMultiset c).sort (· ≤ ·)).get ⟨k.val, by
    have hcard : Multiset.card (Finsupp.toMultiset c) = c.sum (fun _ => id) :=
      Finsupp.card_toMultiset c
    have hsum : c.sum (fun _ => id) = tot c :=
      Finsupp.sum_fintype c (fun _ => id) (fun _ => rfl)
    have hlen : ((Finsupp.toMultiset c).sort (· ≤ ·)).length = tot c := by
      rw [Multiset.length_sort]
      exact hcard.trans hsum
    rw [hlen]
    exact k.isLt⟩

/-- **The bosonic permanent minor** of `M` between configurations `c'`
(rows) and `c` (columns): the permanent of the `tot c × tot c` matrix
of one-particle entries between the sorted enumerations of `c'` and
`c`; `0` when the total counts differ. This is the exact analog of
Rung 9's fermionic `minorDet`, with permanents in place of
determinants because bosonic occupations repeat. -/
noncomputable def perMinor (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ)
    (c' c : Config d) : ℂ :=
  if h : tot c' = tot c then
    Matrix.permanent (fun a b : Fin (tot c) =>
      M (configEnum d c' (finCongr h.symm a)) (configEnum d c b))
  else 0

/-- Permanent minors vanish between different total counts (T1). -/
theorem perMinor_of_tot_ne (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ)
    (c' c : Config d) (h : tot c' ≠ tot c) :
    perMinor d M c' c = 0 :=
  dif_neg h

/-- The bosonic normalization factor `√(∏ i, (c i)!)`. -/
noncomputable def normFactor (d : ℕ) (c : Config d) : ℝ :=
  Real.sqrt (∏ i, (Nat.factorial (c i) : ℝ))

/-- The Γ kernel: permanent minor over the product of normalization
factors. -/
noncomputable def gammaKernel (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ)
    (c' c : Config d) : ℂ :=
  perMinor d M c' c / ((normFactor d c * normFactor d c' : ℝ) : ℂ)

/-- The kernel of `Γ(M)` at the basis vector `e_c`, as a finitely
supported coefficient vector: a finite sum over the configurations of
the same total count. -/
noncomputable def gammaKernelFinsupp (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ)
    (c : Config d) : Config d →₀ ℂ :=
  ∑ c' ∈ configsOfTot d (tot c), (gammaKernel d M c' c) • Finsupp.single c' 1

/-- The coefficient-space bosonic Γ lift, by linear extension of the
kernel on basis vectors. -/
noncomputable def gammaC (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) :
    (Config d →₀ ℂ) →ₗ[ℂ] (Config d →₀ ℂ) :=
  Finsupp.linearCombination ℂ (gammaKernelFinsupp d M)

/-- **Bosonic Γ(M)** on the dense domain `Dom d`, transported from
coefficient space along `boseEquiv`/`boseRepr`. -/
noncomputable def gammaBos (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) :
    Module.End ℂ (Dom d) :=
  (boseEquiv d).toLinearMap ∘ₗ ((gammaC d M) ∘ₗ (boseRepr d).toLinearMap)

/-! ## 3. What the definition proves -/

/-- `gammaBos` acts by transport through coefficient space (T1,
definitional unfolding of the composition). -/
theorem gammaBos_apply (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) (x : Dom d) :
    gammaBos d M x = boseEquiv d (gammaC d M (boseRepr d x)) := rfl

/-- **The kernel formula (T1):** `Γ(M) e_c` is the finite sum, over
configurations `c'` of the same total count, of
`gammaKernel M c' c • e_{c'}`. -/
theorem gammaBos_apply_basis (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) (c : Config d) :
    gammaBos d M ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = ∑ c' ∈ configsOfTot d (tot c), (gammaKernel d M c' c) •
          ⟨boseE d c', Submodule.subset_span (Set.mem_range_self c')⟩ := by
  rw [gammaBos_apply, boseRepr_basis]
  unfold gammaC gammaKernelFinsupp
  rw [Finsupp.linearCombination_single, one_smul, map_sum]
  exact Finset.sum_congr rfl (fun c' _ => by rw [map_smul, boseEquiv_basis])

/-- **Sector preservation (T1):** `Γ(M)` maps `e_c` into the sector
of total count `tot c` in `Dom d`. -/
theorem gammaBos_sector (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) (c : Config d) :
    gammaBos d M ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      ∈ domSector d (tot c) := by
  rw [gammaBos_apply_basis]
  apply Submodule.sum_mem
  intro c' hc'
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨c', (mem_configsOfTot d (tot c) c').mp hc', rfl⟩

/-- **Vacuum preservation (T1):** `Γ(M)` fixes the vacuum — the
`Fin 0` permanent is `1` and the empty normalization is `1`. -/
theorem gammaBos_vacuum (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) :
    gammaBos d M (vacDom d) = vacDom d := by
  have htot0 : tot (0 : Config d) = 0 := by simp [tot]
  have hset : configsOfTot d (tot (0 : Config d)) = {0} := by
    ext c'
    rw [mem_configsOfTot, Finset.mem_singleton]
    constructor
    · intro h
      rw [htot0] at h
      ext i
      rw [Finsupp.zero_apply]
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Nat.zero_le (c' j))).mp h i (Finset.mem_univ i)
    · intro h
      rw [h]
  have hpm : perMinor d M 0 0 = 1 := by
    unfold perMinor
    rw [dif_pos rfl]
    exact Matrix.permanent_eq_one_of_card_eq_zero
      (by rw [Fintype.card_fin]; exact htot0)
  have hnf : normFactor d (0 : Config d) = 1 := by
    simp [normFactor]
  have hk : gammaKernel d M 0 0 = 1 := by
    show perMinor d M (0 : Config d) (0 : Config d) /
        ((normFactor d (0 : Config d) * normFactor d (0 : Config d) : ℝ) : ℂ) = 1
    rw [hpm, hnf]
    simp
  rw [show vacDom d = ⟨boseE d (0 : Config d),
    Submodule.subset_span (Set.mem_range_self (0 : Config d))⟩ from rfl]
  rw [gammaBos_apply_basis, hset, Finset.sum_singleton, hk, one_smul]

end ThetLogos
