import Mathlib.Tactic
import ThetLogos.BoundarySeat
import ThetLogos.BridgeLaplacian
import ThetLogos.FallPin

/-!
# ThetLogos.FallFloorPin — the arrival pin (lane grade)

Scope: `~/workspace/your_files/fall-floor-pin-scope-2026-11-18.md`.
Commissioned by Zero 2026-11-18 00:34 EST ("make gravity hit the
floor"). Working label only; Zero names.

FALL-1 proved falls END. This pin is the arrival statement:
descent doesn't just terminate — it arrives at THE floor.
(a) a global floor exists and its grounded value is exactly 0;
(b) no stranding above it — true as stated, and cheap on this
seat: `hpos` makes the seat complete and `IsFallMin` already
quantifies over all sites, so a descent minimum is a global
minimizer by definition (the scope says so on its face);
(c) uniqueness is FALSE as stated — **K-FALL-FLOOR-DUP fires**
(`ρ = 0` gives `φ ≡ 0`, the floor attained at every site,
exhibited at FF-6) — and the saved form is the sharp dichotomy
FF-5a/FF-5b. FF-7 is the configuration form: the grounded
potential is the unique global minimizer of the fall energy.

Banked per brick (build PASS + olean on disk + axcheck +
mechanical hash per brick). Statements are the scope's frozen
menu; any proof that needs a statement changed stops and
re-scopes at full rank.

FENCES: T5 charter, NO CLAIM, dials 0/4, Dial 2 = 0. The floor
here is a minimum of a finite potential / of a finite Dirichlet
functional — not a falling body, not dynamics, not gravity.
K-FALL-SCOPE stands over any stronger presentation.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Brick 1 — arrival (FF-1..FF-4) -/

/-- **FF-1 — descent minima are global.** `IsFallMin` compares
against every site, so a descent minimum of any potential on a
finite seat is a global minimizer. The bridge lemma of the pin;
its content is the completeness of the seat, stated on its
face. -/
theorem isFallMin_global (φ : V → ℝ) {m : V} (h : IsFallMin φ m) :
    ∀ j, φ m ≤ φ j := by
  intro j
  by_cases hj : j = m
  · subst hj
    exact le_refl _
  · exact h j hj

/-- **FF-2 — termination lands on the floor.** From any start,
some global minimizer of `φ` is reached by a descent path.
(FF-1 composed with FALL-1's `fallPath_terminates`.) The
maximal-path reading is the same statement: a path that cannot
be extended by a strict step ends at an `IsFallMin`, hence at
a global minimizer. -/
theorem fallPath_terminates_at_floor (φ : V → ℝ) (i : V) :
    ∃ m, (∀ j, φ m ≤ φ j) ∧ FallPath φ i m := by
  obtain ⟨m, hm, hp⟩ := fallPath_terminates φ i
  exact ⟨m, isFallMin_global φ hm, hp⟩

/-- **FF-3 — the grounded floor value.** For a nonnegative
source, the floor of the grounded potential is exactly `0`,
attained at the ground. Packaging of FALL-1 §3
(`groundedPotential_nonneg`, `groundedPotential_at_ground`) as
a floor-value statement; weight low, stated as such. -/
theorem groundedPotential_floor_value (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (ρ : V → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) :
    (∀ j, 0 ≤ groundedPotential w hw hw0 hpos b ρ j)
      ∧ groundedPotential w hw hw0 hpos b ρ b = 0 :=
  ⟨fun j => groundedPotential_nonneg w hw hw0 hpos b ρ hρ j,
   groundedPotential_at_ground w hw hw0 hpos b ρ⟩

/-- **FF-4 — the grounded fall hits the floor, any sign.** For
ANY source `ρ` — no sign hypothesis — descent of the grounded
potential from any site reaches a global minimizer. This is
no-stranding in its strongest honest form: what the sign of
`ρ` controls is whether the floor sits at the ground (FF-3,
FF-5), never whether the fall arrives. -/
theorem groundedPotential_fallPath_hits_floor (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (ρ : V → ℝ)
    (i : V) :
    ∃ m, (∀ j, groundedPotential w hw hw0 hpos b ρ m
        ≤ groundedPotential w hw hw0 hpos b ρ j)
      ∧ FallPath (groundedPotential w hw hw0 hpos b ρ) i m := by
  obtain ⟨m, hm, hp⟩ :=
    groundedPotential_fallPath_terminates w hw hw0 hpos b ρ i
  exact ⟨m, isFallMin_global _ hm, hp⟩

/-! ## Brick 2 — the dichotomy and its countermodel (FF-5, FF-6) -/

/-- **FF-5a — uniqueness under one positive site.** For
`ρ ≥ 0` with `ρ i > 0` at some ungrounded site, the ground is
the UNIQUE descent minimum (hence unique global minimizer) of
the grounded potential.

PROOF: by contradiction at a minimizer `m ≠ b`. `IsFallMin`
at `b` gives `φ m ≤ φ b = 0`; FF-3's nonnegativity gives
`φ m = 0`. The Poisson sum at `m`
(`laplacianOp_groundedPotential`, `m ≠ b`) has every term
`w m k * (φ m - φ k) ≤ 0` and sums to `ρ m ≥ 0`, so every term
vanishes (the `Finset.sum_eq_zero_iff_of_nonpos` step of
FALL-1's `groundedPotential_nonneg`); `w m k > 0` then forces
`φ k = φ m = 0` for all `k`. Hence `ρ i = laplacianOp w φ i
= 0` (every term `w i j * (0 - 0)`), against `0 < ρ i`. -/
theorem groundedPotential_unique_floor_of_pos (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (ρ : V → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) {i : V} (hi : i ≠ b) (hρi : 0 < ρ i)
    {m : V}
    (hm : IsFallMin (groundedPotential w hw hw0 hpos b ρ) m) :
    m = b := by
  classical
  by_contra hmb
  have hφb : groundedPotential w hw hw0 hpos b ρ b = 0 :=
    groundedPotential_at_ground w hw hw0 hpos b ρ
  have hle : groundedPotential w hw hw0 hpos b ρ m
      ≤ groundedPotential w hw hw0 hpos b ρ b := hm b (Ne.symm hmb)
  rw [hφb] at hle
  have hge : 0 ≤ groundedPotential w hw hw0 hpos b ρ m :=
    groundedPotential_nonneg w hw hw0 hpos b ρ hρ m
  have hm0 : groundedPotential w hw hw0 hpos b ρ m = 0 :=
    le_antisymm hle hge
  have hterm : ∀ k ∈ Finset.univ,
      w m k * (groundedPotential w hw hw0 hpos b ρ m
        - groundedPotential w hw hw0 hpos b ρ k) ≤ 0 := by
    intro k _
    apply mul_nonpos_of_nonneg_of_nonpos (hw0 m k)
    by_cases hk : k = m
    · rw [hk, sub_self]
    · have hmk := hm k hk
      linarith
  have hsum0 : ∑ k, w m k * (groundedPotential w hw hw0 hpos b ρ m
      - groundedPotential w hw hw0 hpos b ρ k) = 0 := by
    have h1 : ∑ k, w m k * (groundedPotential w hw hw0 hpos b ρ m
        - groundedPotential w hw hw0 hpos b ρ k) ≤ 0 :=
      Finset.sum_nonpos hterm
    have hL : laplacianOp w (groundedPotential w hw hw0 hpos b ρ) m
        = ρ m :=
      laplacianOp_groundedPotential w hw hw0 hpos b ρ hmb
    rw [laplacianOp_apply] at hL
    linarith [hρ m]
  have hzero : ∀ k ∈ Finset.univ,
      w m k * (groundedPotential w hw hw0 hpos b ρ m
        - groundedPotential w hw hw0 hpos b ρ k) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos hterm).mp hsum0
  have hall : ∀ k, groundedPotential w hw hw0 hpos b ρ k = 0 := by
    intro k
    by_cases hk : k = m
    · rw [hk]; exact hm0
    · have hz := hzero k (Finset.mem_univ k)
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h (ne_of_gt (hpos m k (Ne.symm hk)))
      · have hmk : groundedPotential w hw hw0 hpos b ρ m
            = groundedPotential w hw hw0 hpos b ρ k :=
          sub_eq_zero.mp h
        rw [hm0] at hmk
        exact hmk.symm
  have hLi : laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i
      = ρ i :=
    laplacianOp_groundedPotential w hw hw0 hpos b ρ hi
  rw [laplacianOp_apply] at hLi
  have hzero_sum : ∑ j, w i j * (groundedPotential w hw hw0 hpos b ρ i
      - groundedPotential w hw hw0 hpos b ρ j) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hall i, hall j, sub_self, mul_zero]
  rw [hzero_sum] at hLi
  linarith

/-- **FF-5b — the vanishing case.** If the source vanishes at
every ungrounded site, the grounded potential is identically
zero: the floor is attained at every site. The dichotomy's
other half — and the reason naive uniqueness is false (FF-6).

PROOF: `groundedPotential_unique` applied to
`φ = groundedPotential … ρ` and `ψ = 0`: `ψ b = 0` is
`Pi.zero_apply`; at ungrounded `i`,
`laplacianOp w 0 i = ∑ j, w i j * (0 - 0) = 0 = ρ i` by
`laplacianOp_apply` and `(hρ i hi).symm`. -/
theorem groundedPotential_eq_zero_of_source_vanishes
    (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (ρ : V → ℝ)
    (hρ : ∀ i ≠ b, ρ i = 0) :
    groundedPotential w hw hw0 hpos b ρ = 0 := by
  refine groundedPotential_unique w hw hw0 hpos b ρ
    (groundedPotential w hw hw0 hpos b ρ) 0 ?_ ?_ ?_ ?_
  · exact groundedPotential_at_ground w hw hw0 hpos b ρ
  · rfl
  · intro i hi
    exact laplacianOp_groundedPotential w hw hw0 hpos b ρ hi
  · intro i hi
    have h0 : laplacianOp w (0 : V → ℝ) i = 0 := by
      rw [laplacianOp_apply]
      simp
    rw [h0]
    exact (hρ i hi).symm

/-- **FF-6 — the dup exhibit: K-FALL-FLOOR-DUP, made
concrete.** On Fin 2 there is a seat and a (zero) source whose
grounded potential has TWO distinct global minima. Naive
uniqueness of the floor is false; FF-5a/FF-5b are the saved
form.

PROOF: unit off-diagonal weights `w = ![![0, 1], ![1, 0]]`
(the `fin_cases` + `norm_num` pattern of FALL-1 §4),
`ρ = ![0, 0]`; `groundedPotential … = ![0, 0]` by
`groundedPotential_unique` against `![0, 0]` (ground value
`0`; `laplacianOp` of the zero vector is `0` at site `1` by
`Fin.sum_univ_two`); both sites are then descent minima since
the potential is identically `0`; `(0 : Fin 2) ≠ 1` by
`decide`. -/
theorem fall_floor_not_unique :
    ∃ (w : Fin 2 → Fin 2 → ℝ) (hw : ∀ i j, w i j = w j i)
      (hw0 : ∀ i j, 0 ≤ w i j) (hpos : ∀ i j, i ≠ j → 0 < w i j)
      (ρ : Fin 2 → ℝ),
      (0 : Fin 2) ≠ 1
      ∧ IsFallMin (groundedPotential w hw hw0 hpos 0 ρ) 0
      ∧ IsFallMin (groundedPotential w hw hw0 hpos 0 ρ) 1 := by
  classical
  have hwA : ∀ i j : Fin 2,
      ((![![0, 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) i j)
        = ((![![0, 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) j i) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
  have hw0A : ∀ i j : Fin 2,
      0 ≤ ((![![0, 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) i j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
  have hposA : ∀ i j : Fin 2, i ≠ j →
      0 < ((![![0, 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) i j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
  have hpot : groundedPotential
        ![![0, 1], ![1, 0]] hwA hw0A hposA 0 ![0, 0]
      = ![0, 0] := by
    refine groundedPotential_unique _ hwA hw0A hposA 0 ![0, 0]
      (groundedPotential _ hwA hw0A hposA 0 ![0, 0]) _ ?_ ?_ ?_ ?_
    · exact groundedPotential_at_ground _ _ _ _ _ _
    · simp [Matrix.cons_val_zero]
    · intro i hi
      exact laplacianOp_groundedPotential _ _ _ _ _ _ hi
    · intro i hi
      have h2 : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
      rcases h2 i with rfl | rfl
      · exact absurd rfl hi
      · rw [laplacianOp_apply, Fin.sum_univ_two]
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
  refine ⟨![![0, 1], ![1, 0]], hwA, hw0A, hposA, ![0, 0],
    by decide, ?_, ?_⟩
  · rw [hpot]
    intro j hj
    have h2 : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
    rcases h2 j with rfl | rfl
    · exact absurd rfl hj
    · norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
  · rw [hpot]
    intro j hj
    have h2 : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
    rcases h2 j with rfl | rfl
    · norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
    · exact absurd rfl hj

/-! ## Brick 3 — the Dirichlet floor (FF-7) -/

/-- **The fall energy** of a candidate potential `ψ`: the
Dirichlet functional whose global minimizer over grounded
candidates is the grounded potential (FF-7). Half the
Laplacian quadratic form, minus the source pairing over the
ungrounded sites. (The ground's own source value never
enters: a grounded candidate vanishes at `b`.) -/
noncomputable def fallEnergy (w : V → V → ℝ) (b : V) (ρ : V → ℝ)
    (ψ : V → ℝ) : ℝ :=
  (1 / 2) * (∑ i, ψ i * laplacianOp w ψ i)
    - ∑ i ∈ Finset.univ.erase b, ρ i * ψ i

/-- **FF-7a — the grounded potential minimizes the fall
energy** over all grounded candidates.

PROOF: write `ψ = φ + u` with `φ = groundedPotential … ρ`
and `u b = 0` (from `hψb` and `groundedPotential_at_ground`).
Expand the quadratic form by `laplacianOp_apply` /
`laplacianOp_symm_form`:
`∑ ψ * L ψ = ∑ φ * L φ + 2 * ∑ u * L φ + ∑ u * L u`. The cross
term collapses to the erased pairing:
`∑ i, u i * laplacianOp w φ i = ∑ i ∈ univ.erase b, ρ i * u i`,
since `laplacianOp_groundedPotential` gives `L φ = ρ` at
ungrounded sites and `u b = 0` kills the ground term. Hence
`fallEnergy ψ - fallEnergy φ = (1/2) * ∑ u * L u ≥ 0` by
`energy_nonneg`. The erased-sum bookkeeping at `b` is the
fiddly joint (scope §4, Brick 3). -/
theorem groundedPotential_minimizes_fallEnergy (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (ρ : V → ℝ)
    (ψ : V → ℝ) (hψb : ψ b = 0) :
    fallEnergy w b ρ (groundedPotential w hw hw0 hpos b ρ)
      ≤ fallEnergy w b ρ ψ := by

  classical
  set u : V → ℝ := fun k => ψ k - groundedPotential w hw hw0 hpos b ρ k with hu
  have hub : u b = 0 := by
    have e1 : u b = ψ b - groundedPotential w hw hw0 hpos b ρ b := rfl
    rw [e1, hψb, groundedPotential_at_ground w hw hw0 hpos b ρ,
      sub_self]
  have hψu : ∀ i, ψ i = groundedPotential w hw hw0 hpos b ρ i + u i := by
    intro i
    have e1 : u i = ψ i - groundedPotential w hw hw0 hpos b ρ i := rfl
    rw [e1]; ring
  have hLu : ∀ i, laplacianOp w ψ i
      = laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i + laplacianOp w u i := by
    intro i
    rw [laplacianOp_apply, laplacianOp_apply, laplacianOp_apply,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have e1 : ψ i - ψ j
        = (groundedPotential w hw hw0 hpos b ρ i - groundedPotential w hw hw0 hpos b ρ j) + (u i - u j) := by
      rw [hψu i, hψu j]; ring
    rw [e1, mul_add]
  have hquad : ∑ i, ψ i * laplacianOp w ψ i
      = ∑ i, groundedPotential w hw hw0 hpos b ρ i * laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i
        + 2 * (∑ i, u i * laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i)
        + ∑ i, u i * laplacianOp w u i := by
    have hterm : ∀ i, ψ i * laplacianOp w ψ i
        = groundedPotential w hw hw0 hpos b ρ i * laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i
          + (groundedPotential w hw hw0 hpos b ρ i * laplacianOp w u i
            + u i * laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i)
          + u i * laplacianOp w u i := by
      intro i
      rw [hψu i, hLu i]; ring
    have hsplit : (∑ i, ψ i * laplacianOp w ψ i)
        = ∑ i, (groundedPotential w hw hw0 hpos b ρ i * laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i
          + (groundedPotential w hw hw0 hpos b ρ i * laplacianOp w u i
            + u i * laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i)
          + u i * laplacianOp w u i) :=
      Finset.sum_congr rfl (fun i _ => hterm i)
    rw [hsplit]
    simp only [Finset.sum_add_distrib]
    rw [← laplacianOp_symm_form w hw (groundedPotential w hw hw0 hpos b ρ) u]
    ring
  have hpair : ∑ i, u i * laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i
      = ∑ i ∈ Finset.univ.erase b, ρ i * u i := by
    have h := Finset.sum_erase_add Finset.univ
      (fun i => u i * laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i) (Finset.mem_univ b)
    rw [hub, zero_mul, add_zero] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≠ b := (Finset.mem_erase.mp hi).1
    rw [laplacianOp_groundedPotential w hw hw0 hpos b ρ hi',
      mul_comm]
  have hpairψ : ∑ i ∈ Finset.univ.erase b, ρ i * ψ i
      = ∑ i ∈ Finset.univ.erase b, ρ i * groundedPotential w hw hw0 hpos b ρ i
        + ∑ i ∈ Finset.univ.erase b, ρ i * u i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hψu i]; ring

  have hnn := energy_nonneg w hw hw0 u
  unfold fallEnergy
  rw [hquad, hpairψ, ← hpair]
  linarith

/-- **FF-7b — the minimizer is unique.** A grounded candidate
whose fall energy does not exceed the grounded potential's
IS the grounded potential: gravity's floor, in the energy
form, has exactly one seat.

PROOF: FF-7a gives the reverse inequality, so the energies
are equal; the FF-7a difference identity gives
`∑ i, u i * laplacianOp w u i = 0` for `u = ψ - φ`;
`energy_eq_zero_iff` / `eq_const_of_energy_eq_zero` force
`u` constant; `u b = 0` forces `u = 0`. -/
theorem groundedPotential_unique_minimizer_fallEnergy
    (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (ρ : V → ℝ)
    (ψ : V → ℝ) (hψb : ψ b = 0)
    (hmin : fallEnergy w b ρ ψ
      ≤ fallEnergy w b ρ (groundedPotential w hw hw0 hpos b ρ)) :
    ψ = groundedPotential w hw hw0 hpos b ρ := by

  classical
  set u : V → ℝ := fun k => ψ k - groundedPotential w hw hw0 hpos b ρ k with hu
  have hub : u b = 0 := by
    have e1 : u b = ψ b - groundedPotential w hw hw0 hpos b ρ b := rfl
    rw [e1, hψb, groundedPotential_at_ground w hw hw0 hpos b ρ,
      sub_self]
  have hψu : ∀ i, ψ i = groundedPotential w hw hw0 hpos b ρ i + u i := by
    intro i
    have e1 : u i = ψ i - groundedPotential w hw hw0 hpos b ρ i := rfl
    rw [e1]; ring
  have hLu : ∀ i, laplacianOp w ψ i
      = laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i + laplacianOp w u i := by
    intro i
    rw [laplacianOp_apply, laplacianOp_apply, laplacianOp_apply,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have e1 : ψ i - ψ j
        = (groundedPotential w hw hw0 hpos b ρ i - groundedPotential w hw hw0 hpos b ρ j) + (u i - u j) := by
      rw [hψu i, hψu j]; ring
    rw [e1, mul_add]
  have hquad : ∑ i, ψ i * laplacianOp w ψ i
      = ∑ i, groundedPotential w hw hw0 hpos b ρ i * laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i
        + 2 * (∑ i, u i * laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i)
        + ∑ i, u i * laplacianOp w u i := by
    have hterm : ∀ i, ψ i * laplacianOp w ψ i
        = groundedPotential w hw hw0 hpos b ρ i * laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i
          + (groundedPotential w hw hw0 hpos b ρ i * laplacianOp w u i
            + u i * laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i)
          + u i * laplacianOp w u i := by
      intro i
      rw [hψu i, hLu i]; ring
    have hsplit : (∑ i, ψ i * laplacianOp w ψ i)
        = ∑ i, (groundedPotential w hw hw0 hpos b ρ i * laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i
          + (groundedPotential w hw hw0 hpos b ρ i * laplacianOp w u i
            + u i * laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i)
          + u i * laplacianOp w u i) :=
      Finset.sum_congr rfl (fun i _ => hterm i)
    rw [hsplit]
    simp only [Finset.sum_add_distrib]
    rw [← laplacianOp_symm_form w hw (groundedPotential w hw hw0 hpos b ρ) u]
    ring
  have hpair : ∑ i, u i * laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i
      = ∑ i ∈ Finset.univ.erase b, ρ i * u i := by
    have h := Finset.sum_erase_add Finset.univ
      (fun i => u i * laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i) (Finset.mem_univ b)
    rw [hub, zero_mul, add_zero] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≠ b := (Finset.mem_erase.mp hi).1
    rw [laplacianOp_groundedPotential w hw hw0 hpos b ρ hi',
      mul_comm]
  have hpairψ : ∑ i ∈ Finset.univ.erase b, ρ i * ψ i
      = ∑ i ∈ Finset.univ.erase b, ρ i * groundedPotential w hw hw0 hpos b ρ i
        + ∑ i ∈ Finset.univ.erase b, ρ i * u i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hψu i]; ring

  have hEq : fallEnergy w b ρ ψ
      = fallEnergy w b ρ (groundedPotential w hw hw0 hpos b ρ) :=
    le_antisymm hmin
      (groundedPotential_minimizes_fallEnergy w hw hw0 hpos b ρ
        ψ hψb)
  have hQu : ∑ i, u i * laplacianOp w u i = 0 := by
    have hnn := energy_nonneg w hw hw0 u
    unfold fallEnergy at hEq
    rw [hquad, hpairψ, ← hpair] at hEq
    linarith
  have hconst := eq_const_of_energy_eq_zero w hw hw0 hpos u hQu
  funext i
  have hui : u i = 0 := by
    have hiu := hconst i b
    rw [hub] at hiu
    exact hiu
  rw [hψu i, hui, add_zero]

end ThetLogos
