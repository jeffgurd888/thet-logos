import ThetLogos.LatticeCorrelations
import Mathlib.Tactic

/-!
# ThetLogos.LatticeReflection — Pitch 4, Stage 1b-A: the reflection
structure pack and the Wilson action split (T1)

HONESTY LEDGER (read before citing):

- Everything in this file is **T1 finite lattice algebra, finite
  combinatorics, and finite integration**: on Stage 0's concrete
  torus (sites `Fin 4 → ZMod N`, shifts `torusShift N`) with the
  time direction `0` reflected across a hyperplane *between* sites,
  this module constructs the reflection, characterizes its fixed
  link stratum, proves the configuration reflection preserves the
  product-Haar measure and the Gibbs measure, and proves the Wilson
  action split `S = S₊ + S₋ + S₀` with `S₋ = S₊ ∘ θ` and `S₀`
  θ-invariant. Zero sorrys, no new axioms (headline theorems are
  checked against the standard three — `propext`, `Classical.choice`,
  `Quot.sound` — and the audit is recorded in the dossier
  `whitepaper/pitch-4-stage-1b-a-2026-10-17.md`).

- *(finite-lattice discipline)* "Results in this module are about a
  finite lattice at fixed spacing and volume. Nothing here is a
  continuum result; the words 'continuum', 'ℝ⁴', and 'Poincaré' do
  not describe anything proved in this module."

- *(gap discipline)* "Any gap statement in this module is a lattice
  statement at the stated $(a, L, \beta)$. No continuum mass gap is
  claimed; a lattice gap transfers to the continuum only with
  uniformity in the spacing along the tuning curve, which is not
  proved here or anywhere in this corpus." (This module proves no
  gap statement of any kind; the clause travels with the pitch.)

- *(gauge discipline)* "Gauge invariance here is exact invariance of
  a finite lattice action and measure under finite gauge
  transformations. It is not a continuum gauge theory, and this module
  contains no quantized continuum gauge field."

- *(standing charter)* "Parts of the official Clay Yang–Mills
  statement closed by this module: 0."

WHAT THIS MODULE IS, AND IS NOT (Stage 1b decomposition of record —
`whitepaper/gauntlet-parked-fleet-2026-10-17.md` §1): this is
campaign **1b-A only**, the reflection *structure*. It buys the
reflection, its fixed stratum, measure compatibility, and the action
split. It does **not** buy reflection positivity itself (that is
1b-B: no positivity statement of the form `⟨conj (θF) · F⟩_β ≥ 0`
appears or is implied here), no OS scalar product or Hilbert space
(1b-C), and no transfer matrix (1b-D).

DESIGN CHOICES (disclosed):

- **The setup, pinned as the first act** (the parked-fleet gauntlet
  found that the scoping fixed no time extent and that Stage 0's
  abstract-`Λ` presentation carries no reflection): the work is done
  on the concrete torus `Fin 4 → ZMod N` with reflected direction
  `0`, of **even extent `N` with `4 ≤ N`**, at general `(G, ρ)` in
  Stage 0/1a's sense. Extent `2` is excluded: at `N = 2` every time
  link lies in the fixed stratum and the `±` classes contain no
  temporal plaquette at all — the split degenerates. The minimal
  nondegenerate even extent is `4`.
- **Between-sites reflection** (the scoping §6.2 choice: "a
  reflection across a hyperplane between lattice sites"): the time
  coordinate transforms as `k ↦ -1 - k` on `ZMod N`. For even `N`
  this involution has **no fixed sites**; its fixed *links* are
  exactly the time links based in the two layers `N/2 - 1` and
  `N - 1` — the links crossing the two reflection planes. (The
  through-sites alternative, `k ↦ -k`, fixes two whole slices of
  spatial links instead; it is not used here.)
- **The plaquette trichotomy.** A plaquette of the action sum
  (directions `μ < ν`) is classified by the time slices it occupies:
  positive if all of them lie in slices `0, …, N/2 - 1`, negative if
  all lie in `N/2, …, N - 1`, and *crossing* otherwise. Spatial
  plaquettes are never crossing; a temporal plaquette is crossing
  iff its time links lie in the fixed stratum. The reflection maps
  the positive class bijectively onto the negative class and fixes
  every crossing plaquette's index.
- **The configuration reflection** inverts the time links (the
  orientation reversal the between-sites geometry forces) and pulls
  back along the induced link permutation otherwise. On observables
  the OS reflection is the conjugation-composed one (1b-B's concern,
  recorded in the gauntlet); on configurations — this module's level
  — it is the map defined here.

This module is NOT in the root import list of the library (the corpus
pattern for recent exhibits); it is verified by a targeted build.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

/-! ## §1. The site reflection and its shift calculus

Sites are the concrete torus `Fin 4 → ZMod N`; the reflected
direction is `0`. All of §1–§2 is pure combinatorics: no group, no
measure. -/

section Sites

variable {N : ℕ} [NeZero N]

/-- The between-sites reflection of a torus site: the time
coordinate `x 0` is sent to `-1 - x 0` (reflection across the
hyperplane between slices `N - 1` and `0`); every spatial
coordinate is fixed. -/
def reflSite (x : Fin 4 → ZMod N) : Fin 4 → ZMod N :=
  Function.update x 0 (-1 - x 0)

@[simp]
theorem reflSite_apply_self (x : Fin 4 → ZMod N) :
    reflSite x 0 = -1 - x 0 := by
  show Function.update x 0 (-1 - x 0) 0 = -1 - x 0
  exact Function.update_self 0 (-1 - x 0) x

theorem reflSite_apply_of_ne (x : Fin 4 → ZMod N) {j : Fin 4}
    (hj : j ≠ 0) : reflSite x j = x j := by
  show Function.update x 0 (-1 - x 0) j = x j
  exact Function.update_of_ne hj (-1 - x 0) x

/-- The site reflection is an involution. -/
theorem reflSite_involutive : Function.Involutive (reflSite (N := N)) := by
  intro x
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [reflSite_apply_self, reflSite_apply_self]
    ring
  · rw [reflSite_apply_of_ne _ hj, reflSite_apply_of_ne _ hj]

/-- Coordinates of a torus shift. -/
theorem torusShift_apply_coord (μ j : Fin 4) (x : Fin 4 → ZMod N) :
    torusShift N μ x j = (Pi.single μ 1 : Fin 4 → ZMod N) j + x j := by
  rw [torusShift_apply, Pi.add_apply]

/-- Coordinates of an inverse torus shift. -/
theorem torusShift_symm_apply_coord (μ j : Fin 4) (x : Fin 4 → ZMod N) :
    (torusShift N μ).symm x j
      = x j - (Pi.single μ 1 : Fin 4 → ZMod N) j := by
  have key := congrFun (Equiv.apply_symm_apply (torusShift N μ) x) j
  rw [torusShift_apply_coord] at key
  linear_combination key

/-- A spatial shift does not move the time coordinate. -/
theorem torusShift_apply_zero_of_ne {μ : Fin 4} (hμ : μ ≠ 0)
    (x : Fin 4 → ZMod N) : torusShift N μ x 0 = x 0 := by
  rw [torusShift_apply_coord, Pi.single_eq_of_ne (Ne.symm hμ), zero_add]

/-- An inverse spatial shift does not move the time coordinate. -/
theorem torusShift_symm_apply_zero_of_ne {μ : Fin 4} (hμ : μ ≠ 0)
    (x : Fin 4 → ZMod N) : (torusShift N μ).symm x 0 = x 0 := by
  rw [torusShift_symm_apply_coord, Pi.single_eq_of_ne (Ne.symm hμ),
    sub_zero]

/-- Inverse shifts commute with the other shifts (from
`torusShift_comm`). -/
theorem torusShift_symm_apply_comm (μ ν : Fin 4) (x : Fin 4 → ZMod N) :
    (torusShift N μ).symm (torusShift N ν x)
      = torusShift N ν ((torusShift N μ).symm x) := by
  have h := torusShift_comm N μ ν ((torusShift N μ).symm x)
  rw [Equiv.apply_symm_apply] at h
  rw [← h, Equiv.symm_apply_apply]

/-- **Reflection conjugates the time shift to its inverse**:
`θ σ₀ = σ₀⁻¹ θ`. This is the algebraic heart of the pack: the
reflection reverses the time direction. -/
theorem reflSite_torusShift_zero (x : Fin 4 → ZMod N) :
    reflSite (torusShift N 0 x)
      = (torusShift N 0).symm (reflSite x) := by
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [reflSite_apply_self (torusShift N 0 x), torusShift_apply_coord,
      Pi.single_eq_same, torusShift_symm_apply_coord,
      reflSite_apply_self x, Pi.single_eq_same]
    ring
  · rw [reflSite_apply_of_ne _ hj, torusShift_apply_coord,
      Pi.single_eq_of_ne hj, torusShift_symm_apply_coord,
      reflSite_apply_of_ne _ hj, Pi.single_eq_of_ne hj, zero_add,
      sub_zero]

/-- **Reflection commutes with the spatial shifts**: `θ σᵢ = σᵢ θ`
for `i ≠ 0`. -/
theorem reflSite_torusShift_of_ne {μ : Fin 4} (hμ : μ ≠ 0)
    (x : Fin 4 → ZMod N) :
    reflSite (torusShift N μ x) = torusShift N μ (reflSite x) := by
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [reflSite_apply_self (torusShift N μ x), torusShift_apply_coord,
      Pi.single_eq_of_ne (Ne.symm hμ), torusShift_apply_coord,
      Pi.single_eq_of_ne (Ne.symm hμ), reflSite_apply_self x, zero_add,
      zero_add]
  · rw [reflSite_apply_of_ne _ hj, torusShift_apply_coord,
      torusShift_apply_coord, reflSite_apply_of_ne _ hj]

/-- Reflection conjugates the inverse time shift to the time shift:
`θ σ₀⁻¹ = σ₀ θ`. -/
theorem reflSite_torusShift_symm_zero (x : Fin 4 → ZMod N) :
    reflSite ((torusShift N 0).symm x)
      = torusShift N 0 (reflSite x) := by
  have h := reflSite_torusShift_zero ((torusShift N 0).symm x)
  rw [Equiv.apply_symm_apply] at h
  have h2 := congrArg (torusShift N 0) h
  rw [Equiv.apply_symm_apply] at h2
  exact h2.symm

/-- Reflection commutes with the inverse spatial shifts. -/
theorem reflSite_torusShift_symm_of_ne {μ : Fin 4} (hμ : μ ≠ 0)
    (x : Fin 4 → ZMod N) :
    reflSite ((torusShift N μ).symm x)
      = (torusShift N μ).symm (reflSite x) := by
  have h := reflSite_torusShift_of_ne hμ ((torusShift N μ).symm x)
  rw [Equiv.apply_symm_apply] at h
  have h2 := congrArg (torusShift N μ).symm h
  rw [Equiv.symm_apply_apply] at h2
  exact h2.symm

/-- The cast of `N - 1` in `ZMod N` is `-1`. -/
theorem natCast_pred_eq_neg_one : ((N - 1 : ℕ) : ZMod N) = -1 := by
  have hN : ((N : ℕ) : ZMod N) = 0 := ZMod.natCast_self N
  have hsub : ((N - 1 : ℕ) : ZMod N)
      = ((N : ℕ) : ZMod N) - ((1 : ℕ) : ZMod N) :=
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  rw [hsub, hN]
  simp

/-- The reflected time coordinate, as a value: `(θx) 0 = -1 - x 0`
has `ZMod.val` equal to `N - 1 - (x 0).val`. -/
theorem reflSite_val_zero (x : Fin 4 → ZMod N) :
    (reflSite x 0).val = N - 1 - (x 0).val := by
  have hN1 : ((N - 1 : ℕ) : ZMod N) = -1 := natCast_pred_eq_neg_one
  have hle : (x 0).val ≤ N - 1 := by
    have h := (x 0).val_lt
    omega
  have h1 : reflSite x 0 = ((N - 1 - (x 0).val : ℕ) : ZMod N) := by
    rw [reflSite_apply_self, Nat.cast_sub hle, hN1, ZMod.natCast_zmod_val]
  rw [h1, ZMod.val_natCast, Nat.mod_eq_of_lt]
  have h := (x 0).val_lt
  omega

/-- For even `N`, the site reflection has **no fixed sites**: a
fixed site would need `2 * x 0 = -1` in `ZMod N`, an odd number
divisible by the even modulus. -/
theorem reflSite_ne_self (hN : Even N) (x : Fin 4 → ZMod N) :
    reflSite x ≠ x := by
  intro h
  have h0 := congrFun h 0
  rw [reflSite_apply_self] at h0
  -- `h0 : -1 - x 0 = x 0`, so `2 * (x 0).val + 1` is a multiple of `N`.
  have h2 : ((2 * (x 0).val + 1 : ℕ) : ZMod N) = 0 := by
    have h3 : 2 * x 0 + 1 = 0 := by linear_combination -h0
    rw [← ZMod.natCast_zmod_val (x 0)] at h3
    have h4 : ((2 * (x 0).val + 1 : ℕ) : ZMod N)
        = 2 * ((x 0).val : ZMod N) + 1 := by push_cast; ring
    rw [h4]
    exact h3
  rw [ZMod.natCast_eq_zero_iff] at h2
  obtain ⟨k, hk⟩ := h2
  obtain ⟨m, hm⟩ := hN
  have hk2 : 2 * (x 0).val + 1 = 2 * (m * k) := by
    rw [hk, hm]
    ring
  omega

end Sites

/-! ## §2. The induced link reflection and its fixed stratum

A link `(x, μ)` is the oriented edge from `x` to `σ μ x`. Reflecting
the *edge*: for a spatial direction the reflected edge is the edge
at the reflected site in the same direction; for the time direction
the reflected edge runs from `θ x - e₀` to `θ x`, i.e. it is the
time link based at `(σ₀)⁻¹ (θ x)`. -/

section Links

variable {N : ℕ} [NeZero N]

/-- The induced reflection on links: spatial links move with their
base site; a time link `(x, 0)` goes to the time link based at
`(σ₀)⁻¹ (θ x)`. -/
def reflLink (ℓ : Link (Fin 4 → ZMod N)) : Link (Fin 4 → ZMod N) :=
  if ℓ.2 = 0 then ((torusShift N 0).symm (reflSite ℓ.1), 0)
  else (reflSite ℓ.1, ℓ.2)

theorem reflLink_zero (x : Fin 4 → ZMod N) :
    reflLink (x, 0) = ((torusShift N 0).symm (reflSite x), 0) :=
  if_pos rfl

theorem reflLink_of_ne {x : Fin 4 → ZMod N} {μ : Fin 4} (hμ : μ ≠ 0) :
    reflLink (x, μ) = (reflSite x, μ) :=
  if_neg hμ

/-- The link reflection is an involution. -/
theorem reflLink_involutive :
    Function.Involutive (reflLink (N := N)) := by
  intro ℓ
  obtain ⟨x, μ⟩ := ℓ
  by_cases hμ : μ = 0
  · subst hμ
    rw [reflLink_zero, reflLink_zero, reflSite_torusShift_symm_zero,
      reflSite_involutive, Equiv.symm_apply_apply]
  · rw [reflLink_of_ne hμ, reflLink_of_ne hμ, reflSite_involutive]

/-- The link reflection as a permutation of the link set. -/
def reflLinkEquiv : Equiv.Perm (Link (Fin 4 → ZMod N)) :=
  Function.Involutive.toPerm _ reflLink_involutive

@[simp]
theorem reflLinkEquiv_apply (ℓ : Link (Fin 4 → ZMod N)) :
    reflLinkEquiv ℓ = reflLink ℓ :=
  rfl

/-- **The fixed link stratum, characterized** (even extent). A link
is fixed by the reflection iff it is a time link based in one of
the two layers `N/2 - 1` and `N - 1` — exactly the time links whose
edge crosses a reflection plane. No spatial link is fixed (a fixed
spatial link would fix its base site, and there are no fixed
sites). -/
theorem reflLink_eq_self_iff (hN : Even N) (x : Fin 4 → ZMod N)
    (μ : Fin 4) :
    reflLink (x, μ) = (x, μ) ↔ μ = 0 ∧
      ((x 0).val = N / 2 - 1 ∨ (x 0).val = N - 1) := by
  obtain ⟨m, hm⟩ := hN
  have hdiv : N / 2 = m := by
    rw [hm, ← two_mul m, Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 2)]
  have h2M : 2 * (N / 2) = N := by rw [hdiv, two_mul, hm]
  have hM : 1 ≤ N / 2 := by
    have hm0 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0] at hm
        simp only [add_zero] at hm
        exact absurd hm (NeZero.ne N)
      · exact h0
    omega
  constructor
  · intro h
    by_cases hμ : μ = 0
    · subst hμ
      rw [reflLink_zero] at h
      have hx : (torusShift N 0).symm (reflSite x) = x := congrArg Prod.fst h
      have hx2 : reflSite x = torusShift N 0 x := by
        have h2 := congrArg (torusShift N 0) hx
        rwa [Equiv.apply_symm_apply] at h2
      have h0 := congrFun hx2 0
      rw [reflSite_apply_self, torusShift_apply_coord, Pi.single_eq_same]
        at h0
      -- `h0 : -1 - x 0 = 1 + x 0`; equivalently `N ∣ 2 * ((x 0).val + 1)`.
      have h3 : ((2 * ((x 0).val + 1) : ℕ) : ZMod N) = 0 := by
        have h4 : 2 * x 0 + 2 = 0 := by linear_combination -h0
        rw [← ZMod.natCast_zmod_val (x 0)] at h4
        have h5 : ((2 * ((x 0).val + 1) : ℕ) : ZMod N)
            = 2 * ((x 0).val : ZMod N) + 2 := by push_cast; ring
        rw [h5]
        exact h4
      rw [ZMod.natCast_eq_zero_iff] at h3
      obtain ⟨k, hk⟩ := h3
      have hMk : (x 0).val + 1 = (N / 2) * k := by
        have e : 2 * ((x 0).val + 1) = 2 * (m * k) := by
          rw [hk, hm]
          ring
        have e2 : (x 0).val + 1 = m * k := Nat.mul_left_cancel (by norm_num) e
        rw [hdiv]
        exact e2
      have hk1 : 1 ≤ k := by
        rcases k with _ | k
        · simp at hMk
        · omega
      have hk2 : k ≤ 2 := by
        have hle : (N / 2) * k ≤ N := by
          rw [← hMk]
          have := (x 0).val_lt
          omega
        have hle2 : (N / 2) * k ≤ (N / 2) * 2 := by
          rw [mul_comm (N / 2) 2, h2M]
          exact hle
        exact Nat.le_of_mul_le_mul_left hle2 hM
      refine ⟨rfl, ?_⟩
      interval_cases k
      · left
        omega
      · right
        omega
    · exfalso
      rw [reflLink_of_ne hμ] at h
      have hx : reflSite x = x := congrArg Prod.fst h
      exact reflSite_ne_self ⟨m, hm⟩ x hx
  · intro h
    obtain ⟨hμ, hval⟩ := h
    have hμ' : μ = 0 := hμ
    subst hμ'
    rw [reflLink_zero]
    -- It suffices to show `reflSite x = σ₀ x`: then
    -- `(σ₀)⁻¹ (reflSite x) = x` by `Equiv.symm_apply_apply`.
    have h2x : 2 * x 0 = -2 := by
      rcases hval with hv | hv
      · calc 2 * x 0 = 2 * ((x 0).val : ZMod N) := by
              rw [ZMod.natCast_zmod_val]
          _ = ((2 * (x 0).val : ℕ) : ZMod N) := by norm_cast
          _ = ((N - 2 : ℕ) : ZMod N) := by
              rw [show 2 * (x 0).val = N - 2 from by omega]
          _ = -2 := by
              have hsub : ((N - 2 : ℕ) : ZMod N)
                  = ((N : ℕ) : ZMod N) - ((2 : ℕ) : ZMod N) :=
                Nat.cast_sub (by omega)
              rw [hsub, ZMod.natCast_self]
              simp
      · have hx0 : x 0 = -1 := by
          rw [← ZMod.natCast_zmod_val (x 0), hv]
          exact natCast_pred_eq_neg_one
        rw [hx0]
        ring
    have hx2 : reflSite x = torusShift N 0 x := by
      funext j
      by_cases hj : j = 0
      · subst hj
        rw [reflSite_apply_self, torusShift_apply_coord, Pi.single_eq_same]
        linear_combination -h2x
      · rw [reflSite_apply_of_ne _ hj, torusShift_apply_coord,
          Pi.single_eq_of_ne hj, zero_add]
    rw [hx2, Equiv.symm_apply_apply]

end Links

/-! ## §3. The reflection on configurations, and measure compatibility

The configuration reflection reads the reflected configuration off
the link reflection, inverting time links (orientation reversal).
It factors as a coordinate permutation (measure-preserving by the
pi-congruence of Stage 1a's factorization section) followed by a
per-coordinate inversion on time links (measure-preserving by
Haar's inversion invariance). -/

section Configs

variable {G : Type*} [Group G] {N : ℕ} [NeZero N]

/-- The reflection on configurations: the value at a link is the
value of `U` at the reflected link, inverted on time links. -/
def reflConfig (U : Config (Fin 4 → ZMod N) G) :
    Config (Fin 4 → ZMod N) G :=
  fun ℓ => if ℓ.2 = 0 then (U (reflLink ℓ))⁻¹ else U (reflLink ℓ)

theorem reflConfig_apply_zero (U : Config (Fin 4 → ZMod N) G)
    (x : Fin 4 → ZMod N) :
    reflConfig U (x, 0)
      = (U ((torusShift N 0).symm (reflSite x), 0))⁻¹ := by
  show (U (reflLink (x, 0)))⁻¹
      = (U ((torusShift N 0).symm (reflSite x), 0))⁻¹
  rw [reflLink_zero]

theorem reflConfig_apply_of_ne (U : Config (Fin 4 → ZMod N) G)
    {x : Fin 4 → ZMod N} {μ : Fin 4} (hμ : μ ≠ 0) :
    reflConfig U (x, μ) = U (reflSite x, μ) := by
  rw [show reflConfig U (x, μ) = U (reflLink (x, μ)) from if_neg hμ,
    reflLink_of_ne hμ]

/-- The configuration reflection is an involution. -/
theorem reflConfig_involutive :
    Function.Involutive (reflConfig (G := G) (N := N)) := by
  intro U
  funext ℓ
  obtain ⟨x, μ⟩ := ℓ
  by_cases hμ : μ = 0
  · subst hμ
    rw [reflConfig_apply_zero, reflConfig_apply_zero,
      reflSite_torusShift_symm_zero, reflSite_involutive,
      Equiv.symm_apply_apply, inv_inv]
  · rw [reflConfig_apply_of_ne _ hμ, reflConfig_apply_of_ne _ hμ,
      reflSite_involutive]

/-- The time-link inversion part of the reflection. -/
def invConfig (U : Config (Fin 4 → ZMod N) G) :
    Config (Fin 4 → ZMod N) G :=
  fun ℓ => if ℓ.2 = 0 then (U ℓ)⁻¹ else U ℓ

theorem invConfig_apply_zero (U : Config (Fin 4 → ZMod N) G)
    (x : Fin 4 → ZMod N) :
    invConfig U (x, 0) = (U (x, 0))⁻¹ :=
  if_pos rfl

theorem invConfig_apply_of_ne (U : Config (Fin 4 → ZMod N) G)
    {x : Fin 4 → ZMod N} {μ : Fin 4} (hμ : μ ≠ 0) :
    invConfig U (x, μ) = U (x, μ) :=
  if_neg hμ

end Configs

section ConfigMeasure

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  {N : ℕ} [NeZero N]

/-- The coordinate permutation part of the reflection, as a
measurable equivalence (relabeling of the link coordinates). -/
def permConfig : Config (Fin 4 → ZMod N) G ≃ᵐ
    Config (Fin 4 → ZMod N) G :=
  MeasurableEquiv.piCongrLeft (fun _ : Link (Fin 4 → ZMod N) => G)
    reflLinkEquiv

theorem permConfig_apply (U : Config (Fin 4 → ZMod N) G)
    (ℓ : Link (Fin 4 → ZMod N)) :
    permConfig U ℓ = U (reflLink ℓ) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Link (Fin 4 → ZMod N) => G) reflLinkEquiv U
    (reflLinkEquiv.symm ℓ)
  rw [Equiv.apply_symm_apply] at h
  exact h

/-- The configuration reflection factors as permutation followed by
time-link inversion: `θU = invConfig (permConfig U)`. -/
theorem reflConfig_eq (U : Config (Fin 4 → ZMod N) G) :
    reflConfig U = invConfig (permConfig U) := by
  funext ℓ
  obtain ⟨x, μ⟩ := ℓ
  by_cases hμ : μ = 0
  · subst hμ
    rw [reflConfig_apply_zero, invConfig_apply_zero, permConfig_apply,
      reflLink_zero]
  · rw [reflConfig_apply_of_ne _ hμ, invConfig_apply_of_ne _ hμ,
      permConfig_apply, reflLink_of_ne hμ]

theorem measurable_invConfig :
    Measurable (invConfig : Config (Fin 4 → ZMod N) G →
      Config (Fin 4 → ZMod N) G) :=
  measurable_pi_iff.mpr fun ℓ => by
    by_cases hℓ : ℓ.2 = 0
    · have hfun : (fun U : Config (Fin 4 → ZMod N) G => invConfig U ℓ)
          = fun U => (U ℓ)⁻¹ :=
        funext fun U => if_pos hℓ
      rw [hfun]
      exact (measurable_pi_apply ℓ).inv
    · have hfun : (fun U : Config (Fin 4 → ZMod N) G => invConfig U ℓ)
          = fun U => U ℓ :=
        funext fun U => if_neg hℓ
      rw [hfun]
      exact measurable_pi_apply ℓ

/-- The configuration reflection is measurable. -/
theorem measurable_reflConfig :
    Measurable (reflConfig : Config (Fin 4 → ZMod N) G →
      Config (Fin 4 → ZMod N) G) := by
  have hfun : (reflConfig : Config (Fin 4 → ZMod N) G →
        Config (Fin 4 → ZMod N) G)
      = invConfig ∘ (permConfig : Config (Fin 4 → ZMod N) G →
        Config (Fin 4 → ZMod N) G) :=
    funext fun U => reflConfig_eq U
  rw [hfun]
  exact measurable_invConfig.comp permConfig.measurable

variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]

/-- The permutation part preserves the configuration measure. -/
theorem measurePreserving_permConfig :
    MeasurePreserving permConfig
      (configMeasure μG : Measure (Config (Fin 4 → ZMod N) G))
      (configMeasure μG : Measure (Config (Fin 4 → ZMod N) G)) :=
  measurePreserving_piCongrLeft (fun _ : Link (Fin 4 → ZMod N) => μG)
    reflLinkEquiv

/-- The function form of the inversion part, for the pi-measure
argument. -/
theorem invConfig_eq_piMap :
    (invConfig : Config (Fin 4 → ZMod N) G → Config (Fin 4 → ZMod N) G)
      = fun U ℓ => if ℓ.2 = 0 then (U ℓ)⁻¹ else U ℓ :=
  funext fun U => funext fun ℓ => rfl

/-- The inversion part preserves the configuration measure:
inversion invariance of the single-site measure, coordinate by
coordinate. -/
theorem measurePreserving_invConfig :
    MeasurePreserving invConfig
      (configMeasure μG : Measure (Config (Fin 4 → ZMod N) G))
      (configMeasure μG : Measure (Config (Fin 4 → ZMod N) G)) := by
  have hmp : MeasurePreserving
      (fun U ℓ => if ℓ.2 = 0 then (U ℓ)⁻¹ else U ℓ)
      (Measure.pi fun _ : Link (Fin 4 → ZMod N) => μG)
      (Measure.pi fun _ : Link (Fin 4 → ZMod N) => μG) := by
    refine measurePreserving_pi
      (f := fun (ℓ : Link (Fin 4 → ZMod N)) (g : G) =>
        if ℓ.2 = 0 then g⁻¹ else g)
      (fun _ : Link (Fin 4 → ZMod N) => μG)
      (fun _ : Link (Fin 4 → ZMod N) => μG) fun ℓ => ?_
    show MeasurePreserving (fun g : G => if ℓ.2 = 0 then g⁻¹ else g)
      μG μG
    by_cases hℓ : ℓ.2 = 0
    · rw [show (fun g : G => if ℓ.2 = 0 then g⁻¹ else g) = Inv.inv from
        funext fun g => if_pos hℓ]
      exact Measure.measurePreserving_inv μG
    · rw [show (fun g : G => if ℓ.2 = 0 then g⁻¹ else g) = id from
        funext fun g => if_neg hℓ]
      exact MeasurePreserving.id μG
  rw [invConfig_eq_piMap]
  exact hmp

/-- **Measure compatibility of the reflection (strong form)**: the
configuration reflection preserves Stage 0's product measure. -/
theorem configMeasure_map_reflConfig :
    Measure.map reflConfig
        (configMeasure μG : Measure (Config (Fin 4 → ZMod N) G))
      = (configMeasure μG : Measure (Config (Fin 4 → ZMod N) G)) := by
  have hfun : (reflConfig : Config (Fin 4 → ZMod N) G →
        Config (Fin 4 → ZMod N) G)
      = invConfig ∘ (permConfig : Config (Fin 4 → ZMod N) G →
        Config (Fin 4 → ZMod N) G) :=
    funext fun U => reflConfig_eq U
  rw [hfun]
  exact ((measurePreserving_invConfig μG).comp
    (measurePreserving_permConfig μG)).map_eq

/-- Integration against the configuration measure is invariant
under the reflection substitution. -/
theorem integral_reflConfig {f : Config (Fin 4 → ZMod N) G → ℂ}
    (hf : Integrable f
      (configMeasure μG : Measure (Config (Fin 4 → ZMod N) G))) :
    ∫ U, f (reflConfig U)
        ∂(configMeasure μG : Measure (Config (Fin 4 → ZMod N) G))
      = ∫ U, f U
        ∂(configMeasure μG : Measure (Config (Fin 4 → ZMod N) G)) := by
  have h2 : Integrable f
      ((configMeasure μG : Measure (Config (Fin 4 → ZMod N) G)).map
        reflConfig) := by
    rwa [configMeasure_map_reflConfig μG]
  calc ∫ U, f (reflConfig U)
        ∂(configMeasure μG : Measure (Config (Fin 4 → ZMod N) G))
      = ∫ U, f U
          ∂((configMeasure μG : Measure (Config (Fin 4 → ZMod N) G)).map
            reflConfig) :=
        (integral_map measurable_reflConfig.aemeasurable
          h2.aestronglyMeasurable).symm
    _ = ∫ U, f U
          ∂(configMeasure μG : Measure (Config (Fin 4 → ZMod N) G)) := by
        rw [configMeasure_map_reflConfig μG]

end ConfigMeasure

/-! ## §4. Plaquette transport

The plaquette based at the reflected site of the reflected
configuration: for spatial plaquettes it equals the original
plaquette on the nose; for temporal plaquettes it is a conjugate of
the inverse — which the representation trace cannot see, so the
plaquette *density* is transported exactly in both cases. -/

section Transport

variable {G : Type*} [Group G] {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- The trace of a represented group element is unchanged by
inversion (the trace of a unitary is real-part-stable under
`star`). -/
theorem trace_repMatrix_inv (g : G) :
    (Matrix.trace (repMatrix ρ g⁻¹)).re
      = (Matrix.trace (repMatrix ρ g)).re := by
  have h1 : Matrix.trace (repMatrix ρ g⁻¹)
      = star (Matrix.trace (repMatrix ρ g)) := by
    rw [repMatrix_inv, Matrix.star_eq_conjTranspose,
      Matrix.trace_conjTranspose]
  rw [h1, RCLike.star_def, Complex.conj_re]

/-- The base site at which the reflection of the plaquette
`(x, μ, ν)` sits: for a temporal plaquette, the reflected edge's
base `(σ₀)⁻¹ (θ x)`; for a spatial one, the reflected site. -/
def refPlaqSite (x : Fin 4 → ZMod N) (μ : Fin 4) : Fin 4 → ZMod N :=
  if μ = 0 then (torusShift N 0).symm (reflSite x) else reflSite x

theorem refPlaqSite_zero (x : Fin 4 → ZMod N) :
    refPlaqSite x 0 = (torusShift N 0).symm (reflSite x) :=
  if_pos rfl

theorem refPlaqSite_of_ne (x : Fin 4 → ZMod N) {μ : Fin 4}
    (hμ : μ ≠ 0) : refPlaqSite x μ = reflSite x :=
  if_neg hμ

/-- Spatial plaquette transport, exact: the plaquette of the
reflected configuration at the reflected site is the plaquette of
the original configuration. -/
theorem plaquette_reflConfig_spatial (U : Config (Fin 4 → ZMod N) G)
    (x : Fin 4 → ZMod N) {μ ν : Fin 4} (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    plaquette (torusShift N) (reflConfig U) (reflSite x) μ ν
      = plaquette (torusShift N) U x μ ν := by
  have e1 : reflConfig U (reflSite x, μ) = U (x, μ) :=
    (reflConfig_apply_of_ne _ hμ).trans
      (congrArg (fun y => U (y, μ)) (reflSite_involutive x))
  have e2 : reflConfig U (torusShift N μ (reflSite x), ν)
      = U (torusShift N μ x, ν) :=
    (reflConfig_apply_of_ne _ hν).trans
      (congrArg (fun y => U (y, ν))
        ((reflSite_torusShift_of_ne hμ (reflSite x)).trans
          (congrArg (torusShift N μ) (reflSite_involutive x))))
  have e3 : reflConfig U (torusShift N ν (reflSite x), μ)
      = U (torusShift N ν x, μ) :=
    (reflConfig_apply_of_ne _ hμ).trans
      (congrArg (fun y => U (y, μ))
        ((reflSite_torusShift_of_ne hν (reflSite x)).trans
          (congrArg (torusShift N ν) (reflSite_involutive x))))
  have e4 : reflConfig U (reflSite x, ν) = U (x, ν) :=
    (reflConfig_apply_of_ne _ hν).trans
      (congrArg (fun y => U (y, ν)) (reflSite_involutive x))
  unfold plaquette
  rw [e1, e2, e3, e4]

/-- Temporal plaquette transport: the plaquette of the reflected
configuration at the reflected edge's base is the conjugate of the
inverse plaquette, conjugated by the time link at the base. -/
theorem plaquette_reflConfig_temporal (U : Config (Fin 4 → ZMod N) G)
    (x : Fin 4 → ZMod N) {ν : Fin 4} (hν : ν ≠ 0) :
    plaquette (torusShift N) (reflConfig U)
        ((torusShift N 0).symm (reflSite x)) 0 ν
      = (U (x, 0))⁻¹ * (plaquette (torusShift N) U x 0 ν)⁻¹
        * U (x, 0) := by
  have hy : reflSite ((torusShift N 0).symm (reflSite x))
      = torusShift N 0 x :=
    (reflSite_torusShift_symm_zero (reflSite x)).trans
      (congrArg (torusShift N 0) (reflSite_involutive x))
  have e1 : reflConfig U ((torusShift N 0).symm (reflSite x), 0)
      = (U (x, 0))⁻¹ := by
    rw [reflConfig_apply_zero, hy, Equiv.symm_apply_apply]
  have e2 : reflConfig U
        (torusShift N 0 ((torusShift N 0).symm (reflSite x)), ν)
      = U (x, ν) := by
    rw [reflConfig_apply_of_ne _ hν, Equiv.apply_symm_apply,
      reflSite_involutive]
  have e3 : (reflConfig U
        (torusShift N ν ((torusShift N 0).symm (reflSite x)), 0))⁻¹
      = U (torusShift N ν x, 0) := by
    rw [reflConfig_apply_zero, reflSite_torusShift_of_ne hν, hy,
      torusShift_comm, Equiv.symm_apply_apply, inv_inv]
  have e4 : (reflConfig U ((torusShift N 0).symm (reflSite x), ν))⁻¹
      = (U (torusShift N 0 x, ν))⁻¹ := by
    rw [reflConfig_apply_of_ne _ hν, hy]
  unfold plaquette
  rw [e1, e2, e3, e4]
  group

/-- **Plaquette density transport (exact)**: the Wilson action's
summand at the reflected index of the reflected configuration
equals the summand at the original index — for every pair
`μ < ν`. The temporal case goes through the conjugate-of-inverse
identity, which the trace absorbs. -/
theorem plaquetteDensity_reflConfig (U : Config (Fin 4 → ZMod N) G)
    (x : Fin 4 → ZMod N) {μ ν : Fin 4} (hμν : μ < ν) :
    plaquetteDensity (torusShift N) ρ (reflConfig U) (refPlaqSite x μ)
        μ ν
      = plaquetteDensity (torusShift N) ρ U x μ ν := by
  by_cases hμ : μ = 0
  · subst hμ
    have hν : ν ≠ 0 := by
      rintro rfl
      simp at hμν
    unfold plaquetteDensity
    rw [refPlaqSite_zero, plaquette_reflConfig_temporal U x hν]
    have hconj : (U (x, 0))⁻¹ * (plaquette (torusShift N) U x 0 ν)⁻¹
          * U (x, 0)
        = (U (x, 0))⁻¹ * (plaquette (torusShift N) U x 0 ν)⁻¹
          * ((U (x, 0))⁻¹)⁻¹ := by
      rw [inv_inv]
    rw [hconj, trace_repMatrix_conj, trace_repMatrix_inv]
  · have hν : ν ≠ 0 := by
      rintro rfl
      simp at hμν
    unfold plaquetteDensity
    rw [refPlaqSite_of_ne _ hμ, plaquette_reflConfig_spatial U x hμ hν]

end Transport

/-! ## §5. The Wilson action split

The index set of the Wilson action — triples `(x, μ, ν)` with
`μ < ν` — falls under the reflection into three classes by the
*time height* of the plaquette: the height of a plaquette is the
topmost time layer it touches. Positive: height `< N/2` (lies in
the lower half). Negative: bases at time `≥ N/2`, height `< N`
(the reflected image of the positive class). Zero: the rest —
proved below to be exactly the temporal plaquettes based at
`N/2 - 1` and `N - 1`, whose two time links are precisely the fixed
links of §2. -/

section Split

variable {G : Type*} [Group G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- The time height of a plaquette based at `x` in direction `μ`:
a temporal plaquette straddles layers `(x 0).val` and
`(x 0).val + 1`; a spatial one sits at layer `(x 0).val`. -/
def plaqTimeHi (x : Fin 4 → ZMod N) (μ : Fin 4) : ℕ :=
  if μ = 0 then (x 0).val + 1 else (x 0).val

theorem plaqTimeHi_zero (x : Fin 4 → ZMod N) :
    plaqTimeHi x 0 = (x 0).val + 1 :=
  if_pos rfl

theorem plaqTimeHi_of_ne (x : Fin 4 → ZMod N) {μ : Fin 4}
    (hμ : μ ≠ 0) : plaqTimeHi x μ = (x 0).val :=
  if_neg hμ

/-- The positive class: plaquettes with time height `< N / 2`. -/
abbrev IsPosPlaq (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) : Prop :=
  plaqTimeHi p.1 p.2.1 < N / 2

/-- The negative class: plaquettes based at time `≥ N / 2` with
time height `< N`. -/
abbrev IsNegPlaq (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) : Prop :=
  N / 2 ≤ (p.1 0).val ∧ plaqTimeHi p.1 p.2.1 < N

/-- The crossing (zero) class: neither positive nor negative. -/
abbrev IsZeroPlaq (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) : Prop :=
  ¬ IsPosPlaq p ∧ ¬ IsNegPlaq p

/-- The index set of the Wilson action: triples `(x, μ, ν)` with
`μ < ν`. -/
def plaqIndex : Finset ((Fin 4 → ZMod N) × Fin 4 × Fin 4) :=
  Finset.univ.filter (fun p => p.2.1 < p.2.2)

theorem mem_plaqIndex {p : (Fin 4 → ZMod N) × Fin 4 × Fin 4}
    (hp : p ∈ plaqIndex) : p.2.1 < p.2.2 :=
  (Finset.mem_filter.mp hp).2

theorem ioi_eq_filter (μ : Fin 4) :
    Finset.Ioi μ = Finset.univ.filter (fun ν => μ < ν) := by
  ext ν
  simp only [Finset.mem_Ioi, Finset.mem_filter, Finset.mem_univ,
    true_and]

/-- The Wilson action as a single sum over the plaquette index
set (bookkeeping for the split). -/
theorem wilsonAction_eq_sum_plaqIndex (β : ℝ)
    (U : Config (Fin 4 → ZMod N) G) :
    wilsonAction (torusShift N) ρ β U
      = β * ∑ p ∈ plaqIndex,
          plaquetteDensity (torusShift N) ρ U p.1 p.2.1 p.2.2 := by
  have hν : ∀ (x : Fin 4 → ZMod N) (μ : Fin 4),
      (∑ ν ∈ Finset.Ioi μ, plaquetteDensity (torusShift N) ρ U x μ ν)
        = ∑ ν : Fin 4, if μ < ν then
            plaquetteDensity (torusShift N) ρ U x μ ν else 0 := by
    intro x μ
    rw [← Finset.sum_filter, ioi_eq_filter]
  have hprod : (∑ a : (Fin 4 → ZMod N) × Fin 4 × Fin 4,
        if a.2.1 < a.2.2 then
          plaquetteDensity (torusShift N) ρ U a.1 a.2.1 a.2.2 else 0)
      = ∑ x, ∑ μ, ∑ ν, if μ < ν then
          plaquetteDensity (torusShift N) ρ U x μ ν else 0 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type]
  unfold wilsonAction plaqIndex
  rw [Finset.sum_filter, hprod]
  congr 1
  refine Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun μ _ => hν x μ

/-- The positive half-action `S₊`: the sum of the plaquette
densities over the positive class, with the coupling. -/
noncomputable def wilsonActionPlus (β : ℝ) (U : Config (Fin 4 → ZMod N) G) : ℝ :=
  β * ∑ p ∈ plaqIndex.filter IsPosPlaq,
    plaquetteDensity (torusShift N) ρ U p.1 p.2.1 p.2.2

/-- The negative half-action `S₋`. -/
noncomputable def wilsonActionMinus (β : ℝ) (U : Config (Fin 4 → ZMod N) G) : ℝ :=
  β * ∑ p ∈ plaqIndex.filter IsNegPlaq,
    plaquetteDensity (torusShift N) ρ U p.1 p.2.1 p.2.2

/-- The crossing-stratum action `S₀`. -/
noncomputable def wilsonActionZero (β : ℝ) (U : Config (Fin 4 → ZMod N) G) : ℝ :=
  β * ∑ p ∈ plaqIndex.filter IsZeroPlaq,
    plaquetteDensity (torusShift N) ρ U p.1 p.2.1 p.2.2

theorem not_isPos_of_isNeg {p : (Fin 4 → ZMod N) × Fin 4 × Fin 4}
    (h : IsNegPlaq p) : ¬ IsPosPlaq p := by
  intro hp
  have hp' : plaqTimeHi p.1 p.2.1 < N / 2 := hp
  have h1 : (p.1 0).val ≤ plaqTimeHi p.1 p.2.1 := by
    by_cases hμ : p.2.1 = 0
    · rw [hμ, plaqTimeHi_zero (N := N)]
      omega
    · rw [plaqTimeHi_of_ne (N := N) _ hμ]
  omega

/-- **The Wilson action split**: for every configuration, on the
even-extent torus, `S = S₊ + S₋ + S₀` as real numbers — the sum
over all plaquettes is the sum over the positive class, plus the
sum over the negative class, plus the sum over the crossing
stratum. -/
theorem wilsonAction_split (β : ℝ) (U : Config (Fin 4 → ZMod N) G) :
    wilsonAction (torusShift N) ρ β U
      = wilsonActionPlus ρ β U + wilsonActionMinus ρ β U
        + wilsonActionZero ρ β U := by
  have hneg : (plaqIndex (N := N)).filter IsNegPlaq
      = ((plaqIndex (N := N)).filter (fun p => ¬ IsPosPlaq p)).filter
        IsNegPlaq := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro p _
    constructor
    · intro h
      exact ⟨fun hp => absurd hp (not_isPos_of_isNeg h), h⟩
    · intro h
      exact h.2
  have hzero : (plaqIndex (N := N)).filter IsZeroPlaq
      = ((plaqIndex (N := N)).filter (fun p => ¬ IsPosPlaq p)).filter
        (fun p => ¬ IsNegPlaq p) := by
    rw [Finset.filter_filter]
  have step2 : (∑ p ∈ plaqIndex.filter (fun p => ¬ IsPosPlaq p),
        plaquetteDensity (torusShift N) ρ U p.1 p.2.1 p.2.2)
      = (∑ p ∈ plaqIndex.filter IsNegPlaq,
          plaquetteDensity (torusShift N) ρ U p.1 p.2.1 p.2.2)
        + (∑ p ∈ plaqIndex.filter IsZeroPlaq,
          plaquetteDensity (torusShift N) ρ U p.1 p.2.1 p.2.2) := by
    rw [hneg, hzero]
    exact (Finset.sum_filter_add_sum_filter_not _ IsNegPlaq
      (fun p => plaquetteDensity (torusShift N) ρ U p.1 p.2.1
        p.2.2)).symm
  have step1 : (∑ p ∈ plaqIndex,
        plaquetteDensity (torusShift N) ρ U p.1 p.2.1 p.2.2)
      = (∑ p ∈ plaqIndex.filter IsPosPlaq,
          plaquetteDensity (torusShift N) ρ U p.1 p.2.1 p.2.2)
        + (∑ p ∈ plaqIndex.filter (fun p => ¬ IsPosPlaq p),
          plaquetteDensity (torusShift N) ρ U p.1 p.2.1 p.2.2) :=
    (Finset.sum_filter_add_sum_filter_not _ IsPosPlaq
      (fun p => plaquetteDensity (torusShift N) ρ U p.1 p.2.1
        p.2.2)).symm
  rw [wilsonAction_eq_sum_plaqIndex, step1, step2]
  unfold wilsonActionPlus wilsonActionMinus wilsonActionZero
  ring

end Split

/-! ## §5b. Transport of the three classes under the reflection

The reflected index map sends the positive class onto the negative
class and vice versa (the height arithmetic of the even torus),
and fixes the crossing class pointwise — the crossing class is
exactly the temporal plaquettes over the two fixed link layers of
§2. Hence `S₊ ∘ θ = S₋`, `S₋ ∘ θ = S₊`, `S₀ ∘ θ = S₀`, and the
Wilson action itself is reflection-invariant. -/

section ClassTransport

variable {G : Type*} [Group G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

theorem div_two_mul (hN : Even N) : N / 2 * 2 = N := by
  obtain ⟨m, hm⟩ := hN
  rw [hm, ← two_mul m, Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 2),
    mul_comm m 2]

theorem two_le_of_even (hN : Even N) : 2 ≤ N := by
  obtain ⟨m, hm⟩ := hN
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · rw [h0] at hm
    simp only [add_zero] at hm
    exact absurd hm (NeZero.ne N)
  · omega

/-- If `2 * x 0 = -2` in `ZMod N`, the reflected site is the
time-shifted site: `θ x = σ₀ x`. -/
theorem reflSite_eq_torusShift_of {x : Fin 4 → ZMod N}
    (h2x : 2 * x 0 = -2) : reflSite x = torusShift N 0 x := by
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [reflSite_apply_self, torusShift_apply_coord, Pi.single_eq_same]
    linear_combination -h2x
  · rw [reflSite_apply_of_ne _ hj, torusShift_apply_coord,
      Pi.single_eq_of_ne hj, zero_add]

/-- At the two crossing layers, `2 * x 0 = -2`. -/
theorem two_mul_timeCoord_eq (hN : Even N) (x : Fin 4 → ZMod N)
    (hv : (x 0).val = N / 2 - 1 ∨ (x 0).val = N - 1) :
    2 * x 0 = -2 := by
  have h2M : 2 * (N / 2) = N := by
    rw [mul_comm]
    exact div_two_mul hN
  have hN2 : 2 ≤ N := two_le_of_even hN
  rcases hv with hv | hv
  · calc 2 * x 0 = 2 * ((x 0).val : ZMod N) := by
          rw [ZMod.natCast_zmod_val]
      _ = ((2 * (x 0).val : ℕ) : ZMod N) := by norm_cast
      _ = ((N - 2 : ℕ) : ZMod N) := by
          rw [show 2 * (x 0).val = N - 2 from by omega]
      _ = -2 := by
          have hsub : ((N - 2 : ℕ) : ZMod N)
              = ((N : ℕ) : ZMod N) - ((2 : ℕ) : ZMod N) :=
            Nat.cast_sub (by omega)
          rw [hsub, ZMod.natCast_self]
          simp
  · have hx0 : x 0 = -1 := by
      rw [← ZMod.natCast_zmod_val (x 0), hv]
      exact natCast_pred_eq_neg_one
    rw [hx0]
    ring

theorem zmod_val_sub_one {a : ZMod N} (ha : a ≠ 0) :
    (a - 1).val = a.val - 1 := by
  have h1 : a.val ≠ 0 := by
    intro h
    apply ha
    have h2 : a = ((a.val : ℕ) : ZMod N) := (ZMod.natCast_zmod_val a).symm
    rw [h] at h2
    rw [h2]
    simp
  have h3 : (((a.val - 1 : ℕ)) : ZMod N) = a - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr h1),
      ZMod.natCast_zmod_val, Nat.cast_one]
  rw [← h3, ZMod.val_natCast, Nat.mod_eq_of_lt]
  have h := a.val_lt
  omega

/-- The reflected temporal base site, as a value: for a base at
time `≤ N - 2`, the reflected plaquette base `(σ₀)⁻¹ (θ x)` sits at
time `N - 2 - (x 0).val`. -/
theorem refPlaqSite_zero_val (x : Fin 4 → ZMod N)
    (hv : (x 0).val ≤ N - 2) (hN2 : 2 ≤ N) :
    ((refPlaqSite x 0) 0).val = N - 2 - (x 0).val := by
  have hne : reflSite x 0 ≠ 0 := by
    intro hzero
    have hv0 : (reflSite x 0).val = 0 := by
      rw [hzero]
      exact ZMod.val_zero
    rw [reflSite_val_zero] at hv0
    have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    omega
  rw [refPlaqSite_zero, torusShift_symm_apply_coord, Pi.single_eq_same,
    zmod_val_sub_one hne, reflSite_val_zero]
  omega

/-- The reflected spatial base site, as a value. -/
theorem refPlaqSite_val_of_ne (x : Fin 4 → ZMod N) {μ : Fin 4}
    (hμ : μ ≠ 0) :
    ((refPlaqSite x μ) 0).val = N - 1 - (x 0).val := by
  rw [refPlaqSite_of_ne _ hμ]
  exact reflSite_val_zero x

/-- The reflected plaquette index: reflect the base site (in the
temporal case, to the reflected edge's base), keep both
directions. -/
def refPlaq (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    (Fin 4 → ZMod N) × Fin 4 × Fin 4 :=
  (refPlaqSite p.1 p.2.1, p.2.1, p.2.2)

theorem refPlaq_involutive :
    Function.Involutive (refPlaq (N := N)) := by
  intro p
  obtain ⟨x, μ, ν⟩ := p
  show (refPlaqSite (refPlaqSite x μ) μ, μ, ν) = (x, μ, ν)
  congr 1
  by_cases hμ : μ = 0
  · subst hμ
    rw [refPlaqSite_zero, refPlaqSite_zero,
      reflSite_torusShift_symm_zero, reflSite_involutive,
      Equiv.symm_apply_apply]
  · rw [refPlaqSite_of_ne _ hμ, refPlaqSite_of_ne _ hμ,
      reflSite_involutive]

theorem refPlaq_mem_plaqIndex {p : (Fin 4 → ZMod N) × Fin 4 × Fin 4}
    (hp : p ∈ plaqIndex) : refPlaq p ∈ plaqIndex := by
  have hlt : (refPlaq p).2.1 < (refPlaq p).2.2 :=
    mem_plaqIndex (p := p) hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩

/-- The site component of the doubly reflected index is the
original site. -/
theorem refPlaqSite_refPlaqSite
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    refPlaqSite (refPlaq p).1 (refPlaq p).2.1 = p.1 :=
  congrArg Prod.fst (refPlaq_involutive p)

/-- **Class transport, positive to negative**: the reflection
sends the positive class into the negative class. -/
theorem isNeg_of_isPos_refPlaq (hN : Even N)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) (hp : IsPosPlaq p) :
    IsNegPlaq (refPlaq p) := by
  obtain ⟨x, μ, ν⟩ := p
  have h2M : 2 * (N / 2) = N := by
    rw [mul_comm]
    exact div_two_mul hN
  have hN2 : 2 ≤ N := two_le_of_even hN
  show N / 2 ≤ ((refPlaqSite x μ) 0).val
    ∧ plaqTimeHi (refPlaqSite x μ) μ < N
  by_cases hμ : μ = 0
  · subst hμ
    have hp' : (x 0).val + 1 < N / 2 := hp
    have hv : (x 0).val ≤ N - 2 := by omega
    refine ⟨?_, ?_⟩
    · rw [refPlaqSite_zero_val _ hv hN2]
      omega
    · rw [plaqTimeHi_zero, refPlaqSite_zero_val _ hv hN2]
      omega
  · have hp' : (x 0).val < N / 2 := by
      have h : plaqTimeHi x μ < N / 2 := hp
      rwa [plaqTimeHi_of_ne (N := N) _ hμ] at h
    refine ⟨?_, ?_⟩
    · rw [refPlaqSite_val_of_ne _ hμ]
      omega
    · rw [plaqTimeHi_of_ne (N := N) _ hμ, refPlaqSite_val_of_ne _ hμ]
      omega

/-- **Class transport, negative to positive**. -/
theorem isPos_of_isNeg_refPlaq (hN : Even N)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) (hp : IsNegPlaq p) :
    IsPosPlaq (refPlaq p) := by
  obtain ⟨x, μ, ν⟩ := p
  have h2M : 2 * (N / 2) = N := by
    rw [mul_comm]
    exact div_two_mul hN
  have hN2 : 2 ≤ N := two_le_of_even hN
  have hlo : N / 2 ≤ (x 0).val := hp.1
  show plaqTimeHi (refPlaqSite x μ) μ < N / 2
  by_cases hμ : μ = 0
  · subst hμ
    have hhi : (x 0).val + 1 < N := by
      have h : plaqTimeHi x 0 < N := hp.2
      rwa [plaqTimeHi_zero (N := N)] at h
    have hv : (x 0).val ≤ N - 2 := by omega
    rw [plaqTimeHi_zero, refPlaqSite_zero_val _ hv hN2]
    omega
  · have hhi : (x 0).val < N := by
      have h : plaqTimeHi x μ < N := hp.2
      rwa [plaqTimeHi_of_ne (N := N) _ hμ] at h
    rw [plaqTimeHi_of_ne (N := N) _ hμ, refPlaqSite_val_of_ne _ hμ]
    omega

/-- **The crossing class is fixed pointwise by the reflected
index map** — and this uses its characterization: a crossing
index is temporal, based at `N / 2 - 1` or `N - 1` (the arithmetic
in the proof), which is exactly the fixed-stratum condition of
§2. -/
theorem refPlaq_eq_of_isZeroPlaq (hN : Even N)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) (hp : IsZeroPlaq p) :
    refPlaq p = p := by
  obtain ⟨x, μ, ν⟩ := p
  have h2M : 2 * (N / 2) = N := by
    rw [mul_comm]
    exact div_two_mul hN
  have hN2 : 2 ≤ N := two_le_of_even hN
  have hμ : μ = 0 := by
    by_contra hμ
    by_cases hv : (x 0).val < N / 2
    · apply hp.1
      show plaqTimeHi x μ < N / 2
      rw [plaqTimeHi_of_ne (N := N) _ hμ]
      exact hv
    · apply hp.2
      refine ⟨not_lt.mp hv, ?_⟩
      show plaqTimeHi x μ < N
      rw [plaqTimeHi_of_ne (N := N) _ hμ]
      exact (x 0).val_lt
  subst hμ
  have hnp : ¬ ((x 0).val + 1 < N / 2) := hp.1
  have hnn : ¬ (N / 2 ≤ (x 0).val ∧ (x 0).val + 1 < N) := hp.2
  have hv : (x 0).val = N / 2 - 1 ∨ (x 0).val = N - 1 := by
    have hlt := (x 0).val_lt
    omega
  have h2x : 2 * x 0 = -2 := two_mul_timeCoord_eq hN x hv
  have hx2 : reflSite x = torusShift N 0 x :=
    reflSite_eq_torusShift_of h2x
  show (refPlaqSite x 0, (0 : Fin 4), ν) = (x, 0, ν)
  rw [refPlaqSite_zero, hx2, Equiv.symm_apply_apply]

/-- `S₊` of the reflected configuration is `S₋` of the original:
the two halves are θ-transports of each other. -/
theorem wilsonActionPlus_reflConfig (hN : Even N) (β : ℝ)
    (U : Config (Fin 4 → ZMod N) G) :
    wilsonActionPlus ρ β (reflConfig U)
      = wilsonActionMinus ρ β U := by
  unfold wilsonActionPlus wilsonActionMinus
  congr 1
  refine Finset.sum_nbij' refPlaq refPlaq ?_ ?_ ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_filter.mpr
      ⟨refPlaq_mem_plaqIndex (Finset.mem_filter.mp hp).1,
      isNeg_of_isPos_refPlaq hN p (Finset.mem_filter.mp hp).2⟩
  · intro p hp
    exact Finset.mem_filter.mpr
      ⟨refPlaq_mem_plaqIndex (Finset.mem_filter.mp hp).1,
      isPos_of_isNeg_refPlaq hN p (Finset.mem_filter.mp hp).2⟩
  · intro p _
    exact refPlaq_involutive p
  · intro p _
    exact refPlaq_involutive p
  · intro p hp
    have hlt : (refPlaq p).2.1 < (refPlaq p).2.2 :=
      mem_plaqIndex (p := p) (Finset.mem_filter.mp hp).1
    have ht := plaquetteDensity_reflConfig ρ U (refPlaq p).1 hlt
    rwa [refPlaqSite_refPlaqSite] at ht

/-- `S₋` of the reflected configuration is `S₊` of the original. -/
theorem wilsonActionMinus_reflConfig (hN : Even N) (β : ℝ)
    (U : Config (Fin 4 → ZMod N) G) :
    wilsonActionMinus ρ β (reflConfig U)
      = wilsonActionPlus ρ β U := by
  unfold wilsonActionPlus wilsonActionMinus
  congr 1
  refine Finset.sum_nbij' refPlaq refPlaq ?_ ?_ ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_filter.mpr
      ⟨refPlaq_mem_plaqIndex (Finset.mem_filter.mp hp).1,
      isPos_of_isNeg_refPlaq hN p (Finset.mem_filter.mp hp).2⟩
  · intro p hp
    exact Finset.mem_filter.mpr
      ⟨refPlaq_mem_plaqIndex (Finset.mem_filter.mp hp).1,
      isNeg_of_isPos_refPlaq hN p (Finset.mem_filter.mp hp).2⟩
  · intro p _
    exact refPlaq_involutive p
  · intro p _
    exact refPlaq_involutive p
  · intro p hp
    have hlt : (refPlaq p).2.1 < (refPlaq p).2.2 :=
      mem_plaqIndex (p := p) (Finset.mem_filter.mp hp).1
    have ht := plaquetteDensity_reflConfig ρ U (refPlaq p).1 hlt
    rwa [refPlaqSite_refPlaqSite] at ht

/-- `S₀` is reflection-invariant term by term: on the crossing
class the reflected index is the index itself. -/
theorem wilsonActionZero_reflConfig (hN : Even N) (β : ℝ)
    (U : Config (Fin 4 → ZMod N) G) :
    wilsonActionZero ρ β (reflConfig U)
      = wilsonActionZero ρ β U := by
  unfold wilsonActionZero
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp0 : IsZeroPlaq p := (Finset.mem_filter.mp hp).2
  have hlt : p.2.1 < p.2.2 := mem_plaqIndex (Finset.mem_filter.mp hp).1
  have hsite : refPlaqSite p.1 p.2.1 = p.1 :=
    congrArg Prod.fst (refPlaq_eq_of_isZeroPlaq hN p hp0)
  have ht := plaquetteDensity_reflConfig ρ U p.1 hlt
  rwa [hsite] at ht

/-- **The Wilson action is reflection-invariant** — the corollary
of the split and the class transports that 1b-B will consume
(through the Gibbs density). -/
theorem wilsonAction_reflConfig (hN : Even N) (β : ℝ)
    (U : Config (Fin 4 → ZMod N) G) :
    wilsonAction (torusShift N) ρ β (reflConfig U)
      = wilsonAction (torusShift N) ρ β U := by
  rw [wilsonAction_split, wilsonAction_split,
    wilsonActionPlus_reflConfig ρ hN, wilsonActionMinus_reflConfig ρ hN,
    wilsonActionZero_reflConfig ρ hN]
  ring

end ClassTransport

/-! ## §6. The Gibbs measure is reflection-invariant

The density is `exp (−S_β)`, and the action is invariant, so the
density is invariant; the normalization constant is a number,
hence unchanged; and the base measure is invariant by §3. So the
Stage 1a Gibbs measure satisfies `map θ μ_Gibbs = μ_Gibbs` for
every real `β` and every even `N` — the measure-compatibility
input that reflection positivity (Stage 1b-B) consumes. -/

section Gibbs

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]

/-- The Gibbs density is invariant under the configuration
reflection, because the Wilson action is. -/
theorem gibbsDensity_reflConfig (hN : Even N) (β : ℝ)
    (U : Config (Fin 4 → ZMod N) G) :
    gibbsDensity (torusShift N) ρ β (reflConfig U)
      = gibbsDensity (torusShift N) ρ β U := by
  apply Subtype.ext
  show Real.exp (- wilsonAction (torusShift N) ρ β (reflConfig U))
    = Real.exp (- wilsonAction (torusShift N) ρ β U)
  rw [wilsonAction_reflConfig ρ hN β U]

/-- The Gibbs density, coerced to `ℝ≥0∞`, is measurable. -/
theorem measurable_gibbsDensity_coe
    (hρcont : Continuous fun g => repMatrix ρ g) (β : ℝ) :
    Measurable (fun U : Config (Fin 4 → ZMod N) G =>
      (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞)) :=
  measurable_coe_nnreal_ennreal.comp
    (measurable_gibbsDensity (torusShift N) ρ hρcont β)

/-- **The Gibbs measure is invariant under the configuration
reflection** (strong `Measure.map` form), for every real `β` and
every even extent `N`. -/
theorem gibbsMeasure_map_reflConfig
    (hρcont : Continuous fun g => repMatrix ρ g) (hN : Even N)
    (β : ℝ) :
    Measure.map reflConfig (gibbsMeasure (torusShift N) μG ρ β)
      = gibbsMeasure (torusShift N) μG ρ β := by
  ext s hs
  rw [Measure.map_apply measurable_reflConfig hs]
  unfold gibbsMeasure
  rw [Measure.smul_apply, Measure.smul_apply]
  have h1 : ((configMeasure μG :
        Measure (Config (Fin 4 → ZMod N) G)).restrict s)
      = Measure.map reflConfig
          ((configMeasure μG :
            Measure (Config (Fin 4 → ZMod N) G)).restrict
            (reflConfig ⁻¹' s)) := by
    rw [← Measure.restrict_map measurable_reflConfig hs,
      configMeasure_map_reflConfig μG]
  have key : (∫⁻ U, (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞)
        ∂((configMeasure μG :
          Measure (Config (Fin 4 → ZMod N) G)).restrict
          (reflConfig ⁻¹' s)))
      = ∫⁻ U, (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞)
        ∂((configMeasure μG :
          Measure (Config (Fin 4 → ZMod N) G)).restrict s) := by
    rw [h1, lintegral_map (measurable_gibbsDensity_coe ρ hρcont β)
      measurable_reflConfig]
    refine lintegral_congr fun U => ?_
    exact congrArg (fun r : ℝ≥0 => (r : ℝ≥0∞))
      (gibbsDensity_reflConfig ρ hN β U).symm
  have hwd : ((configMeasure μG :
        Measure (Config (Fin 4 → ZMod N) G)).withDensity
        (fun U => (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞)))
        (reflConfig ⁻¹' s)
      = ((configMeasure μG :
          Measure (Config (Fin 4 → ZMod N) G)).withDensity
          (fun U => (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞))) s := by
    rw [withDensity_apply _ (measurable_reflConfig hs),
      withDensity_apply _ hs]
    exact key
  rw [hwd]

end Gibbs

end ThetLogos
