import ThetLogos.XYZTripotents

/-!
# ThetLogos.XYZPoolKill — K-XYZ-2: the named-pool family kill (T3 kill; T5 question OPEN)

This module lands pre-registered kill **K-XYZ-2** from the XYZ campaign
(scoping §4). It is a **FAMILY kill**, in exactly these terms:

- **The named pool is dead.** The sixteen named tripotents assembled below
  as `namedPool` — the identity, the two C_F sector projections, the
  grading `gammaF`, the real structure `UJ`, the colour generator `genC`,
  the three H-sector generators `genH k`, and the seven M-sector
  generators `genM a` with `a ≠ 7` — are all Gaussian-integer-valued, so
  by the R5 entry-ring invariant (`no_gaussInt_triple_reaches_genM7`,
  XYZTripotents §14) **no triple drawn from this pool** generates the
  twelve `smGen`: every such triple provably misses `smGen 11 = genM 7`.
  That is `namedPool_no_xyz`, stated in decision form as
  `namedPool_kill`, the pool-restricted negation of
  `xyz_tripotents_exist`.
- **The question `xyz_tripotents_exist` is NOT dead.** It stays **OPEN**.
  This module is a new entry *beside* the posted statement in
  `ThetLogos.XYZTripotents`; the post itself is untouched, and nothing
  here is a NO on the question. Any reading of this module as settling
  `xyz_tripotents_exist` negatively is a misreading (fence per the
  K-S0-3 precedent).

Why "failure to find is not a kill" does not apply here: nothing in this
module is a search outcome. The kill is an **exact invariant argument**
(rubric rule R5): Gaussian-integer entries are preserved by `star`,
addition, and multiplication, hence by every ternary product and by the
whole generated TRO (`memGenTRO_gaussInt`), while the target `genM 7`
carries the entry `1/√3` at (18, 18), which is provably not a Gaussian
integer (`not_gaussInt_inv_sqrt3`). The invariant decides every triple
from the pool at once; no enumeration of triples is performed or needed.

The boundary, named on the face: the pool **excludes `genM 7`**, the one
pool-adjacent generator whose λ₈ diagonal entries carry `1/√3` (and which
is separately known not to be a tripotent, `not_tripotent_genM7`). That
exclusion is exactly the `1/√3` boundary: it is what XYZ-2's boundary
marker and XYZ-3's live families exist to cross. A viable XYZ triple, if
one exists, must use at least one tripotent outside this named pool with
entries outside `ℤ[i]`.

Status: NO CLAIM. Dials 0/4, nowhere moved. Tier T3 (machine-checked)
for the kill itself; the underlying question remains T5/open.
-/

namespace ThetLogos

/-! ## §1. The named pool as data -/

/-- The named pool: exactly sixteen named tripotents — the six singletons
    `1`, `cfMat`, `1 - cfMat`, `gammaF`, `UJ`, `genC`, the three
    H-sector generators `genH k` (`k : Fin 3`), and the seven M-sector
    generators `genM a` with `a ≠ 7` (`a : Fin 8`, `7` filtered out).
    `genM 7` is deliberately excluded: it is the `1/√3` boundary member.
    Tier T2. -/
noncomputable def namedPool : List (Matrix I32 I32 ℂ) :=
  [1, cfMat, 1 - cfMat, gammaF, UJ, genC]
    ++ (List.finRange 3).map genH
    ++ ((List.finRange 8).filter (· ≠ 7)).map genM

/-- Membership in the named pool. Tier T2. -/
def InPool (X : Matrix I32 I32 ℂ) : Prop := X ∈ namedPool

/-- The named pool has exactly sixteen members: 6 + 3 + 7. Tier T3. -/
theorem namedPool_length : namedPool.length = 16 := by
  decide

/-! ## §2. Entry facts: every pool member is Gaussian-integer-valued

Already in `ThetLogos.XYZTripotents` (consumed, not reproved):
`UJ_gaussInt`, `genH_gaussInt`, and `genM_zero_gaussInt` (the `a = 0`
case only), on top of `gaussInt_zero`, `gaussInt_one`,
`gaussInt_neg_one`, `gaussInt_I`, `gaussInt_neg_I`, `pauli_gaussInt`,
`gellMann_zero_gaussInt`.

New here: a subtraction closure helper `gaussInt_sub`, the entry facts
for `1`, `cfMat`, `1 - cfMat`, `gammaF`, `genC`, and the general
`gellMann`/`genM` entry facts for `a ≠ 7`.
-/

/-- Gaussian integers are closed under subtraction. Tier T3 (proved). -/
theorem gaussInt_sub {x y : ℂ} (hx : IsGaussInt x) (hy : IsGaussInt y) :
    IsGaussInt (x - y) := by
  obtain ⟨a1, b1, rfl⟩ := hx
  obtain ⟨a2, b2, rfl⟩ := hy
  refine ⟨a1 - a2, b1 - b2, ?_⟩
  push_cast
  ring

/-- Entries of the identity matrix are Gaussian integers: `1` on the
    diagonal, `0` off it. Tier T3 (proved). -/
theorem one_gaussInt (i j : I32) :
    IsGaussInt ((1 : Matrix I32 I32 ℂ) i j) := by
  rw [Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos h]; exact gaussInt_one
  · rw [if_neg h]; exact gaussInt_zero

/-- Entries of `cfMat` are Gaussian integers: it is diagonal with
    indicator entries in `{0, 1}`. Tier T3 (proved). -/
theorem cfMat_gaussInt (i j : I32) : IsGaussInt (cfMat i j) := by
  rw [cfMat_apply]
  by_cases h : i = j
  · rw [if_pos h]
    rcases cfIndicator_mem i with h0 | h1
    · rw [h0]; exact gaussInt_zero
    · rw [h1]; exact gaussInt_one
  · rw [if_neg h]; exact gaussInt_zero

/-- Entries of `1 - cfMat` are Gaussian integers, by subtraction closure
    from the identity and `cfMat` entry facts. Tier T3 (proved). -/
theorem one_sub_cfMat_gaussInt (i j : I32) :
    IsGaussInt ((1 - cfMat : Matrix I32 I32 ℂ) i j) := by
  rw [Matrix.sub_apply]
  exact gaussInt_sub (one_gaussInt i j) (cfMat_gaussInt i j)

/-- Entries of the grading `gammaF` are Gaussian integers: it is diagonal
    with entries in `{1, -1}`, and `0` off the diagonal.
    Tier T3 (proved). -/
theorem gammaF_gaussInt (i j : I32) : IsGaussInt (gammaF i j) := by
  by_cases h : i = j
  · subst h
    simp only [gammaF]
    split_ifs <;>
      first
        | exact gaussInt_one
        | exact gaussInt_neg_one
  · rw [gammaF_apply_ne h]; exact gaussInt_zero

/-- Entries of the colour generator `genC` are Gaussian integers: it is
    diagonal with entries in `{Complex.I, 0}`, and `0` off the diagonal.
    Tier T3 (proved). -/
theorem genC_gaussInt (i j : I32) : IsGaussInt (genC i j) := by
  by_cases h : i = j
  · subst h
    rcases genC_diag_I_or_zero i with hI | h0
    · rw [hI]; exact gaussInt_I
    · rw [h0]; exact gaussInt_zero
  · rw [genC_apply_ne h]; exact gaussInt_zero

/-- Entries of `gellMann a` are Gaussian integers for `a ≠ 7`: for
    `a = 0, …, 6` every entry is `0`, `±1`, or `±Complex.I` by
    construction. The hypothesis `a ≠ 7` is consumed exactly here, at
    the λ₈ case: `gellMann 7 = (√3)⁻¹ • !![1, 0, 0; 0, 1, 0; 0, 0, -2]`,
    whose diagonal entries carry the `1/√3` factor and are not Gaussian
    integers. Tier T3 (proved). -/
theorem gellMann_gaussInt {a : Fin 8} (ha : a ≠ 7) (p q : Fin 3) :
    IsGaussInt (gellMann a p q) := by
  fin_cases a <;> fin_cases p <;> fin_cases q <;>
    simp only [gellMann, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] <;>
    first
      | exact gaussInt_zero
      | exact gaussInt_one
      | exact gaussInt_neg_one
      | exact gaussInt_I
      | exact gaussInt_neg_I
      | exact (ha (by decide)).elim

/-- Entries of `genM a` are Gaussian integers for `a ≠ 7`: off the colour
    triplets the entries are `0`, and on a triplet block they are entries
    of `gellMann a`. The hypothesis `a ≠ 7` is consumed exactly at those
    block entries, via `gellMann_gaussInt` — the λ₈ diagonal is the only
    place `1/√3` could enter. Tier T3 (proved). -/
theorem genM_gaussInt {a : Fin 8} (ha : a ≠ 7) (i j : I32) :
    IsGaussInt (genM a i j) := by
  unfold genM
  cases h1 : tripletOf i.val with
  | none =>
    cases h2 : tripletOf j.val with
    | none => simp only [gaussInt_zero]
    | some tp2 => simp only [gaussInt_zero]
  | some tp1 =>
    obtain ⟨t1, p1⟩ := tp1
    cases h2 : tripletOf j.val with
    | none => simp only [gaussInt_zero]
    | some tp2 =>
      obtain ⟨t2, p2⟩ := tp2
      simp only []
      by_cases heq : t1 = t2
      · rw [if_pos heq]; exact gellMann_gaussInt ha p1 p2
      · rw [if_neg heq]; exact gaussInt_zero

/-- Assembly: every member of the named pool is Gaussian-integer-valued
    at every entry. Case split over the finite pool: the six singletons
    by their entry facts above (with `UJ_gaussInt` consumed from
    XYZTripotents), the H-family by `genH_gaussInt` (consumed), and the
    M-family by `genM_gaussInt`, where the filter's `a ≠ 7` condition is
    exactly what that lemma consumes. Tier T3 (proved). -/
theorem inPool_gaussInt {X : Matrix I32 I32 ℂ} (hX : InPool X)
    (i j : I32) : IsGaussInt (X i j) := by
  unfold InPool namedPool at hX
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_finRange, List.mem_filter] at hX
  rcases hX with ((rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, -, rfl⟩) | ⟨a, ⟨-, ha⟩, rfl⟩
  · exact one_gaussInt i j
  · exact cfMat_gaussInt i j
  · exact one_sub_cfMat_gaussInt i j
  · exact gammaF_gaussInt i j
  · exact UJ_gaussInt i j
  · exact genC_gaussInt i j
  · exact genH_gaussInt k i j
  · exact genM_gaussInt (of_decide_eq_true ha) i j

/-! ## §3. The uniform kill (K-XYZ-2)

One application of R5 decides the whole family at once: any pool triple
is Gaussian-integer-valued (`inPool_gaussInt`), so its generated TRO
cannot reach `smGen 11 = genM 7` (`no_gaussInt_triple_reaches_genM7`).
This kills the named pool as a source of XYZ triples. It does **not**
kill, close, or answer `xyz_tripotents_exist`: that question stays
open, and a witness, if one exists, must come from outside this pool.
-/

/-- K-XYZ-2, uniform form: no triple drawn from the named pool reaches
    all twelve `smGen` — every such triple misses `smGen 11`.
    Tier T3 (proved). -/
theorem namedPool_no_xyz (X Y Z : Matrix I32 I32 ℂ)
    (hX : InPool X) (hY : InPool Y) (hZ : InPool Z) :
    ¬ ∀ g : Fin 12,
      MemGenTRO ({X, Y, Z} : Set (Matrix I32 I32 ℂ)) (smGen g) := by
  intro hall
  exact no_gaussInt_triple_reaches_genM7 X Y Z
    (fun i j => inPool_gaussInt hX i j)
    (fun i j => inPool_gaussInt hY i j)
    (fun i j => inPool_gaussInt hZ i j) (hall 11)

/-- K-XYZ-2, decision form: the pool-restricted negation of
    `xyz_tripotents_exist` — there is no XYZ triple with all three
    members in the named pool. A NEW entry beside the post in
    `ThetLogos.XYZTripotents` (relabeling rule); the post itself, and
    the open question it states, are untouched. Tier T3 (proved). -/
theorem namedPool_kill :
    ¬ ∃ X Y Z : Matrix I32 I32 ℂ, InPool X ∧ InPool Y ∧ InPool Z ∧
      Tripotent X ∧ Tripotent Y ∧ Tripotent Z ∧
      ∀ g : Fin 12,
        MemGenTRO ({X, Y, Z} : Set (Matrix I32 I32 ℂ)) (smGen g) := by
  rintro ⟨X, Y, Z, hX, hY, hZ, -, -, -, hall⟩
  exact namedPool_no_xyz X Y Z hX hY hZ hall

end ThetLogos
