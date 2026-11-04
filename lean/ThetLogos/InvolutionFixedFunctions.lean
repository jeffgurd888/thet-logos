/-
# U-3b — FIXED FUNCTIONS OF A FINITE INVOLUTION: THE ABSTRACT MASTER

Brick: U-3b ABSTRACT FINITE-INVOLUTION THEOREM (Jeff's
unification line; scoping `unification-scoping-2026-11-03.md`
§2 U-3, seats §1.2). Lane base: main HEAD `699b926`
(Universal Bridge integration; the brief's stated base
`5050bb2` plus that one integration — census at cut
13,164 strict / 482 modules).

**What this module proves — and all it proves:** for an
arbitrary type `A`, a map `σ : A → A`, and a system of orbit
representatives given as DATA (a `RepSystem`: `repOf`,
`repEmbed`, and exactly three pointwise axioms), the
`σ`-fixed real-valued functions on `A` are exactly the
functions on the representatives:

  `fixedFunctions_equiv_reps : {f : A → ℝ // ∀ x, f (σ x) = f x} ≃ (R → ℝ)`

plus the PRODUCT clause: the representative data of a
product is the product of the representative data, and the
jointly fixed functions on `A × B` — fixed in each coordinate
separately, the two-arm notion of
`MirrorTwentyOneOrthogonal` — are exactly the functions on
`R × S`. The two concrete seats then fall out as corollaries
in this module: `MirrorTwentyOneAlgebra.fixedEquivReps`
(≃ `Fin 11 → ℝ`) and `MirrorTwentyOneOrthogonal`'s joint
equiv (≃ `(Fin 11 × Fin 11) → ℝ`) are re-derived FROM the
master; the original modules are untouched.

**The rep axioms, stated exactly (K-U3-REP audit).** A
`RepSystem` carries three axioms, all pointwise statements
about POINTS, none quantifying over functions:

  (R1) `repOf (repEmbed r) = r` — an embedded representative
       represents itself;
  (R2) `repOf (σ x) = repOf x` — mirror points share a
       representative;
  (R3) `repEmbed (repOf x) = x ∨ repEmbed (repOf x) = σ x` —
       the embedded representative of `x` is `x` or its
       mirror.

These are exactly what the proof consumes and no more: in
particular `Function.Involutive σ` and `Fintype A` are NOT
assumed — the equiv needs neither (finiteness is what the
CONCRETE instances use to exhibit their rep systems, e.g.
the `Fin 21` arithmetic behind `repOf`/`repEmbed`). The
axioms do not smuggle the conclusion: they are checkable
point-by-point for any proposed instance without ever
mentioning a function space, and the kill K-U3-REP
("rep system defined as a section of the fixed-function
quotient") does NOT fire — see the landing dossier.

**Product-clause honesty.** The product representative data
is NOT claimed to be a `RepSystem` for the diagonal
involution `Prod.map σ τ`: axiom (R3) fails for it in the
mixed cases (one coordinate mirrored, the other not). The
product theorem is therefore stated for the two-arm joint
fixedness — fixed under `(σ ·, ·)` and under `(·, τ ·)`
separately — which is exactly the joint notion the
Orthogonal seat uses, and exactly what the mixed cases need.
Diagonal-only fixedness on `A × B` is a different, larger
space in general and is not asserted here.

**Honesty fence (scoping §1.2).** The fixed-function
dimension under negation, `(n+1)/2 = 11` at `n = 21`, is a
DIFFERENT number from the kernel dimension `1` of a
connected web's Laplacian (§1.1): zero modes vs orbit
representatives. This module is about the second; it says
nothing about the first, and the two are not conflated.

**NO CLAIM** — parts of any official Millennium statement
closed by this module: 0. Dials: 0/4. §4 fence respected:
nothing here touches the analytic line, W3, or physics.
-/

import Mathlib.Basic.Real.Basic
import ThetLogos.MirrorTwentyOneOrthogonal

namespace ThetLogos

/-- A system of orbit representatives for a map `σ : A → A`,
as data: a choice `repOf x` of representative index for each
point, an embedding `repEmbed` of representatives back into
`A`, and the three pointwise axioms (R1)–(R3) of the module
header. No hypothesis on `σ` itself (not even involutivity)
and no finiteness on `A` is carried: the master theorem
below consumes exactly these three axioms. -/
structure RepSystem {A R : Type*} (σ : A → A) where
  /-- The representative index of a point. -/
  repOf : A → R
  /-- The embedding of a representative as a point of `A`. -/
  repEmbed : R → A
  /-- (R1) An embedded representative represents itself. -/
  repOf_repEmbed : ∀ r, repOf (repEmbed r) = r
  /-- (R2) A point and its `σ`-image share a representative. -/
  repOf_invol : ∀ x, repOf (σ x) = repOf x
  /-- (R3) The embedded representative of `x` is `x` itself
  or its `σ`-image. -/
  repEmbed_repOf : ∀ x, repEmbed (repOf x) = x ∨ repEmbed (repOf x) = σ x

/-- Extend values on the representatives to a function on
all of `A`, constant on each representative class:
`extendRep S g x = g (repOf x)`. -/
def RepSystem.extendRep {A R : Type*} {σ : A → A} (S : @RepSystem A R σ)
    (g : R → ℝ) : A → ℝ :=
  fun x => g (S.repOf x)

/-- The extension of representative values is `σ`-fixed:
at a mirrored point it takes the same value, by (R2). -/
theorem RepSystem.extendRep_fixed {A R : Type*} {σ : A → A}
    (S : @RepSystem A R σ) (g : R → ℝ) (x : A) :
    S.extendRep g (σ x) = S.extendRep g x := by
  show g (S.repOf (σ x)) = g (S.repOf x)
  rw [S.repOf_invol]

/-- The extension of representative values restricts back to
those values at embedded representatives, by (R1). -/
theorem RepSystem.extendRep_repEmbed {A R : Type*} {σ : A → A}
    (S : @RepSystem A R σ) (g : R → ℝ) (r : R) :
    S.extendRep g (S.repEmbed r) = g r := by
  show g (S.repOf (S.repEmbed r)) = g r
  rw [S.repOf_repEmbed]

/-- A `σ`-fixed function takes the same value at the
embedded representative of a point as at the point itself:
the embedded representative is the point or its mirror, by
(R3), and fixedness absorbs the mirror. -/
theorem RepSystem.fixed_apply_repEmbed_repOf {A R : Type*} {σ : A → A}
    (S : @RepSystem A R σ) (f : A → ℝ) (hf : ∀ x, f (σ x) = f x) (x : A) :
    f (S.repEmbed (S.repOf x)) = f x := by
  rcases S.repEmbed_repOf x with h | h
  · rw [h]
  · rw [h]; exact hf x

/-- **U-3b MASTER.** For any map `σ : A → A` equipped with a
representative system `S`, the `σ`-fixed real-valued
functions on `A` are exactly the functions on the
representatives: restriction to embedded representatives is
a bijection between fixed functions and arbitrary values on
`R`. The proof consumes exactly axioms (R1)–(R3); neither
involutivity of `σ` nor finiteness of `A` is needed. -/
def fixedFunctions_equiv_reps {A R : Type*} {σ : A → A} (S : @RepSystem A R σ) :
    {f : A → ℝ // ∀ x, f (σ x) = f x} ≃ (R → ℝ) where
  toFun := fun f r => f.1 (S.repEmbed r)
  invFun := fun g => ⟨S.extendRep g, S.extendRep_fixed g⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext x
    show f.1 (S.repEmbed (S.repOf x)) = f.1 x
    exact S.fixed_apply_repEmbed_repOf f.1 f.2 x
  right_inv := by
    intro g
    funext r
    show S.extendRep g (S.repEmbed r) = g r
    exact S.extendRep_repEmbed g r

/-- The master restriction map is bijective. -/
theorem fixedFunctions_equiv_reps_bijective {A R : Type*} {σ : A → A}
    (S : @RepSystem A R σ) :
    Function.Bijective (fixedFunctions_equiv_reps S) :=
  (fixedFunctions_equiv_reps S).bijective

/-- The master equiv, applied: a fixed function is read off
at embedded representatives. -/
theorem fixedFunctions_equiv_reps_apply {A R : Type*} {σ : A → A}
    (S : @RepSystem A R σ) (f : {f : A → ℝ // ∀ x, f (σ x) = f x}) (r : R) :
    fixedFunctions_equiv_reps S f r = f.1 (S.repEmbed r) := rfl

/-- The master equiv, inverse applied: values on the
representatives extend constantly on representative
classes. -/
theorem fixedFunctions_equiv_reps_symm_apply {A R : Type*} {σ : A → A}
    (S : @RepSystem A R σ) (g : R → ℝ) (x : A) :
    ((fixedFunctions_equiv_reps S).symm g).1 x = g (S.repOf x) := rfl

/-- The representative index of a product point: the pair of
the coordinates' representatives. This is the product of
the two rep systems' data (see the header for why it is not
packaged as a `RepSystem` for the diagonal involution). -/
def prodRepOf {A B R S : Type*} {σ : A → A} {τ : B → B}
    (SA : @RepSystem A R σ) (SB : @RepSystem B S τ) : A × B → R × S :=
  fun p => (SA.repOf p.1, SB.repOf p.2)

/-- The embedding of a representative pair: coordinatewise. -/
def prodRepEmbed {A B R S : Type*} {σ : A → A} {τ : B → B}
    (SA : @RepSystem A R σ) (SB : @RepSystem B S τ) : R × S → A × B :=
  fun q => (SA.repEmbed q.1, SB.repEmbed q.2)

/-- The product representative data satisfies (R1),
coordinatewise. -/
theorem prodRepOf_prodRepEmbed {A B R S : Type*} {σ : A → A} {τ : B → B}
    (SA : @RepSystem A R σ) (SB : @RepSystem B S τ) (q : R × S) :
    prodRepOf SA SB (prodRepEmbed SA SB q) = q := by
  obtain ⟨r, s⟩ := q
  show (SA.repOf (SA.repEmbed r), SB.repOf (SB.repEmbed s)) = (r, s)
  rw [SA.repOf_repEmbed, SB.repOf_repEmbed]

/-- Mirroring the first coordinate does not change a product
point's representative pair, by (R2) in the first factor. -/
theorem prodRepOf_fst_invol {A B R S : Type*} {σ : A → A} {τ : B → B}
    (SA : @RepSystem A R σ) (SB : @RepSystem B S τ) (p : A × B) :
    prodRepOf SA SB (σ p.1, p.2) = prodRepOf SA SB p := by
  show (SA.repOf (σ p.1), SB.repOf p.2) = (SA.repOf p.1, SB.repOf p.2)
  rw [SA.repOf_invol]

/-- Mirroring the second coordinate does not change a
product point's representative pair, by (R2) in the second
factor. -/
theorem prodRepOf_snd_invol {A B R S : Type*} {σ : A → A} {τ : B → B}
    (SA : @RepSystem A R σ) (SB : @RepSystem B S τ) (p : A × B) :
    prodRepOf SA SB (p.1, τ p.2) = prodRepOf SA SB p := by
  show (SA.repOf p.1, SB.repOf (τ p.2)) = (SA.repOf p.1, SB.repOf p.2)
  rw [SB.repOf_invol]

/-- The product form of (R3): each coordinate of the
embedded representative pair is that coordinate or its
mirror — a conjunction of disjunctions, NOT the single
disjunction the diagonal involution would require (the
mixed cases are genuine, and the joint theorem below is
shaped to absorb them with two-arm fixedness). -/
theorem prodRepEmbed_prodRepOf {A B R S : Type*} {σ : A → A} {τ : B → B}
    (SA : @RepSystem A R σ) (SB : @RepSystem B S τ) (p : A × B) :
    ((prodRepEmbed SA SB (prodRepOf SA SB p)).1 = p.1 ∨
      (prodRepEmbed SA SB (prodRepOf SA SB p)).1 = σ p.1) ∧
    ((prodRepEmbed SA SB (prodRepOf SA SB p)).2 = p.2 ∨
      (prodRepEmbed SA SB (prodRepOf SA SB p)).2 = τ p.2) :=
  ⟨SA.repEmbed_repOf p.1, SB.repEmbed_repOf p.2⟩

/-- Extend values on the representative pairs to a grid
function, constant on representative classes. -/
def prodExtendRep {A B R S : Type*} {σ : A → A} {τ : B → B}
    (SA : @RepSystem A R σ) (SB : @RepSystem B S τ) (g : R × S → ℝ) :
    A × B → ℝ :=
  fun p => g (prodRepOf SA SB p)

/-- The product extension is fixed in the first coordinate. -/
theorem prodExtendRep_fst_fixed {A B R S : Type*} {σ : A → A} {τ : B → B}
    (SA : @RepSystem A R σ) (SB : @RepSystem B S τ) (g : R × S → ℝ) (p : A × B) :
    prodExtendRep SA SB g (σ p.1, p.2) = prodExtendRep SA SB g p := by
  show g (prodRepOf SA SB (σ p.1, p.2)) = g (prodRepOf SA SB p)
  rw [prodRepOf_fst_invol]

/-- The product extension is fixed in the second
coordinate. -/
theorem prodExtendRep_snd_fixed {A B R S : Type*} {σ : A → A} {τ : B → B}
    (SA : @RepSystem A R σ) (SB : @RepSystem B S τ) (g : R × S → ℝ) (p : A × B) :
    prodExtendRep SA SB g (p.1, τ p.2) = prodExtendRep SA SB g p := by
  show g (prodRepOf SA SB (p.1, τ p.2)) = g (prodRepOf SA SB p)
  rw [prodRepOf_snd_invol]

/-- The product extension restricts back to the given values
at embedded representative pairs, by the product (R1). -/
theorem prodExtendRep_prodRepEmbed {A B R S : Type*}
    {σ : A → A} {τ : B → B}
    (SA : @RepSystem A R σ) (SB : @RepSystem B S τ) (g : R × S → ℝ) (q : R × S) :
    prodExtendRep SA SB g (prodRepEmbed SA SB q) = g q := by
  show g (prodRepOf SA SB (prodRepEmbed SA SB q)) = g q
  rw [prodRepOf_prodRepEmbed]

/-- A jointly fixed grid function — fixed in each coordinate
separately — takes the same value at the embedded
representative pair of a point as at the point itself: the
four cases of the product (R3) are absorbed one coordinate
at a time by the two arm fixednesses. -/
theorem jointlyFixed_apply_prodRepEmbed_prodRepOf {A B R S : Type*}
    {σ : A → A} {τ : B → B}
    (SA : @RepSystem A R σ) (SB : @RepSystem B S τ) (f : A × B → ℝ)
    (h₁ : ∀ p, f (σ p.1, p.2) = f p) (h₂ : ∀ p, f (p.1, τ p.2) = f p)
    (p : A × B) :
    f (prodRepEmbed SA SB (prodRepOf SA SB p)) = f p := by
  obtain ⟨a, b⟩ := p
  show f (SA.repEmbed (SA.repOf a), SB.repEmbed (SB.repOf b)) = f (a, b)
  rcases SA.repEmbed_repOf a with ha | ha <;>
    rcases SB.repEmbed_repOf b with hb | hb
  · rw [ha, hb]
  · rw [ha, hb]; exact h₂ (a, b)
  · rw [ha, hb]; exact h₁ (a, b)
  · rw [ha, hb]; rw [h₂ (σ a, b)]; exact h₁ (a, b)

/-- **U-3b PRODUCT CLAUSE.** The rep system of a product is
the product of rep systems: the jointly fixed functions on
`A × B` — fixed under mirroring either coordinate
separately — are exactly the functions on the representative
pairs `R × S`. -/
def fixedFunctions_prod_equiv_reps {A B R S : Type*}
    {σ : A → A} {τ : B → B}
    (SA : @RepSystem A R σ) (SB : @RepSystem B S τ) :
    {f : A × B → ℝ //
      (∀ p, f (σ p.1, p.2) = f p) ∧ (∀ p, f (p.1, τ p.2) = f p)} ≃
      ((R × S) → ℝ) where
  toFun := fun f q => f.1 (prodRepEmbed SA SB q)
  invFun := fun g =>
    ⟨prodExtendRep SA SB g, prodExtendRep_fst_fixed SA SB g,
      prodExtendRep_snd_fixed SA SB g⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext p
    show f.1 (prodRepEmbed SA SB (prodRepOf SA SB p)) = f.1 p
    exact jointlyFixed_apply_prodRepEmbed_prodRepOf SA SB f.1 f.2.1 f.2.2 p
  right_inv := by
    intro g
    funext q
    show prodExtendRep SA SB g (prodRepEmbed SA SB q) = g q
    exact prodExtendRep_prodRepEmbed SA SB g q

/-- The product restriction map is bijective. -/
theorem fixedFunctions_prod_equiv_reps_bijective {A B R S : Type*}
    {σ : A → A} {τ : B → B}
    (SA : @RepSystem A R σ) (SB : @RepSystem B S τ) :
    Function.Bijective (fixedFunctions_prod_equiv_reps SA SB) :=
  (fixedFunctions_prod_equiv_reps SA SB).bijective

/-- The mirror involution is involutive in `Function`
form (the seat `MirrorTwentyOne` states it pointwise as
`involution_involutive`). -/
theorem mirrorInvolution_involutive :
    Function.Involutive involution :=
  fun i => involution_involutive i

/-- **The Mirror-21 rep system as an abstract instance.**
`MirrorTwentyOneAlgebra`'s `repOf`/`repEmbed` satisfy the
three abstract axioms (R1)–(R3) — they are, verbatim, that
module's own lemmas `repOf_repEmbed`, `repOf_involution`,
`repEmbed_repOf`, each proved there by `Fin 21` arithmetic.
No new `Fin` work was needed to discharge the instance. -/
def mirrorRepSystem :
    RepSystem (A := ManifoldIndex) (R := Fin 11) involution where
  repOf := repOf
  repEmbed := repEmbed
  repOf_repEmbed := repOf_repEmbed
  repOf_invol := repOf_involution
  repEmbed_repOf := repEmbed_repOf

/-- **Corollary (i), master form.** The mirror-fixed
functions on `Fin 21` are exactly the functions on the 11
representatives — `MirrorTwentyOneAlgebra.fixedEquivReps`
re-derived from the abstract master at the Mirror instance.
The original module is untouched; this is the same seat,
reached through U-3b. -/
def mirror_fixedEquivReps_master :
    {f : ManifoldIndex → ℝ // ∀ x, f (involution x) = f x} ≃
      (Fin 11 → ℝ) :=
  fixedFunctions_equiv_reps mirrorRepSystem

/-- **Corollary (i), the seat's own form.** The same equiv
with the fixed subtype stated via the pullback `thetaHat`,
exactly `MirrorTwentyOneAlgebra.fixedEquivReps`'s type:
the two fixedness predicates agree by
`thetaHat_fixed_iff`. -/
def mirror_fixedEquivReps_thetaHat :
    {f : ManifoldIndex → ℝ // thetaHat f = f} ≃ (Fin 11 → ℝ) :=
  (Equiv.subtypeEquivRight (fun f => thetaHat_fixed_iff f)).trans
    mirror_fixedEquivReps_master

/-- The master-derived Mirror equiv is bijective (the
master form of `fixedEquivReps_bijective`). -/
theorem mirror_fixedEquivReps_thetaHat_bijective :
    Function.Bijective mirror_fixedEquivReps_thetaHat :=
  mirror_fixedEquivReps_thetaHat.bijective

/-- **Corollary (ii), master form.** The jointly
mirror-fixed grid functions on `Fin 21 × Fin 21` are exactly
the functions on the 11 × 11 representative grid —
`MirrorTwentyOneOrthogonal.jointlyFixedEquivReps` re-derived
from the product clause at the Mirror instance squared.
The original module is untouched. -/
def joint_fixedEquivReps_master :
    {f : GridIndex → ℝ //
      (∀ p, f (involution p.1, p.2) = f p) ∧
        (∀ p, f (p.1, involution p.2) = f p)} ≃
      ((Fin 11 × Fin 11) → ℝ) :=
  fixedFunctions_prod_equiv_reps mirrorRepSystem mirrorRepSystem

/-- **Corollary (ii), the seat's own form.** The same equiv
with joint fixedness stated via the arm pullbacks
`thetaHat₁`/`thetaHat₂`, exactly
`MirrorTwentyOneOrthogonal.jointlyFixedEquivReps`'s type:
the predicates agree by `thetaHat₁_fixed_iff` and
`thetaHat₂_fixed_iff`. -/
def joint_fixedEquivReps_thetaHat :
    {f : GridIndex → ℝ // thetaHat₁ f = f ∧ thetaHat₂ f = f} ≃
      (Fin 11 × Fin 11 → ℝ) :=
  (Equiv.subtypeEquivRight (fun f =>
    and_congr (thetaHat₁_fixed_iff f) (thetaHat₂_fixed_iff f))).trans
    joint_fixedEquivReps_master

/-- The master-derived joint equiv is bijective (the master
form of `jointlyFixedEquivReps_bijective`). -/
theorem joint_fixedEquivReps_thetaHat_bijective :
    Function.Bijective joint_fixedEquivReps_thetaHat :=
  joint_fixedEquivReps_thetaHat.bijective

end ThetLogos
