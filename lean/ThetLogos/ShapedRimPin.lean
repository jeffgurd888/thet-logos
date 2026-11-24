import Mathlib.Tactic
import ThetLogos.BridgeLaplacian
import ThetLogos.GravityShadowPin

/-!
# ThetLogos.ShapedRimPin — the shaped rim: making the adjoint pairing exact by construction (T5)

Commissioned by Zero, 2026-11-23 23:38–23:40 EST. Zero's words,
verbatim: "when I see the adjointed energy trying to reflect evenly
off a flat surface it just can't be done what if the reflective
geometry of the mirror wasn't flat but constructed to reflect
metadata equally restricted or pumped." On BONES's scope offer he
ruled "please" (2026-11-23 23:40 EST). Scope of record:
`~/workspace/your_files/shaped-rim-adjoint-scope-2026-11-23.md`.

TIER: T5 design study. NO CLAIM. Dials 0/4 — Dial 2 (derived
gravity object) stays 0 under EVERY outcome of this line,
including total success. "Shaped rim" is the working label, from
Zero's mirror image; the module name `ShapedRimPin` is a working
name — final naming is his hand.

## The intuition, stated plainly

The Shadow line corrects the adjoint pairing algebraically: the
flat seat's books don't balance, so S-2 carries the correction
term on the theorem's face. Zero's seeing asks the geometric
question instead — don't correct the mirror's arithmetic, SHAPE
the mirror. Build the rim of the seat (its weights and/or its
boundary rule) so that the pairing balances exactly by
construction, the way a parabolic reflector's shape does what no
flat mirror can. His two words name the two routes a boundary
can be shaped:

- **RESTRICTED** — the rim pinned, Dirichlet-style: boundary
  values fixed by rule, so the outflow term is killed by the
  constraint.
- **PUMPED** — the rim driven: an active boundary supply that
  feeds exactly the outflow the correction demands, so the books
  balance by injection.

Either way the "metadata" — the boundary data a flat reflection
throws away — is carried by the rim's construction instead of by
a correction term.

## The ground (proved ground, cited — not conjecture, not re-proved)

- S-2 of the Shadow line (`GravityShadowPin`, banked) carries the
  adjoint pairing in its only true form at this seat:
  `gravShadowPairing_corrected` — for every weighting `φ` and
  every edge field `X`,
  `∑ i, ∑ j, dropVec φ i j * X i j
    = (∑ i, φ i * diverge X i) − ∑ i, φ i * gravShadowOutflow X i`,
  under this tree's conventions (`diverge` the inflow transpose
  sum, the edge pairing the full ordered double sum). The naive
  identity without the correction is FALSE here and is never
  stated in this line. For antisymmetric `X` — the seat's
  currents — the pairing reads `2 * ⟨φ, diverge X⟩`
  (`gravShadowPairing_antisymm`, cited).
- S-4 of the Shadow line (banked) carries the kernel of the
  drop: `gravShadowField φ = 0` iff `φ` is constant
  (`gravShadowField_eq_zero_iff`, cited where this line needs
  it).
- The Vortex line (`VortexAdjointPin`, banked) registered the
  same full ordered pairing for its own outline as
  `vortexPairing`; this line registers its own seat instance
  below and cites the Shadow line's theorems, re-proving none of
  them.

## The seat is all rim

The seat is `Fin 3` with the Shadow line's objects. A fact this
line keeps on its face: at `Fin 3` EVERY vertex is a rim vertex —
the triangle has no interior vertex for a rim to protect. The
pinned rule below is therefore stated for an arbitrary rim set
`R`, and the restricted route (R-1) decides it for every `R` at
once, so no "pin only part of the rim" escape is left unpriced.

## The question (failable, stated at the Fin 3 seat)

Do rim weights and/or a boundary rule exist at the `Fin 3` seat
under which

  ⟨dropVec φ, X⟩ = ⟨φ, diverge X⟩

holds **exactly**, with no correction term —

- **(Q-all)** for all potentials φ and all edge fields X; and,
  separately,
- **(Q-anti)** for all potentials φ and all antisymmetric edge
  fields X?

Existence is not assumed. A proved NO is a full-rank outcome of
this line, not a failure of it. The two questions are registered
below as `shapedRimExactAll` and `shapedRimExactAnti`, with the
rim weight `ρ` weighting the divergence side's potential pairing
(`shapedRimInner`); the flat read is `ρ ≡ 1`.

## The line ahead (scope brick map; this brick is R-0 only)

- R-0 — Registration (this brick): the rim made an object —
  the seat pairing, the rim-weighted inner pairing, the two
  exactness questions under frozen names, the pinned rule, and
  the pumped rim's supply term. No theorems claimed; 0 strict
  by design.
- R-1 — The restricted route: the pinned rim. The pairing under
  the restriction is proved exact exactly where it can be, and
  the degeneracy check is a theorem, not a remark: if the
  pinning only works by forcing the field to vanish, that is
  K-RIM-TRIVIAL's seat, and it is named there.
- R-2 — The pumped route: the driven rim. The pairing is proved
  exact under the pump — and the pump is then measured against
  S-2's correction term itself, on the record: if the supply is
  the correction re-injected, the "shaping" is bookkeeping and
  the brick says so.
- R-3 — The verdict / honesty brick: the exact statement of
  what shaping the rim can and cannot buy at `Fin 3` — the
  existence result, the triviality result, or the non-existence
  result — with the universality fence restated: whatever holds
  here holds for every potential, so it shapes a mirror, never
  an object.

## Kills pre-registered and fences

- **K-RIM-NONE** — pre-registered: no rim weighting or boundary
  rule on the `Fin 3` seat makes the pairing exact for all
  fields; the shaped mirror does not exist at this seat. If it
  fires, it fires as a theorem and is reported at full rank,
  same volume as a landing.
- **K-RIM-TRIVIAL** — pre-registered: a rule exists but only
  degenerately — e.g. it forces φ or X to vanish — so the even
  reflection is bought by emptying the seat. A mirror that
  reflects evenly because nothing is left to reflect is not the
  mirror Zero asked for; if this is the outcome, it is named as
  such on the record.
- **K-SHADOW-OBJECT** (fence, inherited): no gravity object, no
  G, no continuum field, no Einstein slot is constructed or fed
  by this line. Dial 2 stays 0.
- FRONTIER, never priced: the continuum shaped boundary
  (Dial 3), any derivation of G, any coupling of the rim to
  inertia or time.
-/

namespace ThetLogos

/-- The seat pairing of this line: the full ordered double sum
of the field-shadow `dropVec φ` against the edge field `X` —
this tree's one pairing convention, the left side of the
adjoint identity whose exactness is this line's question. (The
Shadow line states it inline in S-2's theorems; the Vortex line
registered its own instance as `vortexPairing`; this is the
shaped-rim line's registered instance, at its seat `Fin 3`.) -/
def shapedRimPairing (φ : Fin 3 → ℝ) (X : Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, dropVec φ i j * X i j

/-- The rim-weighted potential pairing: the divergence side of
the adjoint identity read through rim weights `ρ` — vertex `i`'s
contribution `φ i * ψ i` is weighted by the rim's weight `ρ i`
at that vertex. The flat read is `ρ ≡ 1`:
`shapedRimInner 1 φ ψ = ∑ i, φ i * ψ i`, the pairing S-2's
corrected identity carries. A "shaped rim" in the weighting
route is exactly a choice of `ρ` — the mirror's profile, one
weight per rim vertex. -/
def shapedRimInner (ρ φ ψ : Fin 3 → ℝ) : ℝ :=
  ∑ i, ρ i * φ i * ψ i

/-- **Q-all, frozen.** The exactness question for all fields:
rim weights `ρ` under which the seat pairing equals the
rim-weighted divergence pairing for EVERY potential `φ` and
EVERY edge field `X` — the adjoint identity exact by
construction, no correction term, no restriction on the fields.
Registered as a `Prop`; nothing about it is claimed in this
brick. -/
def shapedRimExactAll (ρ : Fin 3 → ℝ) : Prop :=
  ∀ φ X, shapedRimPairing φ X = shapedRimInner ρ φ (diverge X)

/-- **Q-anti, frozen.** The exactness question for the seat's
currents: rim weights `ρ` under which the seat pairing equals
the rim-weighted divergence pairing for every potential `φ`
and every ANTISYMMETRIC edge field `X` (`X j i = - X i j` —
the hypothesis form of the Shadow line's S-2/S-3). Weaker than
Q-all by exactly the antisymmetry restriction, and registered
separately because the flat seat's own factor of 2
(`gravShadowPairing_antisymm`) lives here. -/
def shapedRimExactAnti (ρ : Fin 3 → ℝ) : Prop :=
  ∀ φ X, (∀ i j, X j i = - X i j) →
    shapedRimPairing φ X = shapedRimInner ρ φ (diverge X)

/-- **The restricted route, as a rule.** The pinned rim: a
boundary rule fixing a potential's values on a rim set `R` to a
boundary datum `φ₀` — Dirichlet-style, in the scope's words
"boundary values fixed by rule, so the outflow term is killed
by the constraint". Registered for an arbitrary rim set `R`:
at this seat every vertex is a rim vertex (the seat is all
rim), and R-1 decides the rule for every `R` at once. The rule
constrains the potential only; what it does to the pairing is
R-1's charge, not this brick's. -/
def shapedRimPinned (R : Finset (Fin 3)) (φ₀ φ : Fin 3 → ℝ) : Prop :=
  ∀ i ∈ R, φ i = φ₀ i

/-- **The pumped route's supply term.** The driven rim's
injection at vertex `i`: exactly the outflow correction's
`i`-th term, `φ i * gravShadowOutflow X i` — the leak S-2's
corrected pairing subtracts, fed back in at the vertex it
leaked from (`gravShadowOutflow` is the Shadow line's S-2
definition, cited). Registered here as the pump's definition;
whether a supply so defined is a shaping of the rim or the
correction term wearing a supply's clothes is R-2's charge,
decided there on the record — the definition's face already
shows the supply is computed from the very pair `(φ, X)` it
corrects, not from the seat alone. -/
def shapedRimPump (φ : Fin 3 → ℝ) (X : Fin 3 → Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  φ i * gravShadowOutflow X i

/-! ## R-1 — the restricted route (this brick)

THE PINNED RIM, DECIDED. The restricted route asks the
constraint to kill the outflow term: pin the potential's rim
values by rule, and hope the pairing balances. This brick
decides the route completely, in three statements of increasing
reach:

1. **One potential, all fields** (`shapedRimExact_single_iff`).
   A single potential's pairing against `diverge` is exact for
   every edge field iff the potential is ZERO. The diagonal
   exhibit decides it: against the field carrying a single unit
   on the diagonal edge `k → k`, the pairing reads the drop on
   that edge — which is `φ k − φ k = 0` — while the divergence
   side reads `φ k` itself. Exactness forces `φ k = 0`, at
   every `k`. No hypothesis on the seat's weights is used; this
   is the pairing's own arithmetic.

2. **The pinned rule, every rim set at once**
   (`shapedRimPinned_exact_iff`). The pinned family — all
   potentials agreeing with a datum `φ₀` on a rim set `R` — is
   exact for all fields iff `R` is the whole seat AND `φ₀ = 0`.
   The forward direction is (1) spent twice: the datum itself
   is admitted, so it must vanish; and at any unpinned vertex
   the family admits a unit bump, which must also vanish — it
   doesn't. So the only exact pinned mirror is the one whose
   admitted family is the single zero potential. At `Fin 3`
   there is no proper-rim escape either: the iff is stated for
   every `R`, and every proper `R` fails by the same bump.

3. **The antisymmetric restriction buys a constant, not a
   field** (`shapedRimPinnedAnti_exact_iff`,
   `shapedRimPinnedAnti_field_vanishes`). Weaken the demand to
   the seat's currents (Q-anti's fields): a single potential is
   exact against every antisymmetric field iff it is CONSTANT —
   the swap exhibits decide it, since S-2's antisymmetric read
   doubles the divergence side and exactness then forces
   `φ j = φ i` on each swapped pair. But a constant potential's
   field-shadow is zero (S-4's kernel, cited): even here, the
   pairing is exact only where the mirror casts no field.

**K-RIM-TRIVIAL — FIRED on the restricted route, at full
rank.** The scope pre-registered it: "a rule exists but only
degenerately — it forces φ or X to vanish — so the even
reflection is bought by emptying the seat." That is exactly
the outcome above, as theorem `shapedRimPinned_trivial`: under
the pinned rule, exactness for all fields forces the datum to
be zero and the field-shadow to vanish identically. The
restricted mirror reflects evenly because nothing is left to
reflect. This is a designed result of the line, reported at
the same volume as a landing. -/

section RestrictedRoute

/-- The diagonal unit field at `k`: a single unit on the
diagonal edge `k → k`, zero elsewhere. The restricted route's
deciding exhibit: the pairing reads the drop on the diagonal
edge (zero, for every potential), while the divergence side
reads the potential's value at `k` itself. -/
def shapedRimDiag (k : Fin 3) : Fin 3 → Fin 3 → ℝ :=
  fun i j => if i = k ∧ j = k then 1 else 0

/-- The antisymmetric unit on the ordered pair `(i, j)`: one
unit flowing `i → j`, minus one on the reverse edge, zero
elsewhere. The seat's smallest current with a chosen direction
— the exhibit that decides the antisymmetric restricted form. -/
def shapedRimSwap (i j : Fin 3) : Fin 3 → Fin 3 → ℝ :=
  fun a b => if a = i ∧ b = j then 1 else if a = j ∧ b = i then -1 else 0

/-- The swap exhibit is one of the seat's currents:
antisymmetric, whenever its two vertices differ. -/
theorem shapedRimSwap_antisymm {i j : Fin 3} (h : i ≠ j) (a b : Fin 3) :
    shapedRimSwap i j b a = - shapedRimSwap i j a b := by
  unfold shapedRimSwap
  by_cases h1 : a = i ∧ b = j
  · have hc1 : ¬ (b = i ∧ a = j) := fun hh => h (hh.1.symm.trans h1.2)
    have hc2 : b = j ∧ a = i := ⟨h1.2, h1.1⟩
    rw [if_pos h1, if_neg hc1, if_pos hc2]
  · by_cases h2 : a = j ∧ b = i
    · have hc1 : b = i ∧ a = j := ⟨h2.2, h2.1⟩
      rw [if_neg h1, if_pos h2, if_pos hc1]
      norm_num
    · have hc1 : ¬ (b = i ∧ a = j) := fun hh => h2 ⟨hh.2, hh.1⟩
      have hc2 : ¬ (b = j ∧ a = i) := fun hh => h1 ⟨hh.2, hh.1⟩
      rw [if_neg h1, if_neg h2, if_neg hc1, if_neg hc2]
      norm_num

/-- The swap exhibit's divergence, vertex by vertex: it
gathers `1` at its head `j`, `-1` at its tail `i`, and `0`
everywhere else — a unit of source contrast between the two
vertices. -/
theorem shapedRimSwap_diverge {i j : Fin 3} (h : i ≠ j) (a : Fin 3) :
    diverge (shapedRimSwap i j) a
      = if a = j then 1 else if a = i then -1 else 0 := by
  rw [diverge_apply]
  by_cases haj : a = j
  · rw [haj, if_pos rfl]
    have hsum : (∑ b, shapedRimSwap i j b j) = shapedRimSwap i j i j := by
      apply Finset.sum_eq_single i
      · intro b _ hb
        unfold shapedRimSwap
        rw [if_neg (fun hh => hb hh.1),
          if_neg (fun hh => h hh.2.symm)]
      · simp
    rw [hsum]
    show shapedRimSwap i j i j = 1
    unfold shapedRimSwap
    rw [if_pos ⟨rfl, rfl⟩]
  · by_cases hai : a = i
    · rw [hai, if_neg (fun hh => haj (hai.trans hh)), if_pos rfl]
      have hsum : (∑ b, shapedRimSwap i j b i) = shapedRimSwap i j j i := by
        apply Finset.sum_eq_single j
        · intro b _ hb
          unfold shapedRimSwap
          rw [if_neg (fun hh => h hh.2),
            if_neg (fun hh => hb hh.1)]
        · simp
      rw [hsum]
      show shapedRimSwap i j j i = -1
      unfold shapedRimSwap
      rw [if_neg (fun hh => h hh.1.symm), if_pos ⟨rfl, rfl⟩]
    · rw [if_neg haj, if_neg hai]
      apply Finset.sum_eq_zero
      intro b _
      unfold shapedRimSwap
      rw [if_neg (fun hh => haj hh.2), if_neg (fun hh => hai hh.2)]

/-- **One potential, all fields.** A single potential's
pairing against `diverge` is exact for EVERY edge field iff
the potential is zero. The diagonal exhibit
(`shapedRimDiag k`) decides it: the pairing against it reads
the drop on the diagonal edge `k → k`, which is `φ k − φ k =
0` for every `φ`, while the divergence side reads `φ k`
itself — exactness forces `φ k = 0` at every vertex. -/
theorem shapedRimExact_single_iff (φ : Fin 3 → ℝ) :
    (∀ X, shapedRimPairing φ X = ∑ i, φ i * diverge X i) ↔ φ = 0 := by
  constructor
  · intro h
    funext k
    have hdiv : ∀ m, diverge (shapedRimDiag k) m = if m = k then 1 else 0 := by
      intro m
      rw [diverge_apply]
      by_cases hm : m = k
      · rw [hm, if_pos rfl]
        have hsum : (∑ j, shapedRimDiag k j k) = shapedRimDiag k k k := by
          apply Finset.sum_eq_single k
          · intro b _ hb
            unfold shapedRimDiag
            rw [if_neg (fun hh => hb hh.1)]
          · simp
        rw [hsum]
        show shapedRimDiag k k k = 1
        unfold shapedRimDiag
        rw [if_pos ⟨rfl, rfl⟩]
      · rw [if_neg hm]
        apply Finset.sum_eq_zero
        intro j _
        unfold shapedRimDiag
        rw [if_neg (fun hh => hm hh.2)]
    have hRHS : (∑ i, φ i * diverge (shapedRimDiag k) i) = φ k := by
      have hsum : (∑ i, φ i * diverge (shapedRimDiag k) i)
          = φ k * diverge (shapedRimDiag k) k := by
        apply Finset.sum_eq_single k
        · intro b _ hb
          rw [hdiv b, if_neg hb, mul_zero]
        · simp
      rw [hsum, hdiv k, if_pos rfl, mul_one]
    have hLHS : shapedRimPairing φ (shapedRimDiag k) = 0 := by
      unfold shapedRimPairing
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      by_cases hik : i = k
      · by_cases hjk : j = k
        · rw [hik, hjk, dropVec_apply]
          simp
        · have hdiag : shapedRimDiag k k j = 0 := by
            unfold shapedRimDiag
            exact if_neg (fun hh => hjk hh.2)
          rw [hik, hdiag, mul_zero]
      · have hdiag : shapedRimDiag k i j = 0 := by
          unfold shapedRimDiag
          exact if_neg (fun hh => hik hh.1)
        rw [hdiag, mul_zero]
    have := h (shapedRimDiag k)
    rw [hLHS, hRHS] at this
    exact this.symm
  · intro h X
    rw [h]
    simp [shapedRimPairing, dropVec_apply]

/-- **The pinned rule, decided for every rim set at once.**
The pinned family — every potential agreeing with the datum
`φ₀` on the rim set `R` — is exact for all fields iff `R` is
the whole seat AND the datum is zero: the only exact pinned
mirror admits the single zero potential and nothing else. -/
theorem shapedRimPinned_exact_iff (R : Finset (Fin 3)) (φ₀ : Fin 3 → ℝ) :
    (∀ φ, shapedRimPinned R φ₀ φ → ∀ X,
      shapedRimPairing φ X = ∑ i, φ i * diverge X i)
      ↔ R = Finset.univ ∧ φ₀ = 0 := by
  constructor
  · intro H
    have hφ₀ : φ₀ = 0 :=
      (shapedRimExact_single_iff φ₀).mp (H φ₀ (fun i _ => rfl))
    have hR : R = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro k
      by_contra hk
      have hadm : shapedRimPinned R φ₀ (Function.update 0 k 1) := by
        intro i hi
        have hik : i ≠ k := fun hh => hk (hh ▸ hi)
        rw [Function.update_of_ne hik]
        simp [hφ₀]
      have hzero := (shapedRimExact_single_iff _).mp (H _ hadm)
      have hk1 : Function.update (0 : Fin 3 → ℝ) k 1 k = 1 :=
        Function.update_self k 1 0
      rw [hzero] at hk1
      simp at hk1
    exact ⟨hR, hφ₀⟩
  · rintro ⟨hR, hφ₀⟩ φ hφ X
    have hφeq : φ = 0 := by
      funext i
      have hi : φ i = φ₀ i := hφ i (hR.symm ▸ Finset.mem_univ i)
      rw [hi, hφ₀]
    exact (shapedRimExact_single_iff φ).mpr hφeq X

/-- **The antisymmetric restricted form.** Against the seat's
currents only, a single potential is exact iff it is CONSTANT:
the swap exhibits double-read the divergence side (S-2's
antisymmetric factor of 2, cited), and exactness forces the
potential to agree across each swapped pair. A wider class
than the zero potential of the all-fields form — and still,
by the next theorem, a class whose field vanishes. -/
theorem shapedRimPinnedAnti_exact_iff (φ₀ : Fin 3 → ℝ) :
    (∀ X, (∀ i j, X j i = - X i j) →
      shapedRimPairing φ₀ X = ∑ i, φ₀ i * diverge X i)
      ↔ ∃ c : ℝ, ∀ i, φ₀ i = c := by
  constructor
  · intro h
    have hval1 : ∑ a, φ₀ a * diverge (shapedRimSwap 0 1) a
        = φ₀ 1 - φ₀ 0 := by
      rw [Fin.sum_univ_three,
        shapedRimSwap_diverge (by decide : (0 : Fin 3) ≠ 1) 0,
        shapedRimSwap_diverge (by decide : (0 : Fin 3) ≠ 1) 1,
        shapedRimSwap_diverge (by decide : (0 : Fin 3) ≠ 1) 2,
        if_neg (by decide : ¬ ((0 : Fin 3) = 1)), if_pos (rfl : (0 : Fin 3) = 0),
        if_pos (rfl : (1 : Fin 3) = 1),
        if_neg (by decide : ¬ ((2 : Fin 3) = 1)),
        if_neg (by decide : ¬ ((2 : Fin 3) = 0))]
      ring
    have hval2 : ∑ a, φ₀ a * diverge (shapedRimSwap 0 2) a
        = φ₀ 2 - φ₀ 0 := by
      rw [Fin.sum_univ_three,
        shapedRimSwap_diverge (by decide : (0 : Fin 3) ≠ 2) 0,
        shapedRimSwap_diverge (by decide : (0 : Fin 3) ≠ 2) 1,
        shapedRimSwap_diverge (by decide : (0 : Fin 3) ≠ 2) 2,
        if_neg (by decide : ¬ ((0 : Fin 3) = 2)), if_pos (rfl : (0 : Fin 3) = 0),
        if_neg (by decide : ¬ ((1 : Fin 3) = 2)),
        if_neg (by decide : ¬ ((1 : Fin 3) = 0)),
        if_pos (rfl : (2 : Fin 3) = 2)]
      ring
    have e1 : φ₀ 1 = φ₀ 0 := by
      have hanti : ∀ a b, shapedRimSwap 0 1 b a
          = - shapedRimSwap 0 1 a b :=
        shapedRimSwap_antisymm (by decide)
      have hX := h (shapedRimSwap 0 1) hanti
      have hpr : shapedRimPairing φ₀ (shapedRimSwap 0 1)
          = 2 * (φ₀ 1 - φ₀ 0) := by
        have hp := gravShadowPairing_antisymm φ₀ (shapedRimSwap 0 1) hanti
        rw [hval1] at hp
        exact hp
      rw [hval1] at hX
      linarith
    have e2 : φ₀ 2 = φ₀ 0 := by
      have hanti : ∀ a b, shapedRimSwap 0 2 b a
          = - shapedRimSwap 0 2 a b :=
        shapedRimSwap_antisymm (by decide)
      have hX := h (shapedRimSwap 0 2) hanti
      have hpr : shapedRimPairing φ₀ (shapedRimSwap 0 2)
          = 2 * (φ₀ 2 - φ₀ 0) := by
        have hp := gravShadowPairing_antisymm φ₀ (shapedRimSwap 0 2) hanti
        rw [hval2] at hp
        exact hp
      rw [hval2] at hX
      linarith
    refine ⟨φ₀ 0, fun i => ?_⟩
    fin_cases i
    · rfl
    · exact e1
    · exact e2
  · rintro ⟨c, hc⟩ X hX
    have hLHS : shapedRimPairing φ₀ X = 0 := by
      unfold shapedRimPairing
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      rw [dropVec_apply, hc i, hc j]
      simp
    have htot : (∑ i, diverge X i) = 0 := by
      have h1 : (∑ i, diverge X i) = ∑ i, ∑ j, X j i :=
        Finset.sum_congr rfl fun i _ => diverge_apply X i
      have h2 : (∑ i, ∑ j, X j i) = ∑ i, ∑ j, X i j := Finset.sum_comm
      have h3 : (∑ i, ∑ j, X i j) = -∑ i, ∑ j, X j i := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        exact hX j i
      linarith
    have hRHS : (∑ i, φ₀ i * diverge X i) = 0 := by
      have hstep : (∑ i, φ₀ i * diverge X i)
          = c * ∑ i, diverge X i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hc i]
      rw [hstep, htot, mul_zero]
    rw [hLHS, hRHS]

/-- **The antisymmetric restriction still casts no field.**
If a potential is exact against every antisymmetric field,
its field-shadow vanishes identically — S-4's kernel of the
drop (`gravShadowField_eq_zero_iff`), cited at the constant
class the previous theorem forces. -/
theorem shapedRimPinnedAnti_field_vanishes (φ₀ : Fin 3 → ℝ)
    (h : ∀ X, (∀ i j, X j i = - X i j) →
      shapedRimPairing φ₀ X = ∑ i, φ₀ i * diverge X i) :
    gravShadowField φ₀ = 0 :=
  (gravShadowField_eq_zero_iff φ₀).mpr
    ((shapedRimPinnedAnti_exact_iff φ₀).mp h)

/-- **K-RIM-TRIVIAL — fired on the restricted route.** Under
the pinned rule, exactness of the pairing for all admitted
potentials and all fields forces the boundary datum to be
zero and the field-shadow to vanish identically: the
restricted mirror reflects evenly because nothing is left to
reflect. The degeneracy the scope's degeneracy check charged
this brick to record — recorded as a theorem, on the face. -/
theorem shapedRimPinned_trivial (R : Finset (Fin 3)) (φ₀ : Fin 3 → ℝ)
    (h : ∀ φ, shapedRimPinned R φ₀ φ → ∀ X,
      shapedRimPairing φ X = ∑ i, φ i * diverge X i) :
    φ₀ = 0 ∧ gravShadowField φ₀ = 0 := by
  have hφ₀ : φ₀ = 0 := ((shapedRimPinned_exact_iff R φ₀).mp h).2
  refine ⟨hφ₀, ?_⟩
  rw [hφ₀]
  funext i j
  show dropVec (0 : Fin 3 → ℝ) i j = 0
  rw [dropVec_apply]
  simp

end RestrictedRoute

/-! ## R-2 — the pumped route (this brick)

THE DRIVEN RIM, MEASURED. The pumped route does not
constrain anything: it feeds the rim a supply, defined in R-0
from the outflow correction itself, and asks whether the
books then balance. They do — `shapedRimPumpedPairing_exact`
is a landing, and this brick states it as one: the pumped
pairing (the flat read plus the rim's total injection) equals
the divergence pairing exactly, for every potential and every
edge field, by S-2's corrected identity cited.

Then the brick measures what was bought, as the scope
charged. Three theorems, one verdict:

- The pump's total injection IS S-2's correction term,
  verbatim (`shapedRimPump_total`): the sum of the supply
  over the seat is `∑ i, φ i * gravShadowOutflow X i` — the
  very term the corrected pairing subtracts.
- The pumped read differs from the flat read by exactly that
  term and nothing else (`shapedRimPumpedPairing_sub`).
- The supply is not a datum of the seat
  (`shapedRimPump_not_seat_datum`): one and the same edge
  field, two potentials, two different supplies. A boundary
  rule is a property of the rim; this supply is a function of
  the measured pair `(φ, X)` — computed from the leak it is
  meant to pre-empt.

So the pumped mirror "reflects evenly" the way a ledger
balances when the discrepancy is posted back as an entry:
exactly, and by construction — the construction being the
correction term itself, re-injected. The scope priced this
outcome in advance ("the pump shown to merely restate the
correction — in which case the 'shaping' is bookkeeping, and
the brick says so"). The brick says so: **the pumped route is
bookkeeping, not geometry.** No rim was shaped; the arithmetic
was fed its own correction. R-3 assembles this with R-1's
verdict into the line's closing statement. -/

section PumpedRoute

/-- The pumped pairing: the flat seat pairing plus the rim's
total injection — what the pairing reads when the rim is
driven by the supply of R-0. -/
def shapedRimPumpedPairing (φ : Fin 3 → ℝ) (X : Fin 3 → Fin 3 → ℝ) : ℝ :=
  shapedRimPairing φ X + ∑ i, shapedRimPump φ X i

/-- **The pump's total is the correction term, verbatim.**
The sum of the pumped rim's supply over the seat is exactly
the outflow correction `∑ i, φ i * gravShadowOutflow X i`
that S-2's corrected pairing subtracts — term for term, by
the supply's definition. -/
theorem shapedRimPump_total (φ : Fin 3 → ℝ) (X : Fin 3 → Fin 3 → ℝ) :
    (∑ i, shapedRimPump φ X i) = ∑ i, φ i * gravShadowOutflow X i :=
  Finset.sum_congr rfl fun i _ => rfl

/-- **Exactness under the pump — the landing.** The pumped
pairing equals the divergence pairing exactly, for every
potential and every edge field: the driven rim balances the
books. Proved from S-2's corrected identity
(`gravShadowPairing_corrected`, cited): the flat read is the
divergence pairing minus the correction, and the pump posts
the correction back. -/
theorem shapedRimPumpedPairing_exact (φ : Fin 3 → ℝ) (X : Fin 3 → Fin 3 → ℝ) :
    shapedRimPumpedPairing φ X = ∑ i, φ i * diverge X i := by
  have hpair : shapedRimPairing φ X
      = (∑ i, φ i * diverge X i) - ∑ i, φ i * gravShadowOutflow X i :=
    gravShadowPairing_corrected φ X
  unfold shapedRimPumpedPairing
  rw [hpair, shapedRimPump_total]
  ring

/-- **The pumped read differs from the flat read by the
correction alone.** Nothing else is added: subtract the flat
pairing from the pumped pairing and what remains is S-2's
correction term, in full. The pump contributes no geometry,
no weight, no rule — only the term it was defined from. -/
theorem shapedRimPumpedPairing_sub (φ : Fin 3 → ℝ) (X : Fin 3 → Fin 3 → ℝ) :
    shapedRimPumpedPairing φ X - shapedRimPairing φ X
      = ∑ i, φ i * gravShadowOutflow X i := by
  unfold shapedRimPumpedPairing
  rw [shapedRimPump_total]
  ring

/-- **The supply is not a datum of the seat.** There is one
edge field whose pumped supply differs between two
potentials: the supply at a vertex is computed from the
potential being measured, not fixed by the rim. A boundary
rule constrains the seat in advance; this supply is read off
the very pair it corrects — which is what makes the pumped
route bookkeeping rather than shaping. -/
theorem shapedRimPump_not_seat_datum :
    ∃ (X : Fin 3 → Fin 3 → ℝ) (φ ψ : Fin 3 → ℝ),
      shapedRimPump φ X ≠ shapedRimPump ψ X := by
  refine ⟨shapedRimSwap 0 1, fun _ => 1, fun _ => 0, fun h => ?_⟩
  have hout : gravShadowOutflow (shapedRimSwap 0 1) 0 = 1 := by
    show (∑ j, shapedRimSwap 0 1 0 j) = 1
    rw [Fin.sum_univ_three]
    simp [shapedRimSwap]
  have h0 := congrFun h 0
  simp only [shapedRimPump, hout] at h0
  norm_num at h0

end PumpedRoute

/-! ## R-3 — the verdict brick (this brick)

THE CLOSING STATEMENT OF THE LINE. R-0 froze the question,
R-1 decided the restricted route, R-2 decided the pumped
route. This brick decides the remaining route — rim weights —
and assembles everything into the line's verdict.

**K-RIM-NONE — FIRED on rim weightings, at full rank.**
`shapedRimExistsClaim` registers the weighting form of the
line's existence question: some rim weight `ρ` makes the
pairing exact for all potentials and all edge fields
(Q-all). It is FALSE, by proof (`shapedRimExistsClaim_false`).
The diagonal exhibits force every rim weight to zero — with
the constant potential `1`, exactness against the diagonal
field at `k` reads `ρ k = 0` — and with `ρ = 0` the weighted
side is identically zero while an off-diagonal field's
pairing is not. No rim weighting makes the flat pairing
exact. The shaped mirror, as a weighting of this seat, does
not exist.

**Q-anti's unique weight is a number, not a shape.**
Weaken the demand to the seat's currents and exactly one rim
weight survives (`shapedRimWeightAnti_unique`): the constant
`ρ ≡ 2` — S-2's antisymmetric factor, the same at every rim
vertex. It works (the ⇐ direction is S-2's antisymmetric
identity restated through the weight) and it is unique (the
swap exhibits read `ρ j` off at each vertex and find `2`).
But a weight that does not vary with the rim is not a profile
of the rim: nothing about the seat's shape is in it. The one
exact "shaping" of the currents' pairing is the factor the
flat seat already carried.

**The verdict** (`shapedRimVerdict`) assembles the line:
no rim weighting is exact for all fields; the currents'
unique exact weight is the constant `2`; the pinned rule is
exact only at the zero datum on the whole seat (R-1, where
K-RIM-TRIVIAL fired); and the pumped supply is the correction
term itself (R-2, where the route was measured as
bookkeeping). Read together: **at `Fin 3`, shaping the rim
buys the exact pairing only by emptying the seat, by
flattening the "shape" into a constant the flat seat already
knew, or by posting the correction back as an entry.** No
shaping with geometric content exists at this seat — and the
seat itself says why: at `Fin 3` every vertex is rim; there
is no interior for a shaped boundary to protect, no bulk for
the metadata to be carried into. The mirror Zero asked for —
a rim whose construction does what the correction term does,
with content of its own — is not there at the three-vertex
seat. That is a proved NO, reported at full rank as the
line's designed outcome, beside its two landings (the
antisymmetric weight `2`, the pumped identity) stated at
theirs.

The universality fence, restated as the scope charged:
everything in this line holds for every potential and is
stated at a finite seat — it shapes a mirror, never an
object. No gravity object was constructed, fed, or
identified; Dial 2 stays 0. The continuum shaped boundary
remains FRONTIER, unpriced. -/

section VerdictBrick

/-- The diagonal exhibit's divergence, as a citable fact
(R-1's deciding computation, extracted): the diagonal unit
field at `k` gathers `1` at `k` and `0` elsewhere. -/
theorem shapedRimDiag_diverge (k m : Fin 3) :
    diverge (shapedRimDiag k) m = if m = k then 1 else 0 := by
  rw [diverge_apply]
  by_cases hm : m = k
  · rw [hm, if_pos rfl]
    have hsum : (∑ j, shapedRimDiag k j k) = shapedRimDiag k k k := by
      apply Finset.sum_eq_single k
      · intro b _ hb
        unfold shapedRimDiag
        rw [if_neg (fun hh => hb hh.1)]
      · simp
    rw [hsum]
    show shapedRimDiag k k k = 1
    unfold shapedRimDiag
    rw [if_pos ⟨rfl, rfl⟩]
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro j _
    unfold shapedRimDiag
    rw [if_neg (fun hh => hm hh.2)]

/-- The pairing against a diagonal exhibit vanishes, for
every potential (R-1's deciding computation, extracted): the
pairing reads the drop on the diagonal edge, and the drop on
a diagonal edge is `φ k − φ k = 0`. -/
theorem shapedRimPairing_diag (φ : Fin 3 → ℝ) (k : Fin 3) :
    shapedRimPairing φ (shapedRimDiag k) = 0 := by
  unfold shapedRimPairing
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hik : i = k
  · by_cases hjk : j = k
    · rw [hik, hjk, dropVec_apply]
      simp
    · have hdiag : shapedRimDiag k k j = 0 := by
        unfold shapedRimDiag
        exact if_neg (fun hh => hjk hh.2)
      rw [hik, hdiag, mul_zero]
  · have hdiag : shapedRimDiag k i j = 0 := by
      unfold shapedRimDiag
      exact if_neg (fun hh => hik hh.1)
    rw [hdiag, mul_zero]

/-- **The weighting existence claim, registered exactly as
it dies.** The shaped mirror in its weighting form: some rim
weight `ρ` makes the seat pairing exact — rim-weighted
divergence side, no correction term — for every potential
and every edge field (Q-all, `shapedRimExactAll`). -/
def shapedRimExistsClaim : Prop :=
  ∃ ρ, shapedRimExactAll ρ

/-- **K-RIM-NONE — FIRED on rim weightings.** No rim weight
makes the pairing exact for all fields. The diagonal
exhibits force `ρ = 0` (against the constant potential `1`,
exactness at the diagonal field at `k` reads `ρ k` against a
pairing of `0`); and at `ρ = 0` the weighted side vanishes
identically while the swap exhibit's pairing against
`δ₁` is `2`. The shaped mirror does not exist at this seat
as a weighting — a proved NO, at full rank. -/
theorem shapedRimExistsClaim_false : ¬ shapedRimExistsClaim := by
  rintro ⟨ρ, hρ⟩
  have hρ0 : ρ = 0 := by
    funext k
    have hX := hρ (fun _ => 1) (shapedRimDiag k)
    rw [shapedRimPairing_diag] at hX
    have hinner : shapedRimInner ρ (fun _ => 1) (diverge (shapedRimDiag k))
        = ρ k := by
      have hsum : (∑ i, ρ i * (fun _ => (1 : ℝ)) i * diverge (shapedRimDiag k) i)
          = ρ k * (fun _ => (1 : ℝ)) k * diverge (shapedRimDiag k) k := by
        apply Finset.sum_eq_single k
        · intro b _ hb
          show ρ b * 1 * diverge (shapedRimDiag k) b = 0
          rw [shapedRimDiag_diverge, if_neg hb, mul_zero]
        · simp
      unfold shapedRimInner
      rw [hsum]
      show ρ k * 1 * diverge (shapedRimDiag k) k = ρ k
      rw [shapedRimDiag_diverge, if_pos rfl]
      simp
    rw [hinner] at hX
    exact hX.symm
  have hInner0 : ∀ (φ ψ : Fin 3 → ℝ), shapedRimInner 0 φ ψ = 0 := by
    intro φ ψ
    unfold shapedRimInner
    apply Finset.sum_eq_zero
    intro i _
    simp
  have hanti : ∀ a b, shapedRimSwap 0 1 b a = - shapedRimSwap 0 1 a b :=
    shapedRimSwap_antisymm (by decide)
  have hLHS : shapedRimPairing (fun i => if i = 1 then (1 : ℝ) else 0)
      (shapedRimSwap 0 1) = 2 := by
    have hpa := gravShadowPairing_antisymm
      (fun i => if i = 1 then (1 : ℝ) else 0) (shapedRimSwap 0 1) hanti
    have hsum : (∑ a, (fun i => if i = 1 then (1 : ℝ) else 0) a
        * diverge (shapedRimSwap 0 1) a) = 1 := by
      have hmain : (∑ a, (fun i => if i = 1 then (1 : ℝ) else 0) a
          * diverge (shapedRimSwap 0 1) a)
          = (fun i => if i = 1 then (1 : ℝ) else 0) 1
            * diverge (shapedRimSwap 0 1) 1 := by
        apply Finset.sum_eq_single 1
        · intro b _ hb
          show (if b = 1 then (1 : ℝ) else 0)
            * diverge (shapedRimSwap 0 1) b = 0
          rw [if_neg hb, zero_mul]
        · simp
      rw [hmain]
      show (1 : ℝ) * diverge (shapedRimSwap 0 1) 1 = 1
      rw [shapedRimSwap_diverge (by decide : (0 : Fin 3) ≠ 1) 1,
        if_pos rfl, mul_one]
    rw [hsum, mul_one] at hpa
    exact hpa
  have hX := hρ (fun i => if i = 1 then (1 : ℝ) else 0) (shapedRimSwap 0 1)
  rw [hρ0, hInner0, hLHS] at hX
  norm_num at hX

/-- **Q-anti's unique exact weight is the constant `2`.** A
rim weight makes the pairing exact for every potential and
every antisymmetric field iff it is `2` at every vertex: the
constant factor S-2's antisymmetric identity already
carries (`gravShadowPairing_antisymm`, cited for the ⇐
direction), read off vertex by vertex by the swap exhibits
for the ⇒ direction. The one exact "shaping" of the
currents' pairing does not vary with the rim — a number,
not a profile. -/
theorem shapedRimWeightAnti_unique (ρ : Fin 3 → ℝ) :
    shapedRimExactAnti ρ ↔ ρ = fun _ => 2 := by
  constructor
  · intro hρ
    have hne : ∀ j : Fin 3, j + 1 ≠ j := by decide
    funext j
    show ρ j = 2
    have hanti : ∀ a b, shapedRimSwap (j + 1) j b a
        = - shapedRimSwap (j + 1) j a b :=
      shapedRimSwap_antisymm (hne j)
    have hp : shapedRimPairing (fun a => if a = j then (1 : ℝ) else 0)
        (shapedRimSwap (j + 1) j) = 2 := by
      have hpa := gravShadowPairing_antisymm
        (fun a => if a = j then (1 : ℝ) else 0) (shapedRimSwap (j + 1) j)
        hanti
      have hsum : (∑ a, (fun a => if a = j then (1 : ℝ) else 0) a
          * diverge (shapedRimSwap (j + 1) j) a) = 1 := by
        have hmain : (∑ a, (fun a => if a = j then (1 : ℝ) else 0) a
            * diverge (shapedRimSwap (j + 1) j) a)
            = (fun a => if a = j then (1 : ℝ) else 0) j
              * diverge (shapedRimSwap (j + 1) j) j := by
          apply Finset.sum_eq_single j
          · intro b _ hb
            show (if b = j then (1 : ℝ) else 0)
              * diverge (shapedRimSwap (j + 1) j) b = 0
            rw [if_neg hb, zero_mul]
          · simp
        rw [hmain]
        show (if j = j then (1 : ℝ) else 0)
          * diverge (shapedRimSwap (j + 1) j) j = 1
        rw [if_pos rfl, shapedRimSwap_diverge (hne j) j, if_pos rfl, mul_one]
      rw [hsum, mul_one] at hpa
      exact hpa
    have hinner : shapedRimInner ρ (fun a => if a = j then (1 : ℝ) else 0)
        (diverge (shapedRimSwap (j + 1) j)) = ρ j := by
      have hsum : (∑ a, ρ a * (fun a => if a = j then (1 : ℝ) else 0) a
          * diverge (shapedRimSwap (j + 1) j) a)
          = ρ j * (fun a => if a = j then (1 : ℝ) else 0) j
            * diverge (shapedRimSwap (j + 1) j) j := by
        apply Finset.sum_eq_single j
        · intro b _ hb
          show ρ b * (if b = j then (1 : ℝ) else 0)
            * diverge (shapedRimSwap (j + 1) j) b = 0
          rw [if_neg hb]
          simp
        · simp
      unfold shapedRimInner
      rw [hsum]
      show ρ j * (if j = j then (1 : ℝ) else 0)
        * diverge (shapedRimSwap (j + 1) j) j = ρ j
      rw [if_pos rfl, shapedRimSwap_diverge (hne j) j, if_pos rfl]
      ring
    have hX := hρ (fun a => if a = j then (1 : ℝ) else 0)
      (shapedRimSwap (j + 1) j) hanti
    rw [hp, hinner] at hX
    exact hX.symm
  · intro hρ φ X hX
    rw [hρ]
    have hp := gravShadowPairing_antisymm φ X hX
    have hinner : shapedRimInner (fun _ => (2 : ℝ)) φ (diverge X)
        = 2 * ∑ i, φ i * diverge X i := by
      unfold shapedRimInner
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      show (2 : ℝ) * φ i * diverge X i = 2 * (φ i * diverge X i)
      ring
    exact hp.trans hinner.symm

/-- **The verdict of the line, assembled.** What shaping
the rim can and cannot buy at `Fin 3`, in one statement,
each conjunct a banked brick's theorem: (1) no rim weighting
makes the pairing exact for all fields (K-RIM-NONE, this
brick); (2) the currents' unique exact rim weight is the
constant `2` — S-2's factor, not a shape (this brick); (3)
the pinned rule is exact only at the zero datum on the
whole seat (R-1, where K-RIM-TRIVIAL fired); (4) the pumped
rim's supply is S-2's correction term itself (R-2, where the
route was measured as bookkeeping). Exactness at this seat
is bought only by emptying, by flattening, or by posting
the correction back — never by a shape with content of its
own. -/
theorem shapedRimVerdict :
    (¬ ∃ ρ, shapedRimExactAll ρ) ∧
    (∀ ρ, shapedRimExactAnti ρ → ρ = fun _ => 2) ∧
    (∀ (R : Finset (Fin 3)) (φ₀ : Fin 3 → ℝ),
      (∀ φ, shapedRimPinned R φ₀ φ → ∀ X,
        shapedRimPairing φ X = ∑ i, φ i * diverge X i) →
      R = Finset.univ ∧ φ₀ = 0) ∧
    (∀ (φ : Fin 3 → ℝ) (X : Fin 3 → Fin 3 → ℝ),
      (∑ i, shapedRimPump φ X i) = ∑ i, φ i * gravShadowOutflow X i) :=
  ⟨shapedRimExistsClaim_false,
   fun ρ hρ => (shapedRimWeightAnti_unique ρ).mp hρ,
   fun R φ₀ h => (shapedRimPinned_exact_iff R φ₀).mp h,
   fun φ X => shapedRimPump_total φ X⟩

end VerdictBrick

end ThetLogos
