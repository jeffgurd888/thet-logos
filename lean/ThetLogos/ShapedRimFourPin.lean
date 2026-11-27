import Mathlib.Tactic
import ThetLogos.BridgeLaplacian
import ThetLogos.GravityShadowPin
import ThetLogos.ShapedRimPin
import ThetLogos.VortexAdjointPin

/-!
# ThetLogos.ShapedRimFourPin — the shaped rim at a seat with an interior (T5)

The Fin 4+ continuation of the shaped-rim line. Zero's decision
of 2026-11-24 09:53 EST ("Scope it at Fin 4 or higher"),
approved 2026-11-24 10:00 EST. Scope of record:
`~/workspace/your_files/shaped-rim-fin4-scope-DRAFT-2026-11-24.md`.

TIER: T5 design study. NO CLAIM. Dials 0/4 — Dial 2 (derived
gravity object) stays 0 under EVERY outcome of this line,
including total success. `dropVec` is not G; the gravitational
constant appears nowhere in this line; no gravity object is
constructed, fed, or identified. "Shaped rim" remains the
working label from Zero's mirror image; final module naming is
his hand.

## The Fin 3 verdict, preserved (cited — never re-proved, never re-graded)

The Fin 3 line is COMPLETE and its verdict is banked
(`ShapedRimPin`, hb `9847cef`, 26 decls / 16 strict; in the
census as of the T11 integration, 2026-11-24): at `Fin 3`,

- **K-RIM-NONE fired** — no rim weighting makes the pairing
  exact for all fields (diagonal exhibits force ρ = 0; at
  ρ = 0 the swap exhibit's pairing against δ₁ is 2 ≠ 0);
- **K-RIM-TRIVIAL fired** — the pinned rule is exact only at
  R = univ ∧ φ₀ = 0, with the field-shadow identically zero,
  and the pumped route's total injection IS S-2's correction
  term (bookkeeping, not geometry);
- the currents' unique exact weight is the constant ρ ≡ 2 —
  the flat seat's own factor, not a profile of the rim.

The reason, stated on the verdict's face: **at `Fin 3` every
vertex is rim; there is no interior for a shaped boundary to
protect.** That verdict stands at `Fin 3` exactly as banked.
Nothing in this module restates, softens, or re-opens it; this
line asks the question again at seats where the missing
ingredient exists, and charge 4 (preservation) is discharged
as a citation in F-3, beside `shapedRimVerdict`.

## Two interiors, registered distinctly

The tree carries two different notions of "interior", and this
line does not let one silently stand for the other:

- **The region-split interior** (this brick's primary reading).
  The tree's own rim is a region split: `gravShadowRimFlux`
  and `gravShadowDivergence_rim` (S-2, arbitrary vertex type)
  read a region `S`'s divergence as the flux across the
  crossings between `S` and `Sᶜ`, because the interior edges
  over `S × S` cancel in pairs. A seat has an interior in this
  reading when a region has something on both sides and
  something to cancel. This reading exists already at `Fin 4`
  (the working split: two vertices in, two out).
- **The face-relative interior.** A vertex no face of the
  family touches. At `Fin 4` the square face `⟨0, 1, 2, 3⟩`
  (`vortexSquareFace`) puts all four vertices on its boundary
  loop, so this reading's interior is EMPTY at `Fin 4`; it
  first exists at `Fin 5`. Registered below beside the region
  reading, with a receipt that the two readings part company
  at this seat. F-2's restricted question is face-shaped and
  sits at `Fin 5`; F-0 and F-1 sit at `Fin 4` under the region
  reading, and say so on their faces.

## Zero's four charges — where each is discharged

1. **The finite structure has a nonempty interior** — F-0,
   region reading: `shapedRim4Region` defines it from the
   rim-flux vocabulary; `shapedRim4Split_region` exhibits the
   working split with both sides nonempty and an off-diagonal
   interior pair.
2. **The Shaped-Rim definition is meaningful on that
   interior** — F-0: the shaped-rim definitions (pairing,
   rim-weighted inner pairing, the two frozen exactness
   questions) are stated over the split — weights live on the
   rim (`shapedRim4Rim`), potentials are free on the interior.
3. **Boundary and interior cases are distinguished** — F-0:
   `shapedRim4Rim` vs the region itself, as a definition pair,
   with `gravShadowDivergence_rim` cited as the theorem that
   already treats them differently (interior edges cancel,
   rim crossings survive); and the face reading registered
   distinctly, with its disagreement receipt.
4. **The original Fin 3 negative result remains preserved** —
   F-3's charge, as a theorem-shaped citation beside
   `shapedRimVerdict`. Not this brick's.

## The question (failable, stated at the new seats)

Do rim weights and/or a boundary rule exist at a seat with an
interior under which

  ⟨dropVec φ, X⟩ = ⟨φ, diverge X⟩

holds **exactly**, with no correction term — (Q-all) for all
potentials and all edge fields, and (Q-anti) for all potentials
and all antisymmetric edge fields — where the rim datum is
genuine content as pre-registered below? Existence is not
assumed; the scope carries the honest prior that the Fin 3
kills' deciding exhibits are not obviously `Fin 3`-specific,
and prices F-1 (the unrestricted question) as a likely
seat-general re-firing. The genuinely open sub-question is
F-2's restricted one, at `Fin 5`.

## Kills pre-registered and fences

- **K-RIM4-NONE** — pre-registered, mirroring K-RIM-NONE: no
  rim weighting or boundary rule at the Fin 4+ seat makes the
  pairing exact for all admissible fields, under BOTH field
  regimes (unrestricted in F-1, support-restricted in F-2).
  If it fires, it fires as a theorem, at full rank.
- **K-RIM4-TRIVIAL** — pre-registered, mirroring K-RIM-TRIVIAL,
  degenerate forms named in advance: exactness bought ONLY by
  (a) the **zero potential**, (b) a **constant weight** (the
  ρ ≡ 2 form included — S-2's factor, not a profile), or
  (c) the **correction term re-injected** (R-2's bookkeeping
  verdict is the precedent, cited).
- **GENUINE CONTENT — pre-registered positively**: an
  exactness theorem at the new seat whose rim datum is none
  of the three degenerate forms — a nonconstant rim weight
  varying with the rim, or a pinned rule with a nonzero datum
  under which some admitted potential has a nonzero
  field-shadow on the interior — with the fields not emptied
  by the rule.
- **K-SHADOW-OBJECT** (fence, inherited): no gravity object,
  no G, no continuum field, no Einstein slot is constructed
  or fed by this line. Dial 2 stays 0.
- FRONTIER, never priced: the continuum shaped boundary
  (Dial 3), any derivation of G, any coupling of the rim to
  inertia or time, any seat whose face/support machinery is
  not already in-tree.

## This brick (F-0)

Registration only: the seat made an object, the region-split
interior defined and exhibited, the distinction stated, the
face reading registered beside it. No exactness is claimed;
0 strict by design. F-1 (the unrestricted question) and F-2
(the restricted question, `Fin 5`) are separate bricks, each
on a fresh parent word.
-/

namespace ThetLogos

/-- The seat pairing of this line at `Fin 4`: the full ordered
double sum of the field-shadow `dropVec φ` against the edge
field `X` — this tree's one pairing convention, the left side
of the adjoint identity whose exactness is this line's
question. The Fin 3 line's instance is `shapedRimPairing`,
cited; this is its re-registration at the new seat, per the
scope's F-0 charge. -/
def shapedRim4Pairing (φ : Fin 4 → ℝ) (X : Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, dropVec φ i j * X i j

/-- The rim-weighted potential pairing at `Fin 4`: the
divergence side of the adjoint identity read through rim
weights `ρ` — vertex `i`'s contribution `φ i * ψ i` weighted
by `ρ i`. The flat read is `ρ ≡ 1`. The Fin 3 line's instance
is `shapedRimInner`, cited. -/
def shapedRim4Inner (ρ φ ψ : Fin 4 → ℝ) : ℝ :=
  ∑ i, ρ i * φ i * ψ i

/-- **Q-all, frozen at `Fin 4`.** Rim weights `ρ` under which
the seat pairing equals the rim-weighted divergence pairing
for EVERY potential `φ` and EVERY edge field `X` — the
adjoint identity exact by construction, no correction term,
no restriction on the fields. Registered as a `Prop`;
nothing about it is claimed in this brick. F-1's question. -/
def shapedRim4ExactAll (ρ : Fin 4 → ℝ) : Prop :=
  ∀ φ X, shapedRim4Pairing φ X = shapedRim4Inner ρ φ (diverge X)

/-- **Q-anti, frozen at `Fin 4`.** Rim weights `ρ` under which
the seat pairing equals the rim-weighted divergence pairing
for every potential `φ` and every ANTISYMMETRIC edge field
`X`. Registered separately, as at `Fin 3`, because the flat
seat's own factor of 2 (`gravShadowPairing_antisymm`) lives
here. F-1's second question. -/
def shapedRim4ExactAnti (ρ : Fin 4 → ℝ) : Prop :=
  ∀ φ X, (∀ i j, X j i = - X i j) →
    shapedRim4Pairing φ X = shapedRim4Inner ρ φ (diverge X)

/-- **The region-split interior, as a property of a region.**
A region `S` of the `Fin 4` seat HAS an interior in the
region reading when the split has something on both sides
and something to cancel: `S` nonempty (an inside exists),
`Sᶜ` nonempty (a rim exists), and an off-diagonal pair inside
`S × S` (interior edges exist for `gravShadowDivergence_rim`'s
cancellation to act on). Defined from the rim-flux vocabulary
alone; nothing is invented. Charge 1's definition. -/
def shapedRim4Region (S : Finset (Fin 4)) : Prop :=
  S.Nonempty ∧ Sᶜ.Nonempty ∧ ∃ i ∈ S, ∃ j ∈ S, i ≠ j

/-- **The rim of a region**: the complement side of the split.
The boundary of the region reading — the vertices across
whose crossings `gravShadowRimFlux` reads the region's
divergence. Charge 3's boundary half of the distinction
pair: the region `S` is the interior side, `shapedRim4Rim S`
the rim side, and the two are different sets with different
theorems about them (interior edges cancel in pairs; rim
crossings survive as flux). -/
def shapedRim4Rim (S : Finset (Fin 4)) : Finset (Fin 4) :=
  Sᶜ

/-- **The interior pairs of a region**: the off-diagonal
ordered pairs inside `S × S` — the cancellation zone of
`gravShadowDivergence_rim`, where an antisymmetric field's
contributions annihilate in pairs and no flux is read. The
interior made an object: what a shaped boundary, if one
exists at this seat, would be protecting. -/
def shapedRim4InteriorPairs (S : Finset (Fin 4)) : Finset (Fin 4 × Fin 4) :=
  (S ×ˢ S).filter (fun p => p.1 ≠ p.2)

/-- **The working split at `Fin 4`**: two vertices in
(`{0, 1}` — the interior side), two out (`{2, 3}` — the rim
side). The smallest split at this seat whose interior side
carries an off-diagonal pair. F-0's and F-1's seat. -/
def shapedRim4Split : Finset (Fin 4) :=
  {0, 1}

/-- **Charge 1, discharged for the working split** (region
reading): the split has an interior — both sides are
nonempty, and the interior side carries the off-diagonal
pair `(0, 1)`. A registration receipt: the seat's interior
exists as a finite check, stated so F-1 can cite the seat
without re-exhibiting it. -/
theorem shapedRim4Split_region : shapedRim4Region shapedRim4Split := by
  refine ⟨⟨0, by decide⟩, ⟨2, by decide⟩, 0, by decide, 1, by decide, by decide⟩

/-- **The working split's rim, computed**: the rim side of
`{0, 1}` is `{2, 3}`. Charge 3's receipt at the working seat:
interior side and rim side are named, different, and cover
the seat between them. -/
theorem shapedRim4Split_rim : shapedRim4Rim shapedRim4Split = {2, 3} := by
  decide

/-- **The pinned rim over a split.** The boundary rule of the
region reading: a potential's values on the rim side of the
split are fixed to a boundary datum `φ₀`; its values on the
interior side are constrained by nothing in the rule. This
asymmetry — rim fixed, interior free — is charge 2's second
half and charge 3's distinction stated as a rule: the
shaped-rim definitions are meaningful on the interior
precisely because the rule leaves it free. (The Fin 3 line's
rule is `shapedRimPinned`, cited; there the seat was all rim,
so the distinction this definition carries could not exist.)
What the rule does to the pairing is F-1/F-2's charge, not
this brick's. -/
def shapedRim4Pinned (S : Finset (Fin 4)) (φ₀ φ : Fin 4 → ℝ) : Prop :=
  ∀ i ∈ shapedRim4Rim S, φ i = φ₀ i

/-- **The working split's interior pairs are inhabited**: the
pair `(0, 1)` lies in the cancellation zone. Charge 1's
receipt at the level of the interior-pairs object itself —
the zone `gravShadowDivergence_rim` cancels over is not
merely defined but nonempty at the working seat. -/
theorem shapedRim4Split_interiorPairs_nonempty :
    (shapedRim4InteriorPairs shapedRim4Split).Nonempty :=
  ⟨(0, 1), by decide⟩

/-! ## The face reading, registered distinctly

The region reading above is this line's primary reading at
`Fin 4`. The tree's other interior — the face-relative one —
is registered here beside it, as its own objects, so that no
later brick can quote "the interior at Fin 4" without saying
which reading it means. The two readings disagree at this
seat, and the disagreement is banked as a theorem below, not
left as a remark. -/

/-- **The face reading's face**: the square face
`⟨0, 1, 2, 3⟩` on `Fin 4`, the Vortex line's exhibit
(`vortexSquareFace`, cited — this line registers its own
handle on it and re-proves nothing about it). -/
def shapedRim4Face : GraphFace (Fin 4) :=
  vortexSquareFace

/-- **The face reading's split**: the region the square face
spans is the whole seat — all four vertices lie on the face's
boundary loop, so the face's region is `univ` and its rim
side (the complement) is empty. Registered as a split so the
region reading's test can be applied to it verbatim, in the
receipt below. -/
def shapedRim4FaceSplit : Finset (Fin 4) :=
  Finset.univ

/-- **The two readings part company at `Fin 4`.** The face
reading's split is NOT a region with an interior in the
region reading's sense: its rim side is empty, so charge 1
fails for it on the region test. This is the scope's
registered disagreement, as a theorem: at `Fin 4` the
region-split interior exists and the face-relative interior
does not; the face-relative interior first exists at
`Fin 5`, which is F-2's seat. Neither reading stands for the
other anywhere in this line. -/
theorem shapedRim4FaceSplit_not_region :
    ¬ shapedRim4Region shapedRim4FaceSplit := by
  rintro ⟨-, hcompl, -⟩
  simp only [shapedRim4FaceSplit, Finset.compl_univ,
    Finset.not_nonempty_empty] at hcompl

/-! ## F-1 — the unrestricted question, decided (this brick)

THE UNRESTRICTED QUESTION AT `Fin 4`, ANSWERED — AND ANSWERED
SEAT-GENERALLY. F-0 froze Q-all (`shapedRim4ExactAll`) and
Q-anti (`shapedRim4ExactAnti`) at the working seat, all fields
admissible, under the region-split reading. This brick runs
the pre-registered kills FIRST, as the scope orders, and both
fire — by arguments that never use anything about `Fin 4`
except that it has two distinct vertices. The deciding
exhibits (a single unit on a diagonal edge; a unit swap on an
ordered pair) exist at every finite seat, and the pairing's
arithmetic that reads them (`gravShadowPairing_corrected`,
`gravShadowPairing_antisymm`) is already stated at an
arbitrary finite vertex type in the Shadow line. So this
brick proves the kills at an arbitrary finite seat `V` and
reads `Fin 4` off as the instance. **F-1's form is
seat-general** — stated here, on the face, because F-2's
drafting waits on it (scope queue rule): nothing in the
unrestricted NO is a fact about four vertices or about the
working split; the interior's existence changes nothing when
the fields are unrestricted, because the diagonal exhibit at
an interior vertex is still an admissible field and the
pairing still reads it.

- **K-RIM4-NONE — FIRED on rim weightings (Q-all).** The
  diagonal exhibits force every rim weight to zero (against
  the constant potential `1`, exactness at the diagonal field
  at `k` reads `ρ k` against a pairing of `0`); at `ρ = 0` the
  weighted side vanishes identically while a swap exhibit's
  pairing against `δⱼ` is `2`. No rim weighting at any finite
  seat with two distinct vertices makes the pairing exact for
  all fields (`shapedRimGen_no_weight`; `Fin 4` instance
  `shapedRim4_no_weight`).
- **K-RIM4-TRIVIAL — FIRED on the pinned rule (degenerate
  form (a), the zero potential).** The pinned family — every
  potential agreeing with a datum `φ₀` on a rim set — is exact
  for all fields iff the rim set is the WHOLE seat and the
  datum is zero (`shapedRimGenPinned_exact_iff`). Read at the
  working split, whose rim is `{2, 3}` and whose region is
  `{0, 1}`: exactness would require the rim to be everything,
  i.e. the region EMPTY, and the datum zero
  (`shapedRim4Pinned_exact_iff`). The pinned mirror reflects
  evenly only when there is no interior left to protect and
  nothing on the rim either. The interior's freedom — charge
  2's asymmetry, the whole point of the seat — is exactly
  what the bump exhibit spends.
- **K-RIM4-TRIVIAL — FIRED on the antisymmetric weighting
  (degenerate form (b), the constant weight).** Q-anti's
  unique exact weight at any seat where every vertex has a
  distinct partner is the constant `ρ ≡ 2`
  (`shapedRimGenWeightAnti_unique`; `Fin 4` instance
  `shapedRim4WeightAnti_unique`) — S-2's antisymmetric
  factor, the same at every rim vertex: a number, not a
  profile of the rim, exactly as at `Fin 3`.
- Degenerate form (c), the correction term re-injected, is
  not re-litigated here: the identity that decides it
  (`gravShadowPairing_corrected`) is already stated at an
  arbitrary finite seat, `Fin 4` included, and the Fin 3
  line's R-2 measurement of the pump is cited, not re-proved.

The Fin 3 verdict is preserved verbatim (charge 4 is F-3's
citation, beside `shapedRimVerdict`); nothing below restates
or re-grades it. What survives for F-2 is exactly what the
scope priced: only a RESTRICTION of the fields can change
this answer, because every exhibit above is an unrestricted
field. NO CLAIM; Dial 2 stays 0; no gravity object.
-/

section F1General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The seat pairing at an arbitrary finite seat: the full
ordered double sum of the field-shadow `dropVec φ` against
the edge field `X`. The seat-general form of
`shapedRim4Pairing` (its `Fin 4` instance) and of the Fin 3
line's `shapedRimPairing`. -/
def shapedRimGenPairing (φ : V → ℝ) (X : V → V → ℝ) : ℝ :=
  ∑ i, ∑ j, dropVec φ i j * X i j

/-- The rim-weighted potential pairing at an arbitrary
finite seat: vertex `i`'s contribution `φ i * ψ i` weighted
by `ρ i`. The seat-general form of `shapedRim4Inner`. -/
def shapedRimGenInner (ρ φ ψ : V → ℝ) : ℝ :=
  ∑ i, ρ i * φ i * ψ i

/-- **Q-all at an arbitrary finite seat.** Rim weights `ρ`
under which the seat pairing equals the rim-weighted
divergence pairing for EVERY potential and EVERY edge field.
The seat-general form of `shapedRim4ExactAll`. -/
def shapedRimGenExactAll (ρ : V → ℝ) : Prop :=
  ∀ φ X, shapedRimGenPairing φ X = shapedRimGenInner ρ φ (diverge X)

/-- **Q-anti at an arbitrary finite seat.** Rim weights `ρ`
under which the seat pairing equals the rim-weighted
divergence pairing for every potential and every
ANTISYMMETRIC edge field. The seat-general form of
`shapedRim4ExactAnti`. -/
def shapedRimGenExactAnti (ρ : V → ℝ) : Prop :=
  ∀ φ X, (∀ i j, X j i = - X i j) →
    shapedRimGenPairing φ X = shapedRimGenInner ρ φ (diverge X)

/-- The diagonal unit field at `k`, at an arbitrary finite
seat: a single unit on the diagonal edge `k → k`, zero
elsewhere. The unrestricted question's deciding exhibit —
admissible at every seat, interior vertex or not. -/
def shapedRimGenDiag (k : V) : V → V → ℝ :=
  fun i j => if i = k ∧ j = k then 1 else 0

/-- The antisymmetric unit on the ordered pair `(i, j)`, at
an arbitrary finite seat: one unit flowing `i → j`, minus
one on the reverse edge, zero elsewhere. -/
def shapedRimGenSwap (i j : V) : V → V → ℝ :=
  fun a b => if a = i ∧ b = j then 1 else if a = j ∧ b = i then -1 else 0

/-- The swap exhibit is a current: antisymmetric, whenever
its two vertices differ. -/
theorem shapedRimGenSwap_antisymm {i j : V} (h : i ≠ j) (a b : V) :
    shapedRimGenSwap i j b a = - shapedRimGenSwap i j a b := by
  unfold shapedRimGenSwap
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

/-- The swap exhibit's divergence, vertex by vertex: `1` at
its head `j`, `-1` at its tail `i`, `0` elsewhere. -/
theorem shapedRimGenSwap_diverge {i j : V} (h : i ≠ j) (a : V) :
    diverge (shapedRimGenSwap i j) a
      = if a = j then 1 else if a = i then -1 else 0 := by
  rw [diverge_apply]
  by_cases haj : a = j
  · rw [haj, if_pos rfl]
    have hsum : (∑ b, shapedRimGenSwap i j b j) = shapedRimGenSwap i j i j := by
      apply Finset.sum_eq_single i
      · intro b _ hb
        unfold shapedRimGenSwap
        rw [if_neg (fun hh => hb hh.1),
          if_neg (fun hh => h hh.2.symm)]
      · simp
    rw [hsum]
    show shapedRimGenSwap i j i j = 1
    unfold shapedRimGenSwap
    rw [if_pos ⟨rfl, rfl⟩]
  · by_cases hai : a = i
    · rw [hai, if_neg (fun hh => haj (hai.trans hh)), if_pos rfl]
      have hsum : (∑ b, shapedRimGenSwap i j b i) = shapedRimGenSwap i j j i := by
        apply Finset.sum_eq_single j
        · intro b _ hb
          unfold shapedRimGenSwap
          rw [if_neg (fun hh => h hh.2),
            if_neg (fun hh => hb hh.1)]
        · simp
      rw [hsum]
      show shapedRimGenSwap i j j i = -1
      unfold shapedRimGenSwap
      rw [if_neg (fun hh => h hh.1.symm), if_pos ⟨rfl, rfl⟩]
    · rw [if_neg haj, if_neg hai]
      apply Finset.sum_eq_zero
      intro b _
      unfold shapedRimGenSwap
      rw [if_neg (fun hh => haj hh.2), if_neg (fun hh => hai hh.2)]

/-- The diagonal exhibit's divergence: `1` at `k`, `0`
elsewhere. -/
theorem shapedRimGenDiag_diverge (k m : V) :
    diverge (shapedRimGenDiag k) m = if m = k then 1 else 0 := by
  rw [diverge_apply]
  by_cases hm : m = k
  · rw [hm, if_pos rfl]
    have hsum : (∑ j, shapedRimGenDiag k j k) = shapedRimGenDiag k k k := by
      apply Finset.sum_eq_single k
      · intro b _ hb
        unfold shapedRimGenDiag
        rw [if_neg (fun hh => hb hh.1)]
      · simp
    rw [hsum]
    show shapedRimGenDiag k k k = 1
    unfold shapedRimGenDiag
    rw [if_pos ⟨rfl, rfl⟩]
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro j _
    unfold shapedRimGenDiag
    rw [if_neg (fun hh => hm hh.2)]

/-- The pairing against a diagonal exhibit vanishes, for
every potential: the pairing reads the drop on the diagonal
edge, and the drop on a diagonal edge is `φ k − φ k = 0`. -/
theorem shapedRimGenPairing_diag (φ : V → ℝ) (k : V) :
    shapedRimGenPairing φ (shapedRimGenDiag k) = 0 := by
  unfold shapedRimGenPairing
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hik : i = k
  · by_cases hjk : j = k
    · rw [hik, hjk, dropVec_apply]
      simp
    · have hdiag : shapedRimGenDiag k k j = 0 := by
        unfold shapedRimGenDiag
        exact if_neg (fun hh => hjk hh.2)
      rw [hik, hdiag, mul_zero]
  · have hdiag : shapedRimGenDiag k i j = 0 := by
      unfold shapedRimGenDiag
      exact if_neg (fun hh => hik hh.1)
    rw [hdiag, mul_zero]

/-- **One potential, all fields — seat-general.** A single
potential's pairing against `diverge` is exact for EVERY
edge field iff the potential is zero. The diagonal exhibit
decides it at any seat: the pairing reads the drop on the
diagonal edge (`φ k − φ k = 0`), the divergence side reads
`φ k` itself. The Fin 3 line's `shapedRimExact_single_iff`,
proved here at an arbitrary finite seat. -/
theorem shapedRimGenExact_single_iff (φ : V → ℝ) :
    (∀ X, shapedRimGenPairing φ X = ∑ i, φ i * diverge X i) ↔ φ = 0 := by
  constructor
  · intro h
    funext k
    have hdiv : ∀ m, diverge (shapedRimGenDiag k) m
        = if m = k then 1 else 0 :=
      fun m => shapedRimGenDiag_diverge k m
    have hRHS : (∑ i, φ i * diverge (shapedRimGenDiag k) i) = φ k := by
      have hsum : (∑ i, φ i * diverge (shapedRimGenDiag k) i)
          = φ k * diverge (shapedRimGenDiag k) k := by
        apply Finset.sum_eq_single k
        · intro b _ hb
          rw [hdiv b, if_neg hb, mul_zero]
        · simp
      rw [hsum, hdiv k, if_pos rfl, mul_one]
    have hX := h (shapedRimGenDiag k)
    rw [shapedRimGenPairing_diag, hRHS] at hX
    exact hX.symm
  · intro h X
    rw [h]
    simp [shapedRimGenPairing, dropVec_apply]

/-- **The pinned rule, decided for every rim set at once —
seat-general.** The pinned family — every potential agreeing
with the datum `φ₀` on a rim set `R` — is exact for all
fields iff `R` is the whole seat AND the datum is zero: the
only exact pinned mirror admits the single zero potential
and nothing else. The datum itself is admitted, so it must
vanish (the single-potential iff); at any unpinned vertex
the family admits a unit bump, which must also vanish — it
doesn't. The Fin 3 line's `shapedRimPinned_exact_iff` at an
arbitrary finite seat. -/
theorem shapedRimGenPinned_exact_iff (R : Finset V) (φ₀ : V → ℝ) :
    (∀ φ, (∀ i ∈ R, φ i = φ₀ i) → ∀ X,
      shapedRimGenPairing φ X = ∑ i, φ i * diverge X i)
      ↔ R = Finset.univ ∧ φ₀ = 0 := by
  constructor
  · intro H
    have hφ₀ : φ₀ = 0 :=
      (shapedRimGenExact_single_iff φ₀).mp (H φ₀ (fun i _ => rfl))
    have hR : R = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro k
      by_contra hk
      have hadm : ∀ i ∈ R, Function.update (0 : V → ℝ) k 1 i = φ₀ i := by
        intro i hi
        have hik : i ≠ k := fun hh => hk (hh ▸ hi)
        rw [Function.update_of_ne hik]
        simp [hφ₀]
      have hzero := (shapedRimGenExact_single_iff _).mp (H _ hadm)
      have hk1 : Function.update (0 : V → ℝ) k 1 k = 1 :=
        Function.update_self k 1 0
      rw [hzero] at hk1
      simp at hk1
    exact ⟨hR, hφ₀⟩
  · rintro ⟨hR, hφ₀⟩ φ hφ X
    have hφeq : φ = 0 := by
      funext i
      have hi : φ i = φ₀ i := hφ i (hR.symm ▸ Finset.mem_univ i)
      rw [hi, hφ₀]
    exact (shapedRimGenExact_single_iff φ).mpr hφeq X

/-- **K-RIM4-NONE — FIRED on rim weightings, seat-general.**
At any finite seat with two distinct vertices, no rim weight
makes the pairing exact for all fields. The diagonal
exhibits force `ρ = 0` (against the constant potential `1`,
exactness at the diagonal field at `k` reads `ρ k` against a
pairing of `0`); and at `ρ = 0` the weighted side vanishes
identically while the swap exhibit's pairing against `δⱼ` is
`2`. The Fin 3 line's `shapedRimExistsClaim_false` at an
arbitrary finite seat. -/
theorem shapedRimGen_no_weight {i₀ j₀ : V} (h : i₀ ≠ j₀) :
    ¬ ∃ ρ : V → ℝ, shapedRimGenExactAll ρ := by
  rintro ⟨ρ, hρ⟩
  have hρ0 : ρ = 0 := by
    funext k
    have hX := hρ (fun _ => 1) (shapedRimGenDiag k)
    rw [shapedRimGenPairing_diag] at hX
    have hinner : shapedRimGenInner ρ (fun _ => 1)
        (diverge (shapedRimGenDiag k)) = ρ k := by
      have hsum : (∑ i, ρ i * (fun _ => (1 : ℝ)) i
          * diverge (shapedRimGenDiag k) i)
          = ρ k * (fun _ => (1 : ℝ)) k * diverge (shapedRimGenDiag k) k := by
        apply Finset.sum_eq_single k
        · intro b _ hb
          show ρ b * 1 * diverge (shapedRimGenDiag k) b = 0
          rw [shapedRimGenDiag_diverge, if_neg hb, mul_zero]
        · simp
      unfold shapedRimGenInner
      rw [hsum]
      show ρ k * 1 * diverge (shapedRimGenDiag k) k = ρ k
      rw [shapedRimGenDiag_diverge, if_pos rfl]
      simp
    rw [hinner] at hX
    exact hX.symm
  have hInner0 : ∀ (φ ψ : V → ℝ), shapedRimGenInner 0 φ ψ = 0 := by
    intro φ ψ
    unfold shapedRimGenInner
    apply Finset.sum_eq_zero
    intro i _
    simp
  have hanti : ∀ a b, shapedRimGenSwap i₀ j₀ b a
      = - shapedRimGenSwap i₀ j₀ a b :=
    shapedRimGenSwap_antisymm h
  have hLHS : shapedRimGenPairing (fun i => if i = j₀ then (1 : ℝ) else 0)
      (shapedRimGenSwap i₀ j₀) = 2 := by
    have hpa := gravShadowPairing_antisymm
      (fun i => if i = j₀ then (1 : ℝ) else 0) (shapedRimGenSwap i₀ j₀) hanti
    have hsum : (∑ a, (fun i => if i = j₀ then (1 : ℝ) else 0) a
        * diverge (shapedRimGenSwap i₀ j₀) a) = 1 := by
      have hmain : (∑ a, (fun i => if i = j₀ then (1 : ℝ) else 0) a
          * diverge (shapedRimGenSwap i₀ j₀) a)
          = (fun i => if i = j₀ then (1 : ℝ) else 0) j₀
            * diverge (shapedRimGenSwap i₀ j₀) j₀ := by
        apply Finset.sum_eq_single j₀
        · intro b _ hb
          show (if b = j₀ then (1 : ℝ) else 0)
            * diverge (shapedRimGenSwap i₀ j₀) b = 0
          rw [if_neg hb, zero_mul]
        · simp
      rw [hmain]
      show (if j₀ = j₀ then (1 : ℝ) else 0)
        * diverge (shapedRimGenSwap i₀ j₀) j₀ = 1
      rw [if_pos rfl, shapedRimGenSwap_diverge h, if_pos rfl, mul_one]
    have hpa' : shapedRimGenPairing (fun i => if i = j₀ then (1 : ℝ) else 0)
        (shapedRimGenSwap i₀ j₀)
        = 2 * ∑ i, (fun i => if i = j₀ then (1 : ℝ) else 0) i
            * diverge (shapedRimGenSwap i₀ j₀) i := hpa
    rw [hsum, mul_one] at hpa'
    exact hpa'
  have hX := hρ (fun i => if i = j₀ then (1 : ℝ) else 0)
    (shapedRimGenSwap i₀ j₀)
  rw [hρ0, hInner0, hLHS] at hX
  norm_num at hX

/-- **Q-anti's unique exact weight is the constant `2` —
seat-general.** At any finite seat where every vertex has a
distinct partner, a rim weight makes the pairing exact for
every potential and every antisymmetric field iff it is `2`
at every vertex: the constant factor S-2's antisymmetric
identity already carries (`gravShadowPairing_antisymm`,
cited for the ⇐ direction), read off vertex by vertex by
the swap exhibits for the ⇒ direction. The Fin 3 line's
`shapedRimWeightAnti_unique` at an arbitrary finite seat. -/
theorem shapedRimGenWeightAnti_unique (hpair : ∀ j : V, ∃ i, i ≠ j)
    (ρ : V → ℝ) :
    shapedRimGenExactAnti ρ ↔ ρ = fun _ => 2 := by
  constructor
  · intro hρ
    funext j
    show ρ j = 2
    obtain ⟨i, hi⟩ := hpair j
    have hanti : ∀ a b, shapedRimGenSwap i j b a
        = - shapedRimGenSwap i j a b :=
      shapedRimGenSwap_antisymm hi
    have hp : shapedRimGenPairing (fun a => if a = j then (1 : ℝ) else 0)
        (shapedRimGenSwap i j) = 2 := by
      have hpa := gravShadowPairing_antisymm
        (fun a => if a = j then (1 : ℝ) else 0) (shapedRimGenSwap i j) hanti
      have hsum : (∑ a, (fun a => if a = j then (1 : ℝ) else 0) a
          * diverge (shapedRimGenSwap i j) a) = 1 := by
        have hmain : (∑ a, (fun a => if a = j then (1 : ℝ) else 0) a
            * diverge (shapedRimGenSwap i j) a)
            = (fun a => if a = j then (1 : ℝ) else 0) j
              * diverge (shapedRimGenSwap i j) j := by
          apply Finset.sum_eq_single j
          · intro b _ hb
            show (if b = j then (1 : ℝ) else 0)
              * diverge (shapedRimGenSwap i j) b = 0
            rw [if_neg hb, zero_mul]
          · simp
        rw [hmain]
        show (if j = j then (1 : ℝ) else 0)
          * diverge (shapedRimGenSwap i j) j = 1
        rw [if_pos rfl, shapedRimGenSwap_diverge hi, if_pos rfl, mul_one]
      have hpa' : shapedRimGenPairing (fun a => if a = j then (1 : ℝ) else 0)
          (shapedRimGenSwap i j)
          = 2 * ∑ a, (fun a => if a = j then (1 : ℝ) else 0) a
              * diverge (shapedRimGenSwap i j) a := hpa
      rw [hsum, mul_one] at hpa'
      exact hpa'
    have hinner : shapedRimGenInner ρ (fun a => if a = j then (1 : ℝ) else 0)
        (diverge (shapedRimGenSwap i j)) = ρ j := by
      have hsum : (∑ a, ρ a * (fun a => if a = j then (1 : ℝ) else 0) a
          * diverge (shapedRimGenSwap i j) a)
          = ρ j * (fun a => if a = j then (1 : ℝ) else 0) j
            * diverge (shapedRimGenSwap i j) j := by
        apply Finset.sum_eq_single j
        · intro b _ hb
          show ρ b * (if b = j then (1 : ℝ) else 0)
            * diverge (shapedRimGenSwap i j) b = 0
          rw [if_neg hb]
          simp
        · simp
      unfold shapedRimGenInner
      rw [hsum]
      show ρ j * (if j = j then (1 : ℝ) else 0)
        * diverge (shapedRimGenSwap i j) j = ρ j
      rw [if_pos rfl, shapedRimGenSwap_diverge hi, if_pos rfl]
      ring
    have hX := hρ (fun a => if a = j then (1 : ℝ) else 0)
      (shapedRimGenSwap i j) hanti
    rw [hp, hinner] at hX
    exact hX.symm
  · intro hρ φ X hX
    rw [hρ]
    have hp := gravShadowPairing_antisymm φ X hX
    have hinner : shapedRimGenInner (fun _ => (2 : ℝ)) φ (diverge X)
        = 2 * ∑ i, φ i * diverge X i := by
      unfold shapedRimGenInner
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      show (2 : ℝ) * φ i * diverge X i = 2 * (φ i * diverge X i)
      ring
    have hp' : shapedRimGenPairing φ X
        = 2 * ∑ i, φ i * diverge X i := hp
    exact hp'.trans hinner.symm

end F1General

/-! ## F-1 at the working seat — the `Fin 4` instances

The seat-general decisions above, read off at `Fin 4` under
the region-split reading (F-0's seat). The instances are the
brick's answer to its frozen questions; the proofs are the
seat-general theorems, because the answers never used the
seat. -/

/-- **K-RIM4-NONE — FIRED at `Fin 4`.** No rim weighting at
the working seat makes the pairing exact for all potentials
and all edge fields: Q-all (`shapedRim4ExactAll`) has no
witness. The `Fin 4` instance of `shapedRimGen_no_weight`. -/
theorem shapedRim4_no_weight :
    ¬ ∃ ρ : Fin 4 → ℝ, shapedRim4ExactAll ρ :=
  shapedRimGen_no_weight (V := Fin 4) (by decide : (0 : Fin 4) ≠ 1)

/-- **Q-anti at `Fin 4`: the unique exact weight is the
constant `2`.** K-RIM4-TRIVIAL's degenerate form (b) at the
working seat: the one exact "shaping" of the currents'
pairing does not vary with the rim — S-2's antisymmetric
factor, not a profile. The `Fin 4` instance of
`shapedRimGenWeightAnti_unique` (every vertex of `Fin 4` has
a distinct partner: its successor). -/
theorem shapedRim4WeightAnti_unique (ρ : Fin 4 → ℝ) :
    shapedRim4ExactAnti ρ ↔ ρ = fun _ => 2 := by
  have hne : ∀ j : Fin 4, j + 1 ≠ j := by decide
  exact shapedRimGenWeightAnti_unique (fun j => ⟨j + 1, hne j⟩) ρ

/-- **The pinned rule at the working seat, decided.** The
family pinned to a datum `φ₀` on the rim of a region `S`
(`shapedRim4Pinned` — rim values fixed, interior values
free) is exact for all fields iff the region is EMPTY and
the datum is zero. At the working split `S = {0, 1}` (rim
`{2, 3}`) exactness therefore fails for every datum: the
interior the seat was built to have is exactly what the
pinned route cannot afford. The `Fin 4` reading of
`shapedRimGenPinned_exact_iff` at the rim set `Sᶜ`. -/
theorem shapedRim4Pinned_exact_iff (S : Finset (Fin 4)) (φ₀ : Fin 4 → ℝ) :
    (∀ φ, shapedRim4Pinned S φ₀ φ → ∀ X,
      shapedRim4Pairing φ X = ∑ i, φ i * diverge X i)
      ↔ S = ∅ ∧ φ₀ = 0 := by
  have hgen := shapedRimGenPinned_exact_iff (V := Fin 4) Sᶜ φ₀
  constructor
  · intro H
    have H' : ∀ φ, (∀ i ∈ Sᶜ, φ i = φ₀ i) → ∀ X,
        shapedRimGenPairing φ X = ∑ i, φ i * diverge X i := H
    have h := hgen.mp H'
    exact ⟨(Finset.compl_eq_univ_iff S).mp h.1, h.2⟩
  · intro H φ hφ X
    have H' : ∀ φ, (∀ i ∈ Sᶜ, φ i = φ₀ i) → ∀ X,
        shapedRimGenPairing φ X = ∑ i, φ i * diverge X i :=
      hgen.mpr ⟨(Finset.compl_eq_univ_iff S).mpr H.1, H.2⟩
    exact H' φ hφ X

/-- **K-RIM4-TRIVIAL — FIRED on the pinned route at
`Fin 4`.** If the pinned family (any region, any datum) is
exact for all fields, the datum is zero and its field-shadow
vanishes identically: the restricted mirror at the seat with
an interior reflects evenly only by emptying — the region
annihilated (previous theorem) and the potential zero. The
degeneracy the scope's check charged this line to record,
recorded as a theorem. -/
theorem shapedRim4Pinned_trivial (S : Finset (Fin 4)) (φ₀ : Fin 4 → ℝ)
    (h : ∀ φ, shapedRim4Pinned S φ₀ φ → ∀ X,
      shapedRim4Pairing φ X = ∑ i, φ i * diverge X i) :
    φ₀ = 0 ∧ dropVec φ₀ = 0 := by
  have hφ₀ : φ₀ = 0 := ((shapedRim4Pinned_exact_iff S φ₀).mp h).2
  refine ⟨hφ₀, ?_⟩
  rw [hφ₀]
  funext i j
  show dropVec (0 : Fin 4 → ℝ) i j = 0
  rw [dropVec_apply]
  simp

/-- **F-1's verdict, assembled.** The unrestricted question
at `Fin 4`, in one statement: (1) no rim weighting makes the
pairing exact for all fields (K-RIM4-NONE); (2) the
currents' unique exact rim weight is the constant `2` —
S-2's factor, not a shape (K-RIM4-TRIVIAL, form (b)); (3)
the pinned rule is exact only at the empty region and the
zero datum (K-RIM4-TRIVIAL, form (a)). **F-1's form is
seat-general**: each conjunct is the `Fin 4` instance of a
theorem proved at an arbitrary finite seat, and the report
of this brick states it so F-2 can draft against it — the
unrestricted NO does not depend on the seat, the split, or
the interior; only a restriction of the fields (F-2's
question) is untouched by it. -/
theorem shapedRim4F1Verdict :
    (¬ ∃ ρ : Fin 4 → ℝ, shapedRim4ExactAll ρ) ∧
    (∀ ρ : Fin 4 → ℝ, shapedRim4ExactAnti ρ → ρ = fun _ => 2) ∧
    (∀ (S : Finset (Fin 4)) (φ₀ : Fin 4 → ℝ),
      (∀ φ, shapedRim4Pinned S φ₀ φ → ∀ X,
        shapedRim4Pairing φ X = ∑ i, φ i * diverge X i) →
      S = ∅ ∧ φ₀ = 0) :=
  ⟨shapedRim4_no_weight,
   fun ρ hρ => (shapedRim4WeightAnti_unique ρ).mp hρ,
   fun S φ₀ h => (shapedRim4Pinned_exact_iff S φ₀).mp h⟩

end ThetLogos
