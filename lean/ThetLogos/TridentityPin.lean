import Mathlib.Tactic
import ThetLogos.IdensityBoundary
import ThetLogos.SubsetMarginalsPin

/-!
# ThetLogos.TridentityPin — the tridentity seats 1 and 2

**Lane-grade pin. NO CLAIM. Pre-registered DIAL-INELIGIBLE; dials
0/4 under every outcome. T5 / Register-A design structure: this
pin seats two terms of Zero's named ternary as finite statement
pins over vocabulary already in the census of record; it asserts
no theorem about any continuum object, and no dial's registered
condition is met by anything here.**

Commissioned: Zero, 2026-11-21 19:24–19:25 EST ("start with the
tridentity seats and build from there in 3's" → "Scope the
tridentity build fresh first" → "resume with Idensity as well").
Scope of record: `tridentity-build-scope-2026-11-21.md`.
Interpretation ruling — Zero, verbatim (2026-11-21 22:20 EST):
"Seat 1 — Containment: Boundary precedence. Seat 2 — Identity:
Determination through boundary and contained invariants.
Universal seat — Containment = Identity: Governed separately by
K-TRID-MERGE. One important restriction: these are structural
interpretations, not yet theorem statements." Fire word — Zero,
2026-11-21 22:24 EST: "yes build it". Every statement below
carries its interpretation source on its face.

**The ternary as named** — Zero's pin, verbatim (2026-11-09
11:21 EST): "pin it as the symmetry breaking ternary,
containment/identity/Idensity". The mechanism of the breaking
was never stated by Zero and is not glossed anywhere in this
pin (K-TRID-BREAK).

**Seat 3 — Idensity**, defined by Zero verbatim (2026-11-09
11:23 EST): *"Idensity (Identity Density): The concentration of
invariant state information and modular energy confined per
unit boundary volume."* The numerator is the ordered PAIR
(invariant state information, reference-modular energy) — pair
form, never a sum (Zero's ruling, 2026-11-09; K-IDENSITY-DOUBLE
stands). Seat 3's built content is ID-1
(`ThetLogos.IdensityCoincidence`) and ID-2
(`ThetLogos.IdensityBoundary`), in the census of record at T1
(integrated T6, 2026-11-19). This pin CITES them; it restates
nothing (K-TRID-RESTATE). **ID-3 — the Idensity definition
itself — is NOT built here**: it remains gated on Zero's two
rulings (the primary boundary form; the empty-boundary
convention), and nothing in this pin forms a ratio or chooses
a denominator (K-TRID-GATE).

**Tonight's rulings** (2026-11-21: "the continuum is Unity";
Unity re-graded to the universal seat; "containment is
identity") are doctrine at T5. The universal-seat relation is
NOT a seat in this tree and no brick states it as a Lean
identity (K-TRID-MERGE): in-tree, the seats keep their
2026-11-09 order and their separate names.
-/

namespace ThetLogos

/-! ## Brick T0 — the tridentity record card (0 strict by design)

The ternary as named, seated as data: three seats, in Zero's
pinned order. The card asserts nothing; the seats' content is
Bricks T1 and T2 below, and ID-1/ID-2 in census for Seat 3. -/

/-- The three seats of Zero's symmetry-breaking ternary, in
    their pinned order (2026-11-09): containment, identity,
    Idensity. A record only — the type names the seats; it
    asserts nothing about them (K-TRID-NAME). -/
inductive TridentitySeat
  | containment
  | identity
  | idensity

/-- The seat order, as data: containment first, identity
    second, Idensity third — the order of Zero's pin, kept
    in-tree under K-TRID-MERGE. -/
def tridentitySeats : List TridentitySeat :=
  [.containment, .identity, .idensity]

/-! ## Brick T1 — Seat 1, containment: boundary precedence

Interpretation source (Zero, 2026-11-21 22:20 EST): "Seat 1 —
Containment: Boundary precedence." Anchor: Gurd Law — "Before
information can be processed or communicated, the boundary
must first be drawn and contained."

Why this form: precedence has no temporal reading inside a
definition; Lean definitions are not ordered in time. The
honest finite content of "the boundary comes first" over
ID-2's vocabulary is determination-independence: the boundary
data of a region — in BOTH of ID-2's forms, with both
denominators — is fixed by the adjacency's values ACROSS the
region's cut alone. Entries with both endpoints inside the
region, or both outside, never enter: they may change freely
and the boundary does not move. The boundary is therefore
determined before, and independently of, any interior
content; and neither denominator takes a state argument at
all, so boundary volume is prior to content in the signature
as well. That is the precedence this seat can honestly carry.

Not a restatement (K-TRID-RESTATE): ID-2 proves membership
and the zero-boundary faces for ONE adjacency. These theorems
quantify over TWO adjacencies and assert what ID-2 nowhere
asserts — they are the seat's own content. -/

section ContainmentSeat

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Seat 1, vertex form (Tier T1 — proved):** the vertex
    boundary of a region depends only on the adjacency's
    values across the cut (outside × inside). Two adjacencies
    agreeing there have the same vertex boundary at `s` —
    interior and exterior entries are never consulted. -/
theorem vertexBoundary_eq_of_agree_out_in {a a' : κ → κ → ℝ}
    {s : Finset κ}
    (h : ∀ x y, x ∉ s → y ∈ s → a x y = a' x y) :
    vertexBoundary a s = vertexBoundary a' s := by
  ext x
  simp only [mem_vertexBoundary]
  constructor
  · rintro ⟨hx, y, hy, hay⟩
    exact ⟨hx, y, hy, by rwa [h x y hx hy] at hay⟩
  · rintro ⟨hx, y, hy, hay⟩
    exact ⟨hx, y, hy, by rwa [← h x y hx hy] at hay⟩

/-- **Seat 1, vertex denominator (Tier T1 — proved):** the
    card-form boundary volume is likewise fixed by the
    cross-cut values alone. -/
theorem boundaryCard_eq_of_agree_out_in {a a' : κ → κ → ℝ}
    {s : Finset κ}
    (h : ∀ x y, x ∉ s → y ∈ s → a x y = a' x y) :
    boundaryCard a s = boundaryCard a' s := by
  rw [boundaryCard, boundaryCard,
    vertexBoundary_eq_of_agree_out_in h]

/-- **Seat 1, edge form (Tier T1 — proved):** the edge cut of
    a region depends only on the adjacency's values across
    the cut (inside × outside). -/
theorem edgeCut_eq_of_agree_in_out {a a' : κ → κ → ℝ}
    {s : Finset κ}
    (h : ∀ x y, x ∈ s → y ∉ s → a x y = a' x y) :
    edgeCut a s = edgeCut a' s := by
  ext p
  simp only [mem_edgeCut]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rwa [h p.1 p.2 h1 h2] at h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rwa [← h p.1 p.2 h1 h2] at h3⟩

/-- **Seat 1, weighted denominator (Tier T1 — proved):** the
    weighted boundary volume is fixed by the cross-cut values
    alone. -/
theorem cutWeight_eq_of_agree_in_out {a a' : κ → κ → ℝ}
    {s : Finset κ}
    (h : ∀ x y, x ∈ s → y ∉ s → a x y = a' x y) :
    cutWeight a s = cutWeight a' s := by
  unfold cutWeight
  rw [edgeCut_eq_of_agree_in_out h]
  apply Finset.sum_congr rfl
  intro p hp
  exact h p.1 p.2 (mem_edgeCut.mp hp).1 (mem_edgeCut.mp hp).2.1

end ContainmentSeat

/-! ## Brick T2 — Seat 2, identity: determination through
    boundary and contained invariants

Interpretation source (Zero, 2026-11-21 22:20 EST): "Seat 2 —
Identity: Determination through boundary and contained
invariants." Anchor: Zero's corollary (2026-10-06): "the
boundary creates identity."

What this seat adds beyond Tet, on the face (the seat's
fence): Tet names equality itself; Seat 2 does not restate
it. Seat 2 pins a region's DETERMINATION DATA — which data
constitute a region's identity (its boundary, together with
its contained invariants) — and proves exactly when that data
suffices to determine the region, and when it does not. The
contained invariant carried here is the region entropy
`regionEntropy` (H-1, in census) — component 1 of Zero's
Idensity pair. The pair's energy component is ID-4's, unbuilt;
this seat does not borrow it. Carrying the entropy as DATA is
not defining Idensity: no ratio is formed and no denominator
is chosen anywhere in this brick (K-TRID-GATE).

Verdicts, stated before the proofs:
- Determination HOLDS through the boundary alone when the
  adjacency crosses at every off-diagonal pair: a nonempty
  region is exactly the complement of its vertex boundary.
  The empty region is the named exception — its vertex
  boundary is empty (ID-2), so the recovery formula would
  return the full region. The exception is the zero-boundary
  family ID-2 carries openly; it is NOT the ID-3
  empty-boundary convention question, which stays gated.
- Determination FAILS in general — the kill, by exhibit:
  under the zero adjacency on `Fin 2` with the constant
  weight, the two singleton regions have identical identity
  data (empty boundary, equal region entropy) and are
  different regions. Identity data determine a seat only
  under a named condition; as a universal law, determination
  is false. -/

section IdentitySeat

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*}
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-- **Seat 2's identity data** (Tier T2 — definition): a
    region's boundary together with its contained invariant —
    the pair (vertex boundary, region entropy). The data a
    region's identity is determined through, when it is
    determined at all. Not an Idensity: no ratio, no
    denominator (K-TRID-GATE). -/
noncomputable def seatIdentityData (a : κ → κ → ℝ)
    (w : (∀ i, X i) → ℝ) (s : Finset κ) : Finset κ × ℝ :=
  (vertexBoundary a s, regionEntropy w s)

/-- The identity data, unfolded. -/
theorem seatIdentityData_eq (a : κ → κ → ℝ)
    (w : (∀ i, X i) → ℝ) (s : Finset κ) :
    seatIdentityData a w s
      = (vertexBoundary a s, regionEntropy w s) :=
  rfl

/-- **Seat 2, determination through the boundary (Tier T1 —
    proved):** under an adjacency crossing at every
    off-diagonal pair, a NONEMPTY region is exactly the
    complement of its vertex boundary — the boundary alone
    recovers the region. -/
theorem univ_sdiff_vertexBoundary_eq (a : κ → κ → ℝ)
    (ha : ∀ x y, x ≠ y → a x y ≠ 0) {s : Finset κ}
    (hs : s.Nonempty) :
    Finset.univ \ vertexBoundary a s = s := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · intro hx
    by_contra hxs
    obtain ⟨y, hy⟩ := hs
    exact hx (mem_vertexBoundary.mpr ⟨hxs, y, hy,
      ha x y (fun hxy => hxs (hxy ▸ hy))⟩)
  · intro hx hxb
    exact (mem_vertexBoundary.mp hxb).1 hx

/-- **Seat 2, determination (Tier T1 — proved):** under the
    same full-crossing adjacency, two nonempty regions with
    the same identity data are the same region — the data
    determine the seat. (The boundary component already
    suffices here; the invariant is carried, not needed.) -/
theorem eq_of_seatIdentityData_eq (a : κ → κ → ℝ)
    (ha : ∀ x y, x ≠ y → a x y ≠ 0)
    (w : (∀ i, X i) → ℝ) {s t : Finset κ}
    (hs : s.Nonempty) (ht : t.Nonempty)
    (h : seatIdentityData a w s = seatIdentityData a w t) :
    s = t := by
  have hb : vertexBoundary a s = vertexBoundary a t := by
    have h' := congrArg Prod.fst h
    rwa [seatIdentityData_eq, seatIdentityData_eq] at h'
  rw [← univ_sdiff_vertexBoundary_eq a ha hs,
    ← univ_sdiff_vertexBoundary_eq a ha ht, hb]

/-- **Seat 2, the kill (Tier T1 — proved): determination
    fails in general.** Under the zero adjacency on `Fin 2`
    with the constant weight, the singleton regions `{0}` and
    `{1}` have IDENTICAL identity data — empty vertex
    boundary, equal region entropy — and are different
    regions. So the identity data do not determine a seat as
    a universal law; determination holds only under a named
    condition (the full-crossing form above).

    Proof route: both vertex boundaries are `∅` by
    `mem_vertexBoundary` (the zero adjacency has no nonzero
    entries); each restricted configuration over a singleton
    has exactly two extensions to a full configuration (the
    value at the other point is free — a `Finset.card_bij`
    count), so both marginals are the constant function `2`
    and both region entropies are `entropyW` of a constant-`2`
    weight on a two-element configuration type, with the same
    closed form. -/
theorem seatIdentityData_not_determining :
    ∃ (a : Fin 2 → Fin 2 → ℝ) (w : (∀ _ : Fin 2, Fin 2) → ℝ)
      (s t : Finset (Fin 2)),
      s ≠ t ∧ seatIdentityData a w s = seatIdentityData a w t := by
  -- Each restricted configuration over a singleton `{j}` in
  -- `Fin 2` has exactly two extensions to a full
  -- configuration: the value at the other point `k` is free.
  have fiber_card : ∀ (j k : Fin 2), k ≠ j →
      ∀ z : ∀ i : (↥({j} : Finset (Fin 2))), Fin 2,
      (Finset.univ.filter (fun y : Fin 2 → Fin 2 =>
        (fun i : (↥({j} : Finset (Fin 2))) => y i.1) = z)).card
        = 2 := by
    intro j k hjk z
    have hz : ∀ i : (↥({j} : Finset (Fin 2))),
        z i = z ⟨j, Finset.mem_singleton_self j⟩ := by
      intro i
      congr 1
      apply Subtype.ext
      exact Finset.mem_singleton.mp i.2
    have hcases : ∀ i : Fin 2, i = j ∨ i = k := by
      have h2 : ({j, k} : Finset (Fin 2)) = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [Finset.card_pair (fun h => hjk h.symm),
          Fintype.card_fin]
      intro i
      have hi : i ∈ ({j, k} : Finset (Fin 2)) := by
        rw [h2]; exact Finset.mem_univ i
      simpa using hi
    have hbij : (Finset.univ.filter (fun y : Fin 2 → Fin 2 =>
        (fun i : (↥({j} : Finset (Fin 2))) => y i.1) = z)).card
        = (Finset.univ : Finset (Fin 2)).card := by
      apply Finset.card_bij (fun y _ => y k)
      · intro y _
        exact Finset.mem_univ _
      · intro y₁ hy₁ y₂ hy₂ h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          at hy₁ hy₂
        funext i
        rcases hcases i with hij | hik
        · rw [hij]
          have e₁ : y₁ j = z ⟨j, Finset.mem_singleton_self j⟩ :=
            congrFun hy₁ ⟨j, Finset.mem_singleton_self j⟩
          have e₂ : y₂ j = z ⟨j, Finset.mem_singleton_self j⟩ :=
            congrFun hy₂ ⟨j, Finset.mem_singleton_self j⟩
          rw [e₁, e₂]
        · rw [hik]
          exact h
      · intro v _
        refine ⟨Function.update (fun _ => v) j
          (z ⟨j, Finset.mem_singleton_self j⟩), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ,
            true_and]
          funext i
          have hi : i.1 = j := Finset.mem_singleton.mp i.2
          show Function.update (fun _ => v) j
            (z ⟨j, Finset.mem_singleton_self j⟩) i.1 = z i
          rw [hi, Function.update_self]
          exact (hz i).symm
        · show Function.update (fun _ => v) j
            (z ⟨j, Finset.mem_singleton_self j⟩) k = v
          rw [Function.update_of_ne hjk]
    rw [hbij, Finset.card_univ, Fintype.card_fin]
  -- The marginal of the constant weight `1` over a singleton
  -- is the constant weight `2`.
  have marg : ∀ (j k : Fin 2), k ≠ j →
      margWeightSet (X := fun _ : Fin 2 => Fin 2)
          (fun _ => (1 : ℝ)) ({j} : Finset (Fin 2))
        = fun _ => 2 := by
    intro j k hjk
    funext z
    simp only [margWeightSet, Finset.sum_const,
      fiber_card j k hjk, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  -- Hence both singleton region entropies have the same
  -- closed form.
  have ent : ∀ j : Fin 2,
      regionEntropy (X := fun _ : Fin 2 => Fin 2)
          (fun _ => (1 : ℝ)) ({j} : Finset (Fin 2))
        = -(2 * (2 * Real.log 2)) := by
    intro j
    obtain ⟨k, hk⟩ : ∃ k : Fin 2, k ≠ j := by
      refine ⟨1 - j, ?_⟩
      fin_cases j <;> decide
    have hcard : Fintype.card
        (∀ i : (↥({j} : Finset (Fin 2))), Fin 2) = 2 := by
      simp [Fintype.card_pi]
    simp only [regionEntropy, marg j k hk, entropyW,
      Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul,
      Nat.cast_ofNat]
  refine ⟨fun _ _ => 0, fun _ => 1, {0}, {1}, by decide, ?_⟩
  simp only [seatIdentityData_eq, Prod.mk.injEq]
  constructor
  · have b0 : vertexBoundary (fun _ _ => (0 : ℝ))
        ({0} : Finset (Fin 2)) = ∅ := by
      ext x
      simp [mem_vertexBoundary]
    have b1 : vertexBoundary (fun _ _ => (0 : ℝ))
        ({1} : Finset (Fin 2)) = ∅ := by
      ext x
      simp [mem_vertexBoundary]
    rw [b0, b1]
  · rw [ent 0, ent 1]

end IdentitySeat

end ThetLogos
