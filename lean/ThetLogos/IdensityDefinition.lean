import Mathlib.Tactic
import ThetLogos.IdensityCoincidence
import ThetLogos.IdensityBoundary
import ThetLogos.SubsetMarginals
import ThetLogos.ModularVariance

/-!
# ThetLogos.IdensityDefinition — ID-4 (the reference-K port) and
# ID-3 (the Idensity definition itself)

**Lane-grade pin, built 2026-11-22 from the Phase A draft of
2026-11-21 (`lane-drafts/IdensityDefinition-draft.lean`,
notes `lane-drafts/id4-id3-draft-notes-2026-11-21.md`) on
Zero's fire word "build it" (2026-11-21 23:21 EST), on the
TridentityPin tip. NO CLAIM. Pre-registered DIAL-INELIGIBLE;
dials 0/4 under every outcome.**

Commissioned: Zero 2026-11-21 19:24–19:25 EST ("resume with
Idensity as well"); queue word — Zero, 2026-11-21 22:31–22:32
EST: "Queue ID-4 and ID-3 behind the seat pins." Scope of
record: `tridentity-build-scope-2026-11-21.md` (Group 2, §2,
§4, §5); primary record: `idensity-scope-2026-11-09.md`
(§§2–6). This module CITES ID-1 (`ThetLogos.IdensityCoincidence`),
ID-2 (`ThetLogos.IdensityBoundary`), H-1 (`ThetLogos.
SubsetMarginals`) and `ThetLogos.ModularVariance`; it restates
nothing (K-TRID-RESTATE).

**The term (Zero's coinage, 2026-11-09).** "Idensity" (Identity
Density) is the third term of Zero's symmetry-breaking ternary
— containment / identity / **Idensity** — defined by Zero,
verbatim: *"The concentration of invariant state information
and modular energy confined per unit boundary volume."* The
mechanism of the breaking was never stated by Zero and is not
glossed anywhere in this module (K-TRID-BREAK).

**The open joint, closed by Zero (2026-11-09):** the numerator
is the ordered **PAIR** (invariant state information,
reference-modular energy) — pair form, never a sum
(K-IDENSITY-DOUBLE stands). "Reference-modular" is the
reference-Hamiltonian reading of the 2026-11-09 scoping
(§§2.2/4, R4): the modular eigenvalues `modEigen E β` of a
REFERENCE energy function `E` (K_ref = βH + log Z·1 in
`ModularVariance`'s form), not the state's own modular
Hamiltonian — the two numerator components are genuinely two
only in this reading, and the own-modular degeneracy is
carried as a proved face (Bricks ID-4b, ID-3), never hidden.

**Zero's three ID-3 rulings (2026-11-21 EST) — the definition
below is built EXACTLY as ruled; a drift from any ruling is
a stop, not a repair (K-TRID-GATE residue):**
1. (22:27) PRIMARY FORM = the vertex boundary, card form:
   the denominator is `boundaryCard a s : ℕ`, cast to ℝ.
   The edge-cut weighted form (`cutWeight`) is the secondary
   form — built in ID-2, kept, not primary.
2. (22:28) EMPTY BOUNDARY = RESTRICT THE DOMAIN: Idensity
   is defined only at regions of nonempty boundary. The
   definition's region argument is therefore the subtype
   `{s : Finset κ // boundaryCard a s ≠ 0}` — at empty
   boundary the definition is SILENT: no stipulated value,
   no by-cases value, and no junk division value is ever
   presented as the definition's value. Every statement
   below is formed only over the subtype, so the
   nonempty-boundary hypothesis is on every face by
   construction.
3. (22:30, verbatim "re-pin with restriction" — REVERSED
   by Zero's ruling of 2026-11-22, 02:57 EST) "Invariant"
   was re-pinned at this seat, restricted to RELABELING
   invariance only; that restriction is reversed:
   "invariant" carries its FULL reading at this seat —
   relabeling, temporal, AND flow-based. The numerator's
   first component — "invariant state information" —
   means information invariant under relabeling of sites
   (the invariance component 1 carries through `entropyW`'s
   relabeling invariance at the marginal, scoping §2.4(c):
   `entropyW_comp_equiv` / `entropyW_comp_perm`, T1), and
   temporal and flow-based invariance belong to the
   definition's MEANING under the full reading. FACE
   NOTE, at full rank: the temporal and flow-based faces
   are meaning, NOT theorems — no temporal or flow
   invariance statement is proved in this module; the
   only invariance proved in this line is the relabeling
   invariance cited above.

**Fences on the face:** K-IDENSITY-PROXY (the denominator is
ID-2's genuine boundary card, never a bulk count),
K-IDENSITY-DIAL (no dial movement in either direction of
presentation; Dial 2 = 0), K-IDENSITY-DOUBLE (at an
own-modular seat the pair is (x, x) — stated as such below,
never "information plus energy"), K-IDENSITY-IMPORT (no
continuum modular theory: no Tomita–Takesaki, no type-III
language, no JLMS-style identifications), K-IDENSITY-LAUNDER
(this definition is not a gravity object, a response law, or
evidence about gravity), K-ID2-COUNT (ID-2's
counting-direction headline is an open literature problem,
not claimed).
-/

namespace ThetLogos

/-! ## Brick ID-4a — reference-K at the region seat: the port

From the 2026-11-09 scoping §6 (ID-4) and the tridentity
scope §3: `ModularVariance`'s `gibbsExpect` / `modEigen`
family, ported to the region configuration type
`(i : s) → X i`. The family is stated in-tree for an
arbitrary Fintype, so the port is form-preserving; what is
genuinely new here is the STATE the expectation is taken
against: not a Gibbs weight of the region energies, but the
region MARGINAL `margWeightSet w s` of an ambient weight
(H-1) — ⟨K_ref⟩ OF the region marginal, as the record names
it. The reference energy function `E` on region
configurations is handed in as declared input, as the
adjacency is in ID-2; choosing it is a design act, not a
theorem.

Section note: the `[∀ i, Nonempty (X i)]` instance is
carried so the region configuration type is nonempty where
the `ModularVariance` family asks for it. Phase B probe
(2026-11-22, uncontended, exit 0): `partSum` / `gibbsProb`
/ `gibbsExpect` / `modEigen` consume no `[Nonempty ι]`;
`gibbsExpect_affine` and `entropyW_gibbsProb_eq` do — and
at the region type `Nonempty (∀ i : s, X i)` is inferred
from this section's instance by Mathlib's Pi instance, so
the instance is needed, sufficient, and otherwise inert. -/

section RegionReferenceK

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*}
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)]

/-- **Expectation under the region marginal** (Tier T2 —
    definition): the expectation of an observable `Y` on
    region configurations against the marginal distribution
    `margWeightSet w s`. The port's expectation functional —
    `gibbsExpect`'s form with the marginal in the Gibbs
    weight's place. -/
noncomputable def margExpect (w : (∀ i, X i) → ℝ) (s : Finset κ)
    (Y : (∀ i : s, X i) → ℝ) : ℝ :=
  ∑ z, margWeightSet w s z * Y z

/-- The marginal expectation, unfolded. -/
theorem margExpect_eq (w : (∀ i, X i) → ℝ) (s : Finset κ)
    (Y : (∀ i : s, X i) → ℝ) :
    margExpect w s Y = ∑ z, margWeightSet w s z * Y z :=
  rfl

/-- Expectation of a constant is the constant times the
    marginal's total mass (Tier T1 — proved): the mass is
    carried explicitly, so no probability hypothesis is
    spent where none is needed. -/
theorem margExpect_const (w : (∀ i, X i) → ℝ) (s : Finset κ)
    (c : ℝ) :
    margExpect w s (fun _ => c)
      = (∑ z, margWeightSet w s z) * c := by
  unfold margExpect
  rw [← Finset.sum_mul]

/-- Under a probability weight the marginal's mass is `1`
    (H-1's `sum_margWeightSet`), so a constant's expectation
    is the constant (Tier T1 — proved). -/
theorem margExpect_const_of_isProbWeight (w : (∀ i, X i) → ℝ)
    (hw : IsProbWeight w) (s : Finset κ) (c : ℝ) :
    margExpect w s (fun _ => c) = c := by
  rw [margExpect_const, sum_margWeightSet, hw.2, one_mul]

/-- The marginal expectation is additive (Tier T1 —
    proved): the port of `gibbsExpect`'s linearity at the
    region seat. -/
theorem margExpect_add (w : (∀ i, X i) → ℝ) (s : Finset κ)
    (Y Z : (∀ i : s, X i) → ℝ) :
    margExpect w s (fun z => Y z + Z z)
      = margExpect w s Y + margExpect w s Z := by
  unfold margExpect
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun z _ => mul_add _ _ _)

/-- The marginal expectation is affine (Tier T1 — proved):
    `⟨a • Y + b⟩ = a • ⟨Y⟩ + b • (total mass)` — the port of
    `gibbsExpect_affine`, with the mass explicit; this is
    the linearity Brick ID-4b's β-form consumes. -/
theorem margExpect_affine (w : (∀ i, X i) → ℝ) (s : Finset κ)
    (Y : (∀ i : s, X i) → ℝ) (a b : ℝ) :
    margExpect w s (fun z => a * Y z + b)
      = a * margExpect w s Y
        + b * (∑ z, margWeightSet w s z) := by
  have hterm : ∀ z, margWeightSet w s z * (a * Y z + b)
      = a * (margWeightSet w s z * Y z)
        + b * margWeightSet w s z :=
    fun z => by ring
  show (∑ z, margWeightSet w s z * (a * Y z + b))
      = a * (∑ z, margWeightSet w s z * Y z)
        + b * (∑ z, margWeightSet w s z)
  calc (∑ z, margWeightSet w s z * (a * Y z + b))
      = ∑ z, (a * (margWeightSet w s z * Y z)
          + b * margWeightSet w s z) :=
        Finset.sum_congr rfl (fun z _ => hterm z)
    _ = a * (∑ z, margWeightSet w s z * Y z)
          + b * (∑ z, margWeightSet w s z) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum]

/-- **The region reference energy** (Tier T2 — definition):
    `⟨E⟩` of the reference energy function under the region
    marginal — the energy-side reading the β-form names. -/
noncomputable def regionRefEnergy (w : (∀ i, X i) → ℝ)
    (s : Finset κ) (E : (∀ i : s, X i) → ℝ) : ℝ :=
  margExpect w s E

/-- **⟨K_ref⟩ of the region marginal** (Tier T2 —
    definition): the expectation of the reference modular
    eigenvalues `modEigen E β` (K_ref = βE + log Z, in
    `ModularVariance`'s form) under the region marginal.
    This is numerator component 2 of Zero's pinned pair at
    the region seat, BEFORE the boundary division (the
    division is ID-3's, under Zero's rulings). -/
noncomputable def regionRefModularEnergy (w : (∀ i, X i) → ℝ)
    (s : Finset κ) (E : (∀ i : s, X i) → ℝ) (β : ℝ) : ℝ :=
  margExpect w s (ModularVariance.modEigen E β)

end RegionReferenceK

/-! ## Brick ID-4b — the port's faces

The β-form read at the region, and the own-modular
degeneracy face. Both are stated against the marginal as
the state; ID-1's assembled coincidence is CITED for the
own-modular face, never re-proved (K-TRID-RESTATE). -/

section RegionReferenceKFaces

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*}
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)]

/-- **The split, mass explicit** (Tier T1 — proved):
    `⟨K_ref⟩ = β • ⟨E⟩_marg + log Z • (total mass)` — the
    modular eigenvalue is the affine image `β • E + log Z`
    of the energy (`modEigen`), and `margExpect_affine`
    discharges it. The working form; the β-form below is
    its probability-weight face. -/
theorem regionRefModularEnergy_eq (w : (∀ i, X i) → ℝ)
    (s : Finset κ) (E : (∀ i : s, X i) → ℝ) (β : ℝ) :
    regionRefModularEnergy w s E β
      = β * regionRefEnergy w s E
        + Real.log (ModularVariance.partSum E β)
          * (∑ z, margWeightSet w s z) := by
  have h := margExpect_affine w s E β
    (Real.log (ModularVariance.partSum E β))
  unfold regionRefModularEnergy regionRefEnergy
  exact h

/-- **The β-form at the region** (Tier T1 — proved):
    `⟨K_ref⟩_β = β • ⟨E⟩_β + log Z`, read at the region
    seat — the analogue of `gibbsExpect_modEigen` (ID-1's
    engine) with the region marginal as the state and a
    probability ambient weight, so the marginal's mass
    is `1`. -/
theorem regionRefModularEnergy_beta_form (w : (∀ i, X i) → ℝ)
    (hw : IsProbWeight w) (s : Finset κ)
    (E : (∀ i : s, X i) → ℝ) (β : ℝ) :
    regionRefModularEnergy w s E β
      = β * regionRefEnergy w s E
        + Real.log (ModularVariance.partSum E β) := by
  rw [regionRefModularEnergy_eq, sum_margWeightSet, hw.2,
    mul_one]

/-- **The own-modular face at the region** (Tier T1 —
    proved): when the region marginal IS the Gibbs state
    of the reference energies, ⟨K_ref⟩ under the marginal
    is the region entropy — the pair's two components
    coincide. This is ID-1's assembled coincidence
    (`entropyW_gibbsProb_eq`) read at the region
    configuration type, composed with `regionEntropy`'s
    definition; nothing is re-proved. **K-IDENSITY-DOUBLE
    on the face:** at such a seat the honest statement is
    "the pair is (x, x)" — never "information plus
    energy" as two independent contributions. -/
theorem regionRefModularEnergy_eq_regionEntropy
    (w : (∀ i, X i) → ℝ) (s : Finset κ)
    (E : (∀ i : s, X i) → ℝ) (β : ℝ)
    (h : margWeightSet w s
      = ModularVariance.gibbsProb E β) :
    regionRefModularEnergy w s E β = regionEntropy w s := by
  unfold regionRefModularEnergy margExpect regionEntropy
  rw [h]
  show (∑ z, ModularVariance.gibbsProb E β z
      * ModularVariance.modEigen E β z)
    = entropyW (ModularVariance.gibbsProb E β)
  exact (entropyW_gibbsProb_eq E β).symm

end RegionReferenceKFaces

/-! ## Brick ID-3 — the Idensity definition itself

The definition, exactly as ruled (the three rulings are on
the module's face). The F1 rider comes first, per the
tridentity scope §3: the edge side's missing zero-boundary
face, closing the asymmetry the scope's §1 recorded — a
face-completion of ID-2's built work, stated here so the
asymmetry is never silently carried. -/

section IdensityDefinition

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*}
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)]

/-- **F1 — the edge side's full-region face** (Tier T1 —
    proved): the weighted boundary volume of the full
    region is `0` — the cut out of `univ` is empty, since
    no site lies outside it. The match of
    `boundaryCard_univ` on the weighted side (the scope's
    §1 asymmetry, closed). -/
theorem cutWeight_univ (a : κ → κ → ℝ) :
    cutWeight a Finset.univ = 0 := by
  unfold cutWeight
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [mem_edgeCut] at hp
  exact absurd (Finset.mem_univ p.2) hp.2.1

/-- **IDENSITY** (Tier T2 — definition): Zero's pinned
    quantity at Seat 2, in the reference-K PAIR form,
    exactly as ruled 2026-11-21:

    `idensity a w s E β =`
    `( regionEntropy w s / boundaryCard a s ,`
    `  ⟨K_ref⟩ of the region marginal / boundaryCard a s )`

    — the ordered pair (invariant state information,
    reference-modular energy), each component per unit
    boundary volume, never a sum. The denominator is the
    CARD form `boundaryCard` (ruling 1, primary), cast to
    ℝ. The region argument `s` ranges over the SUBTYPE of
    regions with nonempty boundary (ruling 2): at empty
    boundary this definition does not exist — it is
    silent there, and the subtype's membership proof
    `s.2 : boundaryCard a s.1 ≠ 0` is what licenses the
    division on every face below. "Invariant" carries its
    FULL reading (Zero's ruling of 2026-11-22, reversing
    the 2026-11-21 relabeling-only re-pin): relabeling,
    temporal, and flow-based. The temporal and flow-based
    faces are the definition's MEANING, not theorems — no
    temporal or flow invariance statement is proved in
    this module. The adjacency `a` and the
    reference energies `E` are declared inputs (ID-2's and
    ID-4's conventions); `β` is the reference inverse
    temperature. -/
noncomputable def idensity (a : κ → κ → ℝ) (w : (∀ i, X i) → ℝ)
    (s : {s : Finset κ // boundaryCard a s ≠ 0})
    (E : (∀ i : s.1, X i) → ℝ) (β : ℝ) : ℝ × ℝ :=
  (regionEntropy w s.1 / (boundaryCard a s.1 : ℝ),
   regionRefModularEnergy w s.1 E β / (boundaryCard a s.1 : ℝ))

/-- The information component, unfolded: the region
    entropy per unit boundary volume (card form). -/
theorem idensity_fst (a : κ → κ → ℝ) (w : (∀ i, X i) → ℝ)
    (s : {s : Finset κ // boundaryCard a s ≠ 0})
    (E : (∀ i : s.1, X i) → ℝ) (β : ℝ) :
    (idensity a w s E β).1
      = regionEntropy w s.1 / (boundaryCard a s.1 : ℝ) :=
  rfl

/-- The modular-energy component, unfolded: ⟨K_ref⟩ of
    the region marginal per unit boundary volume (card
    form). -/
theorem idensity_snd (a : κ → κ → ℝ) (w : (∀ i, X i) → ℝ)
    (s : {s : Finset κ // boundaryCard a s ≠ 0})
    (E : (∀ i : s.1, X i) → ℝ) (β : ℝ) :
    (idensity a w s E β).2
      = regionRefModularEnergy w s.1 E β
        / (boundaryCard a s.1 : ℝ) :=
  rfl

/-- The information component is nonnegative for a
    probability weight (Tier T1 — proved): the region
    entropy is nonnegative (H-1) and the boundary card,
    cast to ℝ, is nonnegative — a density of information
    is a nonnegative number wherever the definition
    speaks. (No sign is claimed for the energy component:
    the reference eigenvalues are signed in general, and
    this face does not invent one.) -/
theorem idensity_fst_nonneg (a : κ → κ → ℝ)
    (w : (∀ i, X i) → ℝ) (hw : IsProbWeight w)
    (s : {s : Finset κ // boundaryCard a s ≠ 0})
    (E : (∀ i : s.1, X i) → ℝ) (β : ℝ) :
    0 ≤ (idensity a w s E β).1 := by
  rw [idensity_fst]
  exact div_nonneg (regionEntropy_nonneg w hw s.1)
    (Nat.cast_nonneg _)

/-- **The own-modular face of the definition** (Tier T1 —
    proved): when the region marginal is the Gibbs state
    of the reference energies, the Idensity pair is
    `(x, x)` over the boundary — both components are the
    region entropy per unit boundary volume. **K-IDENSITY-
    DOUBLE, on the face:** this is the honest own-modular
    statement; the pair at such a seat is one number read
    twice, never two independent contributions, and never
    a sum. -/
theorem idensity_eq_of_marg_eq_gibbs (a : κ → κ → ℝ)
    (w : (∀ i, X i) → ℝ)
    (s : {s : Finset κ // boundaryCard a s ≠ 0})
    (E : (∀ i : s.1, X i) → ℝ) (β : ℝ)
    (h : margWeightSet w s.1
      = ModularVariance.gibbsProb E β) :
    idensity a w s E β
      = (regionEntropy w s.1 / (boundaryCard a s.1 : ℝ),
         regionEntropy w s.1 / (boundaryCard a s.1 : ℝ)) := by
  refine Prod.ext (idensity_fst a w s E β) ?_
  rw [idensity_snd]
  exact congrArg (· / (boundaryCard a s.1 : ℝ))
    (regionRefModularEnergy_eq_regionEntropy w s.1 E β h)

end IdensityDefinition

end ThetLogos
