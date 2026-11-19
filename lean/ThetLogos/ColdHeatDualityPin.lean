import ThetLogos.GibbsSpan
import ThetLogos.FiniteEntropy
/-!
# COLD-0 — documentation pin (DRAFT): the heat⇌cold design
# duality, its fired kills, and the frozen COLD-1/2/3 target
# forms

Queue position 27 (bench queue, QUEUE.md). Source of record:
`cold-heat-duality-scope-2026-11-09.md` (scoping LANDED
2026-11-09, Zero's commission 08:45 EST, fired for scoping
08:47 EST). This pin is the in-repo carrier of that
scoping's OG-0 Spec Note 7 (§5 of the scoping, as amended
by its §7).

## The lines being filed (verbatim, Register A / T5)

Zero, 2026-11-09 08:45 EST: *"if heat is a primitive and
it pushes cold must also be a primitive that pulls. is
cold gravity"*

Zero, 2026-11-09 08:49 EST: *"if heat is alone it must
have two actions push and pull -1 +1"*

Design content filed: HEAT and COLD stand as a primitive
duality of directions. Heat pushes: expansion, pressure,
spread toward uniformity. Cold pulls: contraction,
densification, concentration on the ground. The second
line reframes the first — ONE primitive (heat) carrying
both opposed actions as a signed pair. **Framing-invariance
(parent ruling, scoping §7): the two readings buy the SAME
mathematics** — one temperature/β axis, two directions
along it (heating → COLD-3's end; cooling → COLD-1's end).
The difference is Register-A bookkeeping only; no brick
in this line changes price, statement, or order under
either framing.

**Registered tension (rides with both framings):** the
"must" is a design preference, not a theorem. The corpus
holds a proved ONE-WAY law — FA-4b, the finite H-theorem:
entropy's drift does not reverse. A lone primitive with
symmetric ± actions is a bet against the second law's
shape; at our seats the pull direction exists as a DRIVEN
process (cooling done to a system), not as the system's
own drift. The COLD-1 forms below are statements about
Gibbs WEIGHTS as β varies — a comparison across
equilibria — not a claim that a system spontaneously
pulls itself cold.

## The grading travels attached — kills already fired

- **K-COLD-GRAVITY** — FIRED 2026-11-09 at read level.
  *"Cold is gravity"* is DEAD: cold is a state variable,
  not an agent; thermal energy itself gravitates, so a
  heated body pulls negligibly MORE, not less — the
  identity's sign is backwards. Dial 2 = 0.
- **K-COLD-SEAT** — FIRED in the scoping. *Cold as a
  second gravity primitive:* gravity's primitive seat is
  occupied by Gate B (UNITY, Register A, Zero's ruling
  2026-11-08); nothing in this line seats, rivals, or
  re-opens it.
- **K-COLD-PROXY** — FIRED in the scoping. *Contraction
  readings as evidence of a pull:* the modular gap
  widening (β·ΔE spacing, frozen below as a bookkeeping
  component of COLD-2) is a statement about a state's
  spectrum; no metric or space object exists at any
  finite seat to contract. The corollary survives,
  fenced; the interpretation is killed.
- **K-COLD-LIMITFLOW** — REGISTERED NOT-STATEABLE in the
  scoping. *The β→∞ limit of the modular flow ("cold
  clock"):* the limiting weight is a ground-set
  projection, not a Gibbs state at any β; the packaged
  `GibbsClock` requires finite β; rescaled flow time
  β·s has no finite limit. Design language only.

These kills are RECORD here — they are not re-derived in
this line, and no form below touches them.

## What this pin is

A documentation pin in the house pin pattern: definitions
and frozen statement forms ONLY — 0 theorems BY DESIGN.
It freezes (a) the seat vocabulary the COLD bricks share
(the partition sum as scoped, the normalized Gibbs weight
at the diagonal seat, the mean energy, the ground set),
and (b) the COLD-1 / COLD-2 / COLD-3 statement forms of
the scoping §4 as named Props, exactly the targets the
content bricks (queue positions 28–30) must discharge,
unchanged. Every brick in this line is pre-registered
DIAL-INELIGIBLE. Diagonal seat only: Hermitian/matrix
transport is unpriced and NOT included (scoping §4).

NO CLAIM; dials 0/4; Dial 2 = 0 on every outcome.
-/


namespace ThetLogos

open Filter Topology

/-! ## Seat vocabulary (frozen for the COLD bricks) -/

/-- The partition sum at the diagonal seat — the
scoping's `gibbsSum β E`: `∑ j, exp (−(β · E j))`.
(Positivity in-tree: `GibbsSpan.gibbsSum_pos`.) -/
noncomputable def coldPartition {N : ℕ} (β : ℝ) (E : Fin N → ℝ) :
    ℝ :=
  ∑ j, Real.exp (-(β * E j))

/-- The normalized Gibbs weight at inverse temperature
`β` for energies `E`: the corpus's `gibbsWeightsE` at
`logZ = log (coldPartition β E)`. -/
noncomputable def coldWeight {N : ℕ} (β : ℝ) (E : Fin N → ℝ) :
    Fin N → ℝ :=
  GibbsSpan.gibbsWeightsE β E (Real.log (coldPartition β E))

/-- Mean energy of the Gibbs weight: `⟨E⟩_β`. -/
noncomputable def coldMeanEnergy {N : ℕ} (β : ℝ) (E : Fin N → ℝ) :
    ℝ :=
  ∑ i, coldWeight β E i * E i

/-- The ground set of `E`: the indices whose energy is
minimal (≤ every energy). Total by construction — empty
iff `Fin N` is. -/
noncomputable def coldGround {N : ℕ} (E : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => ∀ j, E i ≤ E j)

/-! ## COLD-1 target forms — cold pull: ground-state
concentration (queue 28, priced M, est. 10–18 strict) -/

section ColdForms

variable {N : ℕ} [NeZero N]

/-- COLD-1 form 1 — the general Gibbs entropy identity
(generalizes `entropyW_z4Weight_eq` off the Z4 seat):
`S(β) = log Z(β) + β · ⟨E⟩_β`. -/
def Cold1EntropyIdentityForm : Prop :=
  ∀ (β : ℝ) (E : Fin N → ℝ),
    entropyW (coldWeight β E)
      = Real.log (coldPartition β E) + β * coldMeanEnergy β E

/-- COLD-1 form 2 — the entropy floor on the cooling
range: `log (card G) ≤ S(β)` for `0 ≤ β`, where `G` is
the ground set. (Frozen at `0 ≤ β`: the shifted-energy
proof route needs `β · ⟨E'⟩ ≥ 0`; the β < 0 mirror
belongs to the maximal set, not this line — disclosed
in STATUS-COLD0 §3.) -/
def Cold1EntropyFloorForm : Prop :=
  ∀ (β : ℝ) (E : Fin N → ℝ), 0 ≤ β →
    Real.log (coldGround E).card ≤ entropyW (coldWeight β E)

/-- COLD-1 form 3 — the exponential off-ground bound:
for `0 ≤ β`, any index `i`, and any ground index `m₀`,
`wᵢ(β) ≤ exp (−β · (Eᵢ − E_{m₀}))`. -/
def Cold1OffGroundBoundForm : Prop :=
  ∀ (β : ℝ) (E : Fin N → ℝ) (i m₀ : Fin N), 0 ≤ β →
    m₀ ∈ coldGround E →
    coldWeight β E i ≤ Real.exp (-(β * (E i - E m₀)))

/-- COLD-1 form 4 — the cold limits, β → ∞: total weight
on the ground set → 1; each off-ground weight → 0;
entropy → `log (card G)`. -/
def Cold1LimitForm : Prop :=
  ∀ (E : Fin N → ℝ),
    (Tendsto (fun β => ∑ i ∈ coldGround E, coldWeight β E i)
      atTop (nhds 1)) ∧
    (∀ i : Fin N, i ∉ coldGround E →
      Tendsto (fun β => coldWeight β E i) atTop (nhds 0)) ∧
    (Tendsto (fun β => entropyW (coldWeight β E))
      atTop (nhds (Real.log (coldGround E).card)))

/-! ## COLD-2 target forms — thermal response: cooling
orders (queue 29, priced M, est. 8–16 strict) -/

/-- COLD-2 form 1 — mean energy antitone in β
(unrestricted β range: `d⟨E⟩/dβ = −Var_β(E) ≤ 0` on the
whole axis). -/
def Cold2MeanEnergyAntitoneForm : Prop :=
  ∀ (E : Fin N → ℝ) (β₁ β₂ : ℝ), β₁ ≤ β₂ →
    coldMeanEnergy β₂ E ≤ coldMeanEnergy β₁ E

/-- COLD-2 form 2 — entropy antitone in β on `[0, ∞)`
(`dS/dβ = −β · Var_β(E) ≤ 0` exactly there). -/
def Cold2EntropyAntitoneForm : Prop :=
  ∀ (E : Fin N → ℝ) (β₁ β₂ : ℝ), 0 ≤ β₁ → β₁ ≤ β₂ →
    entropyW (coldWeight β₂ E) ≤ entropyW (coldWeight β₁ E)

/-- COLD-2 form 3 — the modular spacing corollary
(BOOKKEEPING, K-COLD-PROXY fence on its face: a spacing
in a state's log-spectrum, NOT a spatial contraction):
eigenvalue gaps of the Gibbs modular Hamiltonian equal
`β · (E j − E i)`, from `gibbsK_apply_diag`. -/
def Cold2ModularSpacingForm : Prop :=
  ∀ (β : ℝ) (E : Fin N → ℝ) (i j : Fin N),
    diagModularK (coldWeight β E) j j
        - diagModularK (coldWeight β E) i i
      = β * (E j - E i)

/-! ## COLD-3 target forms — hot push: uniformization at
the general seat (queue 30, priced S, est. 3–7 strict) -/

/-- COLD-3 form 1 — the hot limit of the weights,
β → 0: every weight → the uniform weight `1 / N`
(generalizes the Z4 seat's `z4Weight_zero`). -/
def Cold3UniformForm : Prop :=
  ∀ (E : Fin N → ℝ) (i : Fin N),
    Tendsto (fun β => coldWeight β E i) (nhds 0)
      (nhds ((N : ℝ)⁻¹))

/-- COLD-3 form 2 — the hot limit of the entropy,
β → 0: `S(β) → log N` (generalizes the Z4 seat's
`tendsto_entropyW_z4Weight`). -/
def Cold3EntropyLimitForm : Prop :=
  ∀ (E : Fin N → ℝ),
    Tendsto (fun β => entropyW (coldWeight β E)) (nhds 0)
      (nhds (Real.log N))

end ColdForms

end ThetLogos
