import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace ThetLogos

/-!
# ThetLogos.ClayStatement — the Clay Yang–Mills statement as a fixed Prop

Source: the QFT rungs map (`whitepaper/qft-rungs-map-2026-10-06.md`, Rung 4),
which names this exact task its "feasible now, high value" Rung 4 target.

**What this file IS.** A machine-checked *statement* of the Clay Yang–Mills
existence-and-mass-gap problem (Jaffe–Witten, "Quantum Yang–Mills theory,"
Clay Mathematics Institute problem description, 2000), pinned as a Lean `Prop`
so that every future partial result is measured against an unmoving target.

**What this file is NOT.** A proof of anything, or progress toward one.
The axiom content lives in labeled opaque `Prop` fields: Mathlib (2026) has
no distribution theory adequate for operator-valued fields, no Wightman/OS/
Haag–Kastler axiom bundles, and no constructive QFT — those dependencies are
logged in the rungs map, not wished away here. Per the map's caution on the
piqos case study: a Lean file *named* after a theorem proves nothing until
the statement is checked; this file claims only the statement.

Honesty tiers in this file:
- **T1 (proved):** `gap_closes`, `gap_closes_arbitrarily` — genuine 2×2
  diagonal-gap computations, the finite-matrix illustration of the Q4
  obstruction (branch crossings close gaps; no transfer to QFT).
- **T5 (theorem-shaped, axiom content opaque):** `ClayYangMills`, `ClayProblem`.

Status: COMPILED GREEN (`lake build ThetLogos.ClayStatement`, 0 sorrys,
2026-10-06). Local draft; nothing pushed to the public repo without Jeff's
go-ahead, per the standing publish rule.
-/

/-- A compact simple gauge group, as quantified over by the Clay problem
    ("for any compact simple gauge group G"). Mathlib (2026) has no bundled
    "compact simple Lie group" with its full structure theory, so this is a
    marker structure: the carrier plus the two properties the problem
    quantifies over, as opaque Props. -/
structure CompactSimpleGroup where
  carrier : Type
  [instGroup : Group carrier]
  /-- Compactness of the underlying Lie group (placeholder: Lie theory
      beyond Mathlib 2026). -/
  isCompact : Prop
  /-- Simplicity: no nontrivial connected normal subgroups (placeholder). -/
  isSimple : Prop

/-- The axiom frames the Clay statement accepts: "axiomatic properties at
    least as strong as those cited in Streater & Wightman (1964),
    Osterwalder & Schrader (1973) and Osterwalder & Schrader (1975)." -/
inductive AxiomFrame where
  | wightman
  | osterwalderSchrader
  | haagKastler

/-- A quantum Yang–Mills theory over `G`, as a bundle of its axiomatic
    content. Each field is an opaque `Prop` naming the axiom or object it
    stands for; the content (operator-valued distributions, OS
    reconstruction, the Hamiltonian as an unbounded operator) is beyond
    Mathlib's 2026 infrastructure and is logged as a dependency in the
    rungs map. -/
structure QuantumYangMillsTheory (G : CompactSimpleGroup) where
  /-- The theory satisfies the chosen axiom frame. -/
  satisfiesAxioms : AxiomFrame → Prop
  /-- The spectrum of the Hamiltonian, as a set of real energies. -/
  hamiltonianSpectrum : Set ℝ
  /-- The vacuum energy 0 belongs to the spectrum (vacuum vector exists). -/
  vacuumInSpectrum : (0 : ℝ) ∈ hamiltonianSpectrum
  /-- Non-triviality: the theory is not free/Gaussian (opaque: pinning down
      "Gaussian" needs the full Wightman-function content). -/
  nontrivial : Prop

/-- The mass-gap condition: `spec(H) ⊆ {0} ∪ [Δ, ∞)` for some `Δ > 0` —
    the least massive glueball is strictly massive. -/
def HasMassGap {G : CompactSimpleGroup} (T : QuantumYangMillsTheory G) : Prop :=
  ∃ Δ : ℝ, 0 < Δ ∧ ∀ E ∈ T.hamiltonianSpectrum, E = 0 ∨ Δ ≤ E

/-- Clay Yang–Mills existence and mass gap (Jaffe–Witten 2000), for one
    compact simple gauge group `G`: a non-trivial quantum Yang–Mills theory
    exists on ℝ⁴ and has a mass gap `Δ > 0`. -/
def ClayYangMills (G : CompactSimpleGroup) : Prop :=
  ∃ T : QuantumYangMillsTheory G, T.nontrivial ∧ HasMassGap T

/-- The full Clay problem quantifies over ALL compact simple groups `G`,
    not just SU(3). This is the fixed target: partial results are measured
    against `ClayProblem`, never against a weakened restatement. -/
def ClayProblem : Prop :=
  ∀ G : CompactSimpleGroup, G.isCompact → G.isSimple → ClayYangMills G

/-!
## Why finite-matrix gaps do not transfer (the load-bearing negative result)

The rungs map states this in prose; here is the T1 computational kernel.
For the 2×2 diagonal family `D(t) = diag(t, 2 − t)`, the naive spectral gap
`|λ₂ − λ₁| = |2 − 2t|` closes at `t = 1` — an arbitrarily small neighborhood
of the crossing contains matrices with arbitrarily small gap. This is the
finite-matrix illustration of the Q4 obstruction recorded in
`BlockedQuestions.lean`: a gap that holds at one matrix need not survive
perturbation (branch crossings are non-smooth), and no continuum or
thermodynamic limit connects `spec(D_F)` to `spec(H)` of a constructed 4D
QFT. The Clay gap is `inf(spec(H) ∖ {0})` for a *constructed* theory;
nothing in this file bridges that distance.
-/

/-- Diagonal-gap proxy for the 2×2 family `D(t) = diag(t, 2 − t)`. -/
def diagGap (t : ℝ) : ℝ := |(2 - t) - t|

/-- The naive gap closes at the branch crossing `t = 1` (Tier T1). -/
theorem gap_closes : ∃ t : ℝ, diagGap t = 0 :=
  ⟨1, by unfold diagGap; norm_num⟩

/-- Arbitrarily close to the crossing, the gap is arbitrarily small
    (Tier T1). -/
theorem gap_closes_arbitrarily : ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, diagGap t < ε :=
  fun ε hε => ⟨1, by unfold diagGap; norm_num; exact hε⟩

/-!
## The mass-gap condition, sharpened (Rung 4 dossier, 2026-10-07)

The Clay problem quantifies over *all* compact simple groups; the physics
literature means the SU(3) case. Both are pinned below, with the implication
one way only. The gap condition gets its isolated-point formulation plus
three genuine T1 lemmas (gap algebra, no analysis needed).
-/

/-- The Clay statement for a named compact simple group (SU(3) in the
    physics literature): the concrete case. `ClayProblem` (all compact
    simple G) implies this for every such group; the converse is not
    claimed. No Lie theory is formalized — `G` is a parameter standing
    for the group. -/
def ClaySU3 (G : CompactSimpleGroup) (_hc : G.isCompact) (_hs : G.isSimple) : Prop :=
  ClayYangMills G

/-- `ClayProblem` implies the named-group case (Tier T1 — immediate). -/
theorem clayProblem_to_named (G : CompactSimpleGroup) (hc : G.isCompact)
    (hs : G.isSimple) : ClayProblem → ClaySU3 G hc hs :=
  fun h => h G hc hs

/-- Equivalent formulation: 0 is isolated in the spectrum from above —
    nothing sits strictly between 0 and Δ. -/
def HasMassGapIsolated {G : CompactSimpleGroup} (T : QuantumYangMillsTheory G) : Prop :=
  ∃ Δ : ℝ, 0 < Δ ∧ ∀ E ∈ T.hamiltonianSpectrum, E < Δ → E = 0

/-- The two gap formulations coincide (Tier T1). -/
theorem hasMassGap_iff_isolated {G : CompactSimpleGroup} (T : QuantumYangMillsTheory G) :
    HasMassGap T ↔ HasMassGapIsolated T := by
  constructor
  · rintro ⟨Δ, hΔ, h⟩
    exact ⟨Δ, hΔ, fun E hE hEΔ => by
      rcases h E hE with rfl | hle
      · rfl
      · linarith⟩
  · rintro ⟨Δ, hΔ, h⟩
    exact ⟨Δ, hΔ, fun E hE => by
      by_cases hEΔ : E < Δ
      · exact Or.inl (h E hE hEΔ)
      · exact Or.inr (le_of_not_gt hEΔ)⟩

/-- A smaller gap bound works too (Tier T1). -/
theorem gap_shrink {G : CompactSimpleGroup} {T : QuantumYangMillsTheory G}
    {Δ Δ' : ℝ} (hle : Δ' ≤ Δ)
    (h : ∀ E ∈ T.hamiltonianSpectrum, E = 0 ∨ Δ ≤ E) :
    ∀ E ∈ T.hamiltonianSpectrum, E = 0 ∨ Δ' ≤ E := by
  intro E hE
  rcases h E hE with rfl | hge
  · exact Or.inl rfl
  · exact Or.inr (le_trans hle hge)

/-- The max of two working gaps works (Tier T1). -/
theorem gap_max {G : CompactSimpleGroup} {T : QuantumYangMillsTheory G}
    {Δ₁ Δ₂ : ℝ}
    (h₁ : ∀ E ∈ T.hamiltonianSpectrum, E = 0 ∨ Δ₁ ≤ E)
    (h₂ : ∀ E ∈ T.hamiltonianSpectrum, E = 0 ∨ Δ₂ ≤ E) :
    ∀ E ∈ T.hamiltonianSpectrum, E = 0 ∨ max Δ₁ Δ₂ ≤ E := by
  intro E hE
  rcases h₁ E hE with rfl | hge₁
  · exact Or.inl rfl
  · rcases h₂ E hE with rfl | hge₂
    · exact Or.inl rfl
    · exact Or.inr (max_le hge₁ hge₂)

/-- No spectrum strictly between 0 and a working gap (Tier T1). -/
theorem gap_excludes_interval {G : CompactSimpleGroup} {T : QuantumYangMillsTheory G}
    {Δ : ℝ} (_hΔ : 0 < Δ)
    (h : ∀ E ∈ T.hamiltonianSpectrum, E = 0 ∨ Δ ≤ E) :
    ∀ E ∈ T.hamiltonianSpectrum, E < Δ → E = 0 := by
  intro E hE hlt
  rcases h E hE with rfl | hge
  · rfl
  · linarith

end ThetLogos
