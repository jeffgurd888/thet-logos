# Gauntlet: The Schrödinger Complex

**Date:** 2026-10-16. **Mode:** standard gauntlet — every claim pinned to
exactly one verdict, every verdict grep-evidenced. No Lean was built for this
dossier; it is a map, not a result.

**The gauntlet's rules.** Tiers: **T1** = proved in the corpus, zero sorrys;
**T2** = definition/interface; **T5** = quarantined (statement pinned,
content interpretive or unproved); **FIT** = the corpus already contains the
object, honestly labeled; **PARTIAL** = a proper part is T1, the rest named;
**PRICED** = not built, with a named price (size, dependencies, hard step);
**FRONTIER** = not priced in lines — blocked on infrastructure that does not
exist in Mathlib (2026); **KILL** = the claim is dead, by grep or
counterexample. A claim leaves with exactly one verdict.

**Scope.** Six claim-clusters: picture equivalence; the wavefunction;
Schrödinger dynamics (finite-dim and bosonic); the cat / measurement /
decoherence; the interpretations ledger; the Schrödinger equation as PDE.
Context of record: Pitch 3's scoping
(`pitch-3-interaction-scoping-DRAFT-2026-10-16.md`, §5) *cut* dynamics —
Schrödinger-picture spectral statements only, no unitary evolution. This
gauntlet re-examines that cut.

---

## Verdict table

| # | Claim | Verdict |
|---|---|---|
| 1 | Picture equivalence (Schrödinger/Heisenberg/interaction) is available at our finite-dim level | **PRICED** — not a theorem anywhere in the corpus today; becomes a corollary section of the dynamics build (§3a), +S |
| 2a | "The wavefunction" exists in the corpus (configuration-basis amplitudes) | **FIT (T1)** — the coefficient dialect *is* the wavefunction in the occupation basis |
| 2b | Wavefunction-first formulation: position-space L² wave mechanics, ψ(x,t), the PDE | **FRONTIER** — Schwartz arena T1 exists; an L² one-particle Hamiltonian does not (§6) |
| 3a | Schrödinger dynamics U(t) = e^{−itH}, finite-dimensional (incl. Pitch 3 C1's `hamInt`) | **PRICED — BUILDABLE**, module `SchrodingerDynamics.lean`, **M** (est. 450–700 lines) |
| 3b | Schrödinger dynamics, bosonic unbounded case | **PRICED (sectorwise, M) + FRONTIER (whole-space)** — split verdict, §3b |
| 4a | Superposition / the cat *state* in finite Fock spaces | **FIT (T1 triviality)** — states are vectors; nothing to prove |
| 4b | The measurement problem | **T5-quarantined** — no theorem shape (§4) |
| 4c | Decoherence, finite-dimensional toy | **PRICED — BUILDABLE (TOY)**, module `DecoherenceToy.lean`, **S–M** (est. 250–450 lines) |
| 5 | Interpretations (Copenhagen / many-worlds / QBism / wave realism / Bohm) | **T5-quarantined**, all five — corpus neutrality is by design (§5) |
| 6 | The Schrödinger equation as continuum PDE | **FRONTIER** — owned by Pitch 4; asset/gap ledger in §6 |
| K1 | "Picture equivalence / Schrödinger evolution of a corpus Hamiltonian is already proved" | **KILL** — dead by grep (§1, §3a) |
| K2 | "Finite-dimensional Stone's theorem is still an open gap in this corpus" | **KILL** — stale; discharged at Rung 7 (`StoneFiniteDim2.lean`) |

---

## 1. Picture equivalence

**Audit — what the corpus actually does.** Corpus-wide grep for
`Schrödinger|Heisenberg|interaction picture` returns *nothing* (the only
"picture" hits are prose: eigenbasis picture, represented picture,
geometric picture). No picture is ever named, defined, or compared.

The corpus's working dialect is nonetheless precisely locatable: states are
*vectors*, Hamiltonians are *operators* (`Module.End ℂ (FermionicFock d)`),
and spectral content is extracted as basis coefficients
(`FermionicInteraction.lean:72` `inner_fockBasis_left`, `:1006`
`hamInt_apply_coord`). That is Schrödinger-side bookkeeping — states carry
the structure, operators are fixed — adopted implicitly, never as a stated
choice. The one genuine *evolution* the corpus proves is Heisenberg-side:
`FlowKernel.lean:278` `flowAction` evolves *observables* by conjugation,
`B ↦ e^{−izH} B e^{izH}`, with the unitary built at `:184`
(`modularUnitary`, unitarity T1 at `:193`) — the modular flow, not a
Hamiltonian dynamics for a Fock Hamiltonian. And `StoneFiniteDim2.lean:245`
`stone_finiteDim` (T1) proves the abstract correspondence in the
group⇒generator direction: a strongly continuous unitary 1-parameter group
on a finite-dimensional space is diagonalized phases `exp (i·aₖ·t)` of a
skew-adjoint generator.

**Verdict: PRICED.** Picture equivalence at finite dimension *is* a
theorem-shaped claim — for a fixed Hermitian H, with U(t) = e^{−itH}:
Schrödinger evolution ψ(t) = U(t)ψ₀, Heisenberg evolution
A(t) = U(t)†AU(t), and the intertwining identity
⟪ψ(t), Aψ(t)⟫ = ⟪ψ₀, A(t)ψ₀⟫ are three corollaries of the group law +
unitarity + the derivative law — *once U(t) exists*. It does not exist yet
for any corpus Hamiltonian (K1 below). The equivalence is therefore not a
standalone build; it is the closing section of the §3a dynamics module
(+S, est. 100–150 lines on top of it): `heisenberg_evol`,
`heisenberg_equation` (dA/dt = i[H, A(t)]), `picture_equiv`. The
interaction picture (Duhamel/Dyson identity for H₀ + gV against the free
evolution) is a named stretch item of the same module, not part of the
landing.

**KILL K1 (first half).** Any present-tense claim that picture equivalence
is proved, or that the corpus "uses the Heisenberg picture" as a theorem —
dead by grep. The corpus is picture-*silent*; its dialect is
Schrödinger-side by convention and its one proved flow is modular, not
dynamical.

---

## 2. The wavefunction

**2a — FIT (T1).** In the occupation basis, the wavefunction is already the
corpus's native dialect; it was never missing, only never *named*.
Fermions: `FermionicFock d := EuclideanSpace ℂ (Finset (Fin d))`
(`FermionicFock.lean:45`), basis `fockBasis` (`:52`), and the coefficient
extraction `(fockBasis d S).ofLp U = if U = S then 1 else 0` (`:387`) *is*
the wavefunction ψ(S) — the amplitude of configuration S. Every spectral
theorem of Rungs 9–10 and Pitch 2–3 is stated in this dialect
(`inner_fockBasis_left`, `hamInt_apply_coord`,
`FermionicInteraction.lean:72,1006`; bosonic coefficient forms
`adagC`/`annC` in `BosonicAssembly.lean`, limit-basis coefficients in
`BosonicLimitOps.lean`). A "wavefunction-first" rewrite of what stands
would buy notation, not content: **no build recommended.**

**2b — FRONTIER.** Schrödinger's original wave mechanics — ψ ∈ L²(ℝ³),
H = −Δ + V as an unbounded operator, the PDE — is a different object, and
the corpus does not contain it. What exists toward it: the genuine Schwartz
arena 𝒮(ℝⁿ, ℂ) on Mathlib's `SchwartzMap`, with derivatives, polynomial
multiplication, tempered distributions, and Fourier inversion all T1
(`SchwartzSpace.lean:226` `schwartzFourier_inversion`; Rung 6). What does
not exist: L²(ℝ³) installed as a *one-particle space with a Hamiltonian* —
the corpus's one-particle spaces are finite (`Fin d`), abstract (`V` in
`FieldOperators.lean`, smeared creators T1 there), or the mass shell, whose
one-particle Poincaré representation is still an exact T5 window
(`PoincareAction.lean`, `OneParticleRep_window`). The Schrödinger
*functional* Ψ[φ] — the field's wavefunction — appears nowhere. Both belong
to §6's frontier, owned by Pitch 4.

---

## 3. Schrödinger dynamics

### 3a. Finite-dimensional — PRICED, BUILDABLE

**The honest surprise of this gauntlet: the module is three-quarters built
already, in pieces the program has not been crediting as dynamics assets.**

- `stone_finiteDim` (T1, `StoneFiniteDim2.lean:245`): the full
  finite-dimensional Stone theorem — group ⇒ skew-adjoint generator,
  diagonal form. Its Rung-6 ancestor supplied the analytic core T1
  (`StoneFiniteDim.lean` §1: `continuous_char_lift` — a continuous
  character ℝ → ℂ is `exp(iat)`), and Rung 7 discharged the ONB assembly
  (`jointSpectral_orthonormalBasis`, T1). **KILL K2:** the Rung-6 dossier's
  "honest gap" (full Stone unproved) is *stale* — do not quote it.
- `jointFC` (T1, `SpectralFrontier.lean` §1): a joint functional calculus
  for commuting symmetric families on finite-dimensional spaces —
  `jointFC_coordinate` is the spectral theorem in functional-calculus
  form. U(t) = jointFC applied to χ ↦ e^{−itχ} is a definitional step away.
- The exp pattern is already exercised on matrices: `FlowKernel.lean:184`
  `modularUnitary K s = NormedSpace.exp (i·s • K)` with unitarity proved
  via `Matrix.exp_conjTranspose` + `Matrix.exp_add_of_commute` (`:193`),
  and `KMSBridge.lean:92` proves the exp inverse law. Mathlib side (checked
  in the project checkout): `NormedSpace.exp_add_of_commute` for Banach
  algebras (the CLM algebra `H →L[ℂ] H` qualifies),
  `hasStrictFDerivAt_exp_smul_const_of_mem_ball`
  (`Mathlib/Analysis/SpecialFunctions/Exponential.lean`) — the derivative
  of exp along scalar multiples, even noncommutatively — and a full ODE
  library (`Mathlib/Analysis/ODE/PicardLindelof.lean`) if existence theory
  is ever wanted rather than the explicit formula.
- The target Hamiltonian stands: `hamInt` (`FermionicInteraction.lean:982`),
  symmetric for every coupling tensor (`hamInt_isSymmetric`, `:993`), on a
  space of finrank 2^d (`finrank_fermionicFock`, `:1094`), with gap
  persistence (`hamInt_gap_persistence`, `:1237`).

What is missing is exactly the assembly: no file defines U(t) = e^{−itH}
for a Fock Hamiltonian, proves its group law/unitarity *as an evolution*,
or proves dψ/dt = −iHψ for it. **Price: module
`SchrodingerDynamics.lean`, M, est. 450–700 lines** (calibration:
`FermionicInteraction.lean` is 1,303 lines for a four-task campaign; this
is one focused module porting proved patterns). Theorem inventory
(11 + 1 stretch):

1. `evolOp` — U(t) for a symmetric endomorphism of a finite-dimensional
   inner product space, via `NormedSpace.exp` on the CLM algebra
   (equivalently via `jointFC` phases; the spectral definition is the
   corpus-native route, the exp identification a theorem).
2. `evolOp_zero` — U(0) = 1.
3. `evolOp_add` — U(s + t) = U(s) ∘ U(t) (group law).
4. `evolOp_isometry` — U(t) is a linear isometry equivalence (unitarity).
5. `evolOp_apply_eigen` — on an H-eigenbasis, U(t) bₖ = e^{−itEₖ} • bₖ.
6. `hasDerivAt_evolOp_apply` — d/dt (U(t)ψ) = −i • H(U(t)ψ): the
   Schrödinger equation, finite-dimensional ODE sense.
7. `evolOp_solution_formula` — ψ(t) = Σₖ e^{−itEₖ} ⟪bₖ, ψ₀⟫ • bₖ, with
   uniqueness among C¹ curves satisfying the equation + initial condition.
8. `evolOp_hamiltonianDens` / `evolOp_hamInt` — instantiation to Pitch 3
   C1: the interacting evolution exists; spectral subspaces (in particular
   the persistence gap's two clusters of `hamInt_gap_persistence`) are
   U(t)-invariant.
9. `heisenberg_evol` — A(t) := U(−t) ∘ A ∘ U(t) is a one-parameter group
   of algebra automorphisms.
10. `heisenberg_equation` — d/dt A(t) = i • [H, A(t)] on the eigenbasis
    dialect.
11. `picture_equiv` — ⟪U(t)ψ, A U(t)ψ⟫ = ⟪ψ, A(t)ψ⟫ (the §1 landing).
12. *(stretch)* `interaction_picture_dyson_order1` — first-order Duhamel
    identity for `hamInt` against the free evolution.

This build *reverses* the Pitch 3 scoping §5 cut for the finite-dimensional
case: the cut was justified as "not needed for any gap statement" (true),
not as unbuildable (false). It remains a build order awaiting greenlight,
not a result.

### 3b. Bosonic unbounded — PRICED (sectorwise) + FRONTIER (whole-space)

Why the whole-space version waits, exactly: a unitary group on the full
bosonic Fock space with generator `hamIntBos` requires either the
unbounded spectral theorem / Borel functional calculus or unbounded Stone
— all absent from Mathlib (grep-verified in `SpectralFrontier.lean`'s
header audit: no projection-valued measures, no Borel functional calculus,
"everything unbounded" absent), and pinned in the corpus as the exact T5
statement `StoneUnbounded_sharp` (`StoneFiniteDim.lean:585`). There is no
honest line-count for that; it is Mathlib-infrastructure-shaped.
**FRONTIER.**

The priced intermediate is real, though. Pitch 3 Campaign 2's
`BosonicInteraction.lean` (in flight at audit time; final verdict is the
parent verification's, not this dossier's) lands the Hamiltonian
*sectorwise*: every particle sector is finite-dimensional, the restriction
is symmetric, hence diagonalizable (`hamIntBosSector_spectral`), and the
operator is a formal adjoint of itself as a partial linear map
(`hamPMap ≤ hamPMap†`) — essential self-adjointness explicitly *not*
claimed there. From sector spectral data alone, a **sectorwise dynamics
exhibit** is definable on the finite-particle domain: phases e^{−itE} per
sector, group law + unitarity *on Dom d*, Schrödinger equation sectorwise.
**Price: M, est. 400–600 lines, strictly downstream of Campaign 2's
verified landing.** The gauntlet **kills the upgrade** in advance:
sectorwise evolution on Dom d is not a unitary group on the bosonic Fock
space, and no text may call it one — the domain question (which vectors
the putative whole-space U(t) would even act on) is the FRONTIER content.

---

## 4. The cat, measurement, decoherence

**4a — Superposition: FIT (T1 triviality).** A state in the corpus *is* a
vector of the Fock space; a superposition is a sum of vectors; the corpus
uses them constantly (ground-state expansions in
`FermionicInteraction.lean:1138` `hamInt_inner_eq`; coherent
sector-spanning vectors in the bosonic limit modules). A "cat state"
ψ = (ψ₁ + ψ₂)/√2 across two sectors is a one-line inhabitant of the type.
There is no theorem to want here, and the gauntlet records the triviality
so nobody later sells it as a result.

**4b — The measurement problem: T5-quarantined.** The measurement problem
is not a statement about operators or vectors; it asks which
extra-formal postulate — collapse, branching, hidden variables, an
observer-relative fact — nature supplements the formalism with, and the
competing supplements are constructed to agree on every expectation value
the formalism computes. A Lean theorem is a consequence of stated
hypotheses, so formalizing any one supplement would prove that
supplement's consequences *given the supplement*: it would verify a
postulate's internal consistency, and could not, even in principle,
select among empirically equivalent ones. That is why the problem has no
theorem shape, and why it sits in T5 permanently — not as a dismissal, but
as a type classification.

**4c — Decoherence toy: PRICED, BUILDABLE.** Audit first. Density
matrices exist: `IsDensityMatrix` (`FlowKernel.lean:270` — Hermitian,
positive, trace one), with a Gibbs/KMS apparatus around them
(`flowAction` `:278`, `IsKMSFlow` `:288`). Operator tensor products exist
as a T1 toolkit (`ProductTriple.lean:265` `opTensor`, for spectral-triple
products), and Kronecker matrix products are Mathlib stock, already used
in the corpus (`ThreeGen.lean`, `smDirac3diag_eq_kronecker`). What does
*not* exist: **partial trace** — zero hits in Mathlib, zero in the corpus
— and no channel/purity vocabulary anywhere (grep `decoher|measurement`
over the corpus returns only prose accidents). **Price: module
`DecoherenceToy.lean`, S–M, est. 250–450 lines:** define partial trace at
the matrix level (block trace over Kronecker factors); a dephasing channel
as the diagonal pinching of a density matrix in a product basis; prove
populations invariant, off-diagonals killed by one application (geometric
decay under iteration), purity Tr ρ² non-increasing with equality iff
already diagonal, and the reduced state's diagonal = the system
populations. Labeled **TOY** in its header: finite-dimensional,
single-channel, no environment dynamics, and — per §4b — it models
decoherence's *arithmetic*, which is real and checkable, without touching
the measurement problem, which is not.

---

## 5. Interpretations ledger

The corpus's neutrality rule, stated once: **the corpus proves statements
about operators, vectors, and spectra; an interpretation is a story about
what those objects *mean*, chosen from a family of stories that agree on
every computed expectation; therefore no interpretation is T1-eligible,
none is needed by any rung, and none may be stated in the corpus's voice.**
Neutrality is a design feature — it is what keeps the theorem count
spendable at face value.

| Interpretation | Verdict | One line |
|---|---|---|
| Copenhagen (collapse on measurement) | **T5** | A postulate about measurement events; no operator in the corpus collapses, and none is missing for any theorem. |
| Many-worlds (unitary only, branching) | **T5** | The closest to the corpus's *formalism* (unitary evolution only) — which is a statement about the formalism, not evidence for the ontology. |
| QBism (states as agent beliefs) | **T5** | A stance on what ψ *is for an agent*; the corpus's ψ is a vector with proved properties, and the stance changes none of them. |
| Schrödinger's wave realism (ψ ontic, no jumps) | **T5** | Historically the author's own reading of §2b's object; the corpus has the finite-basis ψ (T1) and takes no position on its reality. |
| de Broglie–Bohm (particles + guiding wave) | **T5** | Adds trajectories the formalism doesn't compute; empirically equivalent by construction, hence unselectable by any theorem here. |

---

## 6. The Schrödinger equation as PDE — FRONTIER (Pitch 4)

**Placement.** Continuum wave mechanics belongs to Pitch 4 (continuum /
real Poincaré), and the gauntlet confirms that ownership: nothing in
Pitch 2 (limit of modes) or Pitch 3 (interaction at finite modes) is a
step *inside* this claim; they are orthogonal walls, as Pitch 3's scoping
§7 already states.

**Assets that pre-exist (T1 unless noted):** the Schwartz arena 𝒮(ℝⁿ, ℂ)
with derivatives, temperate growth, tempered distributions, Fourier
inversion (`SchwartzSpace.lean`, Rung 6); completeness results
(`SchwartzComplete.lean`, Rung 7); the finite-dimensional Stone core
(§3a); the mass shell with rotation invariance T1 and boost invariance
priced at a Jacobian identity (Rung 7); the geometric Poincaré action on
test functions T1 (`PoincareAction.lean`); the OS axioms + reconstruction
*pinned as exact T5 statements* (`OsterwalderSchrader.lean`) — the
Euclidean on-ramp constructive QFT actually uses, with reconstruction
unproved.

**The gap, exactly:** (i) no L²(ℝ³) one-particle Hamiltonian — −Δ as an
unbounded self-adjoint operator on L² is nowhere in the corpus, and its
unitary group is the unbounded-Stone content of `StoneUnbounded_sharp`
(T5); (ii) elliptic/PDE machinery: Mathlib (2026 checkout) has *incipient*
Sobolev material — Bessel-potential Sobolev spaces of tempered
distributions, Fourier-side (`Mathlib/Analysis/Distribution/Sobolev.lean`)
— but no elliptic regularity theory and no existence/uniqueness theory
for time-dependent Schrödinger equations, and the corpus uses none of it;
(iii) interaction in the continuum is Pitch 3's Route C, already deferred
to FRONTIER there (Haag-flavored representation change, renormalization).
**Verdict: FRONTIER** — not priced in lines; re-scoped only as part of
Pitch 4.

---

## BUILDABLE — awaiting greenlight

1. **`SchrodingerDynamics.lean`** — M, est. 450–700 lines. Finite-dim
   unitary evolution for the corpus's Hermitian Hamiltonians, incl.
   `hamInt`: group law, unitarity, eigenbasis phases, the Schrödinger
   ODE, solution formula + uniqueness, Heisenberg evolution + equation,
   and picture equivalence as the closing section (§1, §3a). Reverses
   the Pitch 3 §5 dynamics cut for the finite-dimensional case.
2. **`DecoherenceToy.lean`** — S–M, est. 250–450 lines. Matrix-level
   partial trace (new; absent from Mathlib), dephasing channel, purity
   decay — header-labeled TOY (§4c).
3. **Sectorwise bosonic dynamics** — M, est. 400–600 lines, *blocked on
   Pitch 3 Campaign 2's verified landing* (§3b). Domain-restricted by
   construction; the whole-space claim stays FRONTIER.

## T5 quarantine list (this complex)

`StoneUnbounded_sharp`, `JointSpectralCalculusUnbounded_sharp`
(`StoneFiniteDim.lean` §4) · `OneParticleRep_window`,
`SecondQuantization_window` (`PoincareAction.lean`) ·
`spectrumCondition_window` (`HaagKastlerFree.lean`) · the OS
reconstruction statement (`OsterwalderSchrader.lean`) · the measurement
problem and all five interpretations (§§4b, 5) · the Schrödinger
functional Ψ[φ] (§2b).

## Closing honesty

What this gauntlet changed: the dynamics exhibit moved from a scoping
footnote ("cut, §5") to a named, priced, inventory-listed build — because
the audit found its ingredients already proved and unassembled
(`stone_finiteDim`, `jointFC`, the `modularUnitary` exp pattern), which is
a different situation from the one the cut assumed. Two stale claims died
(K1, K2). Everything interpretive stayed exactly where the Concrete puts
it: T5, permanently, by type rather than by taste. And the bosonic wall
kept its shape: sectorwise yes, whole-space FRONTIER, no upgrades.
Nothing in this dossier is a theorem; it is the map Jeff asked for —
every road on it labeled with what it costs, what it proves, or why it
isn't one.
