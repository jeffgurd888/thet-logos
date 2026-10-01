# Toward unified modular dynamics of thermal entropy: emerging phase space-time from spectral triples, Cartesian quantum to cosmos vortices

*Status note — updated 2026-09-30. Title adopted 2026-09-30 (Jeff's approval)
after gauntlet review: "Toward" governs the whole title as research direction;
"emerging" (not "emergent") marks phase space-time as under investigation, not
achieved; "temporal" was cut as redundant (modular dynamics is already
temporal). Title terms: "Cartesian quantum" = the finite quantum (matrix)
regime of the campaign's spectral triples — the \(\mathbb{C}^{32}\) finite
triple and its inner fluctuations; "cosmos vortices" = the large-scale
structured flows the vision aims at, currently Tier-5 language with no theorem
behind it. This revision keeps the original essay's
conclusions intact and updates its campaign citations to the unified numbering:
**SA numbers are the master** (see `spectral-action-campaign-scope.md` §5 for
the G↔SA concordance). The original draft cited G1/G4/G5 from the campaign
document; those now read SA-1/SA-3/downstream.*

These four notions can be placed side-by-side, but they are not yet fused into a
single working theory. Here is the precise status of each and of their possible
intersections.

### 1. Spectral triple

A spectral triple \((\mathcal{A},\mathcal{H},D)\) encodes a (possibly
noncommutative) geometry in the spectrum of a Dirac-type operator \(D\). In the
almost-commutative case relevant to the Standard Model one takes the product of
an ordinary 4-manifold with a finite spectral triple. In the Chamseddine–Connes
construction, the spectral action
\(\operatorname{Tr}f(D_A/\Lambda)\) then yields, via the heat-kernel expansion,
both gravitational and gauge+Higgs terms (literature result, not proved in this
campaign). This is the geometric starting point of the campaign.

### 2. Thermal entropy and modular dynamics

Given a thermal (KMS) state \(\omega\) on a von Neumann algebra, the
Tomita–Takesaki theory produces a modular operator \(\Delta_\omega\) and a
modular automorphism group

\[
\sigma_t^\omega(a)=\Delta_\omega^{it}a\Delta_\omega^{-it}.
\]

This one-parameter group is often called modular time or modular flow. The
relative entropy between states and the modular Hamiltonian are tightly linked
to thermodynamic entropy. In the algebraic approach to quantum field theory the
modular flow of a local algebra with respect to the vacuum (or a thermal state)
is a well-defined mathematical object.

### 2.1. The one machine-checked foothold (this campaign)

The essay above describes the general theory. This campaign owns exactly one
formal foothold on modular dynamics, and the status note should name it:
`eigenvalue_rigidity` and `modularFlux_selfAdjoint`, proved in
`ModularTime.lean` (Tier T1, zero sorrys, local — not pushed). For \(D\)
hermitian with \(Dv = \lambda v\), \(\langle v|\phi|v\rangle = 0\) where
\(\phi = i[K,D]\) with \(K = -\ln\rho\) the synthesized modular Hamiltonian:
first-order eigenvalue rigidity — spectral *flow*, not spectral deformation.
It is a foothold, not a bridge: it constrains what modular flow can do to the
finite spectrum, and proves nothing about spacetime time.

### 3. Phase space-time

Ordinary classical mechanics has a phase space \(T^*Q\). Relativistic physics
has spacetime \(M\). "Phase space-time" is not a standard term; it usually
signals an attempt to treat space, time and conjugate momenta on a more equal
footing (covariant phase space, polysymplectic geometry, etc.). In the spectral
setting one does not begin with a phase space; one begins with an algebra of
observables and a Dirac operator.

### 4. The missing bridge

The campaign scope lists explicitly as a **non-claim**:

> a bridge from modular time to spacetime time.

Modular flow is an algebraic automorphism group extracted from a state.
Spacetime time is the geometric parameter that appears in the metric of the
manifold factor of a spectral triple. No theorem currently identifies the two,
nor derives one from the other inside the almost-commutative framework. Thermal
entropy appears in both pictures (von Neumann entropy of the state,
thermodynamic entropy of horizons or of the cosmological fluid), but that does
not automatically turn modular flow into a hydrodynamic or geometric time.

### What a synthesis would require

To turn the four-word phrase into a concrete construction one would need at
least:

- a spectral triple whose Dirac operator (or whose state) produces a modular
  flow,
- a controlled limit or duality that recovers an ordinary Lorentzian metric,
- a demonstration that the modular Hamiltonian generates the same proper-time
  flow that the metric defines for observers,
- a derivation of the Einstein–Hilbert term (or its thermodynamic equivalent)
  from the same data.

None of these steps has been completed. They remain open research questions that
sit downstream of the campaign as a whole — in dependency order: the finite
spectral moments (SA-1); the algebraic \(a_2\) identity (SA-2) and the
gauge-orbit audit (SA-5) in parallel; the continuum-gap assessment (SA-3); the
finite spectral action (SA-4); and the foundational audits,
real-structure/orientability (SA-6) and Poincaré duality (SA-7).

### Precedents (added in this revision)

Two results are the closest anyone has come to the bridge, and belong in this
status note:

- **Bisognano–Wichmann:** for a Rindler wedge, the vacuum modular flow *is*
  geometric time — exactly Lorentz boosts. The existence proof that the
  identification can happen; not yet inside the almost-commutative framework.
- **Jacobson (1995; 2015 entanglement version):** Einstein's equations derived
  from thermodynamics / entanglement equilibrium. The live "thermodynamic
  equivalent" route; also still outside the framework.

### Summary

A spectral triple supplies geometry; a thermal state on its algebra supplies
modular dynamics and entropy; phase-space ideas remain optional and
non-standard. The phrase "modular dynamic thermal entropy phase space-time
spectral triple" therefore names an attractive research horizon, not an existing
theorem. The next rigorous steps are still the ones the campaign lists, in
dependency order: the exact finite moments (SA-1); the algebraic \(a_2\)
identity (SA-2) and the gauge-orbit and stability audit (SA-5) in parallel; the
continuum-gap assessment whose hard output is the explicit
`ContinuumSpectralActionHypotheses` interface (SA-3); the finite spectral action
for explicit cutoff classes (SA-4); and the foundational audits, real structure
and orientability (SA-6) and Poincaré duality (SA-7) — and only then any
attempt to link modular flow to geometric time.

### Numbering note (added in this revision)

On 2026-09-30 the campaign's phase numbering was unified: SA numbers are the
single master. The campaign document's G0/G1/G2/G3/G4/G5 and the gap catalog's
G2/G3 are frozen to SA equivalents in `spectral-action-campaign-scope.md` §5.
Note the known collision: bare "G2"/"G3" is ambiguous across the two source
documents (gauge-orbit audit vs. real structure; finite spectral action vs.
Poincaré duality) — always cite the `gap-cat` prefix for gap-catalog items, or
better, the SA number.
