# Engine #12 (Spec): Finite-Lattice Kohn-Sham DFT — Digital Chemistry Prototype

**Status:** Scoping spec only (T5 → T4 pending implementation). 2026-09-27.
**Time box:** 1–2 days. If no falsifiable target survives, kill it and return to order-one.

## 1. The problem

"Digital chemistry" needs a concrete, honest entry point. The thet-logos
program has machine-verified particle-physics geometry (order-zero 144/144)
and a materials-effective-theory pipeline (Engine #11: FRG → constitutive
tensors). Neither directly computes a molecule. The missing layer is
**density functional theory** — the workhorse that turns electron density
into ground-state energies, the actual input to chemistry.

This spec defines the smallest falsifiable DFT prototype that earns the
name "Engine #12": Kohn-Sham DFT on a finite 1D lattice (Hubbard chain),
with the Hohenberg-Kohn mapping checked numerically and energies benchmarked
against exact diagonalization.

**What this is:** A T4 numerical methods prototype proving the pipeline
pattern extends to electronic structure.
**What this is not:** A new exchange-correlation functional, a drug-discovery
tool, a chemistry discovery, or a product. No molecule is "discovered" here.

## 2. Honest chain from Engine #11

| Engine #11 (FRG → materials) | Engine #12 (DFT → molecules) |
|---|---|
| Flows UV theory → mesoscale tensors | Flows electron density → ground-state observables |
| Slow variable: gauge field A_μ at k₀ | Slow variable: density n(r) |
| Integrates out: matter fluctuations | Integrates out: many-body wavefunction → density |
| Output: ε_eff(ω), μ_eff (device inputs) | Output: E_0, n_0(r) (chemistry inputs) |
| Validation: analytic Drude, Kramers-Kronig | Validation: exact diagonalization, Hohenberg-Kohn |

Both engines sit at the **effective-theory rung**: replace an intractable
microscopic description with a tractable slow variable, then verify the
replacement numerically. Engine #12 does not depend on Engine #11's outputs;
the chain is methodological, not data-flow. (A data-flow bridge — FRG-derived
tensors as DFT inputs — is T5 future work, not claimed here.)

## 3. Framework

### 3.1 The lattice system

The 1D Hubbard chain with L sites, N electrons, open boundaries:

$$H = -t \sum_{\langle ij\rangle,\sigma} c^\dagger_{i\sigma} c_{j\sigma}
     + U \sum_i n_{i\uparrow} n_{i\downarrow}
     + \sum_{i,\sigma} v_i\, n_{i\sigma}$$

- $t$: hopping (kinetic energy), $U$: on-site repulsion, $v_i$: external potential.
- This is the standard testbed for lattice DFT: exact diagonalization is
  available for small L (benchmark truth), and the BALDA functional
  (Bethe-Ansatz LDA) is the lattice analogue of continuum LDA.

### 3.2 Kohn-Sham construction

The Kohn-Sham system replaces interacting electrons with non-interacting ones
in an effective potential $v_s[n] = v + v_H[n] + v_{xc}[n]$ reproducing the
exact density. Self-consistency loop:

1. Guess density $n^{(0)}$.
2. Build $v_s[n^{(k)}]$, diagonalize single-particle problem → orbitals.
3. New density $n^{(k+1)}$ from occupied orbitals.
4. Iterate until $\|n^{(k+1)} - n^{(k)}\| < \tau$ (target $\tau = 10^{-10}$).

### 3.3 Hohenberg-Kohn check (the falsifiable core)

HK theorem: the ground-state density determines the external potential
(up to a constant). Numerical test — **potential inversion**:
given a target density $n^*$ from exact diagonalization, iterate a potential
$v$ until the KS density matches $n^*$. If two distinct potentials (differing
by more than a constant) produce the same density to tolerance, HK is violated
in the implementation → prototype fails.

## 4. Falsifiable targets (numbers, not adjectives)

| # | Target | Pass criterion | Tier if met |
|---|---|---|---|
| T1 | KS self-consistency converges | Density residual < 1e-10 within 200 iterations, for (L=6, N=6, U/t ∈ {0, 2, 4, 8}) | T4 |
| T2 | BALDA energy vs exact diagonalization | \|E_KS − E_exact\| / \|E_exact\| within known BALDA error envelope (≤ 5% for U/t ≤ 4; larger U documented as functional limitation, not code bug) | T4 |
| T3 | Hohenberg-Kohn inversion | Recovered potential matches true $v_i$ up to additive constant, max deviation < 1e-6, for at least 3 distinct test potentials | T4 |
| T4 | Dissociation analogue | 1D H₂ analogue (two-site, variable separation): energy curve shows correct qualitative minimum; quantitative error documented | T4 |

## 5. What kills it (falsification criteria)

- **Kill 1:** KS cycle fails to converge (T1) for the specified systems after
  reasonable mixing-scheme attempts (linear + Anderson). → The prototype's
  core loop is broken; stop.
- **Kill 2:** BALDA energies deviate from exact diagonalization far outside
  the documented LDA error envelope (T2), indicating implementation error
  rather than functional limitation. → Fix or stop; do not relabel as "new physics."
- **Kill 3:** Potential inversion finds a genuine counterexample to uniqueness
  (T3) that survives tolerance tightening. → This would be a real finding
  (more likely: a bug). Either way, the prototype as specified fails.
- **Kill 4 (scope):** If implementation exceeds the 2-day box without T1
  passing, shelve it. The spectral-triple program (order-one) is the priority.

## 6. Tier assessment (honest)

- **T4 if targets met:** Numerical DFT prototype on a lattice model system.
  Methods demonstration, not chemistry.
- **Permanently T5:** Any claim about real molecules, drug candidates,
  materials predictions, or "digital chemistry" as a product. This prototype
  computes Hubbard chains, not penicillin.
- **The funding story (honest version):** "We build verified computational
  pipelines. Engine #12 proves the pattern extends from field theory
  (Engines #9–11) to electronic structure. Verified methods are what industry
  pays for; this is step one, not the product."

## 7. Deliverables (if GO after spike)

1. `python/thet_logos/ks_dft_lattice.py` — KS solver, BALDA functional,
   exact-diagonalization benchmark, HK inversion test.
2. This whitepaper updated from spec → results.
3. Ledger entry (Rung 9c) with tier table.
4. Commit + push via API pipeline.

## 8. Explicit non-goals

- No continuum DFT (real-space grids, pseudopotentials) — lattice only.
- No new XC functional — BALDA from literature.
- No molecular geometry optimization, no reaction barriers.
- No claim that the finite spectral triple "derives" DFT — the triple is
  particle physics; DFT is effective theory. The bridge is methodological.
