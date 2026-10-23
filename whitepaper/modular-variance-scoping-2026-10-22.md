# ModularVariance — the distance-from-the-void dial (scoping charter)

Commissioned by Jeff, 2026-10-22 23:10 EDT ("Let's build this the
right way — no q-toy hacks, no clamping, and no circular Lean
axioms"), salvaged from two audited dropped packages the same evening
(verdicts HOLD, on file in the daily log). The salvageable core, in
Jeff's formulation, endorsed in the audit reply: for a finite Gibbs
state with modular Hamiltonian K, **Var(K) = β² · Var(E)** — variance
as the exact distance-from-the-void dial, anchored to the thermal
fluctuation response. This charter builds that statement on
corpus-native objects only.

## Objects (all landed; import unmodified)

- `TeslaVortexMultiSector`: the finite Gibbs weights behind `sepN` —
  expectation under the Gibbs state at energies E : ι → ℝ, inverse
  temperature β, over a finite nonempty ι.
- `GibbsSpan`: `diagModularK = β•diag(E) + logZ•1` — the modular
  Hamiltonian of the Gibbs state is βE plus a scalar.
- `NullStart` (landed 2026-10-22): the degenerate state is the unique
  fully silent state. This brick gives that state a measurement.

## Targets (pre-registered)

- **T1 — The identity.** Var_β(K) = β² · Var_β(E), where Var_β is
  variance under the finite Gibbs state and K is taken in GibbsSpan's
  proved form (eigenvalues β·Eᵢ + log Z; a scalar shifts no variance).
  Route (eigenvalue-level, via the GibbsSpan diagonal form, or
  matrix-level if the builder finds it shorter) is the builder's
  choice; the route taken is reported.
- **T2 — Non-negativity, derived.** Var_β(E) ≥ 0 proved from first
  principles — the sum-of-squares form Σᵢ pᵢ(Eᵢ − Ē)² with pᵢ > 0 at
  finite β — never assumed, never a structure field. (This is the
  exact point both dropped Lean stubs assumed away; it is the
  brick's reason to exist.)
- **T3 — The dial reads the void.** At finite β: Var_β(E) = 0 ⟺ all
  energies equal (∀ i j, E i = E j); hence Var_β(K) = 0 ⟺ the
  degenerate state — NullStart's silent state — and Var_β(K) > 0 ⟺ a
  gap exists. The dial is faithful both directions.
- **T4 — Fluctuation response (stretch; PARTIAL pre-registered).**
  d/dβ ⟨E⟩_β = −Var_β(E): the mean energy's β-derivative is minus
  the variance. Finite sums of exponentials; if the derivative
  machinery prices out of the build, T4 lands PARTIAL with the
  obstruction named, T1–T3 unaffected.

## Fences

- **K-MV1.** Finite Gibbs states only. "Modular Hamiltonian" here is
  the corpus's finite `diagModularK` in GibbsSpan's form — not the
  Tomita–Takesaki modular operator of a von Neumann algebra. The
  house usage is on the module's face.
- **K-MV2.** No heat-kernel coefficients anywhere in this brick: no
  a₀/a₂, no C_v "derived" from them (that chain died in the package
  audits, 2026-10-22). If a heat-capacity analog is named, it is
  β²·Var_β(E) itself — defined here, not extracted.
- **K-MV3.** No q-deformation, no non-Hermitian operators, no
  clamping: every quantity is computed from a genuine state
  (positive Gibbs weights), and a negative variance intermediate is
  a build failure, not a rounding instruction.

## Price and slot

S–M (one module; T4 is the swing factor). Queue: behind the
Pre-Option-A representation build (ratified, in the kiln), ahead of
the Ghys filler. Candidate only; parent verifies and lands.
