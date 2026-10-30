# VISC-2 LANDING — 2026-10-29

**Verdict: FULL.** Appended to `ThetLogos/ViscousLine.lean`
(VISC-2 adds strict 15 / defs 2; module totals strict 28 /
defs 3).

**NO CLAIM. Parts of any Millennium statement closed by this
landing: 0. Dials 0/4.**

## What landed — the general-Hermitian seat

For Hermitian K, the transported step
`stepGen K t X = heatKernelGen K t * X * (heatKernelGen K t)ᴴ`:

- **Self-adjointness** (`heatKernelGen_isHermitian`): the
  kernel of a Hermitian generator is self-adjoint (exp
  route: `(−t)•K` is Hermitian, and the exponential of a
  Hermitian matrix is Hermitian).
- **Eigenbasis multipliers** (`stepGen_eigenbasis`): on the
  eigenbasis units `F i j = U * single i j 1 * star U`, the
  step acts by the scalar `exp(−t·(dᵢ + dⱼ))` — VISC-1's
  matrix-unit spectrum, transported.
- **The bound and the ground line** (PSD scope):
  `stepGen_multiplier_mem_Ioc` — for `K.PosSemidef`,
  `t ≥ 0`, the multiplier lies in (0, 1];
  `stepGen_multiplier_eq_one_iff` — for `t > 0`, the
  multiplier is 1 iff `dᵢ = 0 ∧ dⱼ = 0`: the step is the
  identity exactly on the ground-eigenspace units and
  strictly contracting on every other eigenbasis unit.
- **The transported generator** (`genTransported K X =
  −(K * X + X * K)`; `hasDerivAt_stepGen_zero`): the
  step's derivative at 0, transported from VISC-1 through
  the eigendecomposition conjugation; and **dissipativity
  transported** (`genTransported_dissipative`): for PSD
  Hermitian K and Hermitian X,
  `Re tr (Xᴴ · genTransported K X) ≤ 0` — in the eigenbasis
  the trace is `−∑ i j, (dᵢ + dⱼ)·‖Y j i‖²`.

**The PSD hypothesis is load-bearing and is stated on the
face of every contraction statement.** For indefinite
Hermitian K the multipliers exceed 1 — that is where the
master kill K-VISC lives, and this brick's claims are
fenced to the PSD scope so the kill keeps a clean statement
to register against. **K-VISC does not fire inside the
stated scope** (vacuous by the eigenvalue facts), and
K-VISC-2 (transport obstruction) does not fire: the
transport carried at every joint — self-adjointness,
conjugation, generator, trace.

With VISC-1's and VISC-2's dissipativity in hand, the line
has earned its working name in the scoping's sense:
one-signed dissipation of the owned step, at the diagonal
seat and transported to every positive-Hermitian seat.
"Viscosity" remains Jeff's T5 gloss for that content —
the theorems are the content.

## Verification (parent, independent, from disk)

- Parent count of the whole module from disk: strict 28,
  defs 3. Census after this landing: **7,368 strict /
  7,446 attribute-inclusive / 251 counted modules** (from
  7,353 / 7,431 / 251 — an append).
- Main-tree build green (3,325 jobs). Parent axiom check
  on `genTransported_dissipative`: exactly
  `[propext, Classical.choice, Quot.sound]`.
- Parent grep: placeholder tactic, `native_decide`, banned
  signature word — 0 occurrences in the module.
- One pin seam, recorded on the file: whole-matrix
  `HasDerivAt.const_mul` hits a NormedRing instance
  diamond in this pin, so the derivative transport is
  entrywise (as VISC-1's was).

## Backers since last landing

No new backers recorded since the VISC-1 landing (earlier
today). The backers roll in `BACKERS.md` is unchanged.

## What this does not do

VISC-3 remains: the trace-defect closed form at the
diagonal seat (the relaxation bookkeeping), after which
the viscous line's priced path is complete. Nothing here
extends the claims beyond Hermitian PSD generators, and
nothing touches the normalized step — normalization can
push a slow coherence's multiplier past 1, which is why
the raw step is the line's permanent scope unless a future
brick fences the normalized step separately.
