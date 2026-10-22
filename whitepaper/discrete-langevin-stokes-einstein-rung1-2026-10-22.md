# Discrete Langevin brick — Stokes–Einstein Rung 1: STANDS (T1)

**Date:** 2026-10-22 · **Module:** `lean/ThetLogos/DiscreteLangevin.lean`
(namespace `ThetLogos.DiscreteLangevin`) · **Charter:**
`whitepaper/stokes-einstein-scoping-DRAFT-2026-10-18.md`, §5 Rung 1; §6
kills K1–K4 binding; §7 gate opened by Jeff's word, 2026-10-22 09:43 EDT.
**Status of the direction: NO CLAIM** beyond the exact finite identities
proved. Nothing here is a continuum, Brownian-motion, or Stokes-drag
statement.

## Verdict

**STANDS WHOLE at Rung 1** — the three quantitative targets stand as
stated; Target 3 stands in the exact pinned finite form the charter
itself requests (the advertised rate is the leading term of an exact
increment whose transient is stated on the theorem's face — not a
silent narrowing; the charter's §5 pins precisely this handling).

47 strict theorem/lemma declarations, 0 `@[simp]`, 0 sorry, 0 admits,
0 axiom declarations. Parent-verified: candidate byte-identical to the
built scratch source (md5 `5a80383cc3d8e2eafb500cfdb4028764`); own
comment-stripped scan 47/0/0/0; in-tree `lake build
ThetLogos.DiscreteLangevin` green (exit 0, `.olean` present); `#print
axioms` on the twelve headlines — exactly `[propext, Classical.choice,
Quot.sound]`.

## The model

One particle, discrete time, the damped kicked walker `v ← a·v + F + ξ`
in the smallest finite combinatorial model that carries it: kicks are
the two-point law `±σ`, paths are sign functions summed under the
uniform counting measure. Every probabilistic hypothesis the moment
theorems need — kicks of mean exactly 0, second moment exactly σ²,
distinct kicks exactly uncorrelated — is **computed** in the finite
model (the master orthogonality lemma `sum_sgn_mul_sgn`), not assumed.
Both walkers are defined by exact closed forms; the update rule is
then *proved* as a theorem (`vel_succ_cons`, `velS_succ`).

## Per-target verdicts

1. **Stationary velocity variance σ²/(1−a²) — STANDS.** Relaxation
   form `velVar_eq_div`: variance = stationary value + initial
   deviation damped by `a^(2n)`; one-step recursion `velVar_succ`
   (`Var ← a²·Var + σ²`) with fixed point `statVar_fixed`. Stationary
   regime `velS_var_stationary` (a² < 1): variance equals
   `statVar a σ = σ²/(1−a²)` at every time. Covariance kernel
   `velS_cov`: `E[(v_s − m*)(v_t − m*)] = a^(t−s)·V`.
2. **Mobility μ = 1/(1−a) — STANDS.** `expct_vel_stationary`:
   stationary-start mean is `m* = F/(1−a)` at all times;
   `mstar_eq_mobility`: `m* = mobility a * F`, `mobility a := 1/(1−a)`.
3. **Position-variance growth rate σ²/(1−a)² — STANDS IN PINNED
   FORM.** Exact displacement law `expct_dispS_sq`: `E[(dispS n)²] =
   V · posGrow a n`, with closed form `posGrow_closed`:
   `n·(1+a)/(1−a) − 2a(1−a^n)/(1−a)²`. The pinned increment
   `posVar_rate` (a² < 1): `Var(x_{n+1}) − Var(x_n) = σ²/(1−a)² −
   2a^(n+1)·statVar a σ/(1−a)` — the advertised rate is the exact
   leading term; the subtracted transient is the price of finiteness,
   on the face. The bare rate is the large-n limit, not an exact
   finite identity, and the module says so.
4. **Einstein form D = μ·Θ — STANDS.** `noiseTemp a σ := σ²/(2(1−a))`
   **defined** by the fluctuation–dissipation balance;
   `diffusivity a σ := σ²/(2(1−a)²)` pinned by the 1D convention
   ⟨x²⟩ grows by 2D per step; `einstein`: `diffusivity = mobility *
   noiseTemp` exactly; `two_mul_diffusivity`: `2D = σ²/(1−a)²`,
   tying the definition back to Target 3's measured constant;
   `posVar_rate_diffusivity` restates the increment as
   `2D − 2a^(n+1)·V/(1−a)`.

## Fences (charter §6) — all on the face

- **K1:** `noiseTemp` is a model parameter defined by the FD balance —
  never thermodynamic k_B T; its docstring carries the fence.
- **K2:** no ultrametric route anywhere.
- **K3:** `DiffusionDefect` is NOT imported (imports: `Mathlib.Tactic`
  only) and is cited nowhere as evidence; the shared finite-path
  pattern is technique, not evidence.
- **K4:** no continuum claim by vocabulary; header and the `einstein`
  docstring state the finite-toy scope.

Hypotheses ride on the faces of the theorems that use them
(stationary start; FD balance `σ² = (1−a²)·V`; `w² = V`).

## Census effect

Program census moves 3,460 → **3,507 strict** (3,500 → **3,547**
attribute-inclusive), 124 → **125 counted modules**.

## Not commissioned

Rung 2 (Green–Kubo finite form) and beyond remain uncommissioned; the
charter's ladder does not auto-advance.
