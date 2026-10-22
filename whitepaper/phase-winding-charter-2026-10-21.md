# Phase-Winding Brick — Charter Draft (2026-10-21)

> **STATUS UPDATE (2026-10-22): COMMISSIONED by Jeff 2026-10-22 18:41 EDT
> ("Commission the winding brick (lift-first, A)") and LANDED the same
> evening — STANDS WHOLE (T1), module `ThetLogos.PhaseWinding`,
> dossier `whitepaper/phase-winding-brick-2026-10-22.md`. Route B
> remains unbuilt. The text below is the charter as drafted.

**Status: COMMISSIONED AND LANDED 2026-10-22** (see status update below the title). Prepared 2026-10-21 after Jeff's
afternoon sequence (Abrikosov vortices → winding bricks/blocks → compound knots
and strings → thermal acoustic strings and knots). The main agent named this as
the one buildable door and stated it "enters only on your word." Jeff has not
given that word. This charter exists so that one word, if it comes, starts a
build instead of a scoping session.

**Charter tier: NO CLAIM.** Cabinet tier, same shelf as FluxTwist. Not a rung
on the Yang–Mills ladder, no credit toward Δ, no Abrikosov vortex, no knot
theory, no phonon/acoustics content.

## What the brick is

The finite, honest atom underneath vortex talk: **phase winding around a
ring, counted by an integer.**

Existing anchor (T1, stands): `FluxTwist.lean` (582 lines, 38 theorems,
0 sorry; dossier `whitepaper/flux-twist-2026-10-16.md`). Its eigenphases are
(θ + 2πm)/(n+1) — flux enters the spectrum only through winding, and the
Fourier mode index m is, in everything but name, a winding number. This brick
names and proves that integer directly, instead of letting it ride inside an
eigenphase formula.

## The definition debt (Rung 1 — this is the real cost)

Winding needs a *lift*: real numbers Θ_k with u_k = exp(iΘ_k) at each site.
Two candidate formalizations, priced honestly:

- **A. Lift-first (RECOMMENDED for the core).** A configuration *is* a lift:
  increments d_k = Θ_{k+1} − Θ_k for k on the ring `Fin (n+1)`, with the wrap
  increment closing to Θ_0 + 2πw. The winding number w ∈ ℤ is part of the
  data and the theorems are about how w behaves. Cheap to state, algebraic
  to prove. Cost: w is a property of the lift, and the bridge to "w is a
  property of the phase configuration itself" is a separate, later clause.
- **B. Principal-argument (STRETCH, not core).** Define w from a unit-modulus
  configuration u : Fin (n+1) → ℂ by summing principal-branch increments.
  Canonical, but needs the branch-cut analysis and an exclusion for
  antipodal edges (consecutive phases exactly opposite, where the principal
  increment is ambiguous). Priced M, analysis-heavy. NOT in the core scope.

## Core theorems (Definition A; priced S–M total)

1. **Compound = sum.** Winding adds under pointwise addition of lifts:
   w(Θ + Φ) = w(Θ) + w(Φ). (Jeff's "compound" point, exact: compound
   windings are sums in ℤ — nothing tangles, nothing hides.)
2. **Gauge invariance.** Shifting a lift by a *single-valued* real function
   α (α periodic on the ring) changes every increment by α_{k+1} − α_k,
   which telescopes to zero around the ring: w is unchanged.
   Global phase rotation is the constant-α corollary.
3. **Phase slip = the only door.** Shifting by an α whose wrap mismatch is
   α_wrap − α_0 = 2πs changes w by exactly s. Together with (2): within
   lift-deformations, w changes only through a slip, and by exactly the
   slip amount. This is the algebraic form of "invariant under the flow,
   changeable only by a phase slip" — stated as algebra, NOT as a
   continuity/phase-transition theorem.
4. **FluxTwist bridge.** At θ = 0, the twisted-Fourier phases step by
   2πm/(n+1) per site, total winding exactly m: the mode index in the
   standing T1 module *is* the winding number of its phase configuration.
   (Checkable against `twistedShift_mulVec_twistedFourierVec` /
   `uniformShift_mulVec_fourierVec`; at general θ the total is θ + 2πm,
   which is why the integer is only clean at θ = 0 — stated, not hidden.)

## Explicitly out of scope (captions, not furniture)

- **Abrikosov vortices.** A vortex is a *place* — a core in a material with
  an order-parameter field. The corpus has no manifold, no condensate, no
  core. This brick proves the winding atom a vortex carries; it is not a
  vortex and must never be captioned as one.
- **Knots.** A phase on a ring has no crossing data and cannot knot. The
  genuine bridge is the torus knot (two winding numbers p, q on a torus) —
  a different object, not in this brick.
- **Strings.** A vortex line is a string in continuum theories; this brick
  is a ring of finite sites. No string, no tension theorem.
- **Thermal / acoustic.** No phonon, no acoustic variable, no medium.
  The house heat is spectral (e^{−tK}); nothing here vibrates.
- **Simultaneity triad.** Symmetry break + spectral break + vortex
  generation as one event is a phase-transition (infinite-volume)
  phenomenon; a finite ring cannot contain it. Not claimed, not shadowed.

## Build notes

- New file only, working name `lean/ThetLogos/PhaseWinding.lean`; no
  existing file edited. Sites `Fin (n+1)` to reuse FluxTwist conventions
  (`Real.pi` explicit, no local π binding — per the FluxTwist dossier's
  engineering note).
- Expected friction: ℤ-valued wrap bookkeeping on `Fin (n+1)` successor
  arithmetic — the same fence FluxTwist already crossed.
- Verdict protocol unchanged: build green + axiom spot-checks on the four
  headlines, or the brick reports PARTIAL/KILL at the same speed.
- Count discipline: nothing enters the program total (3,323 strict) until
  the brick compiles clean; a drafted charter moves no number.

## The one decision that remains Jeff's

Commission it (core A only, B as priced stretch), amend it, or leave it
parked. Silence leaves it parked.
