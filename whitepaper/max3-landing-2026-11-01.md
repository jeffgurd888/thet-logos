# MAX-3 LANDING — 2026-11-01

## The cube spectrum: PARTIAL at the pre-registered seam (working label: MAX line)

**Module:** `ThetLogos.MaxwellQuadSpectrum` — strict 87 /
defs 19, parent-verified (independent count, main-tree
build, headline axiom checks on exactly
`[propext, Classical.choice, Quot.sound]`).

**Census at this landing: 10,657 strict / 10,734 total /
359 modules, zero sorrys.**

**Verdict for the claims registry (Card MAX): PARTIAL.**
The card's pre-written PARTIAL sentence is the public
form of this outcome (registry:
`~/workspace/your_files/claims-registry-2026-10-31.md`;
the card's sentences remain subject to Jeff's
review-and-amend pass, as registered there).

MAX-3 was priced L with its risk named in advance
(K-MAX-S): the three-component Fourier block assembly.
The assembly landed. What did not land is one clause of
(M5), and it did not land for a reason worth stating
plainly: **clause 4 is not a mode computation at all.**

## What was discharged (the pin's exact clause forms, general Even N)

Assembled as `maxwellM5_spectrum_part` (the conjunction
of clauses 1 ∧ 2 ∧ 3 ∧ 5, each also a standalone theorem):

- **Clause 1 — the eigenvalues exist.** For every momentum
  k, `maxwellOp N` has eigenvalue `maxwellTransverseEig
  N k` (the registered `4·Σ sin²(πkᵢ/N)`) and eigenvalue 0.
  The modes are real link modes (`cosMode_eigen`,
  `sinMode_eigen`: `maxwellOp N (cosMode K A) =
  (4 * ∑ μ, (modeSin K μ)^2) • cosMode K A` under the
  transversality condition, transported by
  `transverse_eig_eq`); the zero eigenvalue rides on
  MAX-2's M3 (`hasEigenvalue_zero`, via
  `maxwellOp_gaugeAngle`).
- **Clause 2 — transverse multiplicity 2 at k ≠ 0.** Two
  linearly independent transverse modes at the registered
  eigenvalue, by a full case split (the generic case by a
  2×2 determinant equal to `sin(2·angle_j)`; the
  {0, π/2}-angle cases by single- and difference-support
  modes).
- **Clause 3 — the gap value is attained as an
  eigenvalue:** `HasEigenvalue (maxwellOp N)
  (4 * Real.sin (Real.pi / N) ^ 2)`.
- **Clause 5 — attainment at the registered momentum:**
  at k = (1, 0, 0), `maxwellTransverseEig N k =
  4 * Real.sin (Real.pi / (N:ℝ)) ^ 2`.

**K-MAX-3 did not fire:** the computed transverse
eigenvalue is the registered one, read off the
computation; no mode definition was adjusted.
**K-MAX-1 re-checked:** the diagonalization is of the
pin's `maxwellOp N` itself (through MAX-2's proved form
identity); no Fourier-side operator is defined or
diagonalized.

## The seam (K-MAX-S), named on the module's face

**Clause 4 — the gap as a bound — is NOT discharged:**
`∀ μ, HasEigenvalue (maxwellOp N) μ → μ = 0 ∨
4 * Real.sin (Real.pi / (N:ℝ)) ^ 2 ≤ μ`. The registered
spectrum's *values* are proved and its gap value is
attained; what is unproved is that **no eigenvalue lies
strictly between 0 and `4·sin²(π/N)`**. That is a global
Poincaré/Wirtinger-type inequality for the curl-curl
operator over the whole spectrum — a different species of
argument from exhibiting modes, and not obtainable from
the mode computation in this band. Accordingly
`maxwellM5` as a whole is **not asserted** anywhere.

**Re-price (registered):** clause 4 is one
Poincaré-inequality brick — discrete Wirtinger on the
cycle, tensored over the cube, transported through the
Weitzenböck identity — est. L band on its own. Working
label **MAX-4**; it fires under the standing auto-fire
grant in rotation. Until it lands, every house sentence
about the finite gap must carry its exact shape: *the
value `4·sin²(π/N)` is an eigenvalue, attained at
(1,0,0); the bound over the whole spectrum is open.*

One build note, disclosed on the module's face:
`clause2` carries a scoped `set_option maxHeartbeats
1600000 in` — its case-split applications time out at
`whnf` under smaller budgets (verified at default and
4×; 8× compiles). Statements unaffected; the kernel
checks as usual (the axiom sweep above is the
certification).

## What this landing is not

Not the registered spectrum in full (clause 4), not a
continuum dispersion, not a photon (OP-1's disjoint
object), not a gravity statement. The finite dispersion
is labeled finite in every statement, as K-MAX-2 binds.
Dial 2 = 0; NO CLAIM; dials 0/4.

Line state: MAX-0/1/2 FULL; MAX-3 PARTIAL at clause 4;
MAX-4 re-priced (above). GR-PROP-2 fires on the landed
clauses (its gate ruling is on its pack: clause 4 is not
a PROP-2 input).

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you
to everyone reading the stream — the corpus is free for
everyone, forever.

*End of dossier.*
