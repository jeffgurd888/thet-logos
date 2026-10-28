# PW-5b — the Contraction Engine

*Landing dossier, 2026-10-28. Module:
`lean/ThetLogos/PhiAssembly.lean`, section 5b
appended (section strict 24, defs 6, 23 private
helpers; module total strict 35; zero placeholders,
zero `native_decide`; main-tree build green, 3,558
jobs, parent-verified; axiom sets exactly
`[propext, Classical.choice, Quot.sound]` on checked
headlines). **Parts of the Clay Yang–Mills statement
closed by this landing: 0.** The engine the assembly
runs on: support factorization, the twisted
contraction, and the per-site type table — in the
forms the final sub-brick applies mechanically. The
pre-registered kill for a non-Gram cross term does
not engage: none appears.*

## What landed

- **R1 — support factorization**
  (`quadCharMoment_eq_sum_siteInt`). The character
  moment of a C4 quad equals a sum over entry
  functions of frozen-link factors times a product,
  over the four ordered support sites, of site-local
  Haar integrals. The product-of-site-integrals form
  was chosen because the product-measure splitting
  lemma is unconditional in this Mathlib pin — the
  integral over all sites factors with no
  integrability side conditions, and non-support
  sites contribute 1. This is the lemma PW-2's
  scoping named missing; it now exists.
- **R2 — the twisted contraction.** Three
  entry-level sandwich evaluations and two closure
  identities: contracting a running contraction at a
  mixed site (PW-1), at a same-orientation site
  (PW-3's J-insertion), and closing the J-twisted
  object at the paired opposite site into the
  J-twisted Gram summand. Every closed contraction
  produced is an exact evaluation or a
  Frobenius/Gram regrouping. **K-PW-5-2 does not
  engage** — no non-Gram cross term survives, so no
  seat evaluation was owed and no refutation pathway
  opens.
- **The per-site type table**, as lemmas over the
  cycle ordering and the two split patterns: at each
  site, which of the four entry evaluations applies,
  determined by the site's split and the pattern's
  membership of its two incident columns. (One
  correction of record: the fourth entry evaluation
  the table needed — the star-plain mixed form — was
  already owned in PW-1's file under the same name;
  the collision was caught at build time and the
  duplicate dropped, not re-proved.)

## What remains

PW-5c, the assembly: per-pattern evaluation at a C4
via R1+R2, conjugation pairing inside the quad,
Gram regrouping over `primitiveQuads`, and
`phi_diag_nonneg` with its κ₄ corollary — the
diagonal sign of κ₄^dep at order β⁴, irreducible ρ,
even N ≥ 4. Scope fences unchanged from the scoping:
β⁵⁺, reducible ρ, 𝒜 ⪰ 0 in the large, and N = 2 are
all untouched, and the inequality carries no cushion
— nothing bounds Φ away from 0. This dossier asserts
the engine only; no sign is claimed in this section.
NO CLAIM; dials 0/4, unchanged.

Census effect: 6,968 → **6,992 strict** /
7,046 → **7,070 attribute-inclusive** / modules
unchanged at **239** (the append grows the module
landed by PW-5a); the seven quarantined placeholders
are unchanged.

## Backers since last landing

No new backers inscribed in this interval; the roll
stands as recorded in `BACKERS.md`. Every gift is
published with the proof stream, named as the giver
wishes, amounts only with the giver's permission —
the standing reciprocity of this house.
