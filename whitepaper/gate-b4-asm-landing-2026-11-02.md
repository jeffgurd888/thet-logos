# B4-ASM LANDING DOSSIER — GATE-B CLOSES FOR THE DISC CHAIN — 2026-11-02

**Item:** B4-ASM (SHELF-7b-disc chain, GATE-B discharge
campaign, final brick) — the assembly.

## VERDICT: FULL — `shelf7bDiscInterior_proved` is UNCONDITIONAL. The disc spectral mapping theorem stands whole in the interior presentation.

**Artifact:** `lean/ThetLogos/DiscSpectralMappingFull.lean`
— strict 8, defs 0. Verified by the coordinator in the
main tree (build green, 3005 jobs); both headlines on
exactly `[propext, Classical.choice, Quot.sound]`.

**Headlines:**
- `discFactorisationHyp'_proved : ∀ a f R,
  DiscFactorisationHyp' a f R` — the primed hypothesis is
  DISCHARGED. Identically-zero case vacuous (spectrum
  nonempty + the spectral-radius norm bound puts a spectral
  point in the disc, forcing mu into the image); main case
  assembled from B4-TAIL (factorisation at R₀ < R₂ < R;
  every listed zero l has f l = mu, hence lies off the
  spectrum), B4-UNIT (the unit clause), B2′'s summability
  transport, and the identity join (TAIL/PROD coefficient
  identity + `discCoeff_sub_const`, proved by Cauchy-series
  uniqueness; the polynomial-value join by induction over
  lam through 8a's `hfcDisc_discFactor`, with linear-factor
  coefficients identified by a finite series-uniqueness
  lemma).
- `shelf7bDiscInterior_proved : ∀ a f R,
  Shelf7bDiscInterior a f R` — via B4-REPAIR's adapter:
  **for every element a of a complex Banach algebra, every
  f holomorphic on the disc of radius R > spectralRadius(a),
  and every interior radius R₀:**
  `spectrum ℂ (hfcDisc a (discCoeff f R₀)) = f '' spectrum ℂ a`.
  The spectral mapping theorem for the disc holomorphic
  functional calculus, machine-checked, at the spectral
  scale, with no hypotheses left standing.

## The GATE-B chain verdict (complete)

7B-PIN (frozen forms) → **B1a/B1b/B1d FULL**; **B1c KILLED
as frozen** (boundary presentation; corrected interior
form landed) → 7B-PIN-2 (live forms re-frozen; B2Forward
and Disc frozen forms REFUTED in-tree) → **B2′ FULL**
(forward inclusion at the spectral scale) → **B3′ PARTIAL**
(equality under the named `DiscFactorisationHyp`;
multiplicativity FULL; constant case unconditional) →
**B4 scoping: K-B4-LITERAL** (the frozen hypothesis false
as stated — antecedents missing) → **REPAIR FULL**
(refutation in-tree; primed form + adapter) → **FIN FULL**
(zero finiteness; K-B4-FIN silent) → **PROD FULL**
(coefficient-product identity, interior form; the
boundary-radius form REFUTED in-tree) → **TAIL FULL**
(factorisation with analytic-order multiplicities) →
**UNIT FULL** (zero-free ⇒ unit) → **ASM FULL** (this
landing). Four statements died at boundary presentations
along the way (B1c, B2-frozen, Disc-frozen, the PROD
boundary form, the un-primed hypothesis) — every one
killed by proof in the tree and every one standing on the
record beside the interior forms that replaced them. The
pattern is a property of the disc calculus itself:
coefficients presented AT a boundary radius see only
circle values, which open-disc holomorphicity does not
constrain; presented strictly inside, everything holds.

**What remains open, honestly:** SHELF-7b *in full* —
the general neighbourhood calculus — is still pin-blocked
(FULL-1–FULL-4: no winding number, no contour-system type,
no general Cauchy theorem in the pin). The disc chain is
the disc chain; it closed under its own name and is not
7b-in-full. The 8B-3/4/5 extensions remain a registration
decision for parent/Jeff.

## Fences

NO CLAIM; all dials 0/4. K-GELFAND-SUBALGEBRA was never
used on any route in this chain.

**Census after landing: 12,295 strict / 12,702 total / 427 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
