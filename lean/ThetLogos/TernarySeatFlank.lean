/-
# The Tet flank package — T12-0 (the pin) + T12-1 (the flank package
at the ternary seat)
(working label `TernarySeatFlank`; naming is Jeff's)

Commission: Jeff's tap, 2026-11-06 11:49 EST ("Fire the flank
package (T12-0 + T12-1)"), on the scoping
`~/workspace/your_files/tet-one-two-scoping-2026-11-06.md`
(Jeff's "scope it", 2026-11-06 11:42 EST).  The scoping governs:
its §2 grades the readings, its §3 arms the kills, its §4 prices
the menu.  This module builds T12-0 (this header — the pin) and
T12-1 (the flank package below it).  T12-2 (transport to the
center of SU(3)) is NOT commissioned and is NOT built here.

## The fragment (Jeff, 2026-11-06 11:26 EST, from the Android app)

Quoted byte-verbatim, exactly as delivered:

    "(1- 𐤈 ‎ +2)"

The glyph in the middle is Tet (U+10908, Phoenician letter Tet).
The delivered string also carries an invisible left-to-right mark
(U+200E) after the glyph; it is part of the verbatim quote above.

## Transcription discipline (K-T12-TRANSCRIBE — armed)

Tet is a right-to-left character.  Placed inside a left-to-right
line, the bidirectional algorithm can reorder the visual sequence
around it — the house precedent is 2026-10-30, when a commutator
`[D_Tet, bᵢ]` Jeff sent displayed reversed, which would flip the
commutator's sign if transcribed naively.  Jeff's standing brand
rule (2026-10-01) keeps the glyph out of flowing body text and
spells it "Tet".  The plain-form transcription used on this
module's face is:

    (1 − Tet + 2)

This transcription is a READING, not a fact about Jeff's intent.
Jeff has not disambiguated among the readings registered below.
Nothing in this module states a reading as Jeff's settled intent:
each reading is named as a reading, and the one this module
formalizes (R2) is invariant under the R3a regrouping, which is
recorded on the face as well (scoping §2, R3a).  Silently fixing
the transcription — in either direction — is the failure
K-T12-TRANSCRIBE exists to prevent.

## The readings register (scoping §2 — grades as scoped)

* **R1 — the plain sum, Tet := 0 at the seat.**  `1 − 0 + 2 = 0`
  in `ZMod 3`; its substance is the inverse law `2 = −1` — the
  two nonzero residues are additive inverses, so the flank pair
  sums to the center.  Grade: CITATION-GRADE, price 0 — the
  identity is already in the tree in everything but name
  (`zmod3_cases`, `PlaneCrossingKappa4Probe.lean:61`, proved by
  `decide`; `seatChar₃_inv`, `LayerKernelPosTernarySeat.lean:203`).
  It is NOT re-proved here as new content; inside T12-1 it rides
  at citation rank as the package's corollary
  (`ternaryFlank_fragment_sum`).  Re-pricing it as a discovery
  would fire K-T12-FIAT.
* **R1′ — the plain sum, Tet := a boundary/Dirac operator.**
  Grade: NOT STATEABLE — underdetermined; the fragment names no
  operator, and the `D_Tet` of Jeff's 2026-10-30 equation
  `A = Σᵢ aᵢ [D_Tet, bᵢ]` is a separate fragment's object with
  its own corpus home.  NOT built; re-opens only if Jeff names
  the operator.
* **R2 — the residues `{1, 2}` flanking Tet-as-zero at the
  ternary seat.**  Grade: STATEABLE W/DEF — **THIS PACKAGE
  (T12-1).**  The trichotomy with the inverse law, the flank-swap
  automorphism `x ↦ −x` exchanging the flanks and fixing the
  zero alone, and the character shadow (the seat character's
  values on the flanks, with conjugation = the swap's shadow),
  assembled as one named package.  Headline rank, stated plainly:
  IDENTIFICATION / PACKAGING (an A0-weld at miniature scale).
  The pieces were landed separately; the assembly is what is
  new.  It is not a discovery and is not presented as one.
* **R3a — the regrouped reading `−(1 − Tet) + 2`.**  A different
  claim from R1, not a typographical variant: at the seat with
  Tet := 0 it evaluates to `1`, the positive flank, not to zero.
  Grade: STATEABLE AS-IS as a bare identity, NO independent
  content — it earns a line, not a brick: the corollary
  `ternaryFlank_regrouped` in T12-1.  The menu is invariant under
  the regrouping (scoping §2, R3a).
* **R3b — signed charges `(−1) [Tet] (+2)` as a configuration.**
  Grade: NOT STATEABLE as stated — no carrier: the fragment
  specifies no seat and no sites for its two charges.  Refused
  on the record; pricing the nearest neighbor would be
  completing Jeff's fragment for him.  NOT built; re-opens only
  if Jeff supplies the carrier.
* **R4 — the Gurd-Law boundary picture.**  Tet as the drawn
  boundary, `1` and `2` the contained divisions (GURD LAW, Jeff
  2026-10-02: "Before information can be processed or
  communicated, the boundary must first be drawn and contained";
  corollary 2026-10-06: "the boundary creates identity"; the Tet
  glyph is its picture — the circle drawn first, then the
  contained divisions).  Grade: T5 DOCTRINE, price 0 — already
  fully "landed" as Jeff's filed doctrine; no brick exists for
  it, by design.  It appears in this module ONLY as this labeled
  face text (see also the shell-label paragraph below), never
  as a premise or a conclusion.
* **R5 — the center reading.**  The identity of
  `Subgroup.center ↥SU3` flanked by `ω • I` and `ω² • I`, via the
  shipped bridge (`su3CenterEquiv`, `centerChar`).  Grade:
  STATEABLE W/DEF — TRANSPORT ONLY of R2, re-dressing label
  mandatory (the C-4 precedent).  This is T12-2: OPTIONAL and
  NOT commissioned in this build.  NOT built here.

## The tier tension (flagged, NOT resolved — Jeff's call)

Jeff's 2026-10-16 ruling on the shell-label series: **Tet is the
NAME of the equality, never the value.**  Reading R1 puts Tet in
a value-position (a term in a sum).  The two stand in tension.
This module flags the tension on its face and does not resolve
it: the package built here (R2) names the zero's *position* in a
presentation of `ZMod 3`; it assigns no denotation to the glyph
and creates no constant named for it (§5 of the scoping: "Tet
does not acquire a denotation in Lean").  K-T12-CREST arms the
fence: the shell-label crest is never authority for the
arithmetic, and the arithmetic is never a proof of the crest.

## The shell label — family context, doctrine only (K-T12-CREST)

Jeff's 2026-10-16 shell-label series (`{H|t}=[Tet]`, the wordmark
`H[Tet]T`, the sigil `0.[Tet].0`) shares this fragment's skeleton
— a distinguished central mark with exactly two flanks — and the
fragment is the family's first member with *numeric* flanks and
*signed* joins.  That relation is recorded here as provenance,
at T5.  The crest is Jeff's inscription under his ruling "no
redraw"; this module neither extends, completes, nor explains
it, and no statement below cites it.

## A permuted cast, already in the tree (cited, not re-proved)

The ternary seat's own split already proves the fragment's cast
with every role permuted: `seatA₃_add_two_mul_seatB₃`
(`LayerKernelPosTernarySeat.lean:431`): `a₃(β) + 2·b₃(β) = 1` —
a central coefficient, two copies of the flank coefficient, the
total `1`.  It is a rhyme, not an instance (the `1` is the
total, not a flank; the `2` counts copies, it is not a residue;
there is no minus).  It is cited here because it shows the
fragment's shape is a theorem shape this seat already supports;
it is not re-proved and no part of T12-1 depends on it.

## Exactness fences (K-T12-EXACT — armed)

The seat character's values are exactly `{1, ω, ω²}` — pairwise
distinct, the nontrivial ones non-real (`zetaC3_ne_one`,
`zetaC3_sq_ne_one`, `zetaC3_ne_sq`).  **`ω` is NOT `2`, and
`ω²` is NOT `2`.**  The numeral `2` in the fragment is a residue
of `ZMod 3` and an exponent — never a character value.  No
statement in this module states or implies a character value
`2`.  (Dual slide, also fenced: the dimension factor `3` in the
bridge's `charFn_centerScalarSU3 = 3 * seatChar₃` is not a
residue, a flank, or a count of the fragment's terms.)

## Order is not canonical (K-T12-FLANK — armed, decided at T12-1)

The swap `x ↦ −x` is an automorphism of `ZMod 3` exchanging the
flanks and fixing the zero; the character theory sees the swap
as conjugation (`seatChar₃_inv`, `seatChar₃_star`).  The order
in the fragment — `1` on the minus side, `2` on the plus side —
is Jeff's presentation.  T12-1 *uses* it, *names* it, and states
the swap theorems beside it (`ternaryFlank_neg_exchanges`,
`ternaryFlank_neg_fixed_iff`, `ternaryFlank_char_shadow`); it
never calls the order canonical.  Any labeling of `1` as "the
first flank" in this module is the fragment's presentation
order, a labeled convention, nothing more.

## Names (K-T12-NAME — armed)

"Tet" is already occupied in-tree by Jeff's unrelated Axiom Tet
web model (`AxiomTet.lean`, `AxiomTetPartner.lean` — the
equality-first / Axiom Zero scope, 2026-11-03); this line does
not touch it.  No name here reuses the `pattern*₃` prefix (the
TM filter vocabulary) or the `center*` prefix (the SU(3)-bridge
vocabulary), and no object is named simply "Tet".  The name
family used is `ternaryFlank*` and the module label
`TernarySeatFlank` — **working labels only; the module's public
name is Jeff's to give** (naming is Jeff's hand).

## Kill register (scoping §3 — statuses)

* **K-T12-FIAT — ASSESSED AT THIS PIN (T12-0), in the scoping's
  form: the pin STANDS — narrowly.**  Content beyond citation
  exists: the R2 assembly (T12-1) packages the trichotomy, the
  inverse law, the swap automorphism with its unique fixed
  point, and the character shadow as one named flank package —
  none of which exists in-tree as an assembly (§1.3/§1.5 of the
  scoping: no landed name has the flanking shape).  The pin
  stands narrowly because the margin is exactly that assembly:
  if T12-1's content collapsed to the bare identity and
  citations, shape (2) of this kill fires at T12-1 and the menu
  closes at price 0.  Shape (1) — the fragment re-typed as
  notation (`tetExpr := 1 - 0 + 2` with a `decide` about the
  notation) — is refused by construction: no such definition
  exists in this module.
* **K-T12-TRANSCRIBE — ARMED.**  The fragment is carried
  byte-verbatim above; the transcription is labeled a reading;
  the readings are registered separately; the R3a regrouping is
  recorded on the face.  Does not fire.
* **K-T12-NAME — ARMED.**  See the Names paragraph: distinct
  family, no squatting on Axiom Tet / `pattern*₃` / `center*`,
  nothing named "Tet".  Does not fire.
* **K-T12-EXACT — ARMED.**  See the Exactness fences paragraph.
  Does not fire.
* **K-T12-FLANK — ARMED at the pin; DECIDED at T12-1** (the
  swap theorems are stated in the package, so the order is
  never presented as forced).  Status recorded in the T12-1
  landing note at the end of this module.
* **K-T12-CREST — ARMED.**  The crest appears above as doctrine
  context only; no statement cites it; nothing here is presented
  as what the crest meant.  Does not fire.
* **K-T12-GRAV — ARMED.**  This package is finite-level algebra
  about `ZMod 3` and its character — a seat the corpus already
  owns.  It is not a gravity candidate, not a response law, not
  a derived number, not Dial evidence of any species.

**NO CLAIM; dials 0/4; Dial 2 = 0.**

What a landing of T12-1 proves (scoping §5): a named, citable
flank package for the ternary seat, and an honest provenance
record for the fragment — which parts were algebra (R2), which
were already in the tree (R1's identity), which were doctrine
(R4), and which could not be stated (R1′, R3b).  What it does
NOT prove: a new zero, element, or group; a denotation for Tet;
the shell label or evidence for it; a canonical order; a
character value `2`; a triality statement; anything about
SU(3) representations, gravity, or the dials.
-/

import ThetLogos.LayerKernelPosTernarySeat

namespace ThetLogos

/-! ## T12-1 — the flank package at the ternary seat (reading R2)

The assembly, built only from landed pieces: the trichotomy
(`zmod3_cases`), the inverse law, the flank-swap automorphism
and its unique fixed point, and the character shadow
(`seatChar₃_inv` / `seatChar₃_star`).  Rank: IDENTIFICATION /
PACKAGING — the pieces were landed separately; the package is
what is new.  R1's bare identity rides inside at CITATION rank
(`ternaryFlank_fragment_sum`); it is not the headline. -/

/-- A flank of the zero in `ZMod 3`: a nonzero residue.  The two
flanks are `1` and `2` (`ternaryFlank_iff`); the zero itself is
the center they flank.  Working label — the fragment's "Tet"
names the zero's *position* in this presentation (reading R2);
this predicate assigns no denotation to the glyph. -/
def ternaryFlank (x : ZMod 3) : Prop := x ≠ 0

/-- The flanks of the zero are exactly the residues `1` and `2`
(the trichotomy `zmod3_cases`, assembled with the package's
predicate).  Which of the two is written first is the fragment's
presentation order — a labeled convention, not a canonical one
(K-T12-FLANK; the swap theorems are `ternaryFlank_neg_exchanges`
and `ternaryFlank_neg_fixed_iff` below). -/
theorem ternaryFlank_iff (x : ZMod 3) :
    ternaryFlank x ↔ x = 1 ∨ x = 2 := by
  constructor
  · intro h
    rcases zmod3_cases x with h0 | h0 | h0
    · exact absurd h0 h
    · exact Or.inl h0
    · exact Or.inr h0
  · rintro (rfl | rfl)
    · show (1 : ZMod 3) ≠ 0; decide
    · show (2 : ZMod 3) ≠ 0; decide

/-- The inverse law: the second flank is the negative of the
first, `2 = −1` in `ZMod 3` — the arithmetic substance of
reading R1, at its landed (decide-level) strength. -/
theorem ternaryFlank_two_eq_neg_one : (2 : ZMod 3) = -1 := by
  decide

/-- The fragment's arithmetic shadow (reading R1), stated as the
package's corollary at CITATION rank: with the center read as
the zero, `1 − 0 + 2 = 0` in `ZMod 3` — true because the flank
pair sums to the center (`ternaryFlank_two_eq_neg_one`).  The
bare identity was already in the tree in everything but name;
it is recorded here as the package's corollary, not re-priced
as a discovery (K-T12-FIAT). -/
theorem ternaryFlank_fragment_sum : (1 : ZMod 3) - 0 + 2 = 0 := by
  decide

/-- The swap exchanges the flanks: negation sends `1` to `2`
and `2` to `1`.  Together with `ternaryFlank_neg_fixed_iff`,
this is the theorem beside the fragment's presentation order
that keeps the order from ever being called canonical
(K-T12-FLANK). -/
theorem ternaryFlank_neg_exchanges :
    (-1 : ZMod 3) = 2 ∧ (-2 : ZMod 3) = 1 := by
  decide

/-- The zero alone is swap-fixed: `−x = x` in `ZMod 3` iff
`x = 0`.  The center of the flanking picture is the unique
fixed point of the flank swap. -/
theorem ternaryFlank_neg_fixed_iff (x : ZMod 3) :
    -x = x ↔ x = 0 := by
  revert x
  decide

/-- The character shadow of the swap: complex conjugation of
the seat character is the flank swap read through the
character — `conj (seatChar₃ (ofAdd x)) = seatChar₃ (ofAdd (−x))`
for every residue `x`.  Assembled from the landed
`seatChar₃_star` (conjugation is group inversion) and the
identification of inversion in `Multiplicative (ZMod 3)` with
negation under `ofAdd`.  The character's values remain
`{1, ω, ω²}` (`seatChar₃_cases`); the residue `2` appears here
only as an element of `ZMod 3`, never as a value
(K-T12-EXACT). -/
theorem ternaryFlank_char_shadow (x : ZMod 3) :
    star (seatChar₃ (Multiplicative.ofAdd x))
      = seatChar₃ (Multiplicative.ofAdd (-x)) := by
  have hinv : (Multiplicative.ofAdd x)⁻¹ = Multiplicative.ofAdd (-x) := by
    apply Multiplicative.toAdd.injective
    show -(Multiplicative.toAdd (Multiplicative.ofAdd x)) = -x
    rfl
  rw [seatChar₃_star, hinv]

/-- The R3a regrouping line (scoping §2, R3a): with the center
read as the zero, the regrouped form `−(1 − 0) + 2` evaluates
to `1` — the positive flank in the fragment's presentation
order — not to zero.  A corollary line, recorded so the
regrouping is on the face (K-T12-TRANSCRIBE); it carries no
independent content beyond the trichotomy and the inverse
law. -/
theorem ternaryFlank_regrouped : (-(1 - (0 : ZMod 3)) + 2) = 1 := by
  decide

/-! ## T12-1 landing note — kill decisions at this brick

* **K-T12-FIAT shape (2) — DECIDED at T12-1: does NOT fire.**
  The package's content did not collapse to the bare identity
  and citations: beyond the citation-rank corollary
  (`ternaryFlank_fragment_sum`) it assembles the flank
  predicate with its exact characterization
  (`ternaryFlank_iff`), the swap automorphism's action on the
  flanks and its unique fixed point
  (`ternaryFlank_neg_exchanges`, `ternaryFlank_neg_fixed_iff`),
  and the character shadow of the swap
  (`ternaryFlank_char_shadow`, proved from `seatChar₃_star`,
  not a citation).  The line therefore stands at the assembly
  rank the pin declared — narrowly, as assessed at T12-0.
* **K-T12-FLANK — DECIDED at T12-1: does NOT fire.**  The swap
  theorems are stated inside the package itself; no text in
  this module presents the flanking order as forced or
  canonical.
* K-T12-TRANSCRIBE / K-T12-NAME / K-T12-EXACT / K-T12-CREST /
  K-T12-GRAV — remain ARMED; none fired (see the pin header).

NO CLAIM; dials 0/4; Dial 2 = 0. -/

end ThetLogos
