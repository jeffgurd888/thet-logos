import Mathlib.Tactic
import ThetLogos.MeaningBridge
import ThetLogos.SeedCoreEncoding

/-!
# ThetLogos.WritingDirection — WD-0 pin + WD-1: the writing-direction layer (WORKING LABEL — naming is Jeff's)

HONESTY LEDGER (read before citing):

- COMMISSION. Jeff, 2026-11-06 13:25 EST, sent with a screenshot of the
  Wikipedia "Symbol of Chaos" (the eight-arrowed Chaos Star; see
  PROVENANCE below):

  > "scope the writing direction layer with entropy continuum
  > arrow fixed in the out... so ∞|∅=𐤈"

  The phrase "in the out..." is cut off mid-word IN JEFF'S MESSAGE AS
  RECEIVED. It is NEVER completed anywhere in this module, in any
  comment, or in any landing text. The two bounded readings the cut
  admits — (A) OUTWARD and (B) OUTSIDE — are both carried below,
  UNDECIDED. Silently fixing the truncation is a kill condition
  (K-WD-NAME). Scoping: `writing-direction-scoping-2026-11-06.md`
  (audit basis: HEAD d11af71, census 13,855 strict / 520 modules,
  fence 751/751, ledger 66 records). Fired by Jeff's tap 2026-11-06
  13:33 EST: "Fire the core plus the compass (WD-0 + WD-1 + WD-3)."
  WD-2 is NOT commissioned: it is contingent on WD-1's positive
  outcome and is not built here.
- ORIGIN. Jeff's seeing, 2026-11-06 13:19 EST, with a hand drawing
  (circle with three axes crossing INSIDE it — the Tet-glyph
  geometry: boundary drawn first, divisions contained; six ends
  labeled Up / Down / Fwd / Bwd and two circled glyphs, NE read as
  "L"; SW read as "R" OR "P" — UNCERTAIN, carried unresolved; at the
  right a letter layout around a circled "+": "B", "U" above; "L",
  the circled plus, "R" in a row; "D" and an upward wedge/caret
  below — the wedge's role UNCERTAIN, carried unresolved). Jeff's
  caption, verbatim: "I think that we are missing the up down
  Japanese style writing Chinese writing but a unified language
  writing model". The scoping's audit found the gap one level deeper
  than the seeing: the unified-language model as built (the Meaning
  Bridge, `MeaningBridge.lean`) contains NOTHING ORDERED AT ALL —
  `MeaningAlign` is a bare relation over atoms, there is no word,
  list, or sequence type anywhere in the language layer, and the
  seed's links are `Finset`s. The seed is a RIGHT-TO-LEFT alphabet
  (Phoenician) encoded DIRECTION-BLIND. This module is the smallest
  honest repair path priced by that scoping.
- THE CONSTRAINT, BOTH READINGS PINNED UNDECIDED, WITH FENCES.
  (A) OUTWARD: one global direction — the entropy arrow — fixed
  pointing out; writing directions defined relative to it. Honored
  here ONLY at reduced strength, as a PIN-LEVEL CONVENTION: reading
  is a temporal act (a written form is consumed glyph before glyph),
  so a path direction IS a reading order; the layer's directions are
  pinned as reading orders under that convention. Definitional; it
  buys no physics. NOT honored, NOT STATEABLE in this layer:
  "entropy increases outward" — the corpus has no center, no shells,
  no per-shell entropy, and the cube seats are TORI (coordinates in
  `ZMod N`): a torus has NO OUTSIDE, so the radial sentence is false
  of the seats' topology, not merely unbuilt. The word "continuum"
  in the commission is T5 as carried and FRONTIER as worded: the
  corpus has NO continuum arrow (Dial 3 = 0; the Q3 ascent is 0/10).
  Only citing a LANDED finite-arrow referent (the priced, unfired
  FA-1/FA-5 bricks of the finite-arrow line) waits on that line;
  this layer's mathematics does not depend on it.
  (B) OUTSIDE: the entropy arrow fixed in the exterior; the contained
  core still — Jeff's emblem doctrine (2026-10-16 true symbol v2:
  eight irregular arrows AROUND THE OUTSIDE of the ring, chaos
  outside the boundary, core unchanged; 2026-10-24, Jeff verbatim:
  "add the chaos arrows around the outside to represent thermal
  entropy of Time"). The interior half is carried as DOCTRINE ON
  THIS FACE: the drawing's axes cross INSIDE the circle — the ring
  is precisely what the borrowed Chaos Star lacks, and that
  difference is Gurd Law's (the boundary drawn first). The exterior
  half is NOT STATEABLE in this layer: no seat in-tree has an
  outside. The nearest landed rhyme — `ker L`, the fixed locus the
  heat flow does not move — is labeled a RHYME, never a weld.
  Under BOTH readings: `UltimateReduction` Claim 6(b)'s LOCAL time
  arrow stands KILLED in-tree and is not revived here in any dress.
  Jeff's "thermal entropy of Time" gloss stays attached to the
  finite-arrow record with its fences: the chi-squared production
  quantity there is a DIVERGENCE, never renamed "entropy" in this
  layer; the Past Hypothesis stays a hypothesis.
- THE EQUATION. The commission's final equation, transcribed in
  plain form (house rule: the Tet glyph is a right-to-left character
  and is spelled out in flowing text):

      ∞|∅ = Tet

  It is a FILED FRAGMENT — transcribed, read, graded; never a
  premise, never a proved identity, never formalized in this module.
  (R-a) Set-literal: NOT STATEABLE — ∅ is a set; ∞ is NOT a set in
  standard foundations; the equality is ill-formed, not false. As a
  BARRED PAIR in Jeff's own divider notation (cf. his shell labels
  `{H|t}`, 2026-10-16), the shape is T5 doctrine-kin: the extreme
  flanks — everything | nothing — around a fixed center, rhyming
  with the T12 flank package (`TernarySeatFlank.lean`: 1 and 2
  flanking the zero). A rhyme, labeled, never a weld.
  (R-b) Axiom Tet reading: T5 doctrine — equality prior to both
  extremes, Tet naming the equality. It leans toward the side of
  Jeff's 2026-10-16 ruling (Tet = the NAME of the equality, never
  the value); the TIER TENSION between that ruling and the T12
  fragment's value-position reading is flagged UNRESOLVED — Jeff's
  call; no theorem in this module depends on it.
  (R-c) ∞ as a corpus object: FRONTIER / never — the corpus is
  finite by construction; no brick at any price seats ∞.
  EXACTNESS: ∅ is NEVER conflated with the number 0. Jeff's own
  fragments keep them distinct (his "+0 = Tet", 2026-11-06 13:08,
  uses 0; this equation uses ∅). ∞ is never a number, a set, or an
  object in any statement this layer produces.
- PROVENANCE OF THE PICTURES. Jeff's drawing (six directions) is
  his. The screenshot's eight-arrowed star is the "Symbol of
  Chaos": designed by Michael Moorcock for his Eternal Champion
  books, drawn by Jim Cawthorn, first on an Elric cover (Science
  Fantasy, 1962); later popularized through Warhammer and chaos
  magic. It is a public symbol with an owner-history — Moorcock's,
  then fandom's. It is NOT Jeff's coinage and NOT program property;
  its role here is the RADIATING / compass form only. Jeff's own
  chaos-arrows lineage PREDATES the screenshot by weeks (2026-10-16
  v2; 2026-10-24 gloss and emblem; 2026-11-01 eight-arrows proposal,
  audited PROPOSAL ONLY, and his seeing "3 contained by 8" — 2^3 = 8
  cube vertices, 3 directions; the LayerCube at N = 2 carries both
  counts — see the companion module `WritingDirectionCompass.lean`,
  WD-3, GEOMETRY ONLY).
- WHAT THIS MODULE IS. WD-0 (this header and §1): the pin — the
  path-direction datum `WriteDir` (five constant cases), the reading
  each direction induces on a word (`WriteDir.readingOf`), the word
  type (`List Glyph`), and the STIPULATED SEQUENCE READING
  (`seedRead`, `wordDenote`) frozen as definitions BEFORE any test
  runs (the commit order shows it: this pin is its own commit).
  WD-1 (§2–§4): (i) the direction-blindness of the landed model,
  proved over `MeaningAlign` — the four criterion predicates are
  invariant under relabeling (transport along equivalences), which
  is the exact form blindness takes for a relation over atoms:
  reversal of atoms is inexpressible, relabeling is all that exists;
  and the one-glyph vacuity in exact form (a word of length at most
  one is its own reverse, and its denotation is reversal-fixed);
  (ii) the reversal test over the seed's own encoded data
  (`SeedCoreEncoding.lean`, consumed, not edited): decided by the
  data, not rigged — the sequence reading is order-faithful by
  stipulation and favors neither outcome.
  THE TEST SET, STATED HONESTLY (the pin fixes it): words over the
  FOUR FUNCTIONAL GLYPHS {tet, kap, ayin, pe} — the glyphs carrying
  exactly one instrumental link each (tet ↦ MOVE, kap ↦ TOUCH,
  ayin ↦ SEE, pe ↦ SAY) — of length at most 3. The fifth covered
  glyph, yod, is EXCLUDED from the reading's domain: it carries TWO
  links (TOUCH and DO) — it is the seed's conflation witness, and a
  sequence reading (a function) cannot read it without choosing;
  the reading refuses (denotation `none`) rather than choosing, so
  conflation and gaps stay visible in the reading itself. Words
  containing yod or any uncovered glyph have NO sequence denotation.
- THE SEQUENCE READING IS AN ENCODING SEMANTICS. It is stipulated,
  labeled as such on its face, and says nothing about natural
  language. Real composition — pin N2, meaning vs reference — is
  FENCED, untouched, and not built toward by anything here. The
  commutator precedent (2026-10-30: bidi reordering flipped
  [D_Tet, b] into [b, D_Tet] and changed a sign) is an ANALOGY OF
  SHAPE only — order-sensitivity with a meaning change — not a
  shared mechanism; this module does not borrow its authority.
- K-WD-FIAT, ASSESSED AT THE PIN (house practice). The decoration
  kill fires if the direction datum does no work: every landed
  "direction" theorem the old criterion restated with a tag, or the
  reversal test's composition defined so reversal-invariance holds
  by construction of the test rather than by the data. Assessment:
  (shape 1) REFUSED BY CONSTRUCTION — the direction datum is not a
  tag on the criterion; it is a reading-order map on words, a type
  the criterion has never seen, and §3.4's generic restatement of
  the criterion at a directed syntax type is priced 0 (a citation)
  and is NOT built here. (shape 2) GUARDED BY COMMIT ORDER — the
  word type and the sequence reading are frozen in this pin commit
  BEFORE the reversal test exists; the reading is order-faithful by
  stipulation (denotation of a reversed word is the reverse of the
  denotation, §3), which favors NEITHER outcome: whether any word's
  denotation sequence is a palindrome is decided by the seed's DATA
  (the diversity of the four glyphs' primes), not by the reading.
  Final status is decided at WD-1 and reported at full rank.
- KILL REGISTER (armed from this pin onward; final statuses on the
  landing record). K-WD-FIAT (decoration — assessed above, decided
  at WD-1). K-WD-REV (vacuity — fires if the reversal test comes
  back vacuous at word level too; its glyph-level half is §3.2 of
  the scoping, proved in §2 below as a DELIVERABLE: blindness at
  glyph level is a theorem about the model's shape, promoted to a
  result, reported at full rank either way). K-WD-NAME (collision /
  branding — the `WriteDir` family names were collision-scanned
  against the tree at the pin: no hits; the Chaos Star is never
  presented as program insignia or property; the truncation, the
  drawing's uncertain glyphs, and the tier tension are never
  silently fixed in any face text). K-WD-ENTROPY (constraint slide —
  no divergence renamed "entropy"; no continuum arrow, cosmological
  outward, or Past Hypothesis asserted as a conclusion; no entropy
  located in an outside or along a radius as a theorem; the killed
  local arrow never revived). K-WD-EXACT (extremes — ∞ never a
  number/set/object; ∅ never conflated with 0; "2^3 = 8" read as
  finite cube arithmetic only). K-WD-CREST (authority — neither the
  equation, the drawing, nor the emblem doctrine is cited as
  authority for this module's mathematics, nor are its results cited
  as proof of them). K-WD-GRAV (laundering — nothing here is a
  gravity object, a response law, a derived measured number, a
  continuum statement, or Dial evidence of any species; "contains
  every language" stays an UNPROVABLE HORIZON on this face — a
  direction datum is a transcription prerequisite, not containment,
  and discharges nothing).
- NO CLAIM; dials 0/4; Dial 2 = 0.
-/

namespace ThetLogos

/-! ## §1. WD-0 — the pin: the direction datum, the word type, the sequence reading

DEFINITIONAL grade throughout this section: it pins shapes and
proves nothing. The five constant cases of `WriteDir` are the
constant path directions of real scripts named in the scoping
(§3.1(a)); the position-dependent case (boustrophedon — the path
reverses each line) is named in the scoping, second-order, and
deliberately NOT a constructor here. Glyph facing (§3.1(b) of the
scoping) is pin-level only and earns no definition here: the
seed's glyphs are abstract constructors with no shapes to flip. -/

/-- **The path-direction datum (DEFINITIONAL; WORKING LABEL).**
The constant path directions a written unit can be consumed
along: `ltr` (left-to-right), `rtl` (right-to-left — Arabic,
Hebrew, and Phoenician, THE SEED'S OWN native direction),
`ttbRtl` (top-to-bottom, columns advancing right-to-left —
traditional Japanese tategaki, traditional Chinese), `ttbLtr`
(top-to-bottom, columns advancing left-to-right — Mongolian),
`btt` (bottom-to-top — Ogham's line direction). A datum, not a
theorem: its content is decided by the reversal exhibit (§4),
not by this definition (K-WD-FIAT is armed for the decoration
outcome). -/
inductive WriteDir
  | ltr
  | rtl
  | ttbRtl
  | ttbLtr
  | btt
  deriving DecidableEq, Repr

/-- **The reading a direction induces on one word (DEFINITIONAL).**
A word is a finite sequence of glyphs (`List Glyph` — the word
type this pin freezes; none existed in the language layer before
this module). Each direction reads a single word in an order:
`ltr` reads it as written; `rtl` — the seed's native direction —
reads it reversed; `btt` likewise reverses the line; the two
top-to-bottom cases read a single column top-to-bottom as
written — their column-advance acts BETWEEN columns, not within
one word, stated on this face so the collapse is honest data,
not a hidden identification. -/
def WriteDir.readingOf (d : WriteDir) (w : List Glyph) : List Glyph :=
  match d with
  | .ltr => w
  | .rtl => w.reverse
  | .ttbRtl => w
  | .ttbLtr => w
  | .btt => w.reverse

/-- **Relabeling an alignment (DEFINITIONAL).** The transport of
an alignment along equivalences of its syntax and meaning types:
the glyph `s'` carries the meaning `m'` exactly when the glyph it
came from carried the meaning that one came from. This is the ONLY
action on an alignment the landed model's shape supports — there
is no order on atoms for anything else (a reversal, a rotation) to
act on. §2 proves the four criterion predicates are invariant
under it: that invariance IS the model's direction-blindness, in
exact form. -/
def MeaningAlign.transport {S S' M M' : Type*} (A : MeaningAlign S M)
    (e : S ≃ S') (f : M ≃ M') : MeaningAlign S' M' :=
  fun s' m' => A (e.symm s') (f.symm m')

/-- **The sequence reading of one glyph (DEFINITIONAL — the
STIPULATED ENCODING SEMANTICS, frozen at this pin).** Under the
seed's instrumental links (`SeedCoreEncoding.instrumentalLinks`),
exactly four glyphs carry exactly one link each, and the reading
assigns those primes: `tet` ↦ MOVE, `kap` ↦ TOUCH, `ayin` ↦ SEE,
`pe` ↦ SAY. Every other glyph reads as `none`: the seventeen
uncovered glyphs (gaps — the reading does not invent meanings) and
`yod`, the seed's conflation witness, which carries TWO links
(TOUCH and DO) and so has no single denoted prime — the reading
refuses it rather than choosing. §3 proves this table is the
encoded data (`seedRead_faithful`), so the stipulation is
data-true, not invented. -/
def seedRead : Glyph → Option Prime
  | .tet => some Prime.MOVE
  | .kap => some Prime.TOUCH
  | .ayin => some Prime.SEE
  | .pe => some Prime.SAY
  | _ => none

/-- **The sequence reading of a word (DEFINITIONAL — the
STIPULATED ENCODING SEMANTICS, frozen at this pin).** A word's
sequence denotation is the sequence of its glyphs' read primes,
in the word's own order; if any glyph is unread (a gap, or the
conflated `yod`), the word has NO sequence denotation (`none`).
This tests the direction-sensitivity of the ENCODING only; it is
not a semantics for any language, and pin N2 is untouched. -/
def wordDenote : List Glyph → Option (List Prime)
  | [] => some []
  | g :: w => (seedRead g).bind fun p => (wordDenote w).map fun ps => p :: ps

/-! ## §2. WD-1, first half — the landed model is direction-blind (a RESULT)

The scoping's §3.2, proved. A relation over atoms has no order
for a direction to act on: the only action its shape supports is
relabeling (transport along equivalences), and the four criterion
predicates are invariant under it. Reversal of atoms is not false
in the landed model — it is INEXPRESSIBLE — and these four
theorems are the exact, permanent form of that measured
limitation of the unified-language model as built. GENERIC grade:
true of every alignment, which is precisely the point — the
criterion sees only the abstract relation. -/

section Blindness

variable {S S' M M' : Type*}

/-- **Blindness, no-conflation (GENERIC).** Functionality of an
alignment is invariant under relabeling of glyphs and meanings:
the criterion cannot tell a relabeled alignment from the
original, so it cannot see any structure a relabeling would
carry — direction included. -/
theorem MeaningAlign.transport_functional (A : MeaningAlign S M)
    (e : S ≃ S') (f : M ≃ M') :
    (A.transport e f).Functional ↔ A.Functional := by
  constructor
  · intro h s m₁ m₂ h₁ h₂
    have h' := h (e s) (f m₁) (f m₂)
      (by simpa [MeaningAlign.transport] using h₁)
      (by simpa [MeaningAlign.transport] using h₂)
    exact f.injective h'
  · intro h s' m₁' m₂' h₁ h₂
    have h' := h (e.symm s') (f.symm m₁') (f.symm m₂')
      (by simpa [MeaningAlign.transport] using h₁)
      (by simpa [MeaningAlign.transport] using h₂)
    exact f.symm.injective h'

/-- **Blindness, no-gaps (GENERIC).** Totality is invariant
under relabeling, by the same shape-blindness. -/
theorem MeaningAlign.transport_total (A : MeaningAlign S M)
    (e : S ≃ S') (f : M ≃ M') :
    (A.transport e f).Total ↔ A.Total := by
  constructor
  · intro h s
    obtain ⟨m', hm'⟩ := h (e s)
    exact ⟨f.symm m', by simpa [MeaningAlign.transport] using hm'⟩
  · intro h s'
    obtain ⟨m, hm⟩ := h (e.symm s')
    exact ⟨f m, by simpa [MeaningAlign.transport] using hm⟩

/-- **Blindness, no-synonymy (GENERIC).** Injectivity of an
alignment is invariant under relabeling. -/
theorem MeaningAlign.transport_injective (A : MeaningAlign S M)
    (e : S ≃ S') (f : M ≃ M') :
    (A.transport e f).InjectiveAlign ↔ A.InjectiveAlign := by
  constructor
  · intro h s₁ s₂ m h₁ h₂
    have h' := h (e s₁) (e s₂) (f m)
      (by simpa [MeaningAlign.transport] using h₁)
      (by simpa [MeaningAlign.transport] using h₂)
    exact e.injective h'
  · intro h s₁' s₂' m' h₁ h₂
    have h' := h (e.symm s₁') (e.symm s₂') (f.symm m')
      (by simpa [MeaningAlign.transport] using h₁)
      (by simpa [MeaningAlign.transport] using h₂)
    exact e.symm.injective h'

/-- **Blindness, no-unnamed-meanings (GENERIC).** Surjectivity
of an alignment is invariant under relabeling. -/
theorem MeaningAlign.transport_surjective (A : MeaningAlign S M)
    (e : S ≃ S') (f : M ≃ M') :
    (A.transport e f).SurjectiveAlign ↔ A.SurjectiveAlign := by
  constructor
  · intro h m
    obtain ⟨s', hs'⟩ := h (f m)
    exact ⟨e.symm s', by simpa [MeaningAlign.transport] using hs'⟩
  · intro h m'
    obtain ⟨s, hs⟩ := h (f.symm m')
    exact ⟨e s, by simpa [MeaningAlign.transport] using hs⟩

/-- **The one-glyph vacuity, in exact form (the glyph-level
half of K-WD-REV, landed as a deliverable).** A written form in
the landed model is a single glyph; at word level its shadow
is: every word of length at most one is its own reverse, and
its sequence denotation is fixed by reversal. Glyph-level
denotation is direction-blind as a THEOREM about the model's
shape — not an empirical finding about Phoenician. -/
theorem wordDenote_reverse_of_length_le_one (w : List Glyph)
    (hw : w.length ≤ 1) : wordDenote w.reverse = wordDenote w := by
  match w, hw with
  | [], _ => rfl
  | [g], _ => rfl

end Blindness

/-! ## §3. WD-1, second half (machinery) — the reading is data-true and order-faithful

Two honesty lemmas before the exhibit. `seedRead_faithful`: the
pin's stipulated table IS the seed's encoded instrumental data —
for every glyph and prime, the reading assigns the prime if and
only if the pair is an instrumental link; the check is over the
encoding's own enumeration lists, mirroring the landed
`functionalCheck` bridge pattern (list scans, because the
derived `Fintype` instances do not kernel-reduce in this pin).
`wordDenote_reverse`: the sequence reading is order-faithful —
the denotation of a reversed word is the reverse of the
denotation. Stipulated, stated, and load-bearing for the
exhibit's honesty: order-faithfulness favors neither outcome of
§4's test; the DATA decides. -/

/-- **The reading's data-truth.** The stipulated `seedRead`
table is exactly the seed's encoded instrumental link data,
read functionally: `seedRead g = some p` if and only if
`(g, p)` is an instrumental link AND that link is the glyph's
ONLY link. The uniqueness conjunct is the data's own shape,
not a patch: the one glyph with two links — `yod`, TOUCH and
DO — fails it, which is exactly why the reading refuses `yod`
rather than choosing (the conflation stays visible in the
reading itself). Proved from the encoding's enumeration
lists: the Bool scan below decides the iff for all 22 × 65
pairs, and the bridge (`List.all` over complete lists) lifts
it. -/
theorem seedRead_faithful (g : Glyph) (p : Prime) :
    seedRead g = some p ↔ (g, p) ∈ instrumentalLinks ∧
      ∀ q ∈ primeList, (g, q) ∈ instrumentalLinks → q = p := by
  have key : ∀ g ∈ glyphList, ∀ p ∈ primeList,
      (seedRead g = some p ↔ (g, p) ∈ instrumentalLinks ∧
        ∀ q ∈ primeList, (g, q) ∈ instrumentalLinks → q = p) := by
    have h : (glyphList.all fun g => primeList.all fun p =>
        decide (seedRead g = some p ↔ (g, p) ∈ instrumentalLinks ∧
          ∀ q ∈ primeList, (g, q) ∈ instrumentalLinks → q = p)) = true := by
      decide
    simpa only [List.all_eq_true, decide_eq_true_eq] using h
  exact key g (glyph_mem_glyphList g) p (prime_mem_primeList p)

/-- **The reading is order-faithful (stipulated, on its face).**
The sequence denotation of a reversed word is the reverse of
the word's sequence denotation — by induction through an
append form. Order-faithfulness is what makes §4 a TEST rather
than a tautology in either direction: the reading transports
order exactly, so whether a denotation sequence survives
reversal unchanged is a property of the DATA (the primes the
seed assigns), never of the reading. -/
theorem wordDenote_reverse (w : List Glyph) :
    wordDenote w.reverse = (wordDenote w).map List.reverse := by
  have e0 : wordDenote ([] : List Glyph) = some [] := rfl
  have happ : ∀ w₁ w₂ : List Glyph,
      wordDenote (w₁ ++ w₂) =
        (wordDenote w₁).bind fun ps₁ => (wordDenote w₂).map fun ps₂ => ps₁ ++ ps₂ := by
    intro w₁
    induction w₁ with
    | nil =>
      intro w₂
      simp only [List.nil_append]
      rw [e0]
      cases h : wordDenote w₂ with
      | none => rfl
      | some ps₂ => rfl
    | cons g w₁ ih =>
      intro w₂
      have e : wordDenote (g :: (w₁ ++ w₂)) =
          (seedRead g).bind (fun p => (wordDenote (w₁ ++ w₂)).map
            (fun ps => p :: ps)) := rfl
      have e' : wordDenote (g :: w₁) =
          (seedRead g).bind (fun p => (wordDenote w₁).map
            (fun ps => p :: ps)) := rfl
      rw [List.cons_append, e, e', ih w₂]
      cases h₁ : seedRead g with
      | none => rfl
      | some p =>
        cases h₂ : wordDenote w₁ with
        | none => rfl
        | some ps₁ =>
          cases h₃ : wordDenote w₂ with
          | none => rfl
          | some ps₂ => rfl
  induction w with
  | nil => rfl
  | cons g w ih =>
    have e' : wordDenote (g :: w) =
        (seedRead g).bind (fun p => (wordDenote w).map
          (fun ps => p :: ps)) := rfl
    have hsing : wordDenote [g] = (seedRead g).map (fun p => [p]) := by
      have e : wordDenote [g] =
          (seedRead g).bind (fun q => (wordDenote []).map
            (fun ps => q :: ps)) := rfl
      rw [e, e0]
      cases seedRead g with
      | none => rfl
      | some p => rfl
    rw [List.reverse_cons, happ w.reverse [g], ih, hsing, e']
    cases h₁ : seedRead g with
    | none =>
      cases h₂ : wordDenote w with
      | none => rfl
      | some ps => rfl
    | some p =>
      cases h₂ : wordDenote w with
      | none => rfl
      | some ps =>
        show some (ps.reverse ++ [p]) = some (p :: ps).reverse
        rw [List.reverse_cons]

/-! ## §4. WD-1, second half (the exhibit) — THE REVERSAL TEST, decided by the data

The pin's test set (header §1): words over the four functional
glyphs {tet, kap, ayin, pe}, length at most 3. Over that set the
test is decidable and its outcome was genuinely open when the
pin was frozen: either some word's denotation sequence is not a
palindrome — direction is content, at encoding grade — or none
is, and K-WD-REV fires at word level too. THE DATA DECIDES, and
it decides POSITIVE: the word [ayin, pe] (eye, mouth) denotes
[SEE, SAY] read left-to-right; read right-to-left — the seed's
native Phoenician direction — the same written form denotes
[SAY, SEE]. The two readings DIFFER. The witness is minimal —
length 2 — and its content is the diversity of the seed's own
data (ayin ↦ SEE ≠ SAY ↦ pe): the reading, order-faithful by
stipulation, favors neither outcome; had every covered glyph
denoted the same prime, or had the covered set been poorer, the
test would have come back vacuous and K-WD-REV would have fired
as the result, reported the same way.

K-WD-REV: did NOT fire (word level). Its glyph-level half
stands landed in §2 as the blindness deliverable.
K-WD-FIAT: DECIDED at WD-1 — did NOT fire. The direction datum
does work the old criterion cannot do: §4's theorems are about
WORDS, a type the criterion has never quantified over, and their
truth is decided by the seed's data, not by the pin's
stipulations (the stipulation is order-faithfulness, which is
outcome-neutral). -/

/-- **THE EXHIBIT, left-to-right reading.** The written form
[ayin, pe] — eye, mouth — denotes the sequence [SEE, SAY]
under the LTR reading. By computation over the seed's encoded
data (the reading's table, proved data-true in §3). -/
theorem wordDenote_ayin_pe :
    wordDenote (WriteDir.readingOf .ltr [Glyph.ayin, Glyph.pe]) =
      some [Prime.SEE, Prime.SAY] := rfl

/-- **THE EXHIBIT, the seed's native reading.** The SAME
written form [ayin, pe], read right-to-left — Phoenician's own
direction — denotes [SAY, SEE]. By computation over the same
data. -/
theorem wordDenote_ayin_pe_rtl :
    wordDenote (WriteDir.readingOf .rtl [Glyph.ayin, Glyph.pe]) =
      some [Prime.SAY, Prime.SEE] := rfl

/-- **DIRECTION IS CONTENT (at encoding grade).** The two
readings of one written form denote DIFFERENTLY: the LTR and
RTL sequence denotations of [ayin, pe] are unequal. This is
the encoding-grade twin of the 2026-10-30 commutator flip —
an analogy of shape only (order-sensitivity with a meaning
change), stated here without borrowing that result's
authority. It says nothing about natural language: it is a
theorem about the seed's encoded data under the stipulated
sequence reading, and its rank is exactly that. -/
theorem reading_direction_is_content :
    wordDenote (WriteDir.readingOf .ltr [Glyph.ayin, Glyph.pe]) ≠
      wordDenote (WriteDir.readingOf .rtl [Glyph.ayin, Glyph.pe]) := by
  rw [wordDenote_ayin_pe, wordDenote_ayin_pe_rtl]
  decide

end ThetLogos
