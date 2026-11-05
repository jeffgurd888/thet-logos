import Mathlib.Tactic
import ThetLogos.MeaningBridge

/-!
# ThetLogos.SeedCoreEncoding — SC-2: the seed alignment, encoded as data

HONESTY LEDGER (read before citing):

- COMMISSION. Brick SC-2 of the seed-core exhibit (scoping:
  `~/workspace/your_files/seed-core-scoping-2026-11-05.md`; the
  table it consumes: `~/workspace/your_files/seed-core-table-2026-11-05.tsv`,
  brick SC-1). Origin, Jeff (2026-11-05, T5, filed verbatim in
  `~/memory/2026-11-05.md`): the unified language "hasn't been
  written yet"; "we need a computer core humans can read like a
  Unicode". This module is the ENCODING only: the glyph set, the
  prime set, and SC-1's link column transcribed as finite data,
  with proved bridges to the Meaning Bridge's own predicates
  (`MeaningBridge.lean`, pin N1's interface, consumed not
  extended) and decidability of those predicates over the data.
- WHAT THIS MODULE IS NOT. It is NOT the census: SC-3 computes
  and publishes the gap list, the conflation list, the
  glyph-side gaps, and the synonymy list. This brick contains
  exactly ONE evaluation of a predicate on the encoded data (a
  smoke check that the machinery computes), chosen as the
  cheapest; it draws no census conclusion. It is NOT a
  semantics for any natural language: the glyphs are 22 finite
  constructors and the primes are 65 finite constructors, and
  the theorems here are T1 ONLY about this finite encoded
  table. Pin N2 (meaning vs reference) is NOT discharged by a
  seed; N4 is not advanced (SC-1's correlate column is T5
  annotation and is deliberately NOT encoded here — the audit
  never touches it); N5 is not approached. Universality is NOT
  claimed for the seed, for the prime set, or for anything
  else; "contains every language" stays a horizon statement.
  NO CLAIM; dials 0/4.
- DATA PROVENANCE. Glyph identities: the 22 Phoenician letters
  in Unicode codepoint order (U+10900–U+10915), constructor
  names the standard transliterations as in the SC-1 table.
  Glosses are NOT encoded (they are T2 text and live in the
  SC-1 table); only the table's link column is transcribed.
  Links are drawn ONLY from each row's primary gloss;
  alternate glosses are recorded in the table and are NOT
  links here. Link kinds are kept in the data design: two
  Finsets, `denotativeLinks` and `instrumentalLinks`.
- THE 62/65 DISCREPANCY, CORRECTED (SC-2b, 2026-11-05). As
  first landed, this module encoded 62 primes: the scoping
  §2 enumeration's single entry EXIST collapsed the
  canonical table's four-prime location / existence /
  possession / specification cluster into one slot. The
  cluster, verified against the canonical Goddard–
  Wierzbicka (2014) table as reproduced in *Conversatoria
  Linguistica* XVI (2024), Table 1, captioned "(Goddard &
  Wierzbicka 2014)", with the 2014 stabilisation at 65
  confirmed by Wierzbicka (*Russian Journal of Linguistics*
  25(2), 2021), is BE (SOMEWHERE), THERE IS, BE
  (SOMEONE/SOMETHING), (IS) MINE. The possession prime was
  designated HAVE in pre-2014 tables; in 2014 it was
  briefly BE SOMEONE'S and stabilised as (IS) MINE
  (Goddard & Wierzbicka 2016, *Language Sciences* 56) — the
  earlier draft of this note named HAVE, which is the same
  prime under its older designation. This module now
  encodes the canonical 65, in the canonical positions;
  the scoping and the SC-1 dossier are corrected in the
  same brick. The link data did not change: no SC-1 link
  referenced EXIST or any prime of the cluster (the links
  touch only MOVE, TOUCH, DO, SEE, SAY).
-/

namespace ThetLogos

/-! ## §1. The two finite types: glyphs and primes

Both are bare finite types — constructors and nothing else.
The order of constructors is the order of the sources:
codepoint order for glyphs (SC-1 table rows 1–22), the
scoping §2 enumeration order for primes. -/

/-- **The glyphs (DEFINITIONAL).** The 22 Phoenician letters,
in Unicode codepoint order U+10900–U+10915. Constructor names
are the SC-1 table's transliterations, diacritics dropped:
`alep` ʾālep, `bet` bēt, `gimel` gīmel, `dalet` dālet, `he` hē,
`waw` wāw, `zayin` zayin, `het` ḥēt, `tet` ṭēt, `yod` yōd,
`kap` kāp, `lamed` lāmd, `mem` mēm, `nun` nūn, `samek` sāmek,
`ayin` ʿayin, `pe` pē, `sade` ṣādē, `qop` qōp, `res` rēš,
`shin` šīn, `taw` tāw. -/
inductive Glyph
  | alep | bet | gimel | dalet | he | waw | zayin | het | tet | yod | kap
  | lamed | mem | nun | samek | ayin | pe | sade | qop | res | shin | taw
  deriving DecidableEq, Repr

/-- **The primes (DEFINITIONAL).** The NSM prime set AS
ENUMERATED in the scoping §2 (the list the SC-1 dossier pins
by citation to Goddard–Wierzbicka 2014) — 65 constructors, as
corrected in SC-2b; see the header's correction note before
citing the count.
Constructor names are the primes' English exponents with
punctuation flattened: `SOMETHING` is SOMETHING/THING, `OTHER`
is OTHER/ELSE, `THE_SAME` is THE SAME, `MUCH_MANY` is
MUCH/MANY, `LITTLE_FEW` is LITTLE/FEW, `DONT_WANT` is DON'T
WANT, `WHEN_TIME` is WHEN/TIME, `A_LONG_TIME` / `A_SHORT_TIME`
/ `FOR_SOME_TIME` are A LONG TIME / A SHORT TIME / FOR SOME
TIME, `WHERE_PLACE` is WHERE/PLACE, `LIKE_WAY` is LIKE/WAY,
`BE_SOMEWHERE` is BE (SOMEWHERE), `THERE_IS` is THERE IS,
`BE_SOMEONE_SOMETHING` is BE (SOMEONE/SOMETHING), `IS_MINE`
is (IS) MINE. -/
inductive Prime
  | I | YOU | SOMEONE | SOMETHING | PEOPLE | BODY
  | KIND | PART
  | THIS | THE_SAME | OTHER
  | ONE | TWO | SOME | ALL | MUCH_MANY | LITTLE_FEW
  | GOOD | BAD
  | BIG | SMALL
  | THINK | KNOW | WANT | DONT_WANT | FEEL | SEE | HEAR
  | SAY | WORDS | TRUE
  | DO | HAPPEN | MOVE
  | BE_SOMEWHERE | THERE_IS | BE_SOMEONE_SOMETHING | IS_MINE
  | LIVE | DIE
  | WHEN_TIME | NOW | BEFORE | AFTER | A_LONG_TIME | A_SHORT_TIME
  | FOR_SOME_TIME | MOMENT
  | WHERE_PLACE | HERE | ABOVE | BELOW | FAR | NEAR | SIDE | INSIDE
  | TOUCH
  | NOT | MAYBE | CAN | BECAUSE | IF
  | VERY | MORE
  | LIKE_WAY
  deriving DecidableEq, Repr

/-! ### The enumeration lists

The checks of §4 quantify over explicit `List`s of all
constructors, not over `Finset.univ`: the derived
`Fintype` instances for these types do not kernel-reduce in
this Mathlib pin (their generated `elems` field is
ill-typed under the kernel's coercion transparency), and
the manual `Finset` instances blow up the elaborator at
this size (65 constructors; 62 as first landed). Lists
compute; the two membership
theorems below are the completeness of the lists, proved
constructor by constructor. -/

/-- **All glyphs (DATA).** The 22 constructors, in the
codepoint order of §1. -/
def glyphList : List Glyph :=
  [Glyph.alep, Glyph.bet, Glyph.gimel, Glyph.dalet, Glyph.he, Glyph.waw,
   Glyph.zayin, Glyph.het, Glyph.tet, Glyph.yod, Glyph.kap, Glyph.lamed,
   Glyph.mem, Glyph.nun, Glyph.samek, Glyph.ayin, Glyph.pe, Glyph.sade,
   Glyph.qop, Glyph.res, Glyph.shin, Glyph.taw]

/-- **All primes (DATA).** The 65 constructors of the
canonical set, in the scoping §2 order (as corrected in
SC-2b). -/
def primeList : List Prime :=
  [Prime.I, Prime.YOU, Prime.SOMEONE, Prime.SOMETHING, Prime.PEOPLE,
   Prime.BODY, Prime.KIND, Prime.PART, Prime.THIS, Prime.THE_SAME,
   Prime.OTHER, Prime.ONE, Prime.TWO, Prime.SOME, Prime.ALL,
   Prime.MUCH_MANY, Prime.LITTLE_FEW, Prime.GOOD, Prime.BAD, Prime.BIG,
   Prime.SMALL, Prime.THINK, Prime.KNOW, Prime.WANT, Prime.DONT_WANT,
   Prime.FEEL, Prime.SEE, Prime.HEAR, Prime.SAY, Prime.WORDS, Prime.TRUE,
   Prime.DO, Prime.HAPPEN, Prime.MOVE, Prime.BE_SOMEWHERE, Prime.THERE_IS,
   Prime.BE_SOMEONE_SOMETHING, Prime.IS_MINE, Prime.LIVE, Prime.DIE,
   Prime.WHEN_TIME, Prime.NOW, Prime.BEFORE, Prime.AFTER, Prime.A_LONG_TIME,
   Prime.A_SHORT_TIME, Prime.FOR_SOME_TIME, Prime.MOMENT, Prime.WHERE_PLACE,
   Prime.HERE, Prime.ABOVE, Prime.BELOW, Prime.FAR, Prime.NEAR, Prime.SIDE,
   Prime.INSIDE, Prime.TOUCH, Prime.NOT, Prime.MAYBE, Prime.CAN,
   Prime.BECAUSE, Prime.IF, Prime.VERY, Prime.MORE, Prime.LIKE_WAY]

/-- **The glyph list is complete.** Every glyph occurs in
`glyphList` — the list is the whole type. -/
theorem glyph_mem_glyphList (g : Glyph) : g ∈ glyphList := by
  cases g <;> decide

/-- **The prime list is complete.** Every prime occurs in
`primeList` — the list is the whole type. -/
theorem prime_mem_primeList (p : Prime) : p ∈ primeList := by
  cases p <;> decide

/-! ## §2. The link data (SC-1's link column, transcribed)

Kind is kept in the design: a link lives in exactly one of the
two Finsets, and `LinkKind` + `linksOfKind` make the kind a
value the census (SC-3) can quantify over. The transcription
is exact: the SC-1 table's `prime_links` column under the
primary-gloss policy — 6 pairs, all instrumental; the
denotative set is empty, and its emptiness is data, recorded
here as the empty Finset, not as an omission. -/

/-- **Link kind (DEFINITIONAL).** A link is `denotative` when
the glyph's primary gloss IS the prime (or its standard
allolex) and `instrumental` when the gloss names the prime's
organ, instrument, or canonical object (scoping §1.3, rule
4). Anything looser is not a link and appears in neither
set. -/
inductive LinkKind
  | denotative
  | instrumental
  deriving DecidableEq, Repr

/-- **The denotative links (DATA).** SC-1's denotative link
set: EMPTY. No glyph's primary gloss is a prime — the
concrete object-nouns of the glosses and the relational
primes do not meet denotatively anywhere in the 22 rows.
Stated as data; SC-3's census reads it, this brick does not
argue from it. -/
def denotativeLinks : Finset (Glyph × Prime) := ∅

/-- **The instrumental links (DATA).** SC-1's instrumental
link set: exactly 6 pairs, each the organ/instrument reading
of a primary gloss — ṭēt (wheel) → MOVE, the mover's
instrument; yōd (hand) → TOUCH and → DO, the organ of touch
and the canonical instrument of doing; kāp (palm) → TOUCH,
the touching surface; ʿayin (eye) → SEE, the organ of the
prime; pē (mouth) → SAY, the organ of speech. -/
def instrumentalLinks : Finset (Glyph × Prime) :=
  {(Glyph.tet, Prime.MOVE), (Glyph.yod, Prime.TOUCH), (Glyph.yod, Prime.DO),
   (Glyph.kap, Prime.TOUCH), (Glyph.ayin, Prime.SEE), (Glyph.pe, Prime.SAY)}

/-- **The seed links (DATA).** The primary reading of the
seed: denotative ∪ instrumental — every link SC-1 drew, of
either kind. (The denotative-only reading is
`denotativeLinks` itself; SC-3 reports both readings.) -/
def seedLinks : Finset (Glyph × Prime) := denotativeLinks ∪ instrumentalLinks

/-- **Links by kind (DEFINITIONAL).** The kind-indexed view
of the same data: `linksOfKind k` is the link set of kind
`k`. The two kinds partition the seed links — each pair of
`seedLinks` sits in exactly one kind's set. -/
def linksOfKind : LinkKind → Finset (Glyph × Prime)
  | .denotative => denotativeLinks
  | .instrumental => instrumentalLinks

/-! ## §3. The induced alignments

`alignOf` is the scoping §4 encoding, verbatim in shape: the
glyph carries the prime iff the pair is in the link data.
Everything the census will state is a MeaningBridge predicate
of an `alignOf`, converted from data-checks by §4's bridges —
never a hand-asserted list. -/

/-- **The alignment induced by link data (DEFINITIONAL).**
`alignOf links` is the `MeaningAlign Glyph Prime` whose
relation is membership in `links`: the glyph carries the
prime exactly when SC-1's table drew the link. -/
def alignOf (links : Finset (Glyph × Prime)) : MeaningAlign Glyph Prime :=
  fun g p => (g, p) ∈ links

/-- **Reading the induced alignment (DEFINITIONAL).** The
induced alignment at a glyph and a prime is membership in
the data — the definition, checked by `rfl`. -/
theorem alignOf_apply (links : Finset (Glyph × Prime)) (g : Glyph) (p : Prime) :
    alignOf links g p ↔ (g, p) ∈ links := Iff.rfl

/-- **The denotative reading (DEFINITIONAL).** The alignment
of denotative links alone — the strict reading of the seed,
whose link set is empty. -/
def denotativeAlign : MeaningAlign Glyph Prime := alignOf denotativeLinks

/-- **The seed alignment (DEFINITIONAL).** The primary
reading: the alignment induced by all of SC-1's links
(denotative ∪ instrumental). This is the alignment the
census (SC-3) primarily audits. -/
def seedAlign : MeaningAlign Glyph Prime := alignOf seedLinks

/-! ## §4. The data-checks, and the bridges to the predicates

Each MeaningBridge predicate gets a Bool-valued check over
the link data — finite scans over the enumeration lists of
§1 (`glyphList`, `primeList`) with membership in the link
set itself. The bridge theorems identify each check
with the predicate ITSELF (not a paraphrase): the check
returns `true` if and only if the induced alignment has the
property, in `MeaningBridge`'s own definitions. These
bridges are what make SC-3's census computation rather than
assertion: evaluate the check, convert by the bridge. -/

/-- **No-conflation check (DATA CHECK).** Scans every glyph
and every pair of primes: wherever both pairs are links,
the primes must agree. `true` iff the induced alignment
carries no glyph to two distinct primes. -/
def functionalCheck (links : Finset (Glyph × Prime)) : Bool :=
  glyphList.all fun g => primeList.all fun p₁ => primeList.all fun p₂ =>
    decide ((g, p₁) ∈ links → (g, p₂) ∈ links → p₁ = p₂)

/-- **No-gaps check (DATA CHECK).** Scans every glyph for at
least one linked prime. `true` iff every glyph carries
something. -/
def totalCheck (links : Finset (Glyph × Prime)) : Bool :=
  glyphList.all fun g => primeList.any fun p => decide ((g, p) ∈ links)

/-- **No-unnamed-meanings check (DATA CHECK).** Scans every
prime for at least one linked glyph. `true` iff every prime
is carried by something. -/
def surjectiveCheck (links : Finset (Glyph × Prime)) : Bool :=
  primeList.all fun p => glyphList.any fun g => decide ((g, p) ∈ links)

/-- **No-synonymy check (DATA CHECK).** Scans every prime
and every pair of glyphs: wherever both pairs are links,
the glyphs must agree. `true` iff no prime is carried by
two distinct glyphs. -/
def injectiveCheck (links : Finset (Glyph × Prime)) : Bool :=
  glyphList.all fun g₁ => glyphList.all fun g₂ => primeList.all fun p =>
    decide ((g₁, p) ∈ links → (g₂, p) ∈ links → g₁ = g₂)

/-- **Bridge: the no-conflation check IS functionality
(GENERIC over the data).** The check computes
`MeaningAlign.Functional` of the induced alignment — the
predicate itself, by its own definition, converted from the
finite scan in both directions. -/
theorem functionalCheck_eq_true_iff (links : Finset (Glyph × Prime)) :
    functionalCheck links = true ↔ (alignOf links).Functional := by
  constructor
  · intro h g p₁ p₂ h₁ h₂
    have key : ∀ g ∈ glyphList, ∀ p₁ ∈ primeList, ∀ p₂ ∈ primeList,
        ((g, p₁) ∈ links → (g, p₂) ∈ links → p₁ = p₂) := by
      simpa only [functionalCheck, List.all_eq_true, decide_eq_true_eq] using h
    exact key g (glyph_mem_glyphList g) p₁ (prime_mem_primeList p₁) p₂
      (prime_mem_primeList p₂) h₁ h₂
  · intro h
    unfold functionalCheck
    rw [List.all_eq_true]
    intro g _
    rw [List.all_eq_true]
    intro p₁ _
    rw [List.all_eq_true]
    intro p₂ _
    rw [decide_eq_true_eq]
    exact h g p₁ p₂

/-- **Bridge: the no-gaps check IS totality (GENERIC over
the data).** The check computes `MeaningAlign.Total` of the
induced alignment. -/
theorem totalCheck_eq_true_iff (links : Finset (Glyph × Prime)) :
    totalCheck links = true ↔ (alignOf links).Total := by
  constructor
  · intro h g
    have key : ∀ g ∈ glyphList, ∃ p ∈ primeList, (g, p) ∈ links := by
      simpa only [totalCheck, List.all_eq_true, List.any_eq_true,
        decide_eq_true_eq] using h
    obtain ⟨p, -, hp⟩ := key g (glyph_mem_glyphList g)
    exact ⟨p, hp⟩
  · intro h
    unfold totalCheck
    rw [List.all_eq_true]
    intro g _
    rw [List.any_eq_true]
    obtain ⟨p, hp⟩ := h g
    refine ⟨p, prime_mem_primeList p, ?_⟩
    rw [decide_eq_true_eq]
    exact hp

/-- **Bridge: the no-unnamed-meanings check IS surjectivity
(GENERIC over the data).** The check computes
`MeaningAlign.SurjectiveAlign` of the induced alignment. -/
theorem surjectiveCheck_eq_true_iff (links : Finset (Glyph × Prime)) :
    surjectiveCheck links = true ↔ (alignOf links).SurjectiveAlign := by
  constructor
  · intro h p
    have key : ∀ p ∈ primeList, ∃ g ∈ glyphList, (g, p) ∈ links := by
      simpa only [surjectiveCheck, List.all_eq_true, List.any_eq_true,
        decide_eq_true_eq] using h
    obtain ⟨g, -, hg⟩ := key p (prime_mem_primeList p)
    exact ⟨g, hg⟩
  · intro h
    unfold surjectiveCheck
    rw [List.all_eq_true]
    intro p _
    rw [List.any_eq_true]
    obtain ⟨g, hg⟩ := h p
    refine ⟨g, glyph_mem_glyphList g, ?_⟩
    rw [decide_eq_true_eq]
    exact hg

/-- **Bridge: the no-synonymy check IS injectivity
(GENERIC over the data).** The check computes
`MeaningAlign.InjectiveAlign` of the induced alignment. -/
theorem injectiveCheck_eq_true_iff (links : Finset (Glyph × Prime)) :
    injectiveCheck links = true ↔ (alignOf links).InjectiveAlign := by
  constructor
  · intro h g₁ g₂ p h₁ h₂
    have key : ∀ g₁ ∈ glyphList, ∀ g₂ ∈ glyphList, ∀ p ∈ primeList,
        ((g₁, p) ∈ links → (g₂, p) ∈ links → g₁ = g₂) := by
      simpa only [injectiveCheck, List.all_eq_true, decide_eq_true_eq] using h
    exact key g₁ (glyph_mem_glyphList g₁) g₂ (glyph_mem_glyphList g₂) p
      (prime_mem_primeList p) h₁ h₂
  · intro h
    unfold injectiveCheck
    rw [List.all_eq_true]
    intro g₁ _
    rw [List.all_eq_true]
    intro g₂ _
    rw [List.all_eq_true]
    intro p _
    rw [decide_eq_true_eq]
    exact h g₁ g₂ p

/-! ## §5. Decidability of the four predicates over the data

Each predicate of an induced alignment is decidable, and
the decision procedure is the §4 check itself, converted by
the §4 bridge: the instances below are the bridges read as
algorithms. This is SC-2's contract with SC-3 — the census
predicates COMPUTE. (Stated for every link set, so both
readings — denotative-only and the seed — are covered.) -/

instance (links : Finset (Glyph × Prime)) :
    Decidable (alignOf links).Functional :=
  if h : functionalCheck links = true then
    isTrue ((functionalCheck_eq_true_iff links).mp h)
  else
    isFalse fun hf => h ((functionalCheck_eq_true_iff links).mpr hf)

instance (links : Finset (Glyph × Prime)) :
    Decidable (alignOf links).Total :=
  if h : totalCheck links = true then
    isTrue ((totalCheck_eq_true_iff links).mp h)
  else
    isFalse fun hf => h ((totalCheck_eq_true_iff links).mpr hf)

instance (links : Finset (Glyph × Prime)) :
    Decidable (alignOf links).SurjectiveAlign :=
  if h : surjectiveCheck links = true then
    isTrue ((surjectiveCheck_eq_true_iff links).mp h)
  else
    isFalse fun hf => h ((surjectiveCheck_eq_true_iff links).mpr hf)

instance (links : Finset (Glyph × Prime)) :
    Decidable (alignOf links).InjectiveAlign :=
  if h : injectiveCheck links = true then
    isTrue ((injectiveCheck_eq_true_iff links).mp h)
  else
    isFalse fun hf => h ((injectiveCheck_eq_true_iff links).mpr hf)

/-! ## §6. Smoke: the machinery computes (NOT the census)

One evaluation, the cheapest, proving the evaluation path
actually reduces end to end: the seed alignment is not
total, decided by the kernel through §5's instance. This is
a machinery check only — SC-3 states and proves the census
proper (the named gap lists, the conflation list, both
readings); nothing here is a census result and no census
conclusion should be cited from it. -/

/-- **SMOKE (machinery check, NOT a census result).** The
seed alignment fails totality, by kernel decision through
the §5 instance: the encode → check → bridge path reduces.
Which glyphs gap, and every other census question, is
SC-3's, not this brick's. -/
theorem seedAlign_not_total : ¬ seedAlign.Total := by
  show ¬ (alignOf seedLinks).Total
  decide

end ThetLogos
