import Mathlib.Tactic
import ThetLogos.MeaningBridge
import ThetLogos.SeedCoreEncoding

/-!
# ThetLogos.SeedCoreCensus — SC-3: the census of the seed alignment

HONESTY LEDGER (read before citing):

- COMMISSION. Brick SC-3 of the seed-core exhibit (scoping:
  `~/workspace/your_files/seed-core-scoping-2026-11-05.md`; the
  table: brick SC-1, `seed-core-table-2026-11-05.md`; the
  encoding: brick SC-2, `SeedCoreEncoding.lean`). This is the
  chain's final brick: the census itself — every number below
  is COMPUTED from SC-2's link data through SC-2's checks and
  bridges (`functionalCheck` / `totalCheck` / `surjectiveCheck`
  / `injectiveCheck` and their `*_eq_true_iff` bridges to the
  Meaning Bridge's own predicates), plus the per-prime and
  per-glyph coverage reflections of §1, proved here in the
  same style. No list in this module is hand-asserted: each
  characterization theorem is closed by finite case analysis
  and kernel decision over the data.
- THE DENOMINATOR. The prime set is the canonical 65 of
  Goddard–Wierzbicka (2014), INCLUDING the possession prime
  (IS) MINE, as corrected in SC-2b (the scoping §2's original
  enumeration collapsed the four-prime location / existence /
  possession / specification cluster into one entry EXIST and
  named only 62; see the correction records in the scoping
  §2, the SC-1 dossier §6, and `SeedCoreEncoding`'s header).
  Every "of 65" below is that canonical 65.
- THE THREE READINGS. (i) The PRIMARY reading: `seedAlign`,
  SC-1's six instrumental links, denotative set empty —
  covered primes 5 of 65, gap 60. (ii) The DENOTATIVE
  BASELINE: `denotativeAlign`, the empty link set — covered
  0 of 65, gap 65; functional and injective hold VACUOUSLY,
  and the module says so in those words. (iii) The WATCHLIST
  reading: the primary links plus the four pairs SC-1's
  dossier (departure D6) judged too loose and RECORDED
  WITHOUT DRAWING — zayin → DIE (weapon), hē → SEE (window),
  lāmd → MOVE (goad), mēm → SOMETHING/THING (water). Every
  watchlist item is labeled WATCHLIST in its name or
  docstring; the watchlist reading is a sensitivity bound on
  SC-1's judgment calls, not a second seed.
- THE HEADLINE. By `MeaningAlign.functional_total_iff`, the
  primary seed alignment is NOT the graph of any denotation
  function (§3, `seedAlign_not_denotation`): it conflates
  (yōd carries TOUCH and DO), it is synonymous (TOUCH is
  carried by yōd and kāp), it gaps on both sides (17 glyphs
  carry nothing; 60 of 65 primes are carried by nothing).
  The seed is a partial, conflated, synonymous alignment —
  a measured distance to pin N2's seat, NOT a discharge of
  N2, not a semantics for any natural language, and not
  evidence about all languages. Universality is NOT claimed;
  "contains every language" remains a horizon statement.
  NO CLAIM; dials 0/4.
-/

namespace ThetLogos

/-! ## §1. Coverage reflections (per prime, per glyph)

SC-2's four checks are whole-alignment scans. The census
also needs the pointwise questions — is THIS prime carried
by anything? does THIS glyph carry anything? — as Bool
checks with bridges of the same shape, so that the gap
lists of §§3–5 are computations through a proved reflection,
not enumerations someone typed. -/

/-- **Prime-coverage check (DATA CHECK).** Scans every glyph
for a link to the given prime. `true` iff some glyph carries
the prime in the link data. -/
def primeCoveredCheck (links : Finset (Glyph × Prime)) (p : Prime) : Bool :=
  glyphList.any fun g => decide ((g, p) ∈ links)

/-- **Bridge: the prime-coverage check IS being carried
(GENERIC over the data).** The check computes "some glyph
carries this prime" for the induced alignment. -/
theorem primeCoveredCheck_eq_true_iff (links : Finset (Glyph × Prime))
    (p : Prime) :
    primeCoveredCheck links p = true ↔ ∃ g, alignOf links g p := by
  constructor
  · intro h
    have key : ∃ g ∈ glyphList, (g, p) ∈ links := by
      simpa only [primeCoveredCheck, List.any_eq_true, decide_eq_true_eq]
        using h
    obtain ⟨g, -, hg⟩ := key
    exact ⟨g, hg⟩
  · rintro ⟨g, hg⟩
    have hg' : (g, p) ∈ links := hg
    unfold primeCoveredCheck
    rw [List.any_eq_true]
    refine ⟨g, glyph_mem_glyphList g, ?_⟩
    rw [decide_eq_true_eq]
    exact hg'

/-- **Bridge: prime-coverage check false IS the prime being
a gap (GENERIC over the data).** The check is `false` iff
no glyph carries the prime — the pointwise form of
`MeaningAlign.SurjectiveAlign`'s failure. -/
theorem primeCoveredCheck_eq_false_iff (links : Finset (Glyph × Prime))
    (p : Prime) :
    primeCoveredCheck links p = false ↔ ∀ g, ¬ alignOf links g p := by
  constructor
  · intro h g hg
    have ht : primeCoveredCheck links p = true :=
      (primeCoveredCheck_eq_true_iff links p).mpr ⟨g, hg⟩
    rw [ht] at h
    cases h
  · intro h
    cases hc : primeCoveredCheck links p with
    | false => rfl
    | true =>
      obtain ⟨g, hg⟩ := (primeCoveredCheck_eq_true_iff links p).mp hc
      exact absurd hg (h g)

/-- **Glyph-linkage check (DATA CHECK).** Scans every prime
for a link from the given glyph. `true` iff the glyph
carries something in the link data. -/
def glyphLinkedCheck (links : Finset (Glyph × Prime)) (g : Glyph) : Bool :=
  primeList.any fun p => decide ((g, p) ∈ links)

/-- **Bridge: the glyph-linkage check IS carrying something
(GENERIC over the data).** The check computes "this glyph
carries some prime" for the induced alignment. -/
theorem glyphLinkedCheck_eq_true_iff (links : Finset (Glyph × Prime))
    (g : Glyph) :
    glyphLinkedCheck links g = true ↔ ∃ p, alignOf links g p := by
  constructor
  · intro h
    have key : ∃ p ∈ primeList, (g, p) ∈ links := by
      simpa only [glyphLinkedCheck, List.any_eq_true, decide_eq_true_eq]
        using h
    obtain ⟨p, -, hp⟩ := key
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    have hp' : (g, p) ∈ links := hp
    unfold glyphLinkedCheck
    rw [List.any_eq_true]
    refine ⟨p, prime_mem_primeList p, ?_⟩
    rw [decide_eq_true_eq]
    exact hp'

/-- **Bridge: glyph-linkage check false IS the glyph being
a gap (GENERIC over the data).** The check is `false` iff
the glyph carries no prime — the pointwise form of
`MeaningAlign.Total`'s failure. -/
theorem glyphLinkedCheck_eq_false_iff (links : Finset (Glyph × Prime))
    (g : Glyph) :
    glyphLinkedCheck links g = false ↔ ∀ p, ¬ alignOf links g p := by
  constructor
  · intro h p hp
    have ht : glyphLinkedCheck links g = true :=
      (glyphLinkedCheck_eq_true_iff links g).mpr ⟨p, hp⟩
    rw [ht] at h
    cases h
  · intro h
    cases hc : glyphLinkedCheck links g with
    | false => rfl
    | true =>
      obtain ⟨p, hp⟩ := (glyphLinkedCheck_eq_true_iff links g).mp hc
      exact absurd hp (h p)

/-! ## §2. The primary reading's lists (DATA)

Canonical prime order (the order of `primeList`). The lists
themselves are data; that they are THE covered set and THE
gap set of the seed is the content of §3's characterization
theorems, proved by reflection — the lists assert nothing
until those theorems land. -/

/-- **The seed's covered primes (DATA).** The 5 primes the
primary reading carries: SEE (ʿayin, the eye), SAY (pē, the
mouth), DO and TOUCH (yōd, the hand), MOVE (ṭēt, the wheel)
— all instrumental links; the denotative covered set is
empty. -/
def seedCoveredList : List Prime :=
  [Prime.SEE, Prime.SAY, Prime.DO, Prime.MOVE, Prime.TOUCH]

/-- **The seed's gap list (DATA).** The 60 primes of the
canonical 65 that NO glyph carries under the primary
reading — the census's headline list, characterized in
`seedAlign_gap_iff`. -/
def seedGapList : List Prime :=
  [Prime.I, Prime.YOU, Prime.SOMEONE, Prime.SOMETHING, Prime.PEOPLE,
   Prime.BODY, Prime.KIND, Prime.PART, Prime.THIS, Prime.THE_SAME,
   Prime.OTHER, Prime.ONE, Prime.TWO, Prime.SOME, Prime.ALL,
   Prime.MUCH_MANY, Prime.LITTLE_FEW, Prime.GOOD, Prime.BAD, Prime.BIG,
   Prime.SMALL, Prime.THINK, Prime.KNOW, Prime.WANT, Prime.DONT_WANT,
   Prime.FEEL, Prime.HEAR, Prime.WORDS, Prime.TRUE, Prime.HAPPEN,
   Prime.BE_SOMEWHERE, Prime.THERE_IS, Prime.BE_SOMEONE_SOMETHING,
   Prime.IS_MINE, Prime.LIVE, Prime.DIE, Prime.WHEN_TIME, Prime.NOW,
   Prime.BEFORE, Prime.AFTER, Prime.A_LONG_TIME, Prime.A_SHORT_TIME,
   Prime.FOR_SOME_TIME, Prime.MOMENT, Prime.WHERE_PLACE, Prime.HERE,
   Prime.ABOVE, Prime.BELOW, Prime.FAR, Prime.NEAR, Prime.SIDE,
   Prime.INSIDE, Prime.NOT, Prime.MAYBE, Prime.CAN, Prime.BECAUSE,
   Prime.IF, Prime.VERY, Prime.MORE, Prime.LIKE_WAY]

/-- **The seed's glyph-side gap list (DATA).** The 17 glyphs
carrying no prime under the primary reading, in codepoint
order — the pointwise failures of totality, characterized
in `seedAlign_glyph_gap_iff`. -/
def seedGlyphGapList : List Glyph :=
  [Glyph.alep, Glyph.bet, Glyph.gimel, Glyph.dalet, Glyph.he, Glyph.waw,
   Glyph.zayin, Glyph.het, Glyph.lamed, Glyph.mem, Glyph.nun, Glyph.samek,
   Glyph.sade, Glyph.qop, Glyph.res, Glyph.shin, Glyph.taw]

/-! ## §3. The census of the primary reading (`seedAlign`)

Each predicate value is the §4-of-SC-2 check, evaluated by
kernel decision, read through its bridge. Witnesses are
named by separate theorems so the dossier can cite the
conflation and the synonymy by the glyphs themselves. -/

/-- **CENSUS (primary): the no-conflation check evaluates
to `false`.** Computed from the link data by kernel
decision — the seed conflates. -/
theorem seedAlign_functionalCheck_false :
    functionalCheck seedLinks = false := by decide

/-- **CENSUS (primary): the seed alignment is NOT
functional.** No-conflation fails: read off
`seedAlign_functionalCheck_false` through SC-2's
`functionalCheck_eq_true_iff` bridge. The witness is
`seedAlign_conflation_witness`. -/
theorem seedAlign_not_functional : ¬ seedAlign.Functional := by
  intro hF
  have hF' : (alignOf seedLinks).Functional := hF
  have ht : functionalCheck seedLinks = true :=
    (functionalCheck_eq_true_iff seedLinks).mpr hF'
  rw [seedAlign_functionalCheck_false] at ht
  cases ht

/-- **CENSUS (primary): the conflation witness, by name.**
Yōd (the hand) carries two distinct primes — TOUCH, the
organ of touch, and DO, the canonical instrument of doing.
This is `MeaningAlign.conflation_iff_not_functional`
exhibited, not merely implied. -/
theorem seedAlign_conflation_witness :
    ∃ s m₁ m₂, m₁ ≠ m₂ ∧ seedAlign s m₁ ∧ seedAlign s m₂ :=
  ⟨Glyph.yod, Prime.TOUCH, Prime.DO, by decide,
   (alignOf_apply seedLinks Glyph.yod Prime.TOUCH).mpr (by decide),
   (alignOf_apply seedLinks Glyph.yod Prime.DO).mpr (by decide)⟩

/-- **CENSUS (primary): the no-gaps check evaluates to
`false`.** Computed from the link data by kernel decision
— glyphs gap (SC-2's smoke reached the same value by its
cheapest path; the census owns the statement here). -/
theorem seedAlign_totalCheck_false :
    totalCheck seedLinks = false := by decide

/-- **CENSUS (primary): the seed alignment is NOT total.**
No-gaps fails on the glyph side: 17 of the 22 glyphs carry
nothing — the list is `seedAlign_glyph_gap_iff`. (SC-2's
`seedAlign_not_total` is the same fact as a smoke check;
this is the census's own route, through the check and its
bridge.) -/
theorem seedAlign_not_total_census : ¬ seedAlign.Total := by
  intro hT
  have hT' : (alignOf seedLinks).Total := hT
  have ht : totalCheck seedLinks = true :=
    (totalCheck_eq_true_iff seedLinks).mpr hT'
  rw [seedAlign_totalCheck_false] at ht
  cases ht

/-- **CENSUS (primary): the no-unnamed-meanings check
evaluates to `false`.** Computed from the link data by
kernel decision — primes gap, 60 of 65 of them. -/
theorem seedAlign_surjectiveCheck_false :
    surjectiveCheck seedLinks = false := by decide

/-- **CENSUS (primary): the seed alignment is NOT
surjective.** No-unnamed-meanings fails: most primes are
carried by no glyph — the exact list is
`seedAlign_gap_iff`. -/
theorem seedAlign_not_surjective : ¬ seedAlign.SurjectiveAlign := by
  intro hS
  have hS' : (alignOf seedLinks).SurjectiveAlign := hS
  have ht : surjectiveCheck seedLinks = true :=
    (surjectiveCheck_eq_true_iff seedLinks).mpr hS'
  rw [seedAlign_surjectiveCheck_false] at ht
  cases ht

/-- **CENSUS (primary): the no-synonymy check evaluates to
`false`.** Computed from the link data by kernel decision
— a prime is crowded by two glyphs. -/
theorem seedAlign_injectiveCheck_false :
    injectiveCheck seedLinks = false := by decide

/-- **CENSUS (primary): the seed alignment is NOT
injective.** No-synonymy fails: read off
`seedAlign_injectiveCheck_false` through SC-2's bridge.
The witness is `seedAlign_synonymy_witness`. -/
theorem seedAlign_not_injective : ¬ seedAlign.InjectiveAlign := by
  intro hI
  have hI' : (alignOf seedLinks).InjectiveAlign := hI
  have ht : injectiveCheck seedLinks = true :=
    (injectiveCheck_eq_true_iff seedLinks).mpr hI'
  rw [seedAlign_injectiveCheck_false] at ht
  cases ht

/-- **CENSUS (primary): the synonymy witness, by name.**
TOUCH is carried by two distinct glyphs — yōd (the hand)
and kāp (the palm, the touching surface): the
BODY-neighbourhood crowding the scoping predicted, counted
here as data. -/
theorem seedAlign_synonymy_witness :
    ∃ s₁ s₂ m, s₁ ≠ s₂ ∧ seedAlign s₁ m ∧ seedAlign s₂ m :=
  ⟨Glyph.yod, Glyph.kap, Prime.TOUCH, by decide,
   (alignOf_apply seedLinks Glyph.yod Prime.TOUCH).mpr (by decide),
   (alignOf_apply seedLinks Glyph.kap Prime.TOUCH).mpr (by decide)⟩

/-- **CENSUS (primary): the covered primes, characterized.**
A prime is carried by some glyph under the primary reading
if and only if it is one of the five in `seedCoveredList`.
Proved by the §1 reflection: rewrite by the coverage
bridge, then finite case analysis and kernel decision over
the data. Coverage: 5 of 65. -/
theorem seedAlign_covered_iff (p : Prime) :
    (∃ g, seedAlign g p) ↔ p ∈ seedCoveredList := by
  have h : (∃ g, seedAlign g p) ↔ primeCoveredCheck seedLinks p = true :=
    (primeCoveredCheck_eq_true_iff seedLinks p).symm
  rw [h]
  cases p <;> decide

/-- **CENSUS (primary): THE GAP LIST, characterized.** A
prime is carried by NO glyph under the primary reading if
and only if it is one of the sixty in `seedGapList`. This
is the census's headline: the exact set of what a 22-glyph
Phoenician seed cannot say against the canonical 65 —
counted by machine, through the §1 reflection, not
transcribed by hand. -/
theorem seedAlign_gap_iff (p : Prime) :
    (∀ g, ¬ seedAlign g p) ↔ p ∈ seedGapList := by
  have h : (∀ g, ¬ seedAlign g p) ↔
      primeCoveredCheck seedLinks p = false :=
    (primeCoveredCheck_eq_false_iff seedLinks p).symm
  rw [h]
  cases p <;> decide

/-- **CENSUS (primary): the glyph-side gap list,
characterized.** A glyph carries no prime under the
primary reading if and only if it is one of the seventeen
in `seedGlyphGapList`. -/
theorem seedAlign_glyph_gap_iff (g : Glyph) :
    (∀ p, ¬ seedAlign g p) ↔ g ∈ seedGlyphGapList := by
  have h : (∀ p, ¬ seedAlign g p) ↔
      glyphLinkedCheck seedLinks g = false :=
    (glyphLinkedCheck_eq_false_iff seedLinks g).symm
  rw [h]
  cases g <;> decide

/-- **CENSUS (primary): THE HEADLINE.** The seed alignment
is not the graph of any denotation function: there is no
`f : Glyph → Prime` whose graph is `seedAlign`. This is
`MeaningAlign.functional_total_iff` read against the
census — a checkable denotation exists iff no conflation
and no gaps, and the seed has both. The seed is a partial,
conflated, synonymous alignment: a first finite seat for
meaning (pin N2), measured — not a denotation, and not a
discharge of the pin. -/
theorem seedAlign_not_denotation :
    ¬ ∃ f : Glyph → Prime, ∀ s m, seedAlign s m ↔ m = f s := by
  intro h
  have hFT : seedAlign.Functional ∧ seedAlign.Total :=
    (MeaningAlign.functional_total_iff seedAlign).mpr h
  exact seedAlign_not_functional hFT.1

/-! ## §4. The denotative baseline (`denotativeAlign` = ∅)

The strict reading: denotative links only — and SC-1 drew
none. The empty alignment's census, for contrast with §3:
functionality and injectivity hold VACUOUSLY (a relation
with no pairs cannot conflate or crowd), totality and
surjectivity fail completely (every glyph gaps; every one
of the 65 primes is uncovered). -/

/-- **CENSUS (baseline): the no-conflation check on the
empty link set evaluates to `true`.** Vacuously — there
are no pairs to disagree. -/
theorem denotativeAlign_functionalCheck_true :
    functionalCheck denotativeLinks = true := by decide

/-- **CENSUS (baseline): the denotative alignment IS
functional — vacuously.** The empty relation carries no
glyph to two meanings because it carries no glyph to any
meaning. Stated as vacuity, not as a virtue of the seed:
denotation's other half (totality) fails outright below. -/
theorem denotativeAlign_functional : denotativeAlign.Functional :=
  (functionalCheck_eq_true_iff denotativeLinks).mp
    denotativeAlign_functionalCheck_true

/-- **CENSUS (baseline): the no-synonymy check on the empty
link set evaluates to `true`.** Vacuously, same reason. -/
theorem denotativeAlign_injectiveCheck_true :
    injectiveCheck denotativeLinks = true := by decide

/-- **CENSUS (baseline): the denotative alignment IS
injective — vacuously.** No prime is carried by two glyphs
because no prime is carried at all. -/
theorem denotativeAlign_injective : denotativeAlign.InjectiveAlign :=
  (injectiveCheck_eq_true_iff denotativeLinks).mp
    denotativeAlign_injectiveCheck_true

/-- **CENSUS (baseline): the no-gaps check on the empty
link set evaluates to `false`.** Every glyph gaps. -/
theorem denotativeAlign_totalCheck_false :
    totalCheck denotativeLinks = false := by decide

/-- **CENSUS (baseline): the denotative alignment is NOT
total.** No glyph carries anything under the denotative
reading — 22 of 22 glyph-side gaps. -/
theorem denotativeAlign_not_total : ¬ denotativeAlign.Total := by
  intro hT
  have hT' : (alignOf denotativeLinks).Total := hT
  have ht : totalCheck denotativeLinks = true :=
    (totalCheck_eq_true_iff denotativeLinks).mpr hT'
  rw [denotativeAlign_totalCheck_false] at ht
  cases ht

/-- **CENSUS (baseline): the no-unnamed-meanings check on
the empty link set evaluates to `false`.** Every prime
gaps. -/
theorem denotativeAlign_surjectiveCheck_false :
    surjectiveCheck denotativeLinks = false := by decide

/-- **CENSUS (baseline): the denotative alignment is NOT
surjective.** All 65 primes are uncovered under the
denotative reading; `denotativeAlign_gap_iff` names the
whole prime list as the gap list. -/
theorem denotativeAlign_not_surjective :
    ¬ denotativeAlign.SurjectiveAlign := by
  intro hS
  have hS' : (alignOf denotativeLinks).SurjectiveAlign := hS
  have ht : surjectiveCheck denotativeLinks = true :=
    (surjectiveCheck_eq_true_iff denotativeLinks).mpr hS'
  rw [denotativeAlign_surjectiveCheck_false] at ht
  cases ht

/-- **CENSUS (baseline): the covered set is EMPTY,
characterized.** No prime is carried by any glyph under
the denotative reading. Coverage: 0 of 65. -/
theorem denotativeAlign_covered_iff (p : Prime) :
    (∃ g, denotativeAlign g p) ↔ p ∈ ([] : List Prime) := by
  have h : (∃ g, denotativeAlign g p) ↔
      primeCoveredCheck denotativeLinks p = true :=
    (primeCoveredCheck_eq_true_iff denotativeLinks p).symm
  rw [h]
  cases p <;> decide

/-- **CENSUS (baseline): the gap list is EVERYTHING,
characterized.** A prime is uncovered under the denotative
reading if and only if it is a prime at all — the gap list
is `primeList` itself, all 65. -/
theorem denotativeAlign_gap_iff (p : Prime) :
    (∀ g, ¬ denotativeAlign g p) ↔ p ∈ primeList := by
  have h : (∀ g, ¬ denotativeAlign g p) ↔
      primeCoveredCheck denotativeLinks p = false :=
    (primeCoveredCheck_eq_false_iff denotativeLinks p).symm
  rw [h]
  cases p <;> decide

/-! ## §5. The WATCHLIST reading

Everything in this section is WATCHLIST: the primary links
plus the four pairs SC-1's dossier (departure D6) recorded
as judged-too-loose and NOT drawn — zayin → DIE (weapon),
hē → SEE (window), lāmd → MOVE (goad), mēm →
SOMETHING/THING (water). The watchlist reading bounds what
those four judgment calls were worth: coverage rises from
5 to 7 primes (DIE and SOMETHING join), and every failure
mode of the primary reading survives — conflation (still
yōd), totality and surjectivity (still gapped), and
synonymy, which the watchlist makes WORSE (SEE and MOVE
each gain a second carrier). No link is drawn here that
SC-1 did not either draw or record. -/

/-- **WATCHLIST links (DATA).** The primary seed links plus
SC-1 D6's four recorded-not-drawn pairs, transcribed from
the dossier text: zayin (weapon) → DIE, hē (window) → SEE,
lāmd (goad) → MOVE, mēm (water) → SOMETHING/THING. -/
def watchlistLinks : Finset (Glyph × Prime) :=
  seedLinks ∪ {(Glyph.zayin, Prime.DIE), (Glyph.he, Prime.SEE),
   (Glyph.lamed, Prime.MOVE), (Glyph.mem, Prime.SOMETHING)}

/-- **The WATCHLIST alignment (DEFINITIONAL).** The
alignment induced by `watchlistLinks` — a sensitivity
reading over SC-1's loosest judgment calls, labeled
WATCHLIST wherever it appears. -/
def watchlistAlign : MeaningAlign Glyph Prime := alignOf watchlistLinks

/-- **WATCHLIST covered primes (DATA).** The 7 primes the
watchlist reading carries: the primary five plus DIE
(zayin) and SOMETHING/THING (mēm) — exactly the two primes
the D6 pairs add, as `watchlistAlign_covered_iff` proves. -/
def watchlistCoveredList : List Prime :=
  [Prime.SOMETHING, Prime.SEE, Prime.SAY, Prime.DO, Prime.MOVE, Prime.DIE,
   Prime.TOUCH]

/-- **WATCHLIST gap list (DATA).** The 58 primes no glyph
carries even under the watchlist reading. -/
def watchlistGapList : List Prime :=
  [Prime.I, Prime.YOU, Prime.SOMEONE, Prime.PEOPLE, Prime.BODY,
   Prime.KIND, Prime.PART, Prime.THIS, Prime.THE_SAME, Prime.OTHER,
   Prime.ONE, Prime.TWO, Prime.SOME, Prime.ALL, Prime.MUCH_MANY,
   Prime.LITTLE_FEW, Prime.GOOD, Prime.BAD, Prime.BIG, Prime.SMALL,
   Prime.THINK, Prime.KNOW, Prime.WANT, Prime.DONT_WANT, Prime.FEEL,
   Prime.HEAR, Prime.WORDS, Prime.TRUE, Prime.HAPPEN, Prime.BE_SOMEWHERE,
   Prime.THERE_IS, Prime.BE_SOMEONE_SOMETHING, Prime.IS_MINE, Prime.LIVE,
   Prime.WHEN_TIME, Prime.NOW, Prime.BEFORE, Prime.AFTER, Prime.A_LONG_TIME,
   Prime.A_SHORT_TIME, Prime.FOR_SOME_TIME, Prime.MOMENT, Prime.WHERE_PLACE,
   Prime.HERE, Prime.ABOVE, Prime.BELOW, Prime.FAR, Prime.NEAR, Prime.SIDE,
   Prime.INSIDE, Prime.NOT, Prime.MAYBE, Prime.CAN, Prime.BECAUSE,
   Prime.IF, Prime.VERY, Prime.MORE, Prime.LIKE_WAY]

/-- **WATCHLIST glyph-side gap list (DATA).** The 13 glyphs
carrying no prime even under the watchlist reading, in
codepoint order. -/
def watchlistGlyphGapList : List Glyph :=
  [Glyph.alep, Glyph.bet, Glyph.gimel, Glyph.dalet, Glyph.waw, Glyph.het,
   Glyph.nun, Glyph.samek, Glyph.sade, Glyph.qop, Glyph.res, Glyph.shin,
   Glyph.taw]

/-- **CENSUS (WATCHLIST): the no-conflation check evaluates
to `false`.** The D6 pairs add no second prime to any
glyph, but the primary reading's conflation (yōd) is still
there — computed, not assumed. -/
theorem watchlistAlign_functionalCheck_false :
    functionalCheck watchlistLinks = false := by decide

/-- **CENSUS (WATCHLIST): the watchlist alignment is NOT
functional.** The conflation survives the looser reading;
the witness is the same yōd
(`watchlistAlign_conflation_witness`). -/
theorem watchlistAlign_not_functional : ¬ watchlistAlign.Functional := by
  intro hF
  have hF' : (alignOf watchlistLinks).Functional := hF
  have ht : functionalCheck watchlistLinks = true :=
    (functionalCheck_eq_true_iff watchlistLinks).mpr hF'
  rw [watchlistAlign_functionalCheck_false] at ht
  cases ht

/-- **CENSUS (WATCHLIST): the conflation witness, by
name.** Yōd still carries TOUCH and DO — the D6 pairs did
not touch yōd, and the census verifies the witness in the
watchlist data rather than inheriting it. -/
theorem watchlistAlign_conflation_witness :
    ∃ s m₁ m₂, m₁ ≠ m₂ ∧ watchlistAlign s m₁ ∧ watchlistAlign s m₂ :=
  ⟨Glyph.yod, Prime.TOUCH, Prime.DO, by decide,
   (alignOf_apply watchlistLinks Glyph.yod Prime.TOUCH).mpr (by decide),
   (alignOf_apply watchlistLinks Glyph.yod Prime.DO).mpr (by decide)⟩

/-- **CENSUS (WATCHLIST): the no-gaps check evaluates to
`false`.** Four glyphs gain links; thirteen still carry
nothing. -/
theorem watchlistAlign_totalCheck_false :
    totalCheck watchlistLinks = false := by decide

/-- **CENSUS (WATCHLIST): the watchlist alignment is NOT
total.** Glyph-side gaps fall from 17 to 13, not to zero —
the list is `watchlistAlign_glyph_gap_iff`. -/
theorem watchlistAlign_not_total : ¬ watchlistAlign.Total := by
  intro hT
  have hT' : (alignOf watchlistLinks).Total := hT
  have ht : totalCheck watchlistLinks = true :=
    (totalCheck_eq_true_iff watchlistLinks).mpr hT'
  rw [watchlistAlign_totalCheck_false] at ht
  cases ht

/-- **CENSUS (WATCHLIST): the no-unnamed-meanings check
evaluates to `false`.** Coverage rose by two primes; 58
still gap. -/
theorem watchlistAlign_surjectiveCheck_false :
    surjectiveCheck watchlistLinks = false := by decide

/-- **CENSUS (WATCHLIST): the watchlist alignment is NOT
surjective.** The exact remaining gap list is
`watchlistAlign_gap_iff`. -/
theorem watchlistAlign_not_surjective :
    ¬ watchlistAlign.SurjectiveAlign := by
  intro hS
  have hS' : (alignOf watchlistLinks).SurjectiveAlign := hS
  have ht : surjectiveCheck watchlistLinks = true :=
    (surjectiveCheck_eq_true_iff watchlistLinks).mpr hS'
  rw [watchlistAlign_surjectiveCheck_false] at ht
  cases ht

/-- **CENSUS (WATCHLIST): the no-synonymy check evaluates
to `false`.** -/
theorem watchlistAlign_injectiveCheck_false :
    injectiveCheck watchlistLinks = false := by decide

/-- **CENSUS (WATCHLIST): the watchlist alignment is NOT
injective.** Synonymy survives and spreads: besides the
primary reading's TOUCH crowding, the D6 pairs crowd SEE
and MOVE as well — witnesses named in
`watchlistAlign_synonymy_touch`, `watchlistAlign_synonymy_see`,
and `watchlistAlign_synonymy_move`. -/
theorem watchlistAlign_not_injective :
    ¬ watchlistAlign.InjectiveAlign := by
  intro hI
  have hI' : (alignOf watchlistLinks).InjectiveAlign := hI
  have ht : injectiveCheck watchlistLinks = true :=
    (injectiveCheck_eq_true_iff watchlistLinks).mpr hI'
  rw [watchlistAlign_injectiveCheck_false] at ht
  cases ht

/-- **CENSUS (WATCHLIST): synonymy witness — TOUCH.**
Carried by yōd (hand) and kāp (palm), as in the primary
reading. -/
theorem watchlistAlign_synonymy_touch :
    ∃ s₁ s₂ m, s₁ ≠ s₂ ∧ watchlistAlign s₁ m ∧ watchlistAlign s₂ m :=
  ⟨Glyph.yod, Glyph.kap, Prime.TOUCH, by decide,
   (alignOf_apply watchlistLinks Glyph.yod Prime.TOUCH).mpr (by decide),
   (alignOf_apply watchlistLinks Glyph.kap Prime.TOUCH).mpr (by decide)⟩

/-- **CENSUS (WATCHLIST): synonymy witness — SEE, new
under the watchlist.** Carried by ʿayin (eye, the primary
link) and by hē (window, the D6 pair): admitting the loose
window → SEE call crowds SEE. -/
theorem watchlistAlign_synonymy_see :
    ∃ s₁ s₂ m, s₁ ≠ s₂ ∧ watchlistAlign s₁ m ∧ watchlistAlign s₂ m :=
  ⟨Glyph.ayin, Glyph.he, Prime.SEE, by decide,
   (alignOf_apply watchlistLinks Glyph.ayin Prime.SEE).mpr (by decide),
   (alignOf_apply watchlistLinks Glyph.he Prime.SEE).mpr (by decide)⟩

/-- **CENSUS (WATCHLIST): synonymy witness — MOVE, new
under the watchlist.** Carried by ṭēt (wheel, the primary
link) and by lāmd (goad, the D6 pair): admitting the loose
goad → MOVE call crowds MOVE. -/
theorem watchlistAlign_synonymy_move :
    ∃ s₁ s₂ m, s₁ ≠ s₂ ∧ watchlistAlign s₁ m ∧ watchlistAlign s₂ m :=
  ⟨Glyph.tet, Glyph.lamed, Prime.MOVE, by decide,
   (alignOf_apply watchlistLinks Glyph.tet Prime.MOVE).mpr (by decide),
   (alignOf_apply watchlistLinks Glyph.lamed Prime.MOVE).mpr (by decide)⟩

/-- **CENSUS (WATCHLIST): the covered primes,
characterized.** A prime is carried under the watchlist
reading if and only if it is one of the seven in
`watchlistCoveredList` — the primary five, plus DIE and
SOMETHING/THING, and nothing else: the four loose calls
were worth exactly two primes of coverage. -/
theorem watchlistAlign_covered_iff (p : Prime) :
    (∃ g, watchlistAlign g p) ↔ p ∈ watchlistCoveredList := by
  have h : (∃ g, watchlistAlign g p) ↔
      primeCoveredCheck watchlistLinks p = true :=
    (primeCoveredCheck_eq_true_iff watchlistLinks p).symm
  rw [h]
  cases p <;> decide

/-- **CENSUS (WATCHLIST): the gap list, characterized.**
A prime is carried by no glyph even under the watchlist
reading if and only if it is one of the fifty-eight in
`watchlistGapList`. -/
theorem watchlistAlign_gap_iff (p : Prime) :
    (∀ g, ¬ watchlistAlign g p) ↔ p ∈ watchlistGapList := by
  have h : (∀ g, ¬ watchlistAlign g p) ↔
      primeCoveredCheck watchlistLinks p = false :=
    (primeCoveredCheck_eq_false_iff watchlistLinks p).symm
  rw [h]
  cases p <;> decide

/-- **CENSUS (WATCHLIST): the glyph-side gap list,
characterized.** A glyph carries no prime even under the
watchlist reading if and only if it is one of the thirteen
in `watchlistGlyphGapList`. -/
theorem watchlistAlign_glyph_gap_iff (g : Glyph) :
    (∀ p, ¬ watchlistAlign g p) ↔ g ∈ watchlistGlyphGapList := by
  have h : (∀ p, ¬ watchlistAlign g p) ↔
      glyphLinkedCheck watchlistLinks g = false :=
    (glyphLinkedCheck_eq_false_iff watchlistLinks g).symm
  rw [h]
  cases g <;> decide

/-- **CENSUS (WATCHLIST): the headline survives the looser
reading.** Even with the four recorded-not-drawn pairs
admitted, the alignment is not the graph of any denotation
function — the watchlist buys two primes of coverage and
no cleanliness at all. -/
theorem watchlistAlign_not_denotation :
    ¬ ∃ f : Glyph → Prime, ∀ s m, watchlistAlign s m ↔ m = f s := by
  intro h
  have hFT : watchlistAlign.Functional ∧ watchlistAlign.Total :=
    (MeaningAlign.functional_total_iff watchlistAlign).mpr h
  exact watchlistAlign_not_functional hFT.1

end ThetLogos
