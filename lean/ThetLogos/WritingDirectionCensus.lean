import Mathlib.Tactic
import ThetLogos.MeaningBridge
import ThetLogos.SeedCoreEncoding
import ThetLogos.WritingDirection

/-!
# ThetLogos.WritingDirectionCensus — WD-2: the directed criterion's verdict on the seed (WORKING LABEL — naming is Jeff's)

HONESTY LEDGER (read before citing):

- COMMISSION. Jeff, 2026-11-06 14:46 EST: "build it run it" —
  firing WD-2, the contingent brick of the writing-direction
  line. CONTINGENCY HISTORY: WD-2 was priced CONTINGENT in the
  scoping (`writing-direction-scoping-2026-11-06.md`, §3.4 and
  the menu row for WD-2), fireable only on WD-1's POSITIVE
  outcome; WD-1 landed positive and shipped 2026-11-06 (local
  `e8d3b9a` → remote `52cfda3a`; census 13,868 strict / 522
  modules; the exhibit `reading_direction_is_content`:
  [ayin, pe] denotes [SEE, SAY] LTR, [SAY, SEE] RTL). The
  contingency is satisfied; this module is the firing. The
  layer's original commission (Jeff, 2026-11-06 13:25 EST,
  truncation preserved on `WritingDirection.lean`'s face and
  never completed anywhere, here included) stands behind the
  line; both readings of its constraint remain pinned
  UNDECIDED and nothing in this module depends on either.
- WHAT WD-2 IS — the scoping's own words, binding: "§3.4's
  content half only: a named case where distinguishing
  directions changes a census verdict (a conflation the
  directed reading separates, or a gap it closes), proved
  against the seed data." WHAT IT IS NOT: the generic
  restatement of the criterion (`functional_total_iff`) at a
  directed syntax type is CITATION, price 0 — it is not built
  here, and any theorem below that merely re-instantiates the
  criterion without a verdict DIFFERENCE on the seed data is
  not this brick's content and is labeled on its face when it
  appears as a by-construction half of a comparison.
- THE FROZEN CRITERION (fixed in this pin commit, BEFORE the
  hunt's results exist — the anti-rigging discipline of WD-1:
  the reading was frozen before the reversal test; here the
  verdict-difference criterion is frozen before the census
  hunt). A DIFFERING CENSUS CASE is: a named word `w` over
  the seed's glyphs and a census predicate of the Meaning
  Bridge criterion (conflation = `Functional`; gaps =
  `Total` / `SurjectiveAlign`; synonymy = `InjectiveAlign`)
  such that the verdict of the UNDIRECTED word alignment
  (§1: a written form denotes whatever ANY direction's
  reading gives — direction not distinguished, the form's
  direction unrecorded) at `w` DIFFERS from the verdict of
  the DIRECTED word alignment (§1: syntax = word ×
  direction) at the corresponding directed forms, AND the
  difference is decided by the seed's ENCODED DATA via the
  shipped reading (`seedRead` / `wordDenote`, proved
  data-true at WD-1 by `seedRead_faithful`) — not by the
  definitions alone. A difference that would hold for EVERY
  assignment of primes to glyphs is a definitional artifact,
  not a case; the hunt must therefore also locate where the
  undirected verdict does NOT differ (the guard), so the
  case, if any, is shown to live exactly where the data is
  direction-sensitive.
- THE HUNT REGISTER (fixed in advance; every line is
  answered in §2–§4 or in the landing record, at full rank):
  H1 (conflation separated): the WD-1 exhibit word
  [ayin, pe] — is its undirected fiber exactly the two
  exhibit denotations (a conflation), with each directed
  fiber a singleton (separated)? H2 (gap closed): a prime
  sequence denoted under NO undirected form but denoted
  once directions are distinguished — noted in advance
  that the naive form is refuted by shape (directed
  denotations are a subset of undirected ones, the
  undirected being the union over directions), so the live
  H2 question is the honest one: does distinguishing
  directions close any of the seed's ACTUAL gaps (the
  primes the reading never reaches, e.g. DO — `yod`, its
  only link-carrier, is refused by the reading at EVERY
  direction)? H3 (synonymy separated): does the directed
  alignment separate forms the undirected one identifies —
  or does synonymy survive direction (distinct directed
  forms, one denotation)? H4 (glyph-level census): the
  seed census's own verdicts (coverage 5/65, the `yod`
  conflation, the gaps) are verdicts about LINKS; direction
  acts on WORDS; H4 is answered by that observation on this
  face — no glyph-level verdict is a candidate case, and
  none is claimed below.
- VERDICT RULE (pre-registered): WD-2 LANDS iff at least
  one of H1–H3 yields a proved differing case under the
  frozen criterion. If none does, WD-2 is reported
  COLLAPSED at full rank — the scoping pre-wrote that
  outcome ("if no differing case exists, WD-2 does not
  fire and is reported as collapsed") — nothing is shipped
  for it, and no theorem is inflated into a census claim it
  is not. The collapse, if it comes, is a result and is
  reported at the same volume as a landing.
- K-WD-FIAT — DECIDED AT THIS BRICK (the scoping assigns
  the decision here; at WD-1 it was decided for the core —
  the direction datum does work on words — and that
  decision stands untouched). Pre-registered decision rule
  for WD-2: K-WD-FIAT FIRES iff this module's content
  degenerates into the generic restatement (the criterion
  re-instantiated at a directed type with a tag that does
  no work) or the verdict difference is definitional (would
  hold for any data). It does NOT fire iff a named case's
  verdict difference is decided by the seed's encoded data
  — the diversity of the covered glyphs' primes — with the
  guard locating the non-differing region. The decision and
  its grounds are recorded in §5 of this module when the
  hunt completes.
- FENCES (inherited, unchanged): the sequence reading is a
  STIPULATED ENCODING SEMANTICS (WD-0 pin) and says nothing
  about natural language; real composition — pin N2,
  meaning vs reference — is FENCED, untouched, not built
  toward; the shipped interface (`WritingDirection.lean`,
  `WritingDirectionCompass.lean`, `SeedCoreEncoding.lean`,
  `MeaningBridge.lean`) is consumed, never edited; ∅ is
  never conflated with 0; ∞ is never a number, a set, or an
  object in any statement here; the tier tension flagged on
  the layer's faces stays UNRESOLVED; "contains every
  language" stays an UNPROVABLE HORIZON — a census verdict
  about the seed's encoded data discharges nothing toward
  it; the Chaos Star is Moorcock's public symbol, not
  program property (provenance on `WritingDirection.lean`'s
  face); the compass (WD-3) is geometry only and is not
  cited here as writing content.
- NO CLAIM; dials 0/4; Dial 2 = 0.
-/

namespace ThetLogos

/-! ## §1. The two word alignments (DEFINITIONAL — the pin's content)

Both alignments are built ONLY from the shipped frozen
interface: a written form's denotation under a direction is
`wordDenote (WriteDir.readingOf d w)` — read the form in
direction `d`'s order, then take the sequence reading
(WD-0/WD-1, consumed not edited). The UNDIRECTED alignment
forgets the direction: a form denotes a sequence when SOME
direction's reading gives it — the standing of a written
form whose direction was never recorded. The DIRECTED
alignment keeps the direction in the syntax: a directed
form is a (word, direction) pair, and it denotes the one
sequence its own reading gives. The census predicates of
`MeaningBridge` (`Functional`, `Total`, `InjectiveAlign`,
`SurjectiveAlign`) apply to both as they stand; no
predicate is restated or re-proved here (the restatement
is citation, price 0, and is not this brick). -/

/-- **The undirected word alignment (DEFINITIONAL; WORKING
LABEL).** A written form (a word over the seed's glyphs)
denotes a prime sequence when SOME path direction's
reading of the form has that sequence denotation —
direction not distinguished. This is the alignment a
direction-blind census of written forms would compute. -/
def wordAlignUndirected : MeaningAlign (List Glyph) (List Prime) :=
  fun w ps => ∃ d : WriteDir, wordDenote (WriteDir.readingOf d w) = some ps

/-- **The directed word alignment (DEFINITIONAL; WORKING
LABEL).** A directed form — a word together with the
direction it is read in — denotes the prime sequence its
own reading gives, and no other: the alignment is the
graph of the shipped reading, direction recorded in the
syntax. -/
def wordAlignDirected : MeaningAlign (List Glyph × WriteDir) (List Prime) :=
  fun wd ps => wordDenote (WriteDir.readingOf wd.2 wd.1) = some ps

/-! ## §2. Machinery — the undirected fiber, characterized

Five directions induce exactly two readings on a single
word (the pin's collapse, stated on `WriteDir.readingOf`'s
face at WD-0: the vertical cases read one column as
written; `btt` reverses like `rtl`). So the undirected
fiber of a word is characterized by the word's own
denotation and its reverse — and the shipped
`wordDenote_reverse` transports between them. The
characterization theorem at the end of this section is
the hunt's measuring instrument: it says EXACTLY when the
undirected verdict at a word agrees with the directed one
(no conflation undirected) — namely iff the word's
denotation is absent or reversal-fixed — so any differing
case is located in the data, and the non-differing region
is proved, not assumed. -/

/-- **The two readings (DEFINITIONAL content of the pin).**
Every direction reads a word either as written or
reversed — the five cases of `WriteDir.readingOf`
collapse to two readings on a single word. -/
theorem readingOf_eq_self_or_reverse (d : WriteDir) (w : List Glyph) :
    WriteDir.readingOf d w = w ∨ WriteDir.readingOf d w = w.reverse := by
  cases d
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **The undirected fiber, first form.** A word
undirected-denotes a sequence iff its own sequence
denotation is that sequence, or its reverse's is. -/
theorem wordAlignUndirected_iff (w : List Glyph) (ps : List Prime) :
    wordAlignUndirected w ps ↔
      wordDenote w = some ps ∨ wordDenote w.reverse = some ps := by
  constructor
  · rintro ⟨d, hd⟩
    cases readingOf_eq_self_or_reverse d w with
    | inl h => exact Or.inl (h ▸ hd)
    | inr h => exact Or.inr (h ▸ hd)
  · rintro (h | h)
    · exact ⟨.ltr, h⟩
    · exact ⟨.rtl, h⟩

/-- **The undirected fiber of a denoting word.** If `w`
denotes `ps₀`, its undirected denotations are exactly
`ps₀` and `ps₀` reversed — the two readings, no more (the
shipped order-faithfulness, `wordDenote_reverse`, is what
closes the fiber). -/
theorem undirected_fiber_of_denote {w : List Glyph} {ps₀ ps : List Prime}
    (h : wordDenote w = some ps₀) :
    wordAlignUndirected w ps ↔ ps = ps₀ ∨ ps = ps₀.reverse := by
  have hr : wordDenote w.reverse = some ps₀.reverse := by
    rw [wordDenote_reverse, h]
    rfl
  rw [wordAlignUndirected_iff, h, hr]
  constructor
  · rintro (e | e)
    · exact Or.inl (Option.some.inj e).symm
    · exact Or.inr (Option.some.inj e).symm
  · rintro (e | e)
    · subst e; exact Or.inl rfl
    · subst e; exact Or.inr rfl

/-- **THE CHARACTERIZATION (the comparison's spine).**
The undirected alignment is functional AT a word `w` —
no conflation at that form — if and only if `w`'s
sequence denotation is absent or REVERSEAL-FIXED (a
palindrome). So distinguishing directions changes the
no-conflation verdict at exactly the words whose
denotations the seed's data makes non-palindromic: the
difference, wherever it occurs, is decided by the DATA
(the primes the seed assigns), and the agreement region
is everything else. This is the frozen criterion's guard
made theorem: a differing case must be a denoting,
non-palindromic word, and §3 exhibits the seed's own. -/
theorem undirected_functional_at_iff (w : List Glyph) :
    (∀ ps₁ ps₂, wordAlignUndirected w ps₁ → wordAlignUndirected w ps₂ →
      ps₁ = ps₂) ↔
    wordDenote w = none ∨
      ∃ ps₀, wordDenote w = some ps₀ ∧ ps₀.reverse = ps₀ := by
  constructor
  · intro hf
    cases h : wordDenote w with
    | none => exact Or.inl rfl
    | some ps₀ =>
      refine Or.inr ⟨ps₀, rfl, ?_⟩
      have h₁ : wordAlignUndirected w ps₀ :=
        (undirected_fiber_of_denote h).mpr (Or.inl rfl)
      have h₂ : wordAlignUndirected w ps₀.reverse :=
        (undirected_fiber_of_denote h).mpr (Or.inr rfl)
      exact (hf ps₀ ps₀.reverse h₁ h₂).symm
  · rintro (h | ⟨ps₀, h, hrev⟩) ps₁ ps₂ h₁ h₂
    · rw [wordAlignUndirected_iff] at h₁
      cases h₁ with
      | inl e => rw [h] at e; cases e
      | inr e =>
        have hn : wordDenote w.reverse = none := by
          rw [wordDenote_reverse, h]
          rfl
        rw [hn] at e; cases e
    · have f₁ := (undirected_fiber_of_denote h).mp h₁
      have f₂ := (undirected_fiber_of_denote h).mp h₂
      cases f₁ with
      | inl e₁ =>
        cases f₂ with
        | inl e₂ => rw [e₁, e₂]
        | inr e₂ => rw [e₁, e₂, hrev]
      | inr e₁ =>
        cases f₂ with
        | inl e₂ => rw [e₁, e₂, hrev]
        | inr e₂ => rw [e₁, e₂]

/-! ## §3. H1 — THE NAMED CASE: direction repairs a conflation

The verdict difference, on the seed's own exhibit word.
UNDIRECTED: the written form [ayin, pe] (eye, mouth)
carries TWO distinct denotations — [SEE, SAY] and
[SAY, SEE] — because its direction is not distinguished:
the undirected word alignment is NOT FUNCTIONAL, and the
failure is located at this word (its undirected fiber is
exactly the conflated pair, by §2). DIRECTED: each
directed form carries exactly one — ([ayin, pe], ltr)
denotes [SEE, SAY] alone, ([ayin, pe], rtl) denotes
[SAY, SEE] alone — and the directed alignment is
functional. The two denotations the undirected form
lumps together are separated by recording the direction.
The difference is the DATA's: by §2's characterization
it exists iff the word's denotation is non-palindromic,
and [SEE, SAY] is non-palindromic because the seed
assigns ayin ↦ SEE ≠ SAY ↦ pe (`seedRead_faithful`:
the encoded data, not a stipulation's choice).

HONEST LABELS: `wordAlignDirected_functional` below is
the BY-CONSTRUCTION half of the comparison (the directed
alignment is the graph of a function — that half is the
criterion behaving as cited, and it is not this brick's
content). The content is the undirected side's FAILURE
at a named word, the exact fiber, and §2's
characterization locating the phenomenon in the data. -/

/-- **The directed alignment is functional
(BY-CONSTRUCTION half of the comparison — labeled, not
the brick's content).** A directed form denotes the one
sequence its own reading gives. -/
theorem wordAlignDirected_functional : wordAlignDirected.Functional := by
  intro wd ps₁ ps₂ h₁ h₂
  have h₁' : wordDenote (WriteDir.readingOf wd.2 wd.1) = some ps₁ := h₁
  have h₂' : wordDenote (WriteDir.readingOf wd.2 wd.1) = some ps₂ := h₂
  exact Option.some.inj (h₁'.symm.trans h₂')

/-- **The separation, fiber by fiber.** Each directed
form of the exhibit word carries EXACTLY one denotation:
([ayin, pe], ltr) denotes [SEE, SAY] alone;
([ayin, pe], rtl) — the seed's native direction —
denotes [SAY, SEE] alone. The two sequences the
undirected form conflates are the two directed forms'
separate denotations. -/
theorem directed_ayin_pe_fibers :
    (∀ ps, wordAlignDirected ([Glyph.ayin, Glyph.pe], WriteDir.ltr) ps ↔
      ps = [Prime.SEE, Prime.SAY]) ∧
    (∀ ps, wordAlignDirected ([Glyph.ayin, Glyph.pe], WriteDir.rtl) ps ↔
      ps = [Prime.SAY, Prime.SEE]) := by
  constructor
  · intro ps
    constructor
    · intro h
      have h' : wordDenote (WriteDir.readingOf .ltr [Glyph.ayin, Glyph.pe]) =
          some ps := h
      exact Option.some.inj (h'.symm.trans wordDenote_ayin_pe)
    · intro h
      rw [h]
      exact wordDenote_ayin_pe
  · intro ps
    constructor
    · intro h
      have h' : wordDenote (WriteDir.readingOf .rtl [Glyph.ayin, Glyph.pe]) =
          some ps := h
      exact Option.some.inj (h'.symm.trans wordDenote_ayin_pe_rtl)
    · intro h
      rw [h]
      exact wordDenote_ayin_pe_rtl

/-- **The conflation, exactly.** The undirected fiber of
the exhibit word is EXACTLY the pair {[SEE, SAY],
[SAY, SEE]} — both of the word's readings, lumped into
one form because the direction is not recorded. -/
theorem undirected_ayin_pe_fiber (ps : List Prime) :
    wordAlignUndirected [Glyph.ayin, Glyph.pe] ps ↔
      ps = [Prime.SEE, Prime.SAY] ∨ ps = [Prime.SAY, Prime.SEE] :=
  undirected_fiber_of_denote (w := [Glyph.ayin, Glyph.pe])
    (ps₀ := [Prime.SEE, Prime.SAY]) rfl

/-- **THE NAMED CASE (WD-2's content).** The undirected
word alignment is NOT FUNCTIONAL: the written form
[ayin, pe] is conflated — one form, two distinct
denotations — when direction is not distinguished.
Proved against the seed's encoded data: the two
denotations are the shipped exhibit's
(`wordDenote_ayin_pe`, `wordDenote_ayin_pe_rtl`), and
they differ because the seed assigns SEE ≠ SAY to the
word's two glyphs. Together with
`wordAlignDirected_functional` and
`directed_ayin_pe_fibers`: distinguishing directions
CHANGES THE CENSUS VERDICT at this word — conflation
undirected, separated directed. Direction repairs this
conflation. -/
theorem wordAlignUndirected_not_functional :
    ¬ wordAlignUndirected.Functional := by
  intro hf
  have h₁ : wordAlignUndirected [Glyph.ayin, Glyph.pe] [Prime.SEE, Prime.SAY] :=
    ⟨.ltr, wordDenote_ayin_pe⟩
  have h₂ : wordAlignUndirected [Glyph.ayin, Glyph.pe] [Prime.SAY, Prime.SEE] :=
    ⟨.rtl, wordDenote_ayin_pe_rtl⟩
  exact absurd (hf _ _ _ h₁ h₂) (by decide)

/-! ## §4. The rest of the hunt — H2, H3, and the guard (fences, at full rank)

The named case is H1's. The rest of the register is
answered here as NEGATIVES, proved where provable, so
the landing does not overclaim: direction repairs the
§3 conflation and nothing else in the census.

THE GUARD (locatedness, positive side): at a palindromic
word the undirected verdict AGREES with the directed one
— [ayin, ayin] denotes [SEE, SEE], reversal-fixed, and
the undirected alignment IS functional at that word (by
§2's characterization). The undirected criterion is not
broken wholesale; it fails exactly at the
direction-sensitive words. H3 (synonymy): NOT separated
— the directed alignment is not injective either:
[SAY, SEE] is carried by two distinct directed forms,
([ayin, pe], rtl) and ([pe, ayin], ltr). Direction
distinguishes readings OF one form; it does not identify
or separate distinct written forms, and synonymy across
forms survives it. H2 (gaps): NO gap is closed by
distinguishing directions — every denotation of the
sequence reading, under every direction, is built from
the four primes {MOVE, TOUCH, SEE, SAY} (the reading's
range), so a sequence containing any other prime —
named instance: [DO], whose only link-carrier `yod` the
reading refuses at every direction — is denoted by NO
directed form, exactly as by no undirected one. The
seed's gaps are gaps of LINKS, and direction permutes
order; it creates no links. (H4, glyph level, is
answered on this module's face: the seed census's
verdicts are about links and are direction-invariant;
none is claimed here.) -/

/-- **The guard at a named word.** At [ayin, ayin] —
denotation [SEE, SEE], a palindrome — the undirected
alignment IS functional at that word: the verdict
difference of §3 is located at direction-sensitive
words, not spread over the whole census. -/
theorem undirected_functional_at_ayin_ayin :
    ∀ ps₁ ps₂, wordAlignUndirected [Glyph.ayin, Glyph.ayin] ps₁ →
      wordAlignUndirected [Glyph.ayin, Glyph.ayin] ps₂ → ps₁ = ps₂ :=
  (undirected_functional_at_iff _).mpr
    (Or.inr ⟨[Prime.SEE, Prime.SEE], rfl, rfl⟩)

/-- **H3, negative (proved).** The directed alignment is
NOT injective: the sequence [SAY, SEE] is carried by two
distinct directed forms — ([ayin, pe], rtl) and
([pe, ayin], ltr). Distinguishing directions does not
separate synonymy across distinct written forms. -/
theorem wordAlignDirected_not_injective :
    ¬ wordAlignDirected.InjectiveAlign := by
  intro hi
  have h₁ : wordAlignDirected ([Glyph.ayin, Glyph.pe], WriteDir.rtl)
      [Prime.SAY, Prime.SEE] := wordDenote_ayin_pe_rtl
  have h₂ : wordAlignDirected ([Glyph.pe, Glyph.ayin], WriteDir.ltr)
      [Prime.SAY, Prime.SEE] := by
    show wordDenote (WriteDir.readingOf .ltr [Glyph.pe, Glyph.ayin]) =
      some [Prime.SAY, Prime.SEE]
    rfl
  exact absurd (hi _ _ _ h₁ h₂) (by decide)

/-- **The reading's range (per glyph).** Whatever
`seedRead` assigns is one of the four primes MOVE,
TOUCH, SEE, SAY — the seed's functional links, read off
the shipped table. -/
theorem seedRead_range {g : Glyph} {p : Prime} (h : seedRead g = some p) :
    p = Prime.MOVE ∨ p = Prime.TOUCH ∨ p = Prime.SEE ∨ p = Prime.SAY := by
  cases g <;> simp_all [seedRead]

/-- **The reading's range (per word).** Every prime in
any sequence denotation of any word is one of the four
— the sequence reading reaches no other prime, under
any direction (a direction only reorders the word). -/
theorem wordDenote_range {w : List Glyph} {ps : List Prime}
    (h : wordDenote w = some ps) :
    ∀ p ∈ ps, p = Prime.MOVE ∨ p = Prime.TOUCH ∨ p = Prime.SEE ∨
      p = Prime.SAY := by
  induction w generalizing ps with
  | nil =>
    change some ([] : List Prime) = some ps at h
    have hps : ps = [] := (Option.some.inj h).symm
    intro p hp
    rw [hps] at hp
    cases hp
  | cons g w ih =>
    cases hg : seedRead g with
    | none =>
      exfalso
      have h' : wordDenote (g :: w) = none := by
        show (seedRead g).bind
          (fun p => (wordDenote w).map fun ps => p :: ps) = none
        rw [hg]
        rfl
      rw [h'] at h
      cases h
    | some q =>
      cases hw : wordDenote w with
      | none =>
        exfalso
        have h' : wordDenote (g :: w) = none := by
          show (seedRead g).bind
            (fun p => (wordDenote w).map fun ps => p :: ps) = none
          rw [hg, hw]
          rfl
        rw [h'] at h
        cases h
      | some ps' =>
        have hps : ps = q :: ps' := by
          have h' : wordDenote (g :: w) = some (q :: ps') := by
            show (seedRead g).bind
              (fun p => (wordDenote w).map fun ps => p :: ps) =
              some (q :: ps')
            rw [hg, hw]
            rfl
          rw [h'] at h
          exact (Option.some.inj h).symm
        intro p hp
        rw [hps] at hp
        cases List.mem_cons.mp hp with
        | inl e => rw [e]; exact seedRead_range hg
        | inr hm => exact ih hw p hm

/-- **H2, negative (proved, named instance).** The
sequence [DO] is denoted by NO directed form: under
every direction, no word's reading denotes it. DO's
only link-carrier in the seed is `yod` (TOUCH and DO),
and the reading refuses `yod` at every direction, so
the seed's DO gap is direction-invariant —
distinguishing directions closes no gap. (The general
shape is `wordDenote_range`: any sequence containing a
prime outside {MOVE, TOUCH, SEE, SAY} is likewise
undenoted under every direction.) -/
theorem directed_gap_DO (w : List Glyph) (d : WriteDir) :
    wordDenote (WriteDir.readingOf d w) ≠ some [Prime.DO] := by
  intro h
  have hmem := wordDenote_range h Prime.DO (List.mem_singleton_self Prime.DO)
  rcases hmem with e | e | e | e <;> cases e

/-! ## §5. Kill register — final statuses for WD-2

- K-WD-FIAT: DECIDED at this brick — DID NOT FIRE.
  Grounds, per the pin's pre-registered rule: the
  brick's content is a verdict DIFFERENCE decided by
  the seed's encoded data — §2's characterization makes
  the undirected no-conflation verdict at a word turn on
  exactly whether the word's denotation is
  reversal-fixed, a property of the DATA (the primes
  the seed assigns: ayin ↦ SEE ≠ SAY ↦ pe), and §3's
  named case is that data deciding. The generic
  restatement of the criterion at the directed type was
  NOT built; the one by-construction theorem
  (`wordAlignDirected_functional`) is labeled as the
  comparison's cited half on its face, and the brick
  does not rest on it — delete it and §3's undirected
  failure, §2's characterization, and §4's fences all
  stand. The direction datum is not a tag: it is the
  difference between a census that records direction
  and one that does not, and on this seed the two
  censuses return different verdicts at a named word.
- K-WD-REV: DID NOT FIRE (decided at WD-1; this brick
  re-confirms at census grade — the word level carries
  direction-sensitive content, and the census now
  measures it).
- K-WD-NAME / K-WD-ENTROPY / K-WD-EXACT / K-WD-CREST /
  K-WD-GRAV: armed throughout; NONE FIRED. No entropy
  is named or located anywhere in this module; no `∞`
  appears in any statement; `∅` is never conflated with
  0 (it does not appear); no authority is borrowed (the
  commutator analogy is not cited); nothing here is a
  gravity object, a measured number, a continuum
  statement, or Dial evidence of any species.

NO CLAIM; dials 0/4; Dial 2 = 0. -/

end ThetLogos
