# SEED CORE — SC-1: The Table (2026-11-05)

**Status: SC-1 DELIVERABLE.** Research/dossier brick. No Lean code, no repo
edits. This is the completed 22-row glyph table specified in
`seed-core-scoping-2026-11-05.md` §1, with every gloss re-sourced per row
(the scoping's §1.4 draft appendix was re-derived, not copied; departures
are listed in §4 below).

**Claim ceiling (unchanged from the scoping, §5):** T5 exhibit material.
Glosses are T2 scholarly-grade, cited per row. Universality is NOT
claimable; this table is a candidate seed, not a result. No dial moves.

---

## 1. Link policy (from the scoping, §1.3 — restated verbatim in force)

1. Rows in codepoint order, U+10900 → U+10915, one per letter, none
   skipped, none merged.
2. Identity (glyph, codepoint, name) from the Unicode code chart.
   Glosses from a named scholarly reference set — never from popular
   "letter meanings" lists.
3. Flag = `consensus` iff the reference set gives one dominant gloss;
   `contested` iff two or more glosses circulate in scholarly sources.
   Contested is a permanent label on the row.
4. Links are drawn **only from the primary gloss**. A link is
   `denotative` only if the gloss *is* the prime (or its standard
   allolex); `instrumental` if the gloss names the prime's organ,
   instrument, or canonical object; anything looser is **not a link**.
   `none` is data, and it feeds the gap census honestly.
5. Correlates: at most one per row, T5 annotation only, **excluded
   from the audit** (the census audits glyph↔prime only).

**Primitive set (ratified default):** the 65 NSM primes, pinned to the
Goddard–Wierzbicka 2014 table by citation (list as given in the scoping
§2). **Glyph canon (ratified default):** the 22 Phoenician letters by
Unicode codepoint. **Contested alternates (ratified default):** recorded
and flagged; the census later runs under both readings.

**Interpretive line applied in this brick (documented departure D4):**
"contested" is applied to *rival object identifications*, not to
translation variants of one identification. "Hook/peg" (wāw),
"arm/hand" (yōd), "mark/signature" (tāw), and "fence/courtyard/wall"
(ḥēt — one enclosure object) are variants of a single identification and
stay `consensus` with the variants on record; "door/fish",
"throwstick/camel", "tooth/sun/bow" are rival objects and are
`contested`.

---

## 2. Source key (references actually consulted, 2026-11-05)

- **S1** — "Phoenician alphabet", *Wikipedia*, Table of letters (origin
  table, with its cited references [22]–[24]). Encyclopedic scholarly
  summary; consulted in full.
- **S2** — "History of the alphabet", *Wikipedia*, §Consonantal
  alphabets: acrophony table and letter-name discussion (after Sass,
  *The Genesis of the Alphabet*, 1988; Goldwasser 2006; Colless).
  Consulted in full.
- **S3** — G. R. Driver, *Semitic Writing* (1948; rev. ed. 1976),
  letter-name list (fig. 94), as reproduced in F. C. Woudhuizen, "The
  Transmission of the Phoenician Alphabet in the Mediterranean Region",
  *Rivista di Studi Fenici* 34.2 (2006). Consulted directly.
- **S4** — Brian E. Colless, letter-renaming proposals (ziqq → zayin;
  naḥš → nun; piʾt → pe; šimš → šin), as summarized in S2.
- **S5** — Yigael Yadin (1963), battle-equipment identifications
  (samek, zayin), as summarized in S2.
- The acrophonic principle itself: Gardiner (1916), via S3.

---

## 3. The table (22 rows)

| # | Glyph | Codepoint | Name | Gloss (primary) | Flag | Source | Alternate glosses | Prime link(s) | Link type | Correlate (T5) |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 𐤀 | U+10900 | ʾālep | ox (head of cattle) | consensus | S1; S3; S2 | none | none | none | none |
| 2 | 𐤁 | U+10901 | bēt | house | consensus | S1; S3; S2 | none | none | none | none |
| 3 | 𐤂 | U+10902 | gīmel | throwstick (thrown hunting club) | contested | S1 [22]; S3; S2 | camel | none | none | none |
| 4 | 𐤃 | U+10903 | dālet | door | contested | S1 [22]; S2 | fish | none | none | none |
| 5 | 𐤄 | U+10904 | hē | window | contested | S1; S2; S3 | jubilation (haw/hillul) — figure with raised arms; "lo!, behold" (heʾ) | none | none | none |
| 6 | 𐤅 | U+10905 | wāw | hook | consensus | S1; S2 | none (see note) | none | none | none |
| 7 | 𐤆 | U+10906 | zayin | weapon | contested | S1; S2 (S4; S5) | manacle, handcuff (ziqq) | none | none | none |
| 8 | 𐤇 | U+10907 | ḥēt | fence | consensus | S1; S2 | courtyard; wall | none | none | none |
| 9 | 𐤈 | U+10908 | ṭēt | wheel | consensus | S1; S2 | none | MOVE | instrumental | the cycle — rotation, the closed ring; corpus seat: the cyclic structure behind the C₂₁ Laplacian |
| 10 | 𐤉 | U+10909 | yōd | hand (arm and hand) | consensus | S1; S2; S3 | none | TOUCH; DO | instrumental | none |
| 11 | 𐤊 | U+1090A | kāp | palm (of the hand) | consensus | S1; S3 | none | TOUCH | instrumental | none |
| 12 | 𐤋 | U+1090B | lāmd | goad | consensus | S1 [24]; S2; S3 | none | none | none | none |
| 13 | 𐤌 | U+1090C | mēm | water | consensus | S1; S2; S3 | none | none | none | none |
| 14 | 𐤍 | U+1090D | nūn | fish (large fish) | contested | S1 [22]; S2 (S4) | snake, serpent (naḥš) | none | none | none |
| 15 | 𐤎 | U+1090E | sāmek | support | contested | S1; S2 (S5) | pillar; weapon (Yadin's battle-equipment proposal) | none | none | none |
| 16 | 𐤏 | U+1090F | ʿayin | eye | consensus | S1; S2; S3 | none | SEE | instrumental | observation / the measurement interface (annotation only) |
| 17 | 𐤐 | U+10910 | pē | mouth | contested | S1 [22]; S2 (S4); S3 | corner, bend (piʾt) | SAY | instrumental | none |
| 18 | 𐤑 | U+10911 | ṣādē | papyrus plant | contested | S1; S2 | fishhook | none | none | none |
| 19 | 𐤒 | U+10912 | qōp | monkey | contested | S1; S2 | cord (of wool), knot (qaw); back of head; needle | none | none | none |
| 20 | 𐤓 | U+10913 | rēš | head | consensus | S1; S2; S3 | none | none | none | none |
| 21 | 𐤔 | U+10914 | šīn | tooth | contested | S1 [22]; S2 (S4) | sun (šimš); bow (šananuma) | none | none | none |
| 22 | 𐤕 | U+10915 | tāw | mark | consensus | S1; S3; S2 | none (see note) | none | none | none |

**Row notes (only where the table cell cannot carry the content):**

- **Row 4 (dālet)** is the scoping's §1.2 exemplar, unchanged: neither
  "door" nor "fish" is a prime or an organ of one; alternates are not
  links; the row contributes 0 to measured conflation and 1 to the
  latent watchlist.
- **Row 6 (wāw):** S3 renders the same word "peg" — a translation
  variant of one object (departure line D4), recorded here rather than
  as an alternate gloss.
- **Row 8 (ḥēt):** S1 marks the pictograph identification "(?)"; the
  enclosure reading (fence/courtyard/wall) is one object family, so the
  flag stays `consensus` under D4 with the uncertainty on record.
- **Row 9 (ṭēt)** and **Row 16 (ʿayin)** are the scoping's other two
  §1.2 exemplars, unchanged, including the ṭēt correlate and Jeff's
  filed T5 reading of Tet (the picture of Gurd Law — boundary drawn
  first, then the contained divisions), which lives in the scoping and
  the memory record and is not audit material.
- **Rows 10/11/20 (yōd, kāp, rēš):** the BODY-neighbourhood glyphs.
  Hand, palm, and head all *denote body parts*; none *denotes* BODY,
  and PART is a relation, not a body part — so no denotative link is
  drawn. yōd and kāp both link TOUCH (the expected synonymy crowding,
  scoping §4.4).
- **Row 22 (tāw):** S2 renders the acrophonic word "signature" — the
  same cross-shaped mark (D4), recorded here.

---

## 4. Sourcing and flags — counts, disputes, departures

**Final counts: consensus 12 · contested 10 · voided (fabricated /
unsourced) 0.** No row's sourcing failed outright; no row was dropped;
no gloss in the table rests on a popular "letter meanings" list.

**The contested ten, one line each:**

- **gīmel** — pictograph scholarship (S1 [22], S3) reads a thrown
  hunting club; "camel" rests on the later letter name (gīmel ~ gamal).
- **dālet** — the transmitted name means "door"; the Proto-Sinaitic
  pictograph was a fish (digg); scholarship circulates both.
- **hē** — reference tables gloss "window"; the pictograph is a man
  with upraised arms, acrophonically haw/hillul "jubilation" (S2), and
  S3 gives heʾ "lo!".
- **zayin** — the letter name means "weapon"; Colless (S4) holds the
  original pictograph name was ziqq "manacle", later replaced.
- **nūn** — the letter name means "fish"; the pictograph derives from
  the Egyptian snake sign, naḥš "snake" (S4 renaming).
- **sāmek** — the name is from s-m-k "to support"; S1 gives "pillar(?)"
  with the pictograph disputed; Yadin (S5) argued battle equipment.
- **pē** — the letter name means "mouth"; S1 itself lists "mouth (or
  corner)", and Colless (S4) records piʾt "corner" renamed to pe.
- **ṣādē** — S1 prints the dispute in the cell: "papyrus plant/fish
  hook?"; S2's acrophony table gives ṣad "plant".
- **qōp** — "monkey" (S1; S2) against qaw "cord (of wool)" (S2), with
  "back of head" and "needle" also in circulation; priority between
  monkey and cord is itself disputed.
- **šīn** — "tooth" (letter name; S1) against šimš "sun" (S4 renaming)
  and šananuma "bow" (S2 acrophony table): three rival identifications.

**Departures from the scoping note (all with reasons):**

- **D1 — pē flag changed: consensus → contested.** Grounds: the same
  origin table (S1 [22]) that grounds the draft's gimel/dalet flags
  lists "mouth (or corner)" for pē, and S4 records the renaming
  piʾt "corner" → pe "mouth". Applying the draft's own standard
  uniformly changes this flag.
- **D2 — šīn flag changed: consensus → contested.** Grounds: S1 [22]
  lists "tooth (or sun)"; S4 records šimš "sun" → šin "tooth"; S2's
  acrophony table reconstructs šananuma "bow". (Consequence: the
  contested set grows from the draft's 8 to 10, and the latent
  conflation watchlist ceiling for SC-3 rises from 8 to 10 glyphs.)
- **D3 — zayin alternate "axe" removed; "manacle/handcuff (ziqq)"
  entered.** The draft's "axe" could not be confirmed in the scholarly
  sources consulted; the nearest scholarly material is Yadin's
  battle-equipment thesis (S5). The attested rival gloss is ziqq
  (S2, S4). Nothing was carried on the draft's authority alone.
- **D4 — interpretive line added** (stated in §1 above): "contested"
  marks rival *object* identifications, not translation variants of
  one identification. The scoping's §1.3 wording does not draw this
  line; without it, wāw (hook/peg), yōd (arm/hand), tāw
  (mark/signature), and ḥēt (fence/courtyard/wall) would flip on
  wording alone. All variants remain on record in the table or notes.
- **D5 — qōp primary changed: "cord/knot" → "monkey".** Grounds: S1
  and S2 both lead with "monkey" for the letter name; qaw "cord" is
  retained as first alternate, and the priority dispute is stated in
  the row rather than resolved by the choice.
- **D6 — link totals land at the strict end of the scoping's §4
  estimate.** Final: **0 denotative links; 6 instrumental link pairs
  over 5 glyphs, covering 5 primes (MOVE, SEE, SAY, TOUCH, DO);
  17 glyphs carry no link.** The §4 estimate (labeled an estimate)
  expected ≈8–13 instrumental primes and ≈12–16 unlinked glyphs.
  The difference is four recorded judgment calls under §1.3 rule 4,
  each noted in the TSV: weapon → DIE (zayin), window → SEE (hē),
  goad → MOVE (lāmd), and water → SOMETHING/THING (mēm) were all
  judged too loose and **not** linked. SC-3's census will run on
  this table as frozen; if the census is to test the looser calls,
  that is a second-reading decision for SC-2/SC-3, not a silent edit
  here.

**Fabricated-source rule check (scoping §3, SC-1 kill/shrink):** not
triggered. Every primary gloss and every alternate above traces to
S1–S5. Had any gloss rested only on popular lists, that row's links
would stand voided and the row flagged `fabricated-source`; no row
met that condition.

---

## 5. What SC-2 consumes

The machine-readable twin of this table is
`seed-core-table-2026-11-05.tsv` (same 22 rows; columns: num, glyph,
codepoint, name, gloss_primary, gloss_flag, gloss_source,
alternate_glosses, prime_links, link_type, correlate, notes).
`prime_links` is the link column transcribed as data: semicolon-
separated NSM prime names, `none` where empty — 6 pairs total, all
`instrumental`. Alternates are present in the TSV for the latent
watchlist and are **not** links under the ratified policy.

*SC-1 delivered 2026-11-05. Grounding: scoping note §§1–5; sources
S1–S5 as listed. NO CLAIM; dials 0/4.*

---

## 6. Correction (SC-2b, 2026-11-05)

§1 above states the primitive set as "the 65 NSM primes, pinned
to the Goddard–Wierzbicka 2014 table by citation (list as given
in the scoping §2)". That pinned list was wrong, and is
corrected in the scoping §2 in this same brick; the correction
is recorded here so this dossier does not silently contradict
its own citation.

As first written, the scoping §2 enumeration named only **62**
of the 65 primes it announced: its single entry EXIST collapsed
the canonical table's four-prime location / existence /
possession / specification cluster into one slot. Verified
against the canonical table — Goddard & Wierzbicka (2014),
*Words and Meanings: Lexical Semantics Across Domains,
Languages and Cultures* (Oxford University Press), as
reproduced in Bułat Silva & Krzyżostaniak, "Natural Semantic
Metalanguage as a Tool for Mediating Communication",
*Conversatoria Linguistica* XVI (2024), Table 1, captioned
"(Goddard & Wierzbicka 2014)"; the stabilisation at 65 in 2014
is confirmed in Wierzbicka, "'Semantic Primitives', fifty
years later", *Russian Journal of Linguistics* 25(2) (2021) —
the cluster is **BE (SOMEWHERE), THERE IS, BE
(SOMEONE/SOMETHING), (IS) MINE**. The three omitted primes:
**BE (SOMEWHERE)**, **BE (SOMEONE/SOMETHING)**, and the
possession prime **(IS) MINE** — designated HAVE in pre-2014
NSM tables (e.g. the Griffith NSM site's 2010 table, totalling
64 and lacking DON'T WANT); in 2014 HAVE was briefly replaced
by BE SOMEONE'S and then stabilised as (IS) MINE (Wierzbicka
2021, after Goddard & Wierzbicka 2016, "'It's mine!'",
*Language Sciences* 56). EXIST was an attested exponent
variant of THERE IS ("THERE IS/EXIST", Goddard 2011, appendix
table); the error was the merger, not the word.

**Effect on this dossier and its TSV: none.** Verified row by
row for this correction: the `prime_links` column references
only MOVE, TOUCH, DO, SEE, SAY — no link pointed at EXIST or
at any omitted prime — so the table and the TSV stand
unchanged, and no row, flag, or link is affected. The SC-2
module's prime set is corrected in the same brick (SC-2b).
