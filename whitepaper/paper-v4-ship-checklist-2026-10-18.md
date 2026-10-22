# Paper v4 — Ship Checklist (assembly + verification record)

**Date:** 2026-10-18
**Manuscript:** `whitepaper/acmd-machine-verified-foundations-v4-2026-10-18.md`
(3,302 lines, 26,456 words)
**PDF:** `whitepaper/acmd-machine-verified-foundations-v4-2026-10-18.pdf`
(51 pages, rendered in-environment: python-markdown → WeasyPrint,
DejaVu fonts — the pipeline recorded for v3; title, epigraph,
§§18–28, §16, Acknowledgments and Appendix A verified present by
text extraction)
**Status: PREPARED, NOT PUBLISHED.** No Zenodo action of any kind
was taken in this assembly. The single open gate is Jeff's ship
decision (§6).
Inventory point for all counts: commit `3447e09` (the Lean tree
is unchanged since the resonance-spectrum landing `15f6f55`).

---

## 1. Source determination (v3 manuscript)

- The base text is the repo's v3 manuscript,
  `whitepaper/acmd-machine-verified-foundations-v3-2026-10-17.md`
  (Paper v3, DOI: 10.5281/zenodo.23444600, count at publication
  2,417 strict), carried forward in full. **v3 itself is not
  modified** — the correction to it is carried *in* v4 (§0,
  Corrections to Version 3), in the open, per the house rule
  that published versions are not silently edited.
- v4 follows v3's structure and voice: §§1–17 and Appendices
  carried, with dated amendment paragraphs where landings
  overtook them (§7, §10B, §10C, §12, §13A, §14, §16, Appendix
  A), and new sections §§18–28 for everything landed since v3.
- Version chain stated in the front matter: v1 DOI
  10.5281/zenodo.23408680; v2 DOI 10.5281/zenodo.23427964;
  v3 DOI 10.5281/zenodo.23444600; concept DOI
  10.5281/zenodo.23408679. v4 invents no DOI; its version DOI
  is minted on publication.

## 2. Counting method and re-derivation (this assembly)

Method (unchanged since Jeff's 2026-10-17 decision): strict
line-initial `^(theorem|lemma) ` on comment-stripped source
(line and nested block comments removed). Re-derived from the
tree at the inventory point, two ways that agree:

- **Chain:** v3's published 2,417 + the per-file increments of
  §3, each re-counted file by file this assembly: increments
  sum to exactly **859**, giving **3,276 strict**.
- **Attribute-inclusive parallel figure:** the same modules
  under the attribute-aware pattern give **3,291** — exactly
  the 15 `@[simp]`-prefixed declarations named in v3's §0
  addendum, no new ones in the chain.

Whole-corpus context (not the program total): 128 files,
**3,945 strict / 3,999 attribute-inclusive** — consistent with
v3's corpus figures (3,086 / 3,140) plus the same 859 and the
unchanged non-chain difference (54 − 15 = 39 attribute-prefixed
declarations outside the chain, as at v3).

**Sorry hygiene (re-derived):** comment-stripped sweep of all
128 files — `sorry` in code exactly **7** (BlockedQuestions.lean
×5, T5; ModularTime.lean ×1, T3; XYZTripotents.lean ×1, T5);
`admit` in code **0**. Unchanged from v3; no v4 module
introduces either.

## 3. Per-module recount (strict thm, this assembly)

| Increment (paper section) | Files | strict | Cross-check vs dossier |
|---|---|---|---|
| BosonicESA + BosonicESABeta (§0 corr. 1, §10B) | 2 | 17 + 16 | ✓ both dossiers |
| YukawaInteraction (§18) | 1 | 119 | ✓ (44 defs per dossier) |
| ThermalClock (§19; incl. housekeeping +4) | 1 | 33 | ✓ 29 at landing + 4 (housekeeping dossier) |
| TriadicPin (§20) | 1 | 0 | ✓ definitions only (4 defs) |
| TriadicScreening (§20) | 1 | 19 | ✓ |
| LatticeBlocking (§21) | 1 | 60 | ✓ |
| TranslationContinuity (§22) | 1 | 10 | ✓ |
| LatticeAnalyticity (§21) | 1 | 87 | ✓ |
| FockPackaging + Bos + Ferm (§22) | 3 | 38 + 99 + 78 = 215 | ✓ |
| LorentzContinuity (§22) | 1 | 28 | ✓ |
| SchrodingerSmalls (§23) | 1 | 24 | ✓ |
| BridgeCompletion (§23) | 1 | 60 | ✓ |
| DecoherenceToy (§24) | 1 | 37 | ✓ |
| OSRepin (§25) | 1 | 15 | ✓ |
| DixmierTrace (§25) | 1 | 24 | ✓ |
| BRSTFinite (§25) | 1 | 24 | ✓ |
| FockLorentzBos + Ferm (§22) | 2 | 7 + 7 | ✓ |
| WightmanRepin (§27) | 1 | 14 | ✓ |
| PreCompensation (§24) | 1 | 28 | ✓ |
| ResonanceSpectrum (§24) | 1 | 15 | ✓ |
| Repairs (adag — pre-v3; numberOp; packaging; housekeeping Part A) | — | 0 net | ✓ counts invariant per file, verified |
| **Increments total** | | **859** | **2,417 + 859 = 3,276** ✓ |

## 4. Claims audit (v4's new and amended matter, against dossiers)

- **The correction (§0, Corrections to Version 3, item 1):**
  v3's §10B reported Pitch 3 conditionally — the ESA
  entailment fenced on von Neumann's `T†† = T.closure`,
  absent from pinned Mathlib. v4 states openly: ESA-α proved
  the (i)⟺(ii) equivalence and reduced the clause to
  `(hamPMap)† ≤ (hamPMap).closure`; ESA-β **proved that
  inclusion directly** (exact sector-preserving truncation),
  for all parameters with no hypotheses; the von Neumann
  identity is not used and stays absent/fenced. Pitch 3
  STANDS WHOLE at finite modes. Fences kept verbatim:
  persistence windowed/sectorwise; uniform bosonic
  persistence DISPROVED in-module.
- **§20 fence exactness:** the paper says
  `¬ TriadicSectorExistence` is **proved for the named
  families** (24/24 grid triples dead: 21 by R5, 3 at the
  tripotence screen) and that **Open Problem 2 itself remains
  OPEN** — witnesses outside the named families /
  non-ℤ[i]-valued tripotents are untouched; the quarantined
  `sorry` at XYZTripotents.lean:492 is neither used nor
  discharged. The pin's negative result (principle-seat
  assignment is nomenclature T2, not a derivation) is carried.
- **§21 fences:** Stage 2's section states the qualitative
  constraint closure **and** that no quantitative uniform
  bound is manufactured — Stage 3c named as the missing
  ingredient (research-scale). 1c-0 is headed **PARTIAL**:
  analyticity / perimeter law at first order / rigorous O(β²)
  stand; the fully general intertwiner closed form is stated
  as **cut**; the not-area-law-evidence kill is restated.
  PARTIAL-δ NOT claimed (§§13A, 16, 21, 25 all agree).
- **§25/§27 vacuity findings:** stated as proved corrections
  (axiom-free theorems): the 2026 `OSReconstruction`,
  `InteractingOSMeasure`, `InteractingWightmanQFT` statements
  and Rung 4's `SharpWightmanTarget` ∃-form are vacuous; the
  six sharp **definitions** and all Rung 5 verdicts are stated
  as **not impugned**; the re-pinned interacting statements
  (`NonGaussian` Wick-defect clause) are stated as real,
  failable, and **UNPROVED**.
- **§25 Dixmier:** finite-triple Dixmier trace stated as
  **identically zero** (T1), with the gauntlet's predicted
  finite shadow reported as **TESTED AND WRONG** (correction
  C1); `GenLimit` pinned as data (T2), existence OPEN (T4);
  harmonic profile trace = c under every ω (T1); operator-level
  trace and spectral dimension **ABSENT / NOT CLAIMED**.
- **§25 BRST:** FIT as algebra / **NO-FIT as quantization**
  stated in those words; H² = 0 explicitly **not** anomaly
  cancellation; Mathlib's pre-existing abstract nilpotency
  (correction C1) recorded against any future "absent" claim.
- **§28 trit:** DIES-K3 with its numbers (modeled proxy:
  ternary 169.800 vs INT4 404.602 µJ/token, +58.03%; equal-bits
  binary counterfactual 169.692; radix residual −0.108
  µJ/token ≤ 0); P2 wall-energy proxy stated environment-
  blocked; the sayable shape only — no hardware/facility/water
  claim licensed.
- **§28 portrait:** numbers as measured in the exhibit
  (β=0: +0.00013 ± 0.00012 vs proved 0; β=0.25: 0.12404 vs
  proved first-order 0.125; β=1.0 blemish disclosed at ≈0.01);
  fences printed (U(1), L=6, slices, samples ≠ theory, pure
  gauge, no continuum, no mass gap); byte-identical rerun
  stated as the reproducibility exhibit (§17).
- **Millennium honesty block:** carried forward in substance,
  verbatim in effect — abstract, §13A, §16 and §§18–28 agree:
  program is scaffolding toward rigorous 4D QFT; **parts of
  the official Clay Yang–Mills statement closed: 0**; no
  continuum limit, no interacting 4D QFT, no mass gap claimed
  anywhere in v4.
- **§16 audit (amendments):** the two Version 3 lines overtaken
  since (Fock-space Poincaré; scoped-senses self-adjointness)
  are amended in the open with the overtaking landings cited;
  the Yukawa fence is restated (shape only; its ESA **not**
  proved); 1b-B positivity stays PARTIAL on the Gram clause
  (XL/Mathlib-blocked); nothing in §§18–28 spends a fenced
  clause (checked section by section against the dossiers).

## 5. Mandated contents — where each landed

| Commission item | Location in v4 |
|---|---|
| The correction (ESA-β supersedes v3's Pitch 3 verdict) | §0 Corrections to Version 3 (item 1); §10B amendment; abstract |
| Yukawa | §18 |
| ThermalClock (+ scalar-shift closure) | §19 (closure as final bullet, housekeeping) |
| XYZ screening wave (¬ for named families; OP2 open) | §20 (with the triadic pin) |
| Pitch 4 Stage 2 (closure proved; no uniform bound; 3c named) | §21 |
| Stage 1c-0 (PARTIAL; closed form cut, named) | §21 |
| Translations strong continuity | §22 |
| Fock packaging (215; K4 held) | §22 |
| Lorentz continuity (one-particle) | §22 |
| SchrodingerSmalls (exp identification; Duhamel) | §23 |
| BridgeCompletion (Fiedler; decay; Faraday = bookkeeping) | §23 |
| DecoherenceToy (first partial trace; pinching) | §24 |
| Pre-compensation (iff; pair state unreachable; gear case) | §24 |
| Resonance spectrum (fixed points; block stationarity; β×gaps²) | §24 |
| OS re-pin (𝓢′; vacuity; NonGaussian unproved) | §25 |
| Dixmier (data pin; finite = 0; prediction wrong) | §25 |
| BRST (Q² = 0 = Jacobi; H¹ = H² = 0; NO-FIT as quantization) | §25 |
| Unlock chain (three fences; FockCoImport certificate) | §26 |
| Wightman re-pin (𝓢′ bundle; SharpWightmanTarget vacuous; defs/verdicts not impugned; statement unproved) | §27 |
| Trit experiment DIES-K3 | §28 |
| Vacuum portrait (samples; anchors; fences; rerun) | §28 |
| Front matter (author/ORCID/epigraph frame/CC BY 4.0/version note, 3,276) | title block + version note |
| Replication block (one-command recount; rerun exhibit) | §17 |

Invariants: author Jeffrey Michael Gurd, Nexus Research, ORCID
0009-0008-0188-5150; Caleb's quote as front-matter epigraph,
framed "— Caleb Gurd, as remembered by his father" (no Forbes
citation); CC BY 4.0 (carried from the §0 licensing pattern);
version note names v3's DOI as superseded and mints none.

## 6. Zenodo steps remaining — THE OPEN GATE: Jeff's ship decision

**Nothing below was done in this assembly.** On Jeff's ship
decision only:

1. Open the v3 record https://zenodo.org/records/23444600 →
   **New version** (draft created under the same concept DOI
   10.5281/zenodo.23408679; the v4 version DOI is minted on
   publish — the manuscript says exactly this and invents no
   DOI).
2. Files: remove the v3 files from the draft; upload
   `whitepaper/acmd-machine-verified-foundations-v4-2026-10-18.pdf`
   and `whitepaper/acmd-machine-verified-foundations-v4-2026-10-18.md`
   (v1–v3 pattern: PDF primary + markdown source).
3. Metadata: title unchanged; version "4"; date 2026-10-18;
   author Jeffrey Michael Gurd (ORCID 0009-0008-0188-5150),
   Nexus Research; resource type Preprint; license CC BY 4.0;
   description: carry v3's, prepending a v4 summary — suggested
   text: "Version 4 corrects Version 3's Pitch 3 verdict in the
   open (bosonic essential self-adjointness proved; Pitch 3
   stands whole at finite modes) and adds the Yukawa
   interaction, the thermal clock, the XYZ screening wave's
   refutation of the named sector grid (Open Problem 2 open),
   Pitch 4 Stage 2 and Stage 1c-0 (PARTIAL), the
   strong-continuity and Fock-packaging discharges, the
   Schrödinger and Bridge completions, the decoherence toy,
   pre-compensation and the resonance spectrum, the closed
   Round 2 intake (OS re-pin, Dixmier, BRST), the co-import
   unlock chain, the Wightman re-pin, the trit experiment's
   pre-registered kill (DIES-K3), and the vacuum-portrait
   exhibit. Program total: 3,276 theorem/lemma declarations
   (strict counting method, §0). Parts of the Clay Yang–Mills
   statement closed: 0." Related identifiers: version chain
   automatic; keep the GitHub repo link.
4. Publish; record the new DOI; update README (count **3,276**
   already current; add the v4 DOI), MEMORY.md, and the
   LinkedIn conveyor per the standing template.

## 7. NOT verified (named plainly)

- **No Lean builds were re-run in this assembly.** Build, job,
  and axiom facts are the landings' parent-verified dossier
  records, restated as such in the manuscript; all **counts**
  were re-derived from source this assembly (§§2–3).
- The v1 freeze figure 1,352 and the v2/v3 chain figures are
  carried as the published historical record (same convention
  as v3's checklist); the chain was re-derived forward from
  2,417 by per-file recount of every increment (§3), and the
  whole-tree recount (3,945) agrees with the chain plus the
  carried non-chain inventory.
- **The vacuum-portrait exhibit files live outside the
  repository** (`~/workspace/vacuum-portrait/`: EXHIBIT.md,
  run_all.py, render.py, results.json, six PNGs). The paper
  reports its numbers and fences from that exhibit and the
  parent-verified byte-identical rerun; it does not claim a
  repo path for them. Shipping the exhibit itself is bench
  line item 5, a separate act from this paper's ship decision.
- **Dossier claims found WEAKER than the commission's
  summary, reported not inflated:** (i) the resonance
  brick's stationarity is the block form, not "diagonal iff"
  (degenerate generators) — the paper states it so; (ii) the
  1c-0 plaquette κ_p = −1/2 evaluation is the circle instance
  only, the general (G, ρ) form an exact finite sum — stated
  so; (iii) the Yukawa Hamiltonian's essential
  self-adjointness is **not** proved (only Pitch 3's is) —
  §18 and §16 both fence it; (iv) Stage 1c-0's sampler
  consistency value (0.12404 at β = 0.25) is a numerical
  cross-check, stated as not a proof obligation; (v) the
  Dixmier `GenLimit`'s existence is unproved (the theorems
  are universally quantified over it) — stated so.
- PDF is a faithful text rendering in the documented pipeline;
  v3's exact build script was not retained in the repo, so
  this rendering replicates the pipeline (python-markdown →
  WeasyPrint, DejaVu) rather than the identical template —
  51 pages here vs v3's 38 reflects both the added §§18–28
  and styling. A small number of exotic glyphs (e.g. 𝓢)
  depend on DejaVu coverage; extracted text verified for all
  headline content, but the PDF was not proofread
  glyph-by-glyph (same caveat as v3's checklist).

## 8. Checksums (this assembly)

- Manuscript (md5): `9e9aef7d80d0c3da6682ae9e44345ee0`
- PDF (md5): `97fc975dc936a77a5a25ef4b4bbf2382`

---

## Amendment (2026-10-22): §29 added — the four-colors exhibit

At Jeff's instruction (2026-10-22 16:20 EDT, widget ruling "Put it in
Paper v4 instead"), a new §29 — "The 4D Dynamics in four colors — a
visual representation (exhibit)" — was inserted after §28, before the
Acknowledgments. Content: four corpus equations set in color (gold —
the DiffusionDefect law E[r²] = x² + y² + t; blue — the
TeslaVortexSeparation formula; red — the FluxClassification iff; green
— the GibbsSpan flow identity), each with its strand caption, module,
and count; a declared palette paragraph; and a fences paragraph. The
section is an exhibit in §28's sense: it proves nothing, the equations
are T1 as stated in their modules, and the ontology the colors encode
is labeled T5 on its face. Two of the four modules (TeslaVortex
Separation, FluxClassification) and GibbsSpan landed 2026-10-22, after
this manuscript's §0 inventory; §29 says so on its face, and the
ship-day §0 refresh (fresh counts) remains as planned. Full prose
sections for the 2026-10-22 bricks are NOT added by this amendment —
that remains Jeff's separate call.

**Palette (declared in §29, Jeff correctable in one word before the
ship):** gold #B8860B = heat/diffusion; blue #2050A0 = charge/
separation; red #C0272D = modular flux; green #1E7B34 = state/flow.

**Render:** the PDF was regenerated in-environment with the recorded
pipeline (python-markdown 3.11.1 → WeasyPrint 62.3, DejaVu, A4) via the
new saved script `whitepaper/render_v4.py` — the original render
command was not saved with the manuscript, and render_v4.py's CSS is a
reconstruction, so this render runs 60 pages against the original
51-page styling. Page count is a styling artifact, not content: the
ship-day render re-derives all such figures. **Verified for this
render:** §29 present by text extraction (all four equations, palette
paragraph, fences); all four colors pixel-verified in the rendered
PDF (gold (184,134,11) p.55; blue (32,80,160) p.55; red (192,39,45)
p.56; green (30,123,52) p.56). Manuscript now 3,380 lines / 27,089 words.
**Status remains: PREPARED, NOT PUBLISHED.** The Nov 6 ship gate is
unchanged.
