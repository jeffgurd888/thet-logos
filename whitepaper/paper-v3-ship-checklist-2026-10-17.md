# Paper v3 — Ship Checklist (assembly + verification record)

**Date:** 2026-10-17
**Manuscript:** `whitepaper/acmd-machine-verified-foundations-v3-2026-10-17.md`
(1,999 lines, 16,006 words)
**PDF:** `whitepaper/acmd-machine-verified-foundations-v3-2026-10-17.pdf`
(33 pages, rendered in-environment: python-markdown → WeasyPrint,
DejaVu fonts; title, epigraph, §13A, §16, Acknowledgments and
Appendix A verified present by text extraction)
**Local commits (NOT pushed, NOT uploaded):**
`6ebc733` (manuscript + PDF); this checklist committed separately.
Inventory point for all counts: commit `4380a2a`.

---

## 1. Source determination (v2 manuscript)

- The repo contains exactly one v2 manuscript source:
  `whitepaper/acmd-machine-verified-foundations-v2-2026-10-16.md`,
  whose header reads "Version 2 draft. Review copy for the
  author." **No separate final published markdown exists.** The
  parked-fleet gauntlet names this file the "V2 of record," and
  v3 was assembled from it.
- `~/workspace/your_files/acmd-machine-verified-foundations.pdf`
  is a v2 rendering (title, abstract, §0 freeze table all match
  the draft), but its embedded DOI string could not be
  text-extracted (the "Version 2" line extracts; "zenodo"
  matches are body-text repository-path strings). Its identity
  as the exact file uploaded to Zenodo is therefore **not fully
  confirmed** — immaterial here, since v3 derives from the repo
  markdown.

## 2. Counting method (the one used for every v3 number)

Comment-stripped source (line + nested block comments removed);
count lines matching
`^(@\[[^\]]*\] )?(private |protected )?(theorem|lemma) ` —
i.e. declarations whose keyword begins a source line at column
0, with an optional same-line attribute prefix. Definitions:
same pattern over `def|abbrev|structure|instance` (incl.
`noncomputable` variants). This is the method stated in the
manuscript's §0 v3 addendum.

**⚠ DECISION POINT FOR THE PARENT — the headline total.**
The task brief and the repo README say 2,427 ("column-0 grep
convention"). Re-derivation shows 2,427 is the sum of the
landing dossiers' figures, which mixed two grep patterns, and
it does **not** reproduce under any single uniform method:

| Uniform method | Program total |
|---|---|
| Strict column-0 only (`^(theorem|lemma) `) | 2,417 |
| Attribute-aware (manuscript's stated method) | **2,432** |

The dossiers themselves were split: Rung 9 and Stage 0 counted
strict column-0; Pitch 2 and MassShellBoost counted
attribute-aware. Exactly five real declarations sit between the
two conventions, all present since their files' first commits
(git-verified): `gamma_apply` (`@[simp]`, SecondQuantGamma.lean,
Rung 9: 51 attribute-aware vs 50 strict) and LatticeGauge's four
`@[simp]` loop lemmas `loopEnd_nil`, `loopEnd_cons`,
`loopProd_nil`, `loopProd_cons` (Stage 0: 72 vs 68 — the Stage 0
dossier itself states its method as "line-initial grep … 68
theorem/lemma + 22 defs + 11 instances").

**Resolution shipped in the manuscript:** one uniform method
(attribute-aware), headline **2,432**, with the reconciliation
printed in §0 (2,427 + 1 + 4 = 2,432) and both dossier-pattern
differences named. Shipping 2,427 under a stated method that
does not reproduce it would violate the re-derivation mandate.
**Parent action:** accept 2,432 (and refresh README/ledger from
2,427 → 2,432 at publication) or direct a different convention
and the manuscript's §0 note + table must be re-cut before
upload.

## 3. Per-module recount (attribute-aware thm / defs, comment-stripped)

Program chain (chain arithmetic: 1,352 + 297 = 1,649 at v2
scope; + 783 v3 increments = **2,432**):

| Module(s) | thm | defs | Dossier cross-check |
|---|---|---|---|
| Rungs 1–8 era (v1 freeze, carried record) | 1,352 | — | published figure, not recounted at freeze commit |
| SecondQuantGamma + SecondQuantDGamma (Rung 9) | 51 (33+18) | 13 | dossier 50 — +1 = `gamma_apply` (see §2) |
| BosonicAssembly (8B) | 31 | 6 | ✓ |
| BosonicSecondQuant + BosonicGamma (Rung 10) | 31 (25+6) | 13 | ✓ |
| SexagesimalClock (App A) | 31 | 13 | ✓ (12 defs + 1 structure) |
| BosonicGammaFunctor | 42 | 8 | ✓ |
| FluxTwist (App A) | 38 | 10 | ✓ |
| WeldDuality (App A) | 73 | 18 | ✓ |
| FockLimit + FermionicLimit + BosonicLimit (P2-A) | 61 (6+26+29) | 26 | ✓ |
| FermionicLimitOps + BosonicLimitOps (P2-B) | 80 (32+48) | 31 | ✓ → Pitch 2 = 141 / 57 |
| FermionicInteraction (P3-C1) | 58 | 15 | ✓ (raw grep 59; 59th is header-comment prose, disclosed in dossier) |
| SchrodingerDynamics | 49 | 10 | ✓ (raw 52 − 3 prose, disclosed in dossier) |
| BosonicInteraction (P3-C2) | 69 | 21 | ✓ (raw 75 − 6 docstring prose) |
| MassShellBoost | 86 | 15 | ✓ (80 line-initial + 6 `@[simp]`, reconciled in dossier) |
| BridgeLaplacian (App A) | 29 | 7 | ✓ |
| LatticeGauge (Stage 0) | 72 | 33 | dossier 68 strict — +4 `@[simp]` loop lemmas (see §2) |
| LatticeCorrelations (1a) | 68 | 13 | ✓ |
| LatticeReflection (1b-A) | 67 | 16 | ✓ |
| LatticePositivity (1b-B) | 44 | 10 | ✓ |
| LatticeOSSpace (1b-C) | 42 | 17 | dossier report said 16 defs; stripped recount gives 17 (defs incl. instances) — manuscript uses 17 under the stated method |
| LatticeTransfer (1b-D) | 58 | 13 | ✓ |
| TritGrading (App A, qualitative only) | 27 | 14 | ✓ — no chain increment, as at v2 |

Whole corpus (context, not the program total): 103 files;
3,140 declarations attribute-aware / 3,086 strict column-0
(comment-stripped).

**Sorry hygiene (re-derived):** comment-stripped sweep of all
103 files — `sorry` in code exactly **7** (BlockedQuestions.lean
×5, T5; ModularTime.lean ×1, T3; XYZTripotents.lean ×1, T5);
`admit` in code **0** (3 prose occurrences corpus-wide).

## 4. §16 audit (every v2 line, against the current ledger)

| v2 §16 line | Verdict | Action in v3 |
|---|---|---|
| No 4D QFT | TRUE, one clause stale ("no interacting theory is constructed") | clause qualified; fence restated at the new line below |
| No continuum limit | TRUE | unchanged |
| No mass gap | TRUE | unchanged + explicit "Parts of the official Clay statement closed: **0**" |
| No derived masses/couplings | TRUE | unchanged |
| No physical predictions | TRUE | unchanged |
| Baryon asymmetry not addressed | TRUE | unchanged |
| No derivation from analysis | TRUE | unchanged |
| Represented U(1) ≠ hypercharge | TRUE | unchanged |
| Free-theory gaps ≠ mass gap | TRUE, incomplete list | extended to §§10A, 10B, 13A gaps |
| **No interacting theory of either statistics** | **FALSE (overtaken by Pitch 3)** | **withdrawn in the open**; replaced by "No interacting continuum theory" (no gauge coupling; Yukawa unstatable until `adag` repair; no scattering) |
| **No infinite-mode or continuum Γ** | **FALSE since Pitch 2 (2026-10-16)** | **withdrawn in the open**; replaced by "No continuum Γ" |
| No continuum Poincaré representation | partially overtaken (one-particle measure invariance now T1) | amended: "No Poincaré representation on Fock space, and no interacting Poincaré representation" (strong continuity + Fock packaging priced; Stage 4 FRONTIER) |
| No string landscape / M-theory | TRUE | unchanged |
| Derivation-from-first-principles boundary | TRUE | unchanged |
| No bridge from background algebra | TRUE | unchanged + bridge exhibit added to the fenced module list |
| — (new) | — | **No reflection positivity at general β**; PARTIAL-δ NOT claimed |
| — (new) | — | **No lattice gap at general β; no uniformity** (exact gap at β = 0 only; Stage 3c research-scale) |
| — (new) | — | **Bosonic Hamiltonian not self-adjoint unqualified** (ESA priced) |

Abstract audited the same way: its "No interacting theory of
either statistics" line rewritten; its gap list updated to
§§9, 10, 10A, 13A; "Parts closed: 0" added. §14 items 2 and 3
marked DISCHARGED; item 4 repriced; items 9–16 added (ESA,
adag/Yukawa, Gram clause, general-β gap, Pitch 4 stages,
Schrödinger smalls, Bridge follow-ons, decoherence toy). §15
gains: uniform bosonic persistence DISPROVED; weak-dichotomy
exact gaps (both campaigns) false; plane-link OS positivity
false; SymmetricAlgebra Fock route re-killed; Round 2 OS
fit-audit killed-as-redundant.

## 5. Mandated contents — where each landed

0. Pitch 2 first + §16 Γ line: §10A (mandatory spectral-gap
   qualifier carried verbatim in substance); corrections note
   in §0; §16 amended in place.
1. Pitch 3 verdict: §10B with the verdict block (C1 whole; C2
   except ESA; uniform persistence disproved in-module).
2. SchrodingerDynamics: §10C (49 T1; exp-identification and
   Dyson fences priced).
3. MassShellBoost: §7 amendment in place (86 T1; full
   restricted-Lorentz invariance of the free mass-shell
   measure).
4. BridgeLaplacian: Appendix A, fifth entry, fenced as
   background algebra.
5. Pitch 4: §13A (scoping NO CLAIM; Stage 0; 1a with Elitzur
   at general (G,ρ) every β; 1b-A stands; 1b-B PARTIAL
   γ-extended, Gram clause XL/Mathlib-blocked; 1b-C stands,
   L² route; 1b-D stands, β=0 gap exactly 1, general-β gap
   fenced M–L; PARTIAL-δ NOT claimed).
6. Acknowledgments: new section, staircase condensed from
   `ACKNOWLEDGMENTS.md`, originators first, closing line
   carried.
7. Caleb epigraph: front matter, exact frame "— Caleb Gurd,
   as remembered by his father." No Forbes.
8. Counts: §3 above; method stated in the paper's §0.
9. §16: §4 above; Clay parts closed 0 stated (abstract, §13A,
   §16).

Invariants: author Jeffrey Michael Gurd, Nexus Research, ORCID
0009-0008-0188-5150 (front matter + §0 pattern carried); CC BY
4.0 (§0 licensing pattern carried from v2); v1 DOI
10.5281/zenodo.23408680 and v2 DOI 10.5281/zenodo.23427964
cited in the version note as previous versions.

## 6. Zenodo steps remaining (parent)

1. Open the v2 record https://zenodo.org/records/23427964 →
   **New version** (draft created under the same concept;
   the v3 version DOI is minted on publish — the manuscript
   says exactly this and invents no DOI).
2. Files: remove the v2 files from the draft; upload
   `whitepaper/acmd-machine-verified-foundations-v3-2026-10-17.pdf`
   and `whitepaper/acmd-machine-verified-foundations-v3-2026-10-17.md`
   (v1/v2 pattern: PDF primary + markdown source).
3. Metadata: title unchanged; version "3"; date 2026-10-17;
   author Jeffrey Michael Gurd (ORCID 0009-0008-0188-5150),
   Nexus Research; resource type Preprint; license CC BY 4.0;
   description: carry v2's, prepending a v3 summary — suggested
   text: "Version 3 adds the infinite-mode free theory
   (Pitch 2), interacting Hamiltonians at finite modes with the
   Pitch 3 verdict (Pitch 3), Schrödinger dynamics, the
   discharged Rung 7 boost window, and Pitch 4 Stages 0/1a/1b
   (finite lattice gauge theory through the transfer matrix).
   Program total: 2,432 theorem/lemma declarations (uniform
   counting method, §0). Parts of the Clay Yang–Mills
   statement closed: 0." Related identifiers: the version
   chain is automatic; keep the GitHub repo link.
4. Publish; record the new DOI; update README (count **2,432**
   per §2 decision + v3 DOI), MEMORY.md, and the LinkedIn
   conveyor per the standing template.
5. Push the local commits (`6ebc733` + this checklist's commit)
   via the standard delta-push route when ready.

## 7. NOT verified (named plainly)

- No Lean builds were re-run in this assembly. Build/job/axiom
  facts are the landings' parent-verified dossier records,
  restated as such in the manuscript; all **counts** were
  re-derived from source this session (§3).
- The v1 freeze figure 1,352 is carried as the published
  historical record (the program-chain convention, same as
  v2); it was not recounted at the freeze commit under the v3
  method.
- Stage 1b-B's two counterexamples are dossier-recorded hand
  computations, not Lean theorems — stated as such in the
  manuscript.
- The published v2 Zenodo file set was not fetched for
  comparison (§1).
- PDF is a faithful text rendering; a small number of exotic
  Unicode glyphs (e.g. ⟪ ⟫) depend on DejaVu coverage —
  spot-checked pages render cleanly, but the PDF was not
  proofread glyph-by-glyph.

## 8. Decision + re-cut (2026-10-17, after assembly)

The author decided the counting convention: **strict line-initial**
(`^(theorem|lemma) ` on comment-stripped source). **Program total:
2,417.** The manuscript was re-cut before any upload: §0's method
statement and recount note rewritten (all fifteen `@[simp]`-prefixed
declarations named; the Version 2 scope recounts to exactly its
published 1,648; the README chain's 2,427 explained as the
mixed-pattern sum — Pitch 2 +4 and MassShellBoost +6 over strict);
table increments Rung 9 +50, Pitch 2 +137, boost discharge +80,
Stage 0 +68; corpus reference figure 3,086 (strict,
comment-stripped); §7 (80), §10A (137; Campaign A 57), §13A
Stage 0 (68) aligned. PDF re-rendered from the corrected
manuscript (38 pp. in this environment's WeasyPrint styling) and
text-verified: "2,417" ×3, "2,432" ×1 (the named
attribute-inclusive alternative), "1,649" ×0. In §6's suggested
Zenodo description, read 2,417 (strict counting method, §0) for
the total.
