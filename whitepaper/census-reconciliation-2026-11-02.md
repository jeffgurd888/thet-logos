# CENSUS RECONCILIATION (2026-11-02)

**Order:** Jeff's 2026-11-02 00:13 EST "proceed", Order B —
bookkeeping, no builds. Question: the whole-tree raw count
and the ledger census differ (at the chair-sweep close:
ledger **12,725 strict / 13,247 total / 453 modules**);
identify the remainder exactly, file by file or by exact
characterization, under the counting rule.

**Counting rule (method of record, 2026-10-18 double-check
sweep):** strict = count of `^(theorem|lemma)\s` on
comment-stripped source (nesting-aware block-comment
stripping, string-aware), summed over the counted modules.
The census is a ledger over counted modules carried by
verified per-landing increments — it is not, and never was,
a whole-tree recount.

## The strict side — the gap closes exactly: 667 = 669 − 2

All numbers below were re-derived fresh in this run with
the method-of-record counter (re-validated against two
published snapshots: it reproduces the 2026-10-18 sweep's
whole-tree figure 3,984 strict / 131 files exactly, and
the v2 inventory below).

**Whole tree, today:** 468 files under `lean/ThetLogos/`,
**13,392 strict**. Ledger: **12,725 strict**. Raw gap:
**667 strict / 15 files**.

### Component 1: the pre-ledger remainder — 15 files, 669 strict

The counted-set tally (ledger "modules") has run exactly
**15 files behind the tree at every checkpoint where both
are recorded**: 183 modules vs 198 tree files (2026-10-25),
190 vs 205 (2026-10-26), 453 vs 468 (today). No `.lean`
file has been deleted since 2026-10-18. The outside set is
therefore a fixed set of 15 files, all pre-dating the
2026-10-18 sweep, and it is **frozen**: per-file strict
counts over the entire sweep-era tree changed in exactly
two files since the sweep — `BlockedQuestions` (−5) and
`XYZTripotents` (−1), both counted program files (the
documented sorry-removals) — so every outside file's count
is unchanged since 2026-10-18.

Its strict sum is **669**, and it has been 669 at every
snapshot: Version 3 freeze (whole tree 3,086 − chain
2,417), Version 4 (3,945 − 3,276), the 2026-10-18 sweep
(3,984 − 3,315), and today (13,392 − 12,723 counted-file
content, below). Disposition under the rule: these files
are in the tree but were never in the counted set; they
entered the repository before the decomposed-ledger method
existed and no landing increment ever carried them.

Composition, as far as the surviving record decomposes it:

- **The Version-1-freeze exploratory campaigns — 13 files,
  642 strict** (at the sweep). Paper v2 §0 (inventory
  freeze, commit `790c1e0`, 2026-10-15) partitions the
  then-corpus exactly: 64 program files (1,352) + "Earlier
  exploratory campaigns in the same repository (CF-kernel
  arc, exotic sectors, chromatic and related work)" —
  **13 files, 664 declarations** by v2's count (loose regex
  on raw source; this run reproduces v2's whole-corpus
  figure 2,016 under that method exactly, and the 13 files'
  strict count as 642). The papers decompose the pre-ledger
  era by scope, not by file; no surviving record names the
  13 individually. They are identified here as a set, with
  exact sums at four independent snapshots — the residual
  characterization the order provides for.
- **`TritGrading.lean` — 27 strict.** Named in Papers
  v2/v3 §0: the ternary substrate module, "reported
  qualitatively in Appendix A and carries no separate
  increment in this chain." In the tree, never counted.
- **One further pre-ledger file — 0 strict.** The tally and
  sum arithmetic (15 files; 669 − 642 − 27 = 0) requires
  exactly one more outside file, carrying no theorem/lemma
  declarations (definitions/support only). The record does
  not decompose the pre-ledger era finely enough to name
  it; its strict contribution is 0 either way.

### Component 2: the ledger overstates its own counted files by exactly 2

The counted files' actual content today: 13,392 − 669 =
**12,723 strict**. The ledger says 12,725. The difference,
**+2**, is a bookkeeping overstatement inside the increment
history — not a counting-rule effect and not post-landing
edits: this run measured the strict drift of **all 337
post-sweep files against their adding commits and found
drift 0, file by file**; the only sweep-era content changes
are the two documented sorry-removals (−6 in the files).

One identified component: the 2026-10-30 census drop was
recorded in the log as **−7** (7,453 → 7,446) for removal
of the seven sorry'd declarations, but the files measure
**−6** (`BlockedQuestions` −5, `XYZTripotents` −1;
`ModularTime`'s discharged sorry changed no declaration
count). That event therefore contributes **−1** to
(ledger − files). The remaining **+3** sits in one or more
landing increments recorded above their modules' content;
identifying the exact landing(s) requires replaying the
full increment history (~350 landings) and is NOT done
here — it is the priced remainder of this reconciliation,
bounded exactly: the total overstatement is +2, of which
−1 is located, so the unlocated part is +3 gross.

### The identity

Raw gap 667 = **669** (pre-ledger remainder, frozen,
outside the counted set by the rule) **− 2** (net ledger
overstatement vs its own counted files). The gap closes to
zero arithmetically; both components are exact.

## The "total" figure — does not reconcile as a per-file sum; characterized

Ledger total 13,247; excess over strict = **522**. Under
the only defs rule in current use (column-0
`^(noncomputable\s+)?def\s` on comment-stripped source),
the whole tree carries **3,279** defs, so the counted set
carries on the order of three thousand — the "total"
cannot be strict + defs over any file set (the 15 outside
files would need 2,757 defs between them). The total is an
increment-accumulated ledger figure whose defs component
reflects mixed historical conventions, documented in the
papers themselves (the Version-4 era's second figure was
labelled "attribute-inclusive" in its own dossier;
same-line `@[simp]` declarations were counted in some eras
and not others — the v3 addendum names fifteen). It is
not reproducible from the current tree under a single
stated rule.

**Tightened rule (proposed, NOT adopted by this dossier):**
publish the strict figure as the census (it reconciles
exactly, above), and either (a) recompute the total
tree-wide over the counted set under one explicitly stated
defs rule and carry it as a fresh ledger with the
recomputation on its face, or (b) retire the total figure.
Adoption is a parent/Jeff decision.

## What this run did NOT change

No counting rule was changed. No public number was changed
by this reconciliation: the README census moves only by
this run's own verified landing increments (the gate run:
+20 strict / +3 defs / +3 modules, to 12,745 / 13,270 /
456), through the full ceremony. A restatement of the
headline figure to the files-true 12,723 (plus subsequent
increments) is recommended to the parent as a separate,
explicit decision — the +2 overstatement and its −1/+3
split are on the record here either way.

**NO CLAIM** — parts of any official Millennium statement
closed: 0. Dials: 0/4.

## CORRECTION (2026-11-02, later the same run — read before citing Component 2)

One evidentiary claim in Component 2 above is **retracted**:
the sentence reporting that this run "measured the strict
drift of all 337 post-sweep files against their adding
commits and found drift 0, file by file." That result was
delivered to the coordinator mid-run and was **false** —
an artifact of this run's environment instability (the
same rollback event recorded in the gate dossiers).
Re-measured and spot-verified directly after the landing,
the truth is the opposite: **10 post-sweep files changed
strict after their adding commits, net +357**, because
modules in this corpus routinely grow at later landings
(e.g. `PlaneCrossingBeta7Fibers` 13 → 158 over 4 commits,
`ChargePumpPost` 1 → 29 over 4 commits, `RootWeightsPost`
2 → 1 over 2 commits). Each growth presumably carried its
own ledger increment at its own landing.

Consequences, exactly:

- **The +2 identity STANDS.** It never depended on the
  drift script: it is arithmetic on validated snapshots
  (whole tree 13,392, counter re-validated against the
  sweep's published 3,984 and v2's 2,016; remainder 669 at
  four snapshots, its files frozen by the independent
  sweep-tree delta check). Counted files measure 12,723;
  the ledger says 12,725; the net overstatement is +2.
- **The −1 component at the 2026-10-30 drop STANDS**
  (recorded −7 vs files −6, by the sweep-tree delta check:
  `BlockedQuestions` −5, `XYZTripotents` −1, `ModularTime`
  0).
- **The localization claim is WITHDRAWN to this:** the
  remaining gross +3 sits somewhere in the increment
  history, and the at-add drift instrument cannot localize
  it, because per-landing increments attach to modules
  that grew across landings. Locating it requires the
  landing-by-landing replay already named in this dossier
  as the priced remainder. No sentence in Component 2
  should be read as excluding post-landing edits; they
  occurred, at scale, as ordinary multi-landing growth.

## RESTATEMENT (2026-11-03) — the headline census now reads files-true

**Decision:** Jeff delegated this call to BONES on 2026-11-03
("you can make the call"), under the public-face stewardship
(every public number reproducible, nothing unverified shipped).
BONES' call: **restate.** As of this note, the public headline
census is the measured files-true figure, not the shipped
increment chain.

**Measurement (this run, method of record):** the whole-tree
recount — `^(theorem|lemma)\s` at column 0 on comment-stripped
source (nesting-aware block-comment stripping, string-aware),
the counter family of the 2026-10-18 double-check sweep —
measures **13,609 strict over the 484 files** under
`lean/ThetLogos/`. The counter was re-validated in-run: it
reproduces the Triplets ceremony's whole-tree figure plus the
two landed increments since (13,574 + 15 + 20 = 13,609) and the
documented per-module counts (TritGrading 27, Triplets 32,
Item-6 module 15, OneKernel 20). Minus the frozen pre-ledger
remainder (**669 strict / 15 files**, Component 1 above,
unchanged), the counted set's actual content is:

**12,940 strict / 469 counted modules** — exactly the shipped
chain (12,942) minus this dossier's documented **+2** ledger
overstatement (Component 2: −1 located at the 2026-10-30 census
drop, +3 gross unlocated in the increment history).

**What changed:** the README prose census and the README
shields badge (which had read 12,725, stale across three
ceremonies) now read **12,940**. Past dossiers and landing
records keep their historical shipped figures untouched —
only the current headline restates. The +2 history above and
the priced full-replay remainder stand on this record
unchanged: history is preserved, not airbrushed.

**The "total" figure:** the README carries no total; the
chain total (13,468 at the U-1 ceremony) is, per this
dossier's own finding, an increment-accumulated figure under
mixed historical conventions and is **not** reproducible from
the tree under a single stated rule. This run's whole-tree
attribute-inclusive recount under the one stated rule
(strict + same-line `@[…]`-prefixed declarations) measures
13,701 tree-wide; the counted set's share is not exactly
separable from the frozen remainder's under that rule from
surviving records. Accordingly **no total is restated as a
measured figure here**; the chain total's disposition —
recompute under one stated rule or retire, per the tightened
rule proposed above — remains the open parent/Jeff decision
it was. The strict figure is the census.

**NO CLAIM** — parts of any official Millennium statement
closed: 0. Dials: 0/4.
