---
name: External review
about: Report an outside check of this corpus — a verification run, a statement-fidelity finding, a priority find, or a failure to reproduce. Every received review is logged verbatim in EXTERNAL-REVIEWS.md and answered in the open.
title: "[External review] "
labels: external-review
---

<!-- Thank you for checking this work. The proofs in this repo are
machine-checked; what a kernel cannot judge is whether a proved
statement says what the prose claims it says. That is the review
this template is for — but verification failures and priority finds
are equally welcome. REVIEW.md lists the load-bearing claims and
where we would press them. -->

## What was checked

<!-- The claim, theorem, or published figure you examined. If it is
a REVIEW.md row, give the row number. Give the theorem name and
file path where one exists. -->

## Method

<!-- How you checked it: read the statement, ran
scripts/verify-external.sh (say whether --fence), rebuilt from a
clean clone, compared against a primary source, other. Include
the commit hash you checked against, if you have it. -->

## Verdict

<!-- One of:
  CONFIRMS — the statement says what the claim says / the figure reproduces.
  FIDELITY FAILURE — the proved statement and the published claim come apart (say where).
  PRIORITY — the result, or a load-bearing piece of it, exists earlier elsewhere (cite it).
  CANNOT REPRODUCE — a mechanical check failed on your machine (attach the verdict sheet).
  OTHER — say what. -->

## Evidence

<!-- Links, command output, verdict-sheet lines, quotations of the
statement as written. Enough for a third party to re-run your
check without taking your word for it. -->

## Permission to quote

<!-- This review will be logged verbatim in EXTERNAL-REVIEWS.md
with its date and source, and answered there. -->

- [ ] You may quote this review verbatim in EXTERNAL-REVIEWS.md and the epistemic ledger.
- [ ] Quote with attribution to the name/handle below.
- [ ] Do not quote; summarize only.

Name / handle (optional):
