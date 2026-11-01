# Bench Event Schema — Forward Instrumentation SPEC (working label)

**Status: SPEC ONLY — NOT BUILT.** This document specifies an append-only
JSONL bench-event schema for future runs. Writing it builds nothing: the
build/integration into the coordinator's wrapper and the parent ceremony is
priced M in the governing scoping memo
(`scoping-kernel-visualization-2026-11-01.md`, §6) and is a **separate
ratification** — an operations decision, not an exhibit decision. It is not
fired by the Kernel Visualization v1 ratification, and v1 neither waits for
it nor pretends to have it.

**Why it exists.** The historical record (v1's data audit, memo §1) is
check-heavy and search-light by construction: landings commit to git, but
failed attempts, abandoned routes, and in-flight revisions were recorded
only where numbered log series happened to be kept. Only with this schema
written from ratification forward do future benches acquire a true search
interior to replay.

## The schema

One JSON object per line, append-only, written by the build wrapper (attempt
events) and the parent ceremony (check events) at the moment the event
happens. No field is back-filled; a field the writer does not know is
omitted, never estimated.

```json
{
  "ts_utc": "2026-11-01T00:00:00Z",
  "brick": "SHELF-5",
  "lane": "main | side | lane-2",
  "attempt_index": 3,
  "target_module": "ThetLogos.PerronFrobenius",
  "headline_statement": "<the statement the attempt aims at, verbatim>",
  "kind": "attempt-start | attempt-end | check",
  "outcome": "compiled | compile-failed | killed:<kill-id> | partial:<seam> | probe-pass | probe-fail | check-standard-three | check-deviation",
  "jobs": 3325,
  "duration_s": 847,
  "error_kinds": ["Unknown identifier", "subscriptTerm not implemented"]
}
```

Field rules:

- `ts_utc` — UTC, written at event time by the writer's own clock. No label
  times, no later normalization: the normalization v1 had to perform on the
  historical log is exactly what this schema retires.
- `kind` / `outcome` — the closed vocabularies above, mirroring the house's
  landing vocabulary. A new outcome value is a schema amendment, recorded as
  a new entry in this document's amendment log — never an ad-hoc string.
- `jobs`, `duration_s`, `error_kinds` — recorded only where the build
  actually reports them; absence means "not reported", never zero.
- `killed:<kill-id>` carries the pre-registered kill id verbatim;
  `partial:<seam>` carries the named seam verbatim. Kills and partials are
  first-class outcomes, at the same rank as landings.
- Check events (`kind: check`) are written by the parent ceremony from the
  axiom query's actual output: `check-standard-three` only when the verdict
  is exactly [propext, Classical.choice, Quot.sound] with no sorryAx;
  anything else is `check-deviation` with the deviation in `error_kinds`.

## Fences carried from the governing memo

- The schema records **events and verdicts**, never kernel or elaborator
  interior — none exists to record (K-KV-THEATRE applies to any future
  rendering of this stream).
- The stream is a record, not a claim: NO CLAIM attaches to it; P vs NP
  parts 0. Any exhibit built on it inherits the memo's fence set in full,
  including K-KV-FILL (stream gaps are gaps).
- Appending is the only write. Corrections are new lines that name the line
  they correct; history is never rewritten.

## Amendment log

- 2026-11-01 — spec issued with Kernel Visualization v1 (working labels).
  Build NOT fired.
