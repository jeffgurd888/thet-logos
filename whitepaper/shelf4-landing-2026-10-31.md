# SHELF-4 — LANDED: partial trace stocked; the Schrödinger-gauntlet fence retired

**Date:** 2026-10-31 · **Fill:** SHELF-4 (S–M), first fill
of Jeff's "fill the shelf" commission (2026-10-30 23:20
EDT), per `scoping-shelf-map-2026-10-30.md` §4.
Module: `ThetLogos.PartialTrace`. **Verdict: LANDED**
(strict 24 / defs 4, parent-verified from disk; main-tree
build green; trace preservation and the Kronecker
factorization on exactly [propext, Classical.choice,
Quot.sound]). The pin re-check ran first: the pin owns no
partial trace (grep-certified under its possible names),
so the fill did not strike.

**Fences: NO CLAIM. Dials: 0/4.** General-API stock —
this landing proves nothing about any corpus line's
results; it retires an absence. No entropy is defined or
named (purity is not entropy; the T-ENT gate stands).

## The fence retired (named, per the commission)

`whitepaper/gauntlet-schrodinger-2026-10-16.md`: "What
does not exist: **partial trace** — zero hits in Mathlib,
zero in the corpus — and no channel/purity vocabulary
anywhere." **Retired as of this landing** — with one precision,
added as an addendum the same night (the builder's
report surfaced it after the landing commit): the corpus
was no longer at zero when this fill landed —
`ThetLogos/DecoherenceToy.lean` carries a seat-specific,
one-direction block trace `partialTraceB` with its own
small package, built for the dephasing toy after the
2026-10-16 fence was written. What this fill retires is
the **general-API absence** the fence named: both
directions, general finite index types, and the purity
vocabulary as standalone stock (none of which
DecoherenceToy has). The new module states exactly this
on its own face.

## What is stocked

- `partialTraceRight` / `partialTraceLeft`: trace out
  one factor of a matrix on `Matrix (ι × κ) (ι × κ) ℂ`,
  as explicit entry sums — no new machinery, imports no
  corpus module.
- First properties, proved: entry formulas, zero/add/smul
  (linearity), **trace preservation**
  (`trace (partialTraceRight M) = trace M`, both sides),
  adjoint compatibility (both sides).
- Factorization over product states, in the tree's
  Kronecker idiom: `partialTraceRight (kronecker A B)
  = (trace B) • A` (and its Left twin), with the
  trace-one corollary — the reduced state of a product
  state is the factor.
- `purity`: named plainly as the complex trace of the
  square, with its Hermitian real-valued form — the
  channel/purity vocabulary the fence named, at finite
  level.

**Census: 8,454 → 8,478 strict / 8,532 → 8,556
attribute-inclusive / 289 modules** (recounted from disk).

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you to
everyone reading the stream — the corpus is free for everyone,
forever.

*End of dossier.*
