# AXIOM DEPENDENCY GRAPH LANDING — method + artifact — 2026-11-02

Jeff's order (2026-11-01 23:04 EST, "fire 1→4"), vector 2. NO CLAIM;
dials 0/4; census unchanged (12,641 / 13,153 / 445, zero sorrys).

## What shipped

- **`lean/scripts/axiom_graph.py`** — the generator.
- **`lean/scripts/axiom-graph.json`** — the emitted graph
  (schema tag `thet-logos/axiom-graph@1`).

## Method

Two layers, collected in one pass:

1. **declaration → axioms.** The generator assembles a single Lean check
   file from the axiom-fence registry (`scripts/axiom-fence.txt`):
   registry `import` lines verbatim, then one `#print axioms` per
   registered declaration; runs it once under `lake env lean`; parses
   each declaration's reported axiom set literally (apostrophe-safe —
   the same fix the fence runner carries). Each declaration record
   names its owning module from the registry.
2. **module → modules.** Every `.lean` file under `lean/ThetLogos/` is
   parsed for `import` commands. Edges to other `ThetLogos.*` modules
   are recorded directly; external imports (Mathlib.*, etc.) are counted
   per module, not expanded. Each module also records the size of its
   transitive ThetLogos import closure.

## Verified run (2026-11-02, current tree)

- Module layer: **460 nodes, 711 internal edges**, max transitive
  closure 38 modules. (460 = the 445 counted modules plus the 15
  in-tree remainder files of the census reconciliation gap — the graph
  counts files, the census counts the verified chain; both numbers are
  stated as what they are.)
- Declaration layer: **21/21 registered declarations reported**; the
  axiom universe over all of them is exactly
  {propext, Classical.choice, Quot.sound} — every checked declaration
  carries precisely the standard three, none carries `sorryAx`.

## Limits, stated on the face

- The declaration layer covers **the fence registry only** — a named
  subset (21 headlines), not the corpus's ~13k declarations. This is
  deliberate: axiom-checking is priced per declaration run, and the
  registry is the corpus's admission-controlled headline set. Growing
  coverage = growing the registry (Order 1's admission rule), then
  re-running this generator.
- Module edges are **direct source imports** as written; they do not
  see through `import` re-exports beyond the recorded transitive
  closure sizes, and external (Mathlib) structure is counted, not
  graphed.
- `#print axioms` reports the axioms a declaration's *proof term*
  transitively depends on. It is a dependency statement, not a
  soundness certificate: the fence {propext, Classical.choice,
  Quot.sound} is the corpus's accepted basis, and this graph shows
  nothing outside it is used by the registered headlines.
