# Z4-KMS-0 — the ladder is the Gibbs state of a named generator

**Date:** 2026-10-30 · **Brick:** Z4-KMS-0 (S), per
`scoping-z4-toothed-kms-2026-10-30.md` §§1–2, 5–6. New module:
`ThetLogos.ThermalZ4KMS`. **Verdict: LANDED FULL** (strict 5 /
defs 1, parent-verified from disk; below the 8–14 estimate because
the cast chain went through in two helpers).

**Fences: NO CLAIM. Parts of any official statement closed: 0.
Dials: 0/4.**

## The seat and the convention

The seat is the **full algebra M₄(ℂ)** — `KMSCondition`'s
quantifiers range over all matrix pairs, off-diagonals included.
The diagonal-subalgebra seat is expressly rejected on the module's
face (K-Z4K-3 vacuity guard: there every factor commutes and the
identity collapses toward scalar trace arithmetic — the vacuity
anti-pattern in miniature).

`z4Generator := Matrix.diagonal (fun k : Fin 4 => ((k.val : ℝ)/4 : ℂ))`
— the ladder's declared input energies on the diagonal.
**Convention pinned:** KMSBridge's `gibbsWeight` carries β as a
separate scalar, so the ladder's /4 lives *inside* the generator.
The rival pairing (diagonal k, temperature β/4) is a different
statement about a different pair, named as such on the face.

## K-Z4K-1 checkpoint — PASSES; the kill does not fire

`z4_gibbsZ_eq : gibbsZ z4Generator β = ((z4Partition β : ℝ) : ℂ)`
— the two modules' normalizations agree **numeral-for-numeral**
with the pinned convention. No factor-4 fork; nothing was patched.

## Headline 1 — the identification (the brick's content)

`z4_gibbsState_eq : gibbsState z4Generator β =
  Matrix.diagonal (fun k : Fin 4 => ((z4Weight β k : ℝ) : ℂ))`

The ladder's scalar weight function **is** the Gibbs state of the
named generator, as a matrix identity over the full algebra.
Falsifiable on its face (scoping §4): a wrong generator kills it
by computation — diag(k²/4) differs at sites 2 and 3; diag(k)
(dropping the /4) is wrong at every site for β ≠ 0.

## Headline 2 — KMS at the seat, a SPECIALIZATION, labeled as such

`z4_ladder_kms : KMSCondition (diagonal z4Weight) z4Generator β`,
proved **by transport only**: `z4_gibbsState_eq ▸ gibbs_kms`.
The general Gibbs–KMS theorem is owned (`KMSBridge.gibbs_kms`,
all K, all β); re-proving it was forbidden in this brick and was
not done. The module's face says Headline 2 is a specialization
and Headline 1 is the content.

All three named results carry exactly
`[propext, Classical.choice, Quot.sound]`. Module and full-tree
builds green.

## Fences kept

The dropped file's vacuous `KMSState` is named on the module's
face as the refused anti-pattern — not imported, not built; nor
are its `InternalAlgebra` / `ModularAutomorphismGroup`. No entropy
language (T-ENT is not a dependency of this line, by design). No
bearing claimed on W1; G1/G2 untouched. Raw material for the
Q7CR line's C⁴ factor, nothing more.

**Census: 7,451 → 7,456 strict / 7,529 → 7,534
attribute-inclusive / 256 → 257 modules** (recounted from disk).

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you to
everyone reading the stream — the corpus is free for everyone,
forever.

*End of dossier.*
