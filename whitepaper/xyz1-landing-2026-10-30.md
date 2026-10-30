# XYZ-1 — K-XYZ-2 FIRED: the named pool of sixteen is dead; the question is not

**Date:** 2026-10-30 · **Brick:** XYZ-1 (S–M, named-pool
family kill), per `scoping-xyz-tripotents-2026-10-30.md`
§4. Module: `ThetLogos.XYZPoolKill`. **Verdict: LANDED —
the family kill is a theorem** (strict 12 / defs 2,
parent-verified from disk; module build green;
`namedPool_kill` on exactly [propext, Classical.choice,
Quot.sound]).

**Fences: NO CLAIM. Parts of any official statement closed: 0.
Dials: 0/4.** This is **K-XYZ-2, a FAMILY kill**: the
named pool is dead; **the question `xyz_tripotents_exist`
stays OPEN** — nothing here answers it NO, and the module
says so in exactly those terms. This is an exact invariant
argument (rubric rule R5), not a search: "failure to find
is not a kill" does not apply, and the header says why.

## What landed

- **The pool as data** (`namedPool`, length 16 proved):
  {1, cfMat, 1 − cfMat, gammaF, UJ, genC} ∪ {genH k} ∪
  {genM a : a ≠ 7} — every tripotent the corpus has named
  as a candidate ingredient.
- **Every pool entry is a Gaussian integer**
  (`inPool_gaussInt`): the landed facts for UJ and genH
  consumed directly; new entry facts for cfMat,
  1 − cfMat, gammaF, genC, and genM a (a ≠ 7) — the
  a ≠ 7 hypothesis consumed exactly at the λ₈ diagonal,
  where the 1/√3 entry lives.
- **The uniform kill**: `namedPool_no_xyz` (any triple
  drawn from the pool fails the generation condition at
  g = 11, by the landed R5 theorem
  `no_gaussInt_triple_reaches_genM7`) and `namedPool_kill`
  — the pool-restricted negation of the posted existence
  statement, a new entry beside the post; the post itself
  is untouched.

The named-pool chapter is therefore CLOSED, not merely
losing: no triple of the sixteen named tripotents can
generate the twelve generators, because all sixteen are
ℤ[i]-valued and ℤ[i]-valued triples provably miss
genM 7. What remains open is everything the pool is not —
tripotents with entries outside ℤ[i], starting at the
1/√3 boundary that `genM 7` itself marks. XYZ-2 builds
the boundary marker (one explicit such tripotent);
XYZ-3 runs the first live families across it.

**Census: 8,230 → 8,242 strict / 8,308 → 8,320
attribute-inclusive / 283 modules** (recounted from disk).

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you to
everyone reading the stream — the corpus is free for everyone,
forever.

*End of dossier.*
