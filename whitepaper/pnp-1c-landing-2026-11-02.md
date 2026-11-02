# PNP-1c LANDING DOSSIER — the K-PNP-1 witness — 2026-11-02

**Item:** PNP-1c (Millennium Lane 3) — K-PNP-1 Part B: the
time-hierarchy witness, statable or the kill fires.

## VERDICT: PART B RECEIPT LANDED — KPNP1Witness is fully formed in the pin's vocabulary; K-PNP-1 does NOT fire

**Artifact:** `lean/ThetLogos/PvsNPWitness.lean` — strict
4, defs 9. Verified by the coordinator in the main tree
(build green); all four proved contents on exactly
`[propext, Classical.choice, Quot.sound]`. PNP-1a/1b
untouched.

**The witness, as landed:** `decode` composes the pin's
two Gödel decodings (`Nat.Partrec.Code` of the unpairing's
first component; the pair-chain coefficient list →
polynomial on the second). Both are total, so `decode`
returns `some (M, p)` for every string — there are no
undecodable strings and the `none` branch is unused,
stated on the face. Acceptance is the pin's
`Nat.Partrec.Code.evaln` — **not a TM2 step count** (no
TM2 execution of `Code` exists in-pin and none is
claimed), with the bound parameter's offset disclosed on
the face; `acceptsWithin_sound` ties it to the pin's
`evaln_sound`. The diagonal language:

```
Ldiag := {x | ∀ M p, decode x = some (M, p) →
  ¬ AcceptsWithin M x (p.eval x.length)}
```

and **`KPNP1Witness : Prop := Ldiag ∉ PClass`** — fully
formed, every constituent defined, `PClass` unweakened.

**What the receipt certifies, exactly:** the pin's P is
the kind of notion a known non-polytime language can be
*stated* outside of — K-PNP-1's audit test, passed. The
Prop is STATED, not proved; the time-hierarchy theorem
behind its truth is classical (T4), fenced as such, and
is not a house theorem. With Part A's audit PASS
inherited by PNP-1a's defs, **K-PNP-1 is fully armed and
fully answered at statement grade: the PNP pin is not
vacuous.**

## Fences

NO CLAIM; **parts of P vs NP closed: 0.** The PNP board's
registered content is complete with this landing: pin
(PNP-1a/b) + witness (PNP-1c) + barrier map (PNP-2,
paper-grade, in flight).

**Census after landing: 12,566 strict / 13,057 total / 438 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
