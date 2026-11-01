# D1-A′ PIN LANDING DOSSIER — 2026-11-01 (gauntlet stage 1)

**Item:** the D1-A′ statement pin, stage 1 of the gauntlet fired
by Jeff's order 2026-11-01 14:59 EST, with his 15:01 EST addition
(Step 0: the COMMON HYPERCHARGE MATRIX, his coinage verbatim).
D1-A′ is a NEW ENTRY under the relabeling rule; D1-A's kill
(`dial1_forcing_killed`) stands untouched beside it.

**Status: PIN LANDED. Commonality PROVED AS STATED. The pin
asserts neither pre-check; Dial 1 stays 0.**

**Artifact:** `lean/ThetLogos/DialOneSeatTiePin.lean` — strict 8,
defs 6, zero `sorry`. Verified by the coordinator in the main
tree (build green, 3134 jobs); all theorems on exactly
`[propext, Classical.choice, Quot.sound]`.

## Step 0 — the COMMON HYPERCHARGE MATRIX (Jeff's term)

`commonHyperchargeMatrix`: the diagonal U(1)-weight operator on
ℂ³², entry at seat i = `W i + W (partner i)` from the landed
π₁ slot weights and the landed J seat-pairing; its diagonal is
proved to be `3 * hypercharge f` at each sector
(`commonHyperchargeMatrix_diag`). **Commonality:
`commonHyperchargeMatrix3 = smDirac3diag commonHyperchargeMatrix`
— PROVED.** The seated generations DO share one matrix: the
full three-generation weight operator is the one common matrix
repeated by the corpus's landed triplication. (Fence on the
face: triplication is imposed, not derived — commonality is a
fact about the corpus's seated operator.)

## The pin

`DialOneBase` (the landed D1-A clauses conjoined — no packaged
base predicate exists in `HyperchargeForcing.lean`; the
conjunction is verbatim in substance, noted on the face);
`SeatTie` (the lifted-eigenvalue at each particle seat equals
that at its J-mirror seat, in the only π-general lift-weight form
the landed forcing vocabulary owns — no weight value, no table,
no Yukawa anywhere in or upstream of the clause);
`DialOneStrengthened` := base ∧ tie; `DialOneForcing` as a Prop
— every strengthened π's lifted eigenvalues are
`exp(κ·t · (common hypercharge matrix entry) · I)` along every
unimodular direction: the forcing statement over the named
object, the matrix in the conclusion only. Kills K-D1A′-1/-2/-3
on the face.

## ⚠️ The stage-2 flag (raised by the pin builder, priced in)

The lifted-eigenvalue reading of the tie has a symmetry: for any
matrix M, the diagonal entry of `M * piOp M` at `partner i` is a
partner-reindexing of its entry at i. If that symmetry survives
the unimodular-direction specifics, **`SeatTie` as pinned may
hold for every π — including piFlip** — in which case pre-check
(b) fails, the strengthened set still admits the known
counterexample, and the gauntlet stops at the gate with the kill
reported (the fire order: re-examine posing if piFlip passes the
tie). The alternative raw-entry readings of the tie fail π₁
outright (K-D1A′-3 territory). Stage 2 (the pre-checks) is
dispatched with this flag as its first question: prove
`SeatTie pi1`, and decide `SeatTie piFlip` one way or the other —
either outcome is a full-rank verdict and the gauntlet obeys it.

## Fences

NO CLAIM — no Millennium problem is claimed solved or advanced.
A pin is not a derivation: **Dial 1 stays 0**, and moves only if
the forcing theorem lands whole with the tie proved
non-vacuous.

**Census after landing: 11,057 strict / 11,243 total / 377 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
