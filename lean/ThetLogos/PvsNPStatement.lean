import ThetLogos.PvsNPDefs

namespace ThetLogos

/-!
# ThetLogos.PvsNPStatement — P vs NP board statement brick (PNP-1b)

Board charter: **NO CLAIM.** Parts of P vs NP closed by this house:
**0** — now, and after this brick lands (a statement brick closes
no part of the problem). This module is the statement half of
PNP-1 (Lane 3), split per the PNP-0 audit
(`routeb-general-scratch/scoping-pnp-0-2026-11-02.md` §5): it
states the board against ONLY the frozen names of
`ThetLogos.PvsNPDefs` (PNP-1a — its names are frozen; nothing
there is renamed, extended, or edited). It proves NO inclusion,
NO equality, and NO non-equality of the classes.

## The board statement — adoption, not re-statement (RH-1 pattern)

`PvsNPBoardStatement : Prop := PeqNP` — the board's statement is
PNP-1a's landed definition, adopted. `PeqNP` is set equality
`PClass = NPClass` (PNP-0 §3.2): both directions, neither baked
in; its negation is equally statable. NO CLAIM — this definition
asserts neither the equality nor its negation.

## Direction fence — labels mirrored EXACTLY from PNP-0

The equality's two directions, labelled exactly as the PNP-0
audit puts them (§3.2, §5) and as Cook's formulation puts them
(P = NP asks whether every NP language is in P):

- **`P ⊆ NP` — the KNOWN inclusion, stated as T4 in this fence,
  NEVER as a house theorem.** It is true in the textbook theory
  (empty certificate — PNP-0 §3.2), and that is a cited textbook
  fact (T4), not a result of this house: it is UNPROVED in this
  corpus, no proof of it appears in this module or in PNP-1a,
  and it is not baked into the board statement. Baking it in —
  taking the one-way inclusion as `PeqNP` — is forbidden by the
  audit (§3.2, §6): it would hide a proof obligation inside
  the pin.
- **`NP ⊆ P` — the Clay question's direction** (Cook: whether
  every NP language is in P). This direction is classical-open:
  it is the substantive working direction any future attack
  works on, and it is named separately as `NPSubsetP` (PNP-1a).

## `NPSubsetP`'s fenced role — on the face

`NPSubsetP : Prop := ∀ L : Language Bool, L ∈ NPClass → L ∈ PClass`
is the ONE-WAY inclusion `NP ⊆ P` as a **named weaker Prop**:

- It is **NOT the board statement**, and the board statement is
  not it. The board statement is the equality `PeqNP` — both
  inclusions exhibited separately (see the unfold theorem
  below); `NPSubsetP` names only the `NP ⊆ P` direction and
  carries no `P ⊆ NP` content at all.
- Stating this Prop is not proving it: no inclusion is proved
  or asserted anywhere in this module. Its definitional unfold
  (`npSubsetP_iff_subset` below) is a statement-grade
  self-check about the *definition*, not about P vs NP.

## K-PNP-1 fence — carried forward (PNP-0 §4)

Kill condition: a pin whose polytime notion is satisfiable by
construction artifacts — every language polytime by construction
— is vacuous; kill and re-enter.

- **Part A (unit/totality audit): PASS, inherited.** PNP-1a's
  definitions are unchanged by this brick (this module only
  adopts `PeqNP` and unfolds it), so Part A's PASS — genuine
  pin step-count unit, total deciders only, both verifier
  guards present — is inherited exactly as landed in PNP-1a.
- **Part B (time-hierarchy witness statability): STILL
  CONDITIONAL on PNP-1c's D5.** The diagonal witness (`Ldiag`,
  `KPNP1Witness`, via the audit's route (ii) `Nat.Partrec.Code`
  decode) is PNP-1c's brick, not this one. **The board
  statement does NOT claim the K-test:** nothing in this module
  states or discharges Part B, and K-PNP-1 remains armed and
  conditional until PNP-1c lands the witness brick separately.

Honesty tiers in this file:
- **T1 (proved):** only the definitional / subset-antisymmetry
  unfold theorems below — about these *statements*, not about
  P vs NP.
- **T4 (cited, not proved):** `P ⊆ NP` is the known inclusion
  (textbook theory, empty certificate — PNP-0 §3.2), stated in
  the fence above only; never a house theorem.
- **Definitions (no tier):** `PvsNPBoardStatement`. A definition
  asserts nothing.
- **NO CLAIM:** P vs NP itself. Unproved here, unrefuted here,
  untouched here.
-/

/-- **The P vs NP board statement:** PNP-1a's landed `PeqNP`,
adopted verbatim as the frozen statement of this board (the
RH-1 adoption pattern — adoption, not re-statement). `PeqNP`
is set equality `PClass = NPClass`: both directions, neither
baked in. NO CLAIM — this definition pins the statement; it
proves nothing. -/
def PvsNPBoardStatement : Prop := PeqNP

/-- Pin self-check (T1, statement grade): the board statement
unfolds definitionally to the adopted landed definition
`PeqNP`. Proved by `Iff.rfl`. Asserts nothing about P vs NP. -/
theorem pvsNPBoardStatement_iff :
    PvsNPBoardStatement ↔ PeqNP :=
  Iff.rfl

/-- **The two-directions unfold** (T1, statement grade): the
board statement is exactly the conjunction of its two
inclusions, exhibited separately — `PClass ⊆ NPClass` (the
direction `P ⊆ NP`: the known inclusion, T4 in the fence above,
never a house theorem) and `NPClass ⊆ PClass` (the direction
`NP ⊆ P`: the Clay question's direction, named separately as
`NPSubsetP`).

Proof grade: **NOT `Iff.rfl`** — set equality does not unfold
definitionally to the subset conjunction, so this is proved by
the subset-antisymmetry step: forward, each inclusion is read
off the equality; reverse, `Set.Subset.antisymm` rebuilds the
equality from the two inclusions. Asserts nothing about whether
either inclusion holds. -/
theorem pvsNPBoardStatement_two_directions :
    PvsNPBoardStatement ↔ PClass ⊆ NPClass ∧ NPClass ⊆ PClass := by
  constructor
  · intro h
    have heq : PClass = NPClass := h
    exact ⟨fun _ hx => heq ▸ hx, fun _ hx => heq.symm ▸ hx⟩
  · rintro ⟨hPNP, hNPP⟩
    exact Set.Subset.antisymm hPNP hNPP

/-- Fenced-role self-check (T1, statement grade): the named
weaker Prop `NPSubsetP` unfolds definitionally to exactly the
one-way inclusion `NPClass ⊆ PClass` — the `NP ⊆ P` direction
alone. It is NOT the board statement (the board statement is
the equality, both directions; see
`pvsNPBoardStatement_two_directions`). Proved by `Iff.rfl`.
Stating this unfold proves no inclusion. -/
theorem npSubsetP_iff_subset :
    NPSubsetP ↔ NPClass ⊆ PClass :=
  Iff.rfl

end ThetLogos
