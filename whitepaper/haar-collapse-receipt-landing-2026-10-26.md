# Collapse Receipt — Ledger Item 8 Is Item 7

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/HaarAvgKernelReceipt.lean` (strict 5, defs 1, zero
`sorry`, zero `native_decide`; main-tree build green, 3,442 jobs,
parent-verified on the shipped text). **Parts of the Clay
Yang–Mills statement closed by this landing: 0.***

## What this landing is — and is not

This receipt adds **no theorems about the world** — only an
identification, made machine-visible so no future session re-fires
it as a separate object.

The Curiosity Ledger carried two lines: item 7, the
*plane-averaged kernel*, and item 8, the *Haar-averaged OS kernel*,
described in identical words ("the third, uncomputed object"). The
item-8 scoping (routeb-general-scratch/haar-kernel-scoping-2026-10-26)
traced both to the seat-kernel gate dossier's own sentence: the OS
form's plane links are "Haar-averaged by the Gibbs measure," so its
effective kernel is "a third object (the plane-averaged kernel)."
No source gives the Haar phrase a distinct formula, group action,
domain, or question. The genuine group-twirl objects of the corpus
(`averagingOperator`, `haarTwirl`, `twirlEndo`) are different-typed
and are *not* identified with K̄ anywhere.

## The receipt

`haarAvgKernel` is defined as a definitional alias of
`planeAvgKernel` (`haarAvgKernel_eq_planeAvgKernel`, by `rfl`), and
the landed results are transported under the alias:
`osForm_eq_haarAvgKernel` (the reduction identity),
`haarAvgKernel_symm`, `haarAvgKernel_zero` (K̄₀ ≡ 1),
`haarAvgKernel_circle_pairing_nonneg` (the U(1) seat). All five
theorems' axiom sets: exactly `[propext, Classical.choice,
Quot.sound]`. The scoping's KILL-separateness check ran: the alias
is faithful to every use the record makes of the "Haar" phrase.

**Item 8 closes as COLLAPSED into item 7.** General-(G, ρ)
positivity remains L+/open, untouched by this receipt.

## Census effect

Strict 5,870 → **5,875**; attribute-inclusive 5,937 → **5,942**;
modules 194 → **195**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
