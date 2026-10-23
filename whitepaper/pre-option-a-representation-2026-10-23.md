# Pre-Option-A Representation — dossier (landed 2026-10-23)

**Module:** `lean/ThetLogos/PreOptionARepresentation.lean` (3,190 lines
as built; 106 strict theorem/lemma declarations, 9 further
attribute-line `@[simp]` theorems — 115 attribute-inclusive — 12 defs,
0 sorry/admit).
**Charter:** `whitepaper/pre-option-a-representation-scoping-2026-10-22.md`.
**Commission:** Jeff, 2026-10-22 22:06 EDT (the bounded reading of
"build all the bricks… full standard model": the buildable brick
first). **Parent verification:** in-tree targeted build exit 0 on the
shipped text; parent recount (106/115/12/0) matches the builder's;
`#print axioms` on nine headline declarations — exactly
`[propext, Classical.choice, Quot.sound]` for every one. (Cosmetic
only: `if_neg` deprecation warnings.)

## What was built

`pi0`, a block-diagonal action of the finite algebra
`AF = ℂ⊕ℍ⊕M₃(ℂ)` on the corpus's `I32 = Fin 32`, over the four
8-slot sectors: ℍ alone on H_L; ℂ alone on H_R; `λ̄•q̄` / `q̄⊗m` on
H_L^c; and on H_R^c, `λ̄` on the singlets and **`m` alone** on the
right antiquarks — pure color, naked.

## Verdicts (per-target, as pre-registered)

- **T1 — PARTIAL, obstruction proved (T1).** Proved: `pi0_one`,
  `pi0_afMul`, `pi0_zero`, `pi0_afStar`, grading-evenness vs `gammaF`
  — π₀ is a representation of AF's multiplicative structure, the same
  species as the corpus's own `pi`. **Additivity fails**
  (`pi0_not_additive`, failure pinpointed in the bilinear antilepton
  block) and is *proved incompatible* with the hypercharge seat:
  `additive_rep_u1_eL_trivial` — in **any** additive algebra
  representation of the direct-sum algebra with ℍ acting as full `q`
  on the doublets, summand-annihilation forces the ℂ-U(1) to act as
  identity at the e_L particle entry. The seat can only be occupied
  by a multiplicative (group) representation. **Order-zero w.r.t.
  `piOp` FAILS** (`pi0_order_zero_fails`, explicit counterexample,
  entries `i` vs `−i`); first-order not attempted (it presupposes
  order-zero); the OrderOne machinery does not port.
- **T2 — STANDS (T1).** `pi0_ker_iff : pi0 a = 0 ↔ a = afZero`;
  π₀ injective. Pure color acts nontrivially
  (`pi0_pure_color_entry`: the right-antiquark block of `pi0 ⟨0,0,m⟩`
  is `m` itself) — the exact contrast with Option A's
  `pi_pure_color_zero`.
- **T3 — STANDS in sector form, forced exception proved (T1).** On
  the e_L sector slots {1, 17}, `pi0 ⟨λ,1,1⟩ = diag(1, λ̄)` —
  nontrivial; Option A's triviality on all of I32 is gone. The
  particle entry stays 1, provably unavoidable for additive reps
  (and π₀'s charge reaches the sector through its antiparticle half).
- **T4 — STANDS in the stated form (T1 over a T2 input).**
  `pi0_det_unimodular`: `det (pi0 (u1Param t)) = 1` — the diagonal
  weight sum `−4·3 + 12·1 = 0`, so the unimodularity condition
  *selects* the direction α = 3β rather than fitting it.
  `pi0_hypercharge_pattern`: at every one-generation sector slot, the
  lifted gauge action `pi0 u * piOp (pi0 u)` has eigenvalue exactly
  `exp (3 · t · i · Y f)` — the ratios are the table's, with **one**
  overall normalization (3, forced), and **no sector deviates**.
  Face disclosure (module §8 + K-PA2): the statement imports the T2
  table `SMFermions.hypercharge` at sector level; what is proved is
  (π₀ + unimodularity) ⇒ ratios. The table is not derived from
  nothing, and this dossier does not say otherwise.

**Kill criterion: not triggered.**

## What moves in the record

SM-Match Track 1 ("Full finite gauge algebra") was **PARTIAL** on two
named obstructions: Option A's kernel is exactly pure color, and its
represented U(1) is not hypercharge. After this landing:

- The **faithfulness obstruction is discharged — by a different
  construction**, not by repairing π: a faithful action of the full
  AF exists on the same Hilbert space (π₀), with pure color naked.
- The **hypercharge-seat obstruction is discharged in implication
  form**: a surviving U(1) whose sector eigenvalue ratios are
  exactly the SM hypercharge ratios exists, with the normalization
  fixed by unimodularity — at the price, now *proved* unavoidable,
  that the representing map is multiplicative, not additive.
- **New obstructions, proved, take their place on the ledger:**
  additivity-vs-hypercharge incompatibility (a theorem about every
  additive rep, not a defect of this one), and order-zero failure
  for π₀ w.r.t. `piOp` — so π₀ does not carry the corpus's
  first-order/fluctuation machinery. Which representation a future
  full spectral-triple assembly uses, and at what price, is now a
  question with both sides proved.

**Track 1 therefore remains PARTIAL** — narrowed, repriced, and with
its remaining content stated exactly: no single representation in the
corpus yet carries faithfulness + hypercharge ratios + additivity +
order-zero/first-order together, and the first two pairs are now
proved to be in tension for structural reasons. An addendum pointing
here is appended to `whitepaper/sm-match-2026-10-11.md`.

## Fences held

K-PA1 (finite representation theory only; manifold factor and
continuum untouched — Stage 3c/4 unmoved), K-PA2 (hypercharge values
T2-cited; masses, couplings, triplication untouched inputs; the
Standard Model is not derived), K-PA3 (no other landed verdict
changed by this file; Track 1's update is recorded in this dossier
alone).

## Census

Program: **3,738 strict / 3,787 attribute-inclusive, 133 counted
modules** (was 3,632 / 3,672 / 132).
