# U-3b ABSTRACT FINITE-INVOLUTION THEOREM — LANDING (2026-11-04)

## VERDICT: FULL

The abstract master, the product clause, and BOTH corollary
wirings landed. **Master:** for any type `A`, any map
`σ : A → A`, and a representative system given as data,
`fixedFunctions_equiv_reps : {f : A → ℝ // ∀ x, f (σ x) = f x} ≃
(R → ℝ)`. **Product clause:** `fixedFunctions_prod_equiv_reps` —
jointly fixed functions on `A × B` ≃ `((R × S) → ℝ)` from the
product representative data. **Corollaries:** (i)
`MirrorTwentyOneAlgebra.fixedEquivReps` re-derived from the
master at `A = Fin 21` (`mirror_fixedEquivReps_master`, plus the
seat's own `thetaHat` form `mirror_fixedEquivReps_thetaHat`);
(ii) the joint case re-derived via the product clause
(`joint_fixedEquivReps_master`, plus the seat's own arm form
`joint_fixedEquivReps_thetaHat`). Original modules untouched.
**K-U3-REP did NOT fire** (audit below). **NO CLAIM; dials 0/4.**

Module: `lean/ThetLogos/InvolutionFixedFunctions.lean` —
**strict 18 theorems + 11 defs + 1 structure** (`RepSystem`),
zero sorrys, no `native_decide`. Targeted build green
(802 jobs), module warning-clean (forced rebuild: zero
warnings/errors attributable to the module). Lane: worktree
`~/workspace/thet-logos-u3b`, branch `u3b-lane`, cut from main
HEAD `699b926` (Universal Bridge integration — one integration
past the brief's stated base `5050bb2`; census at cut
13,164 strict / 482 modules, re-derived from that commit's
message). Not integrated, not pushed — lane commit only;
parent integration re-bases.

## The rep system, stated exactly

`RepSystem {A R : Type*} (σ : A → A)` is a structure with two
data fields and three axiom fields, all pointwise statements
about points of `A` and `R` — none quantifies over functions:

- data: `repOf : A → R`, `repEmbed : R → A`;
- (R1) `repOf_repEmbed : ∀ r, repOf (repEmbed r) = r`;
- (R2) `repOf_invol : ∀ x, repOf (σ x) = repOf x`;
- (R3) `repEmbed_repOf : ∀ x, repEmbed (repOf x) = x ∨
  repEmbed (repOf x) = σ x`.

That is exactly what the proof consumes, and no more. Two
honesty notes at full rank:

1. **Neither `Function.Involutive σ` nor `Fintype A` is
   assumed anywhere in the master or the product clause** —
   the equiv needs neither. (The brief's target quantified
   over a finite type with an involution; the landed theorem
   is strictly more general, and says so. The concrete
   instance does supply involutivity separately:
   `mirrorInvolution_involutive`.) Finiteness is what the
   *instances* use to exhibit rep systems, not what the
   master uses to consume them.
2. Each axiom is used exactly where expected: (R2) makes the
   extension `g ∘ repOf` fixed; (R1) makes restriction ∘
   extension the identity; (R3) + fixedness makes extension ∘
   restriction the identity.

## K-U3-REP audit — DID NOT FIRE

The pre-registered kill fires if the rep axioms smuggle the
conclusion (rep system effectively a section of the
fixed-function quotient / axioms equivalent to the equiv
itself). Audit: (R1)–(R3) mention only `repOf`, `repEmbed`,
`σ`, and equality in `A`/`R`. They are checkable
point-by-point for any proposed instance without reference
to any function space — and at the Mirror instance they are
discharged by `MirrorTwentyOneAlgebra`'s pre-existing lemmas
(`repOf_repEmbed`, `repOf_involution`, `repEmbed_repOf`),
proved there by `Fin 21` arithmetic in 2026-11-02, before
this abstraction existed. The conclusion, by contrast,
quantifies over all functions `A → ℝ`. A rep system is a
section of the *point* quotient `A → A/σ`, which is the
honest combinatorial content of "orbit representatives";
it is not a section of the fixed-function quotient. The
abstraction is not a costume. **K-U3-REP: armed, tested,
did not fire.**

## Product clause — the one shaping decision, on the face

The product representative data (`prodRepOf`, `prodRepEmbed`,
coordinatewise) is **not** a `RepSystem` for the diagonal
involution `Prod.map σ τ`, and is not claimed to be: axiom
(R3) fails for it in the mixed cases (first coordinate
mirrored, second not — the embedded representative pair is
then neither the point nor its diagonal mirror). What
*is* proved:

- product (R1) `prodRepOf_prodRepEmbed`, product (R2) in
  each coordinate (`prodRepOf_fst_invol`, `prodRepOf_snd_invol`),
  and product (R3) as a conjunction of coordinatewise
  disjunctions (`prodRepEmbed_prodRepOf`);
- the equiv for the **two-arm joint fixedness** — fixed
  under `(σ ·, ·)` and under `(·, τ ·)` separately —
  which absorbs the four (R3) cases one coordinate at a
  time (`jointlyFixed_apply_prodRepEmbed_prodRepOf`).

This is exactly the joint notion `MirrorTwentyOneOrthogonal`
uses (`thetaHat₁ f = f ∧ thetaHat₂ f = f`), so the seat is an
instance of the clause as stated. Diagonal-only fixedness on
`A × B` is a different, larger function space in general
(its dimension counts diagonal orbits, not representative
pairs) and is **not** asserted anywhere in this brick.

## Corollary wiring

All by addition — no statement in `MirrorTwentyOneAlgebra`
or `MirrorTwentyOneOrthogonal` was edited, renamed, or
re-proved; their frozen statements stand untouched, and the
equivs below have (up to the fixedness-predicate transport)
the seats' own types:

- **Instance discharge, zero new `Fin` work:**
  `mirrorRepSystem : RepSystem involution` at
  `A = ManifoldIndex`, `R = Fin 11`, fields filled verbatim
  by the seats' lemmas named above. The brief's contingency
  ("if an instance resists, land PARTIAL") did not arise.
- (i) `mirror_fixedEquivReps_master :=
  fixedFunctions_equiv_reps mirrorRepSystem`;
  `mirror_fixedEquivReps_thetaHat` transports the subtype
  along `thetaHat_fixed_iff` (`Equiv.subtypeEquivRight`) to
  the exact type of `fixedEquivReps`; bijectivity re-derived
  (`mirror_fixedEquivReps_thetaHat_bijective`, the master
  form of `fixedEquivReps_bijective`).
- (ii) `joint_fixedEquivReps_master :=
  fixedFunctions_prod_equiv_reps mirrorRepSystem
  mirrorRepSystem`; `joint_fixedEquivReps_thetaHat`
  transports along `thetaHat₁_fixed_iff` /
  `thetaHat₂_fixed_iff` to the exact type of
  `jointlyFixedEquivReps`; bijectivity re-derived
  (`joint_fixedEquivReps_thetaHat_bijective`).

## Axiom audit (`#print axioms`, exact sets)

- All master/product headlines and both transported
  corollaries: exactly `{propext, Classical.choice,
  Quot.sound}`.
- `mirrorInvolution_involutive`, `mirrorRepSystem`:
  `{propext, Quot.sound}`.
- `prodRepOf_prodRepEmbed`, `prodRepOf_fst_invol`,
  `prodRepOf_snd_invol`, `prodRepEmbed_prodRepOf`:
  **no axioms at all**.
- No `sorryAx` anywhere; no headline exceeds the standard
  trio.

## Declaration inventory (measured)

Theorems (strict, 18): `RepSystem.extendRep_fixed`,
`RepSystem.extendRep_repEmbed`,
`RepSystem.fixed_apply_repEmbed_repOf`,
`fixedFunctions_equiv_reps_bijective`,
`fixedFunctions_equiv_reps_apply`,
`fixedFunctions_equiv_reps_symm_apply`,
`prodRepOf_prodRepEmbed`, `prodRepOf_fst_invol`,
`prodRepOf_snd_invol`, `prodRepEmbed_prodRepOf`,
`prodExtendRep_fst_fixed`, `prodExtendRep_snd_fixed`,
`prodExtendRep_prodRepEmbed`,
`jointlyFixed_apply_prodRepEmbed_prodRepOf`,
`fixedFunctions_prod_equiv_reps_bijective`,
`mirrorInvolution_involutive`,
`mirror_fixedEquivReps_thetaHat_bijective`,
`joint_fixedEquivReps_thetaHat_bijective`.
Defs (11): `RepSystem.extendRep`, `fixedFunctions_equiv_reps`
(the master), `prodRepOf`, `prodRepEmbed`, `prodExtendRep`,
`fixedFunctions_prod_equiv_reps` (the product clause),
`mirrorRepSystem`, `mirror_fixedEquivReps_master`,
`mirror_fixedEquivReps_thetaHat`, `joint_fixedEquivReps_master`,
`joint_fixedEquivReps_thetaHat`.
Structure (1): `RepSystem`. Total 30 declarations, inside the
priced band (M, est. strict 15–35).

## What did NOT land / fences (unchanged)

- **Honesty fence (scoping §1.2) kept explicit:** the
  fixed-function count `(n+1)/2 = 11` under negation and the
  Laplacian kernel dimension `1` on a connected web are
  different theorems (orbit representatives vs zero modes).
  This brick is entirely about the first; it neither proves
  nor touches the second.
- U-3a (CRT transport / odd-n mirror organization) is a
  separate brick, already landed on its own lane; nothing
  here depends on it or re-states it.
- TR-4 strata untouched and unclaimed.
- §4 fence: nothing here touches the analytic line
  (LayerKernelPos / FACT / GATE-3 / W3), SHELF-8B, BSD, or
  Hodge; no measured number is derived, no gravity object
  appears, no continuum limit is proved, nothing external is
  predicted.

**NO CLAIM. Dials 0/4.**

## INTEGRATION (main tree, 2026-11-04)

Integrated from u3b-lane commit `8d62be2` onto main-tree HEAD
`3ae9e54` (lane base `699b926`; module + dossier new files).
Module and dossier copied **byte-identical** (md5-verified:
module `60ff925821426b7c0945ac94411a80b7`, dossier at copy
`26e83b6f6332ef5b0226ccd2d3991249`). Declaration-level
collision scan of all 30 InvolutionFixedFunctions names plus
the 5 `RepSystem` projections (`repOf`, `repEmbed`,
`repOf_repEmbed`, `repOf_invol`, `repEmbed_repOf`) against
the **current** main tree: **zero collisions** (re-scanned at
integration, not only at the lane base; MirrorTwentyOneAlgebra's
top-level `repOf`/`repEmbed`/`repOf_repEmbed`/`repEmbed_repOf`
are `ThetLogos`-level names, distinct from the
`ThetLogos.RepSystem.*` projections). Main-tree targeted build
green (**802 jobs**, matching the lane), zero sorrys
(zero-sorry gate PASS, 500 files), module **warning-clean**
(fresh main-tree compile emitted no warnings). Recount:
module **18 strict + 11 defs + 1 structure** exact; census
files-true (whole-tree 13,876/500 minus frozen remainder
669/15): 13,189/484 → **13,207 strict / 485 modules**;
README prose + badge both 13,207/485, kept equal. Fence: the
23 declarations named in this dossier's axiom audit — all 18
strict theorems, the master `fixedFunctions_equiv_reps`, the
product clause `fixedFunctions_prod_equiv_reps`, both
transported corollaries, and `mirrorRepSystem` — admitted
WITH the `import ThetLogos.InvolutionFixedFunctions` line in
the same commit as the module — **FENCE PASS 245/245**,
axiom sets exactly as audited above (headlines + transported
corollaries on {propext, Classical.choice, Quot.sound};
`mirrorRepSystem`/`mirrorInvolution_involutive` on
{propext, Quot.sound}; the four product-data lemmas on no
axioms), no sorryAx. Ledger record
`u3b-involution-fixed-functions` (standing, T3, kill_id
null — K-U3-REP did not fire), validator **PASS**
(31 records).

**VERDICT CARRIED AT FULL RANK: FULL — K-U3-REP DID NOT
FIRE.** The master consumes exactly (R1)–(R3) and assumes
neither `Function.Involutive σ` nor `Fintype A`; the product
clause is the two-arm joint fixedness only, the product data
not claimed as a `RepSystem` for the diagonal involution;
the fixed-dimension `(n+1)/2` ≠ kernel-dimension `1` fence
stands explicit. **NO CLAIM; dials 0/4.**
