# MIRROR-21 — scoping and landing dossier

**Date:** 2026-11-02 (lane work ~20:15–21:00 EST)
**Commission:** Jeff, 2026-11-02 20:09 EST — "report it scope it build it run it"
**Origin:** a Lean + Python sketch Jeff dropped the same evening (a "21-element
involution algebra" plus a "heat-kernel asymptotics" engine with a central
zero-mode), audited by the parent before this lane opened.
**Lane:** isolated worktree `~/workspace/thet-logos-mirror21`, branch
`mirror-21-lane`, from master `821cf01`. No commit, no push, no post from this
lane — the landing ceremony (independent count, main-tree build, axiom check,
fence admission, push) is the parent's.

**NO CLAIM** — parts of any official Millennium statement closed by this
work: 0. **Dials: 0/4.** This is a finite, elementary cabinet object. It
connects to nothing on the Yang–Mills ladder and is not evidence for or
against any open gate.

---

## 1. Scope, as commissioned

The parent audit of the dropped sketch returned HOLD, on three findings:

1. **The Lean did not compile.** Both of its lemmas fail at the `ext` tactic
   ("No applicable extensionality theorem found for type ManifoldIndex" —
   the plain `def` alias hides `Fin`'s extensionality lemma).
2. **The "algebra" was a shell.** `CentralInvolutionAlgebra` defines no
   multiplication anywhere; its two axioms are structure fields (assumed,
   not derived); its `involution_map` is never tied to the `Fin 21`
   involution; no instance exists. "21-dimensional" was a title, not a
   result: `basis` is a bare function into an arbitrary ring.
3. **The Python's zero-mode was inserted, not derived** —
   `eigenvalues[10] = 0.0` overwrote the middle of the *sorted* spectrum of
   a random matrix — and its headline readout, "effective spectral
   dimension 0.0622", is a finite-matrix artifact of fitting a continuum
   asymptotic to a finite trace (see §5).

The commissioned scope was the honest version of the same idea, in four
bricks with frozen module names:

| Brick | Artifact | Content |
|---|---|---|
| 1 | `lean/ThetLogos/MirrorTwentyOne.lean` | `Fin 21`, center, mirror involution Θ, involutive + center-fixed + fixed-**unique** |
| 2 | `lean/ThetLogos/MirrorTwentyOneAlgebra.lean` | the real algebra: functions `Fin 21 → ℝ` (Pi ring), pullback Θ̂ as ring automorphism, fixed-function characterization; stretch: 11 degrees of freedom |
| 3 | `python/mirror21_heat.py` | cycle-graph Laplacian C₂₁, Θ-symmetry verified, zero-mode count derived, Laplacian heat trace, polynomial small-t coefficients, artifact line |
| 4 | this dossier | report |

## 2. What landed, per brick

### Brick 1 — `MirrorTwentyOne.lean` — FULL (T1)

Definitions (3): `ManifoldIndex := Fin 21`; `TethCenter := ⟨0, _⟩`;
`involution i := ⟨(21 - i.val) % 21, _⟩` (the dropped closed form of
`Θ i = -i (mod 21)`, kept verbatim).

Theorems (strict 4):

| Declaration | Statement | Axioms |
|---|---|---|
| `involution_val` | `(involution i).val = (21 - i.val) % 21` | none |
| `involution_involutive` | `involution (involution i) = i` | propext, Quot.sound |
| `involution_center_fixed` | `involution TethCenter = TethCenter` | none |
| `involution_fixed_unique` | `involution i = i → i = TethCenter` | propext, Quot.sound |

The uniqueness theorem was **not in the dropped sketch** — the sketch never
stated it. It is true because 21 is odd (`2i ≡ 0 (mod 21)` forces `i = 0`),
and it is the mathematical heart of the line: Θ pairs the other 20 points
into 10 mirror pairs and leaves exactly one point unpaired. Proof pattern:
`Fin.ext` + explicit arithmetic form + `omega` (the repair the parent
kernel-checked in scratch before the lane opened).

Targeted build (`lake build ThetLogos.MirrorTwentyOne`): **green,
warning-clean**. Strict count: **4** (defs 3). Zero sorrys.

### Brick 2 — `MirrorTwentyOneAlgebra.lean` — FULL, stretch included (T1)

The algebra is the function ring `Fin 21 → ℝ` with the pointwise (Pi) ring
structure — an actual algebra with actual multiplication, which is what the
sketch's class named but never built. The pullback `thetaHat f i = f (Θ i)`:

Theorems (strict 15), all axiom-checked (§3):

- `thetaHat_involutive` — Θ̂ is an involution on functions.
- `thetaHat_mul`, `thetaHat_add`, `thetaHat_zero`, `thetaHat_one` — Θ̂
  preserves `*`, `+`, `0`, `1` (pointwise; each by `rfl`).
- `thetaEquiv` (def) — Θ̂ packaged as a `RingEquiv`
  `(ManifoldIndex → ℝ) ≃+* (ManifoldIndex → ℝ)`, self-inverse;
  `thetaEquiv_apply` — its underlying map is `thetaHat`.
- `thetaHat_center` — Θ̂ fixes the value at the center.
- `thetaHat_fixed_iff` — **characterization:** `thetaHat f = f ↔
  ∀ i, f (involution i) = f i`.

Stretch — **landed FULL, not partial:** the fixed functions are exactly the
functions determined by their values on the 11 representatives
`{0, …, 10}` (10 mirror pairs + the unique center = 11 degrees of freedom):

- `repEmbed` (def) — embed `Fin 11` into the 21 points;
  `repEmbed_val`.
- `repOf` (def) — the representative index of a point (its own index if
  ≤ 10, else its mirror's); `repOf_val`.
- `repOf_involution` — a point and its mirror share a representative.
- `repOf_repEmbed` — the representative of a representative is itself.
- `repEmbed_repOf` — an embedded representative of a point is the point or
  its mirror.
- `extendReps` (def) + `thetaHat_extendReps` — mirror-symmetric extension
  of arbitrary representative values is Θ̂-fixed.
- `fixedEquivReps` (def) — the equivalence
  `{f : ManifoldIndex → ℝ // thetaHat f = f} ≃ (Fin 11 → ℝ)`;
  `fixedEquivReps_bijective` — restriction to representatives is bijective.

Targeted build: **green, warning-clean**. Strict count: **15** (defs 6).
Zero sorrys.

### Brick 3 — `python/mirror21_heat.py` — RAN (T2)

Builds the cycle-graph Laplacian `L = 2I − S − S⁻¹` of C₂₁ on Z₂₁,
verifies programmatically that L commutes with Θ's permutation matrix,
computes the spectrum, **counts** the zero modes from that spectrum
(exactly 1 — derived, not inserted), reports the Laplacian heat trace
`K(t) = Tr exp(−tL)` (labeled as such; not dressed as a D² trace), and
takes the small-t coefficients from the exact polynomial form
`K(t) = Σⱼ (−t)ʲ Tr(Lʲ)/j!`, not from any log-log dimensional fit. Full
output verbatim in §4.

### Brick 4 — this dossier.

**Lane totals: strict 19 (4 + 15), defs 9, 2 modules, zero sorrys.**
Lane-side census arithmetic for the parent's ceremony (to be re-derived
there, not shipped from here): 12,750 + 19 = 12,769 strict; 460 + 2 = 462
modules, if integrated as-is.

## 3. Axiom check results

Method: `#print axioms` under `lake env lean` in the lane, on every
theorem in both modules (19 declarations). The fence is
{propext, Classical.choice, Quot.sound}; `sorryAx` or anything outside it
fails.

- Brick 1: involutive, fixed-unique → [propext, Quot.sound];
  center-fixed, val → **no axioms**. All ⊆ fence. PASS.
- Brick 2: thetaHat_involutive, thetaHat_mul, thetaHat_add, thetaHat_zero,
  thetaHat_one, thetaEquiv_apply, thetaHat_center, thetaHat_fixed_iff,
  thetaHat_extendReps, fixedEquivReps_bijective →
  [propext, Classical.choice, Quot.sound] exactly; repOf_val,
  repOf_involution, repOf_repEmbed, repEmbed_repOf → [propext, Quot.sound];
  repEmbed_val → **no axioms**. All ⊆ fence. PASS.
- No `sorryAx` anywhere; the word `sorry` occurs 0 times in both files.

Candidate fence-registry headlines for the parent's admission decision
(NOT registered by this lane): `ThetLogos.involution_fixed_unique`,
`ThetLogos.thetaHat_fixed_iff`, `ThetLogos.fixedEquivReps_bijective`.

## 4. Python results, verbatim

```
========================================================================
MIRROR-21 — cycle Laplacian C_21, honest numerics (T2)
Companion to ThetLogos.MirrorTwentyOne{,Algebra}.lean (T1).
This script illustrates the finite object; it proves nothing.
========================================================================
Theta permutation is an involution:   max |P^2 - I|   = 0.000e+00
L commutes with Theta (mirror symm.): max |PL - LP|   = 0.000e+00
Spectrum vs analytic 2-2cos(2 pi k/21): max abs err   = 1.554e-15

Zero modes DERIVED from the spectrum (lambda < 1e-10): 1
  (exactly 1: the constant functions — counted, not inserted)
Degeneracy profile of the spectrum: [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  (1 simple + 10 doublets: 10 mirror pairs + the unique center)
Spectral gap lambda_1 = 0.088854   (exact 4 sin^2(pi/21) = 0.088854)

Laplacian heat trace K(t) = Tr exp(-tL)   [NOT a D^2 trace]
  K( 0.001) = 20.958063
  K(  0.01) = 20.586231
  K(   0.1) = 17.365710
  K(   0.5) = 9.780952
  K(   1.0) = 6.478675
  K(   5.0) = 2.684500

Small-t expansion from the polynomial form K(t) = sum_j (-t)^j Tr(L^j)/j!:
  a_0        = Tr I     = 21.0
  t^1 coeff  = -Tr L    = -42.0
  t^2 coeff  = Tr(L^2)/2 = 63.0   (Tr L^2 = 126.0)
  t^3 coeff  = -Tr(L^3)/6 = -70.0   (Tr L^3 = 420.0)
  Series vs direct K(0.01): abs err = 6.081e-07

ARTIFACT NOTE (on the record): the dropped sketch reported an
'effective spectral dimension' of 0.0622 from a log-log fit of
K(t) at small t. For ANY finite matrix, K(t) -> dim (here 21) as
t -> 0, so the log-log slope -> 0 and the 'dimension' -> 0 no
matter what the operator is: the readout measured finiteness,
not dimension. The (4 pi t)^(-d/2) Seeley-DeWitt prefactor it
imitated exists only for infinite-dimensional (continuum) heat
kernels. The honest small-t behavior of a finite heat trace is
the polynomial above: K(t) = 21 - 42 t + 63 t^2 - 70 t^3 + ...
========================================================================
NO CLAIM; dials 0/4.
```

The degeneracy profile deserves one line of its own: the Laplacian's
spectrum falls into **1 simple eigenvalue + 10 doublets** — the numerical
shadow of the Lean-proved structure (unique fixed center + 10 mirror
pairs). It is a consistency illustration (T2), not a proof of anything in
the Lean bricks (T1), and the two are labeled accordingly.

## 5. What did NOT land, and why

Against the *commissioned* scope: **nothing failed.** All four bricks
landed FULL, including the Brick-2 stretch (priced as a stretch precisely
because it might have fought back; it compiled cleanly, so no remainder
is priced).

Against the *dropped sketch's own claims*, the following did not land and
never will in this form, by design:

- **The `CentralInvolutionAlgebra` class** was not carried into the tree.
  It is not an algebra (no multiplication), its axioms are assumed fields,
  and no instance can be exhibited. Replaced by the Pi function ring and
  an exhibited `RingEquiv` (Brick 2).
- **"Seeley–DeWitt coefficient extraction"** was not reproduced. For a
  finite matrix there are no Seeley–DeWitt coefficients in the continuum
  sense; the honest finite analogue is the polynomial trace expansion
  (§4). Calling the log-log slope an "effective spectral dimension" is
  the artifact named in the script's printed note.
- **A "D² heat trace"** was not produced, because no Dirac-type operator
  D was ever defined — in the sketch or here. The sketch set the
  eigenvalues of a random matrix by hand and squared them; this lane
  instead built one concrete operator (the cycle Laplacian) from the
  actual structure and labeled its trace honestly.
- **The sketch's "central" index inconsistency** (center = index 0 in the
  Lean, sorted-spectrum index 10 in the Python) is resolved by
  construction: one Θ, one center, both bricks about the same object.

Coordinator slip, owned on the record: the first draft of Brick 3
carried a hand-guessed `Tr L³ = 504` (coefficient −84); the script's own
computed trace gave 420 (coefficient −70), and the file was corrected to
the computed values before the run was logged. The script computes its
coefficients from the matrix; it does not assert them.

Verification scope, stated plainly: the lane ran **targeted** builds of
the two new modules (their dependency closure resolved against the main
tree's prebuilt Mathlib oleans via a symlinked `.lake` — build artifacts
only, no source shared) and `#print axioms` on all 19 theorems. The
main-tree full build, independent recount, fence-registry admission, and
push belong to the parent's landing ceremony and have not been done by
this lane.

## 6. Verdict

**MIRROR-21 lands FULL at its commissioned scope.** What stands, at T1:
negation on `Fin 21` is an involution with a unique fixed point; its
pullback is a ring automorphism of the function algebra; the fixed
functions are exactly the mirror-symmetric ones, freely determined by 11
values. At T2: the C₂₁ Laplacian is Θ-symmetric with derived zero-mode
count 1 and the polynomial heat expansion above. Everything else the
original sketch appeared to claim — a 21-dimensional involution
*algebra* as a class, Seeley–DeWitt coefficients, a spectral dimension —
was title, assumption, or artifact, and is recorded here as such.

**NO CLAIM. Dials 0/4.**

## Parent landing ceremony (BONES, 2026-11-02 evening EST)

Independent verification in the MAIN tree, not the lane's word:
- Recount (comment-stripped, theorem/lemma at column 0): MirrorTwentyOne strict 4 / defs 3; MirrorTwentyOneAlgebra strict 15 / defs 6. Total strict +19. Census on landing: **12,769 strict / 462 modules**, zero sorrys.
- Main-tree targeted build: `lake build ThetLogos.MirrorTwentyOne ThetLogos.MirrorTwentyOneAlgebra` — green (800 jobs).
- Axiom check re-run in the main tree on all 19 theorems: every set ⊆ {propext, Classical.choice, Quot.sound}; no sorryAx. Matches the lane's table exactly.
- Fence admissions (same commit as the modules, per the 2026-11-02 CI lesson): `ThetLogos.involution_fixed_unique`, `ThetLogos.thetaHat_fixed_iff`, `ThetLogos.fixedEquivReps_bijective` added to lean/scripts/axiom-fence.txt.
- Python companion re-run in the main tree: exit 0; degeneracy profile [1, 2x10]; gap 0.088854; Tr L^3 = 420 (the corrected value).
- Ledger record: epistemic-ledger/records/mirror-21-involution-algebra.json.
NO CLAIM; dials 0/4.
