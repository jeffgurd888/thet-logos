# DUCT–GAP D1 + D2 — LANDING DOSSIER — 2026-11-04

**Verdict: LANDED FULL (both bricks, as scoped).** Lane:
`duct-lane` in worktree `~/workspace/thet-logos-duct`,
module `lean/ThetLogos/DuctGap.lean` (680 lines).
Base: main-tree HEAD `8eaf57d` at lane cut (the build
brief named `aa04767`; the tree had advanced by the R2a
integration — census 13,117/480 — before the lane was
cut; the lane was cut from the verified current HEAD).
Scoping: `your_files/duct-gap-scoping-2026-11-04.md`
governs statements, prices, kills. Fired by Jeff's word
2026-11-04 ("Build D1 + D2 (floor + dispersion)").
**No integration, no push — lane commit only.**

**NO CLAIM** — parts of any official Millennium
statement closed: 0. Dials: 0/4. Nothing here is
progress on Δ (the Yang–Mills mass gap): the floors
proved below are handed to their models by a graph,
exactly as a machined guide's cutoff is handed to it by
its width; Δ is handed its scale by nobody (scoping
§2d, §5). Finite graph model of a duct cross-section
only; no claim about any real atmospheric duct (the
operational object is a leaky waveguide in the ray
regime, scoping §2b).

## What landed

### D1 — the finite duct floor (strict spectral gap of the transverse section)

Attainment engine (finite-dimensional sphere
attainment, via the compact pi-box
`∏ i, [-1, 1]` and closedness of the admissible sets —
`isCompact_of_mem_Icc_pi`, `energyForm_continuous`):

- **`fiedler_attained`** — when two distinct vertices
  exist, the Fiedler infimum of `BridgeLaplacian` is
  attained: a mean-zero unit potential whose energy
  *is* `fiedler w`. **This pays `BridgeLaplacian`'s
  standing attainment debt**, carried in that module's
  header as "not claimed" — landed here in exactly the
  form that module's gap needs (an admissible
  minimizer, not a decay-rate statement; the priced
  exponential-decay follow-on remains unclaimed).
- **`fiedler_pos`** (D1-layered) — for symmetric
  nonneg weights with **every off-diagonal weight
  strictly positive**, `0 < fiedler w`.
- **`ductFloor` / `ductFloor_pos` / `ductFloor_le_energy`**
  (D1-Dirichlet) — for the path graph on `Fin n`
  (weights `pathWeight`: 1 between consecutive
  vertices), every `n ≥ 1`: an exhibited cutoff
  `ductFloor n hn > 0` with the Rayleigh bound
  `ductFloor n hn · ‖F‖² ≤ ⟨F, LF⟩` for every
  boundary-vanishing `F` (`path_dirichlet_floor_exists`
  is the existence form).
- **`dirichlet_minimizer_exists`** — for `n ≥ 3` the
  cutoff is attained by an actual mode.
- **`path_eq_zero_of_laplacian_eq_zero`** — trivial
  kernel: the path Laplacian restricted to
  boundary-vanishing potentials is injective.

Statement-match note (on the record, not a narrowing):
the scoping quantifies the Dirichlet form over
`n ≥ 1`, and the landed statement holds for **all**
`n ≥ 1` exactly as scoped. The proof case-splits: for
`n ≥ 3` the floor is the attained minimum energy; for
`n ≤ 2` the Dirichlet subspace is `{0}` (no interior
vertex — a zero-length duct carries no mode), so the
Rayleigh bound is vacuous there and `λ = 1` is
exhibited. The vacuity is stated in the module header
and in the proof's doc, not hidden.

### D2 — the finite dispersion split (after D1, consuming it)

- **`prodLap_tensor_eig`** (headline) — on the product
  `section × guide` with `prodLap = lapFst + lapSnd`
  (the `MirrorTwentyOneOrthogonalSpectral` `lapSum`
  pattern, generalized from its `Fin 21 × Fin 21` grid
  to a general section × longitudinal factor, both
  seats being `BridgeLaplacian` Laplacians): every
  separated eigenfunction `u ⊗ v` with `L_⊥ u = λ u`,
  `L_∥ v = μ v` satisfies
  `L (u ⊗ v) = (λ + μ) · (u ⊗ v)` pointwise.
- **`prodLap_energy_tensor`** — the energy form:
  total energy `= (λ + μ) · ‖u ⊗ v‖²`.
- **`prodLap_eig_floor`** (floor corollary, consumes
  D1) — with the section the Dirichlet path, `u`
  nonzero and boundary-vanishing, `v` nonzero, and the
  longitudinal weights symmetric nonneg:
  `ductFloor n hn ≤ λ + μ`.
- **`prodLap_floor_at_zero_momentum`** — the `μ = 0`
  case named: at zero longitudinal momentum the
  transverse eigenvalue alone clears the floor.

Honesty on the face (module header): of
`ω² = ω_c² + c²k_z²`, the finite model keeps the
**additive split** and the **floor**; the squares,
`c²`, and all physical constants do not survive and
are not claimed. No "effective mass" theorem (scoping
D4-b) was built.

## Counts vs price

Measured (comment-stripped, `theorem`/`lemma` at
column 0): **30 strict + 11 defs** total.

- D1 (§1+§2): **23 strict** — scoped 10–22, one over
  the sub-band top; the overage is the attainment
  infrastructure (`isCompact_of_mem_Icc_pi`,
  `energyForm_continuous`, `laplacianOp_smul_duct`,
  `energyForm_smul`, two `rfl` value lemmas for the
  path ends), which D2's floor corollary also consumes.
- D2 (§3): **7 strict** — scoped 8–20, one under the
  sub-band bottom; the split landed cheaper than
  priced because `laplacianOp` already existed in
  exactly the coordinate form the product seats need.
- Package: **30 strict**, inside the scoped package
  band 18–42. D1+ (exact eigenvalue
  `2 − 2cos(π/(n+1))`) was NOT built — priced
  separately in the scoping, not in this fire.

## Verification

- Targeted build `lake build ThetLogos.DuctGap`:
  **green** (3,118 jobs), in-lane.
- **Zero sorrys** (0 `sorry` tokens in the module);
  no `native_decide` anywhere.
- **Warning-clean**: no warning in the final build log
  names `DuctGap.lean` (the log's warnings all belong
  to the pre-existing dependency `BridgeLaplacian`,
  replayed because the fresh worktree recompiled it).
- **Axiom audit** (`#print axioms`, 15 headlines and
  supports audited): **every one on exactly
  `{propext, Classical.choice, Quot.sound}`** —
  `fiedler_attained`, `fiedler_pos`,
  `path_eq_zero_of_laplacian_eq_zero`,
  `dirichlet_minimizer_exists`,
  `path_dirichlet_floor_exists`, `ductFloor_pos`,
  `ductFloor_le_energy`, `prodLap_tensor_eig`,
  `prodLap_energy_tensor`, `prodLap_eig_floor`,
  `prodLap_floor_at_zero_momentum`,
  `energyForm_continuous`, `lapFst_tensor`,
  `lapSnd_tensor`, `path_eq_start_of_energy_eq_zero`.
  No `sorryAx`, nothing outside the fence trio.

## Kill status

- **K-DUCT-1 — did NOT fire.** The landed statements
  carry exactly the hypotheses the scoping mandates
  (off-diagonal `w > 0` for the layered form; exhibited
  `pathWeight` with adjacency entries `1 ≠ 0` for the
  Dirichlet form). No zero mode appeared, and no
  pressure to drop a hypothesis arose. The bare
  ∀-form over arbitrary nonnegative weights remains
  FALSE, unattempted, as registered.
- **K-DUCT-2 — did NOT fire.** The product separates
  exactly (`lapFst_tensor` / `lapSnd_tensor` are
  unconditional), so the eigenvalue identity landed as
  stated; no re-pin to the energy split was needed.
  (The energy form was landed anyway as
  `prodLap_energy_tensor`.)

## Construction friction (on the face)

- Pin quirk: the strict-positivity sum lemma in this
  Mathlib is `Finset.sum_pos'` (nonneg + one strict
  term); `Finset.sum_pos` is the all-strict form —
  one misfire diagnosed from the `#check` signature,
  no mathematics moved. `if_pos` → `ite_eq_left`,
  `push_neg` → `push Not`,
  `continuous_finset_sum` → `continuous_finsetSum`
  (pin deprecations, replaced).
- The unused-section-variable linter cascade was
  discharged at five sites with `omit` blocks carrying
  the linter's verbatim variable lists (placed before
  the doc comments, per the recorded lane quirk):
  `abs_apply_le_one_of_sum_sq_eq_one` `[DecidableEq V]`,
  `isCompact_of_mem_Icc_pi` `[Fintype V] [DecidableEq V]`,
  `fiedlerAdmissible_isClosed`, `laplacianOp_smul_duct`,
  `energyForm_smul` (each `[DecidableEq V]`).
  Statements unchanged throughout.
- Infrastructure: the worktree's `.lake` cache was
  seeded by hardlinking the main tree's artifacts at
  the same HEAD; builds ran under heavy multi-lane
  contention and one VM reboot (build wall times
  400–730 s against ~30 s of dependency checking
  uncontended). No mathematics affected.

## Fences restated

Frozen statements elsewhere unedited (the lane adds
one new module and this dossier; `BridgeLaplacian` and
`MirrorTwentyOneOrthogonalSpectral` were read and
consumed, never modified). D3 (continuum waveguide)
and D4 (real-duct spectrum, effective-mass costume,
any D→Δ mapping) remain NO-GO per the scoping. **NO
CLAIM; dials 0/4.**

## AMENDMENT — 2026-11-04 — integration Step 1 collision-gate rename (lane-side fix)

The parent integration of this lane STOPPED at its
Step 1 collision gate: two `DuctGap` declarations
already exist in the main tree's
`lean/ThetLogos/BridgeCompletion.lean` (both in
namespace `ThetLogos`). Lane-side fix only — no
integration, no push to master; the parent integration
resumes from its Step 1 collision gate against this
amended lane commit.

Rename map (old → new, `DuctGap` side only;
`BridgeCompletion` untouched):

- `fiedlerAdmissible` → `ductFiedlerAdmissible`
  (DuctGap def, ex-line 150; collides with
  `BridgeCompletion.lean:201` — same body,
  section-variable vs explicit-binder form).
- `laplacianOp_smul` → `laplacianOp_smul_duct`
  (DuctGap theorem, ex-line 178; collides with
  `BridgeCompletion.lean:117` — same content,
  unfolded statement form).

Both suggested replacement names were verified free
in the whole main tree before use; no fallback name
was needed. A full declaration-level scan of all 41
`DuctGap` names (post-rename) against every
`theorem`/`lemma`/`def` in the main tree found NO
remaining collisions. The derived names
`fiedlerAdmissible_isClosed` and
`fiedlerAdmissible_nonempty_of_exists_ne` are separate
declarations, were already collision-free, and are
NOT renamed — only their internal references to the
renamed def were updated (6 bare references to
`ductFiedlerAdmissible` and 2 to
`laplacianOp_smul_duct` in the module; the dossier's
two `laplacianOp_smul` mentions, in Counts vs price
and Construction friction above, updated in place).

Statements, proofs, and counts MUST NOT and did NOT
change: re-measured **30 strict + 11 defs**, module
still 680 lines, zero sorrys, no `native_decide`.
Neither renamed name is one of the 15 audited fence
headlines; all 15 headlines are untouched.

Re-verification in-lane: targeted build
`lake build ThetLogos.DuctGap` green (3,118 jobs);
module WARNING-CLEAN (every warning in the log names
the pre-existing dependency `BridgeLaplacian`, none
names `DuctGap.lean`); `#print axioms` spot-check on
the 15 dossier headlines — plus both renamed
declarations — still exactly
`{propext, Classical.choice, Quot.sound}`, no
`sorryAx`. **NO CLAIM; dials 0/4.**

## INTEGRATION — 2026-11-04 — parent integration (restart) into the main tree

Restarted from Step 1 against the fixed lane commit
`e988ced` (rename fix only: `ductFiedlerAdmissible`,
`laplacianOp_smul_duct`; see AMENDMENT above). Step 1
re-run: main tree at `8eaf57d`, tracked files clean,
module + dossier new, declaration-level collision scan
for ALL 41 `DuctGap` names against the main tree found
ZERO collisions. Module + dossier copied BYTE-IDENTICAL
from lane commit `e988ced` (md5-verified:
module `8de02c1848b9f90f6b39594df9a32fd9`, dossier
pre-integration `c3a821ce678eed38e92b8cba5d2b147f`).
Main-tree targeted build `lake build ThetLogos.DuctGap`
green (3,118 jobs, matching the lane), zero sorrys,
module WARNING-CLEAN (every build warning names the
pre-existing dependency `BridgeLaplacian`). Recount:
module strict 30 + 11 defs exact; census FILES-TRUE
13,117/480 → **13,147 strict / 481 modules** (whole-tree
13,816/496 minus frozen remainder 669/15); README prose
+ badge both 13,147/481, kept equal. Fence: the 15
audited headlines admitted WITH `import ThetLogos.DuctGap`
in the same commit as the module — FENCE PASS **190/190**,
every new headline on exactly
`{propext, Classical.choice, Quot.sound}`, no `sorryAx`.
Ledger record `duct-gap-d1d2` (standing, T3), validator
PASS 27 records. Verdict face unchanged: D1 + D2 FULL,
`BridgeLaplacian` attainment debt paid, K-DUCT-1 /
K-DUCT-2 did not fire, finite graph model only, NO
real-duct claim, NO Δ mapping. **NO CLAIM; dials 0/4.**
