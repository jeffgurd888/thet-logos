# STS — The Surface-Tension Seat: Landing Dossier (2026-11-05)

Brick STS (Jeff's commission "build it", 2026-11-05 00:44 EST;
charter `surface-tension-seat-charter-2026-11-05.md`). Lane:
worktree `~/workspace/thet-logos-sts`, branch
`sts-surface-tension-seat`, base main-tree HEAD `dc54c2b`, lane
tip `2a85486`. Module: `lean/ThetLogos/SurfaceTensionSeat.lean` —
**17 strict** (`theorem`/`lemma` at column 0, comment-stripped)
+ 5 defs, zero sorry, no `native_decide`, warning-clean.

**Verdict: LANDED FULL, exactly as chartered.** Every chartered
item is proved at T1; both armed kills (K-STS-FLOOR, K-STS-EVEN)
were armed and did **not** fire — the floor and evenness hold.
The seat is a finite analog exhibit, pre-registered
DIAL-INELIGIBLE: the literal identity gravity = surface tension
was NO-GO before the build (interface-only, material-dependent,
scalar/short-range vs. bulk, universal, tensor, long-range), and
nothing in this module is a gravity object. **Dial 2 = 0 before,
during, and after.**

---

## §1 — The seat and the chartered content, as landed

One finite cycle: labelings `f : Fin n → Bool` on a ring of `n`
sites (`[NeZero n]`). Definitions:

- `tensionCount f` — the number of phase boundaries:
  `#{i | f i ≠ f (i + 1)}` (Finset card of the filtered univ).
- `labelMass f` — the number of sites labeled `true`.
- `tensionEnergy γ f = γ * tensionCount f`.
- Exhibits: `singleSiteLabel` (true exactly at `0`),
  `twoSiteLabel` (true exactly at `0` and `1`).

Charter items → theorems:

1. **Complement symmetry:** `tensionCount_comp` —
   `T(¬f) = T(f)`; the energy inherits it (`tensionEnergy_comp`).
2. **Evenness:** `tensionCount_even` — `T(f)` is always even
   (ZMod 2 telescoping; the shift-by-1 permutes the ring).
   K-STS-EVEN did not fire.
3. **Isoperimetric floor (finite Young–Laplace):**
   `const_of_tensionCount_eq_zero` (zero tension forces
   constancy, by walking the ring) + `tensionCount_even` give
   `two_le_tensionCount_of_nonconstant` — a nonconstant labeling
   pays `T(f) ≥ 2`. K-STS-FLOOR did not fire.
4. **Sharpness:** `tensionCount_singleSite` and
   `tensionCount_twoSite` — both exhibits attain `T = 2` at
   `n ≥ 3`; masses `labelMass_singleSite` = 1, `labelMass_twoSite`
   = 2.
5. **Bulk-blindness (the audit's teeth, K-SR-4's spirit):**
   `tensionCount_does_not_determine_mass` — at `n ≥ 4` the two
   exhibits have *equal* tension and *unequal* mass (1 ≠ 2): the
   boundary functional provably cannot see bulk mass. This is the
   seat's pre-registered D2 failure (no bulk coupling), proved
   rather than asserted.
6. Energy corollary: `tensionEnergy_nonneg` — `E ≥ 0` for
   `γ ≥ 0`.

Helpers (6): `fin_succ_mk`, `zero_add_one`, `one_ne_zero_fin`,
`eq_last_of_add_one_eq_zero`, `eq_zero_of_add_one_eq_one`,
`last_add_one`.

## §2 — The D2 fence (pre-registered, unchanged by the landing)

- Reproduces: area/boundary law, a minimization floor, phase
  symmetry — the true finite content of surface tension.
- Provably cannot: bulk coupling (item 5), universality,
  long-range attraction, clock/light effects. No continuum limit
  is attempted or implied. FRONTIER beyond the seat; nothing
  priced past this one module.

## §3 — Deviations (declared on the lane commit, carried here)

1. **`[NeZero n]` on `tensionCount` and its theorems.** In this
   Mathlib pin (v4.35.0-rc3), `OfNat (Fin n) 1` — hence the cyclic
   shift `i + 1` — does not synthesize at a variable `n` without
   `NeZero`; the first lane compile failed at the definition
   itself. The degenerate empty ring `n = 0` is thereby excluded
   from the model. The charter's ring presupposes sites and every
   chartered statement lives at `n ≥ 1` or carries a stronger
   bound, so no chartered content changed.
2. **`labelMass_singleSite`'s `1 ≤ n` hypothesis is unused** by
   its proof (mass 1 needs only `NeZero`); kept in the statement
   as chartered, binder renamed `_hn` to stay warning-clean.
3. Lane process (for the record): a VM reboot mid-run wiped the
   lane's /tmp scratch and session records; all lane builds were
   sequential, never raced in the shared `.lake`.

## §4 — Integration record (parent, 2026-11-05)

- Precondition: main tree tracked-clean at `dc54c2b` (WB-4
  shipped state). Lane diff vs. base = exactly one new file,
  438 insertions.
- Module copied byte-identical: sha256
  `02f448081d6c5e7c70242d075bf024ef1528701c3cf8ab18b88f57e9eedd37fe`,
  verified against the lane's git object at `2a85486`.
- Declaration-level collision scan of all 22 new names + the
  module name against the main tree: ZERO collisions.
- Main-tree targeted build green (8,976 jobs, matching the
  lane); main-tree FULL build green (3,325 jobs); module
  warning-clean in both (no warning/error line names
  SurfaceTensionSeat; wider-log warnings are pre-existing
  dependency linter notes).
- Zero-sorry source gate PASS (517 files).
- Fence admissions (all 11 headlines) WITH
  `import ThetLogos.SurfaceTensionSeat` in
  `lean/scripts/axiom-fence.txt`, in the same commit as the
  module — **FENCE PASS 493/493** (482 → 493); every headline on
  exactly {propext, Classical.choice, Quot.sound}, no sorryAx.
- Recount 17 strict exact (whole-tree 14,130/517 − frozen
  remainder 669/15).
- Ledger record `sts-surface-tension-seat` (standing, T3,
  kill_id null — K-STS-FLOOR / K-STS-EVEN did not fire).
- Census 13,444/501 → **13,461 strict / 502 modules**; README
  prose + badge updated to 13,461 / 502.

NO CLAIM; dials 0/4.
