# PW-5a — the Φ Assembly's Interface

*Landing dossier, 2026-10-27. Module:
`lean/ThetLogos/PhiAssembly.lean`, section 5a
(strict 11, defs 0, 11 private helpers; zero
placeholders, zero `native_decide`; main-tree build
green, 3,558 jobs, parent-verified; axiom sets
exactly `[propext, Classical.choice, Quot.sound]` on
every checked headline). **Parts of the Clay
Yang–Mills statement closed by this landing: 0.**
The assembly's first sub-brick: the e1 baseline
pack, the cycle ordering, and the split-list check —
which confirms the scoping's orientation enumeration
exactly, so the pre-registered kill does not fire.*

## What landed

- **The e1 pack.** At irreducible ρ with 2 ≤ d,
  e1 = 0 (from PW-1's owned vanishing). The d = 1
  case the tree was missing: a nontrivial
  one-dimensional character (nontriviality in owned
  vocabulary: ∃ h, χ(h) ≠ 1) also integrates to zero,
  by Haar left-invariance — χ(h) · ∫χ = ∫χ forces
  ∫χ = 0; and for the trivial representation the
  diagonal Φ contribution is identically zero
  (quadReMoment = e1⁴ = 1 there). The baseline is
  now settled at every d: Φ_C = quadReMoment C u u
  whenever ρ is irreducible and nontrivial, and 0 in
  the trivial case. (Correction of record: e1 lives
  in `PlaneCrossingBeta2`, not Beta4 as the scoping
  memo supposed; the pack matches the owned def.)
- **`c4_cycle_ordering`.** From C4 pattern data at
  (Even N, 3 ≤ N): an ordering of the quad's columns
  P : Fin 4 → LayerColumn N and sites
  s : Fin 4 → LayerSite N, both injective, covering
  C, with colSites (P i) = {s i, s (i+1)} cyclically —
  the function form the contraction engine consumes.
- **The split list (`c4_split_list`), K-PW-5-1's
  check.** Every C4's site splits are exactly one of
  **PLAQ** — (2,0), (1,1), (0,2), (1,1) with source
  and sink at opposite corners (cyclic distance 2) —
  or **WRAP** — (1,1) at all four sites. The two
  extra shapes the raw grammar allows are excluded
  by proof: the alternating source/sink shape by the
  2 = 2 step identity, the adjacent shape by the
  1 = 3 step identity — the scoping's shift-vector
  arithmetic, now machine-checked. **K-PW-5-1 does
  not fire.**

## What remains of PW-5

5b, the contraction engine (R1 support
factorization; R2 the entry-level twisted
contraction — the line's cost center and its honest
risk, K-PW-5-2 pre-registered), then 5c, the
assembly to `phi_diag_nonneg`. The endpoint's scope
is unchanged: the diagonal sign of κ₄^dep at order
β⁴, irreducible ρ, even N ≥ 4, no cushion. This
dossier asserts the interface only. NO CLAIM; dials
0/4, unchanged.

Census effect: 6,957 → **6,968 strict** /
7,035 → **7,046 attribute-inclusive** / 238 → **239
modules**; the seven quarantined placeholders are
unchanged. (The module grows by append in 5b/5c;
their landings update the strict count in their own
dossiers.)

## Backers since last landing

No new backers inscribed in this interval; the roll
stands as recorded in `BACKERS.md`. Every gift is
published with the proof stream, named as the giver
wishes, amounts only with the giver's permission —
the standing reciprocity of this house.
