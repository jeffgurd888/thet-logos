# CLS-3c LANDING DOSSIER — 2026-11-02

**Item:** CLS-3c (Dial-1 classification lane) — the
antiparticle direction chapter: the classification's
boundary made explicit.

## VERDICT: PARTIAL at the pre-named seam — the kill is transported at the axis endpoint π₀ and proved there; the pure direction's own base status is named OPEN

**Artifact:** `lean/ThetLogos/DialOneAntiparticleChapter.lean`
— strict 11, defs 4. Verified by the coordinator in the
main tree (build green, 3144 jobs); all six headlines on
exactly `[propext, Classical.choice, Quot.sound]`.

**The audit corrected the scoping's picture in two places.**
(1) No in-tree definition of the pure §2.6 direction
existed, and the axis endpoint π₀ is **not** the pure
direction — it additionally carries the bolted blocks
(antilepton and left-antiquark blocks, `Track1RouteB` §2
anatomy), and π₀'s own C3 trace is in fact **nonzero**.
(2) The chapter therefore defines the direction minimally,
on its face as this chapter's def: `piAnti` = π₁ with M₃
un-conjugated in both antiparticle blocks (slots 18–23 and
26–31), nothing else changed.

**Landed at T1:**
- **C3-invisibility of the pure direction, proved**
  (the scoping carried it at T2): the direction's
  γ-weighted β-difference sum is exactly 0
  (`gamma_weighted_beta_direction_zero`), hence
  `trace_gammaF_piAnti_u1Gen = 0` and `c3_piAnti`;
  `piAnti ≠ pi1`.
- **The base kill at the axis endpoint, exactly cited and
  transported:** `Track1Closure.first_order_killed`
  (entry identity `DF_first_order_entry_09`: the (0,9)
  entry `−(1 + I) * ye`). Since `rho0 = piOp ∘ pi0` by its
  landed definition, this is precisely `DialOneBase`
  clause 9 at π₀, and the chapter proves
  `not_dialOneBase_pi0 : ¬ DialOneBase pi0` and
  `not_strengthenedFam_pi0`.
- **The boundary:** `antiparticle_unique_nontoggle` — over
  the named direction space (CLS-0 record toggles + CLS-3a's
  piEFlip + the CLS-2 orbit, plus this axis), every
  non-toggle named direction is `piAnti` or `pi0`. New
  non-toggle directions are new entries, never extensions.

**The seam, named on the face:** `piAnti`'s **own** base
status is OPEN. π₀'s kill witnesses read the bolted blocks,
which `piAnti` lacks; transporting the kill to the pure
direction would need a new first-order computation and
would silently upgrade the scoping's T2 sentence. Not done.
A future brick computing πAnti's first-order status is a
new entry at its own price.

**Lane 1 state:** the classification chapters are now all
landed — orbit (CLS-2/2b), lepton (CLS-3a), colour (CLS-3b),
antiparticle (CLS-3c at this seam). Grade T: complete at
every named direction, with piAnti's base status the one
named open cell. Grade W: open (CLS-1 at ExtractionLemma,
shrunk by CLS-1a-X; re-pose = decision item). Grade R:
unposed.

## Fences

NO CLAIM; **Dial 1: 0.**

**Census after landing: 12,245 strict / 12,634 total / 420 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
