# B6-PROBE LANDING — 2026-10-29

**Verdict: FULL — pre-registered outcome (ii): the regress
continues.** New module `ThetLogos/PlaneCrossingBeta6Probe.lean`
(strict 96 / defs 41), plus the Python exact side
(`routeb-general-scratch/b6probe_seat.py`, output
`b6probe-run.txt`) and registry entry BR1-004.

**NO CLAIM. Parts of any Millennium statement closed by this
landing: 0. Dials 0/4.**

## The pre-registered question

Per the β⁶ scoping §2: at N = 4, seats (C₃, χ) and (S₃, std),
assemble each new order-6 channel's diagonal form, restrict to
the joint kernel K = ker κ₄^dep (the dressing terms of
κ₆^dep vanish on K by construction, so the new channels are
the first content that can decide those directions), and
evaluate. The kill **K-K6** was armed at full rank: a certified
negative of any new channel on K at a seat would make 𝒜
indefinite for all small β > 0 along that direction — β2's
perturbative route FALSE, landed with the same ceremony as a
win.

## The verdict

**K-K6 does not fire.** Every new channel vanishes identically
on K at both seats. The mechanism is the β⁵ pattern one order
up: each channel kernel is an exact positive multiple of the
seat's κ₄ kernel, hence zero exactly where κ₄^dep is zero.

| channel | (C₃, χ) | (S₃, std) |
|---|---|---|
| (3,1,1,1) | 3 × κ₄ | 12 × κ₄ |
| (2,2,1,1)-adjacent | 2 × κ₄ | 8 × κ₄ |
| (2,2,1,1)-opposite | 1 × κ₄ | 4 × κ₄ |
| C6 | ¼ × κ₄ | ¼ × κ₄ |
| Θ(2,2,2) | ¼ × κ₄ (holonomy-sum coordinate) | vanishes on the convention span |

Per the pre-registered table this is outcome **(ii)**: all new
channels vanish on K at both seats, so the β⁶ coefficient
decides nothing on the joint kernel — the decision passes to
the next order at which a new channel meets the shrunken
kernel. There is no parity law and no internal stop; nothing
about the general β⁶ sign follows (it stays FRONTIER on
quadruple twirls), and nothing about 𝒜 ⪰ 0 follows in either
direction — the registered target `LayerKernelPos` is
untouched by this verdict.

## Method and cross-checks (BRIDGE-1 discipline)

Both sides were built and they agree exactly. The Python side
first reproduced ker κ₄^dep at both seats from its own κ₄
extraction (constants at (C₃, χ); {φ₀ = φ₂} at (S₃, std)) as
its convention check, and found e₁ = 0 at both seats (the
fully-split baselines vanish; raw channel = excess at seats).
The Lean side re-derived both kernel characterizations
in-module, defined every channel kernel from channel content,
and proved the proportionalities as theorems — every constant
reproduced the Python table entry-for-entry, with no
disagreement recorded. The parent re-ran the Python script at
landing (output identical) and ran the headline axiom check:
`verdict_B6Probe` depends on exactly
`[propext, Classical.choice, Quot.sound]`.

## The Θ convention (recorded, not smoothed)

Θ at (S₃, std) is the one place the pre-registered table
needed a convention the sources had not fixed: K is fixed on
the single-loop holonomy class space, while Θ's observable
space is pairs (g₃, g₅) modulo simultaneous conjugation, and
no landed source named K's pullback there. The Python side
stopped that channel (K-PROBE-a) and verified diagnostically
that the restriction is exactly zero under **every** candidate
pullback reading. The Lean module then fixed the convention on
its face — the pullback is the joint candidate span
{1, s₁, s₂, s₁s₂} (constants with the three 4-cycles' sign
pullbacks), the largest candidate reading — and proved the Θ
form vanishes on the whole span: its orbit kernel is
(1/32)·m mᵀ with m = (2, 0, −1, 0, 0, 0, 0, −1, 0, −1, 2), so
the form is a square (1/32)·(L ψ)² whose linear functional L
vanishes on every span profile. Vanishing on the joint span
implies vanishing under every candidate sub-reading, so the
outcome (ii) does not depend on the convention choice; the
convention is recorded here because it is a convention.

## Verification (parent, independent, from disk)

- Parent count of the module from disk: strict 96, defs 41,
  no same-line attribute declarations (the builder's count of
  98 theorems included two private helpers, which the house
  rule does not count). Census after this landing: **7,257
  strict / 7,335 attribute-inclusive / 248 counted modules**
  (from 7,161 / 7,239 / 247).
- Main-tree build green (`Build completed successfully`,
  3,325 jobs).
- Per-type fence, on the module's face: at (C₃, χ) the
  plaquette and wrap-chain quad kernels agree (Python table);
  the Lean fiber derivations are carried at the plaquette,
  and the class kernels are the per-quad-type kernels.

## Backers since last landing

No new backers recorded since the B6-1 landing (earlier
today). The backers roll in `BACKERS.md` is unchanged.

## What this does not do

It does not prove or refute 𝒜 ⪰ 0, does not decide the β⁶
sign anywhere off the two seats' joint kernels, and does not
shorten the regress: the perturbative kill-detector has now
passed order 6 at both seats, and the decision passes onward.
The assembly (B6-2) follows, and the β⁵ sign stays FRONTIER.
