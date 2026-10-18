# Trit / Data-Center Scoping — Ternary Representation vs the Heat-and-Water Bill

**DRAFT SCOPING — NOT A SOLUTION, NOT A DOSSIER. Nothing in this document
is built, measured, or claimed. It is a formulation: a problem pinned with
sourced numbers, a hypothesis stated as a hypothesis, an honest inventory
of what this program actually owns, one priced first experiment, and the
kills named in advance. Written 2026-10-17. Format and honesty template:
`pitch-4-continuum-scoping-DRAFT-2026-10-17.md` and
`thermal-clock-charter-DRAFT-2026-10-17.md`.**

**NO CLAIM charter.** This scoping makes no claim — on data centers, on
water, on ternary hardware, or on anything else. It does not say ternary
computing saves a single gallon. It says: here is a real problem (§1),
here is a hypothesis with three named mechanisms and the evidence tier of
each (§2), here is the small verified floor this program stands on and
the large floor it does not (§3), here is the first experiment that could
move the hypothesis one tier in either direction (§4), and here is what
kills it (§5). Negative findings from §4, if they come, are results and
will be reported at the same speed as positive ones.

Tier labels used throughout, and binding on every line:

- **T1** — proved by us, machine-checked in Lean, zero sorry.
- **T4** — literature: published or reported by others, cited; not
  verified by us. Authors' reported numbers stay authors' reported
  numbers.
- **T5** — hypothesis, framing, or vision. Spendable nowhere.

One framing sentence, labeled T5 so it can never be mistaken for a
result: *a data center is a heat problem wearing a water problem's
clothes — every gallon it drinks is heat leaving the building.* §1 is the
sourced version of that sentence; §6 is what may be said in public, and
it is much less than the sentence suggests.

---

## 0. Verdict preview

**Recommendation: formulate, price one desk experiment, build nothing
yet.** In order:

1. The problem is real, current, and Michigan-local (§1): hyperscale
   cooling drinks water at town scale, the withdrawals are incompletely
   metered, and the state's first gigawatt-scale fight (Saline Township)
   and its first water bill (HB 6138) are both already on record.
2. The hypothesis (§2) — that higher-radix / ternary representation can
   cut energy per inference operation at fixed accuracy — has exactly
   one strong empirical leg, and it is T4 and narrower than its press:
   BitNet b1.58's reported wins are dominated by *fewer bits moved* and
   *cheaper arithmetic*, mechanisms binary low-precision schemes also
   capture. Whether anything is left over that belongs to the radix
   itself is precisely what is not known. That unknown is the
   experiment.
3. What this program owns (§3) is real and small: a T1 ternary algebra
   (27 theorems) and a T1 graph-heat-flow algebra (29 theorems). No
   device, no benchmark, no power model, no empirical result of any kind
   in this direction. The connection between §3 and §2 is currently at
   the level of shared vocabulary — the word "trit," the Laplacian —
   and this charter says so rather than implying more.
4. The first honest experiment (§4) is software emulation with modeled
   energy, priced S–M of desk work, with its proxy status labeled in
   advance and its kill thresholds pre-registered. Real energy on real
   ternary hardware is FRONTIER: the hardware does not exist to buy,
   rent, or borrow.
5. Nothing in §6 — the public-language section — is unlocked by this
   charter. It is unlocked, partially, only by a §4 landing, and the
   gallon-denominated language is not unlocked by anything short of a
   hardware measurement this program cannot currently make.

---

## 1. The problem, pinned with sourced numbers

Heat first, because water here is heat's shadow. Essentially all
electrical energy a data center consumes ends as heat that must leave
the building; where evaporative cooling carries the heat out, water is
consumed (evaporated, not returned) in rough proportion to the heat
rejected. Cut the joules at fixed work and every downstream term —
cooling energy, evaporated water — falls with them. That proportionality
is physics, not a finding of this program; everything below it is cited.

### 1.1 Scale of the drink (T4, cited)

- A large hyperscale data center consumes **1–5 million gallons of water
  per day** for cooling — the daily use of a town of 10,000–50,000
  people; enterprise facilities average 300,000–500,000 gallons/day.
  Sources: Nature Forward, "Data Centers and Water Use,"
  https://natureforward.org/data-centers-and-water-use/ ; FLOW Water
  Advocates fact sheet,
  https://flowwateradvocates.org/big-tech-data-centers-target-michigans-resources/
- Most of an evaporative facility's withdrawal is *consumed*, not
  returned: roughly 70–85% evaporates. Withdrawal figures understate the
  loss to the local supply; closed-loop systems consume a small fraction
  of their initial fill. Source: RocTel, "How Much Water Does a Data
  Center Use? The 2026 Numbers,"
  https://roctelecom.com/insights/data-center-water-usage/
- The efficiency overhead: the industry-average PUE (total facility
  energy ÷ IT energy) has **plateaued at ≈ 1.54–1.58** in Uptime
  Institute's annual surveys (1.56 in the 2024 survey; ~1.54 in 2025),
  essentially flat since ~2019, while leading hyperscale builds report
  ~1.1. At PUE 1.56, ≈ 36% of facility energy is overhead rather than
  IT, and cooling is the largest single overhead component — commonly
  cited at **30–40% of total facility power**. Sources: Uptime Institute
  Global Data Center Survey 2025,
  https://datacenter.uptimeinstitute.com/rs/711-RIA-145/images/2025.Annual.Survey.Report.pdf
  ; "Global Data Center PUE Stalls at 1.54,"
  https://mgrid.org/2025/10/01/uptime-institute-data-center-pue-stagnation-2025-liquid-cooling/
  ; Huawei Digital Power, "Demystifying PUE,"
  https://digitalpower.huawei.com/en/blogs/data-center-power-usage
- The floor under all of it (T4, textbook physics): Landauer's bound —
  erasing one bit dissipates at least kT ln 2 ≈ 2.9 × 10⁻²¹ J at 300 K,
  experimentally confirmed (Bérut et al., Nature 2012). Modern devices
  operate many orders of magnitude above this floor per operation, so
  the bound is not where the fight is; architecture and data movement
  are. Source: "Landauer's principle,"
  https://en.wikipedia.org/wiki/Landauer%27s_principle

### 1.2 Michigan, specifically (T4, cited)

- The Alliance for the Great Lakes, *A Finite Resource* (August 2025),
  forecasts hyperscale data centers to **withdraw 150.4 billion gallons
  of water between 2025 and 2030** — stated by the report as the
  equivalent of 4.6 million U.S. households — and notes that a single
  hyperscale facility can use more than 365 million gallons per year.
  **Read the figure correctly: it is a five-year cumulative withdrawal,
  not a per-year rate.** (Secondary coverage that prints it as an
  annual figure is garbling the report; this charter uses the report's
  own statement.) The report also records that withdrawals are in many
  cases shielded from public disclosure by nondisclosure agreements,
  and that 40–75% of Great Lakes residents rely on groundwater for
  drinking water. Source (the report itself):
  https://greatlakes.org/wp-content/uploads/2025/08/AGL_WaterUse_Report_Aug2025_Final.pdf
- **Saline Township (Washtenaw County):** a ~1.4 GW campus ("The Barn,"
  developed by Related Digital for Oracle / OpenAI) proceeded under a
  consent judgment after the township's rezoning denial was sued and
  settled; the judgment includes a **commitment not to use
  water-intensive evaporative cooling** and service by an on-site well
  system. Construction began June 2026; DTE reports the Oracle 1.4 GW
  agreement among 2.4 GW of executed Michigan data-center power
  agreements. The project became an issue in Michigan's 2026 statewide
  races. Sources: DataCenterDynamics, "Township in Michigan settles
  lawsuit, allows data center project to proceed,"
  https://www.datacenterdynamics.com/en/news/township-in-michigan-settles-lawsuit-allows-data-center-project-to-proceed/
  ; The Sun Times News, "Saline Township Data Center Draws Attention in
  Michigan Election Debates,"
  https://thesuntimesnews.com/saline-township-data-center-draws-attention-in-michigan-election-debates/
- **HB 6138**, the "data center water regulation act": introduced
  June 25, 2026 (lead sponsor Rep. Jason Morgan), referred to the
  Committee on Government Operations. As introduced, it would bar
  construction or operation of a Michigan data center unless it uses a
  closed-loop cooling system or municipal water only, require
  noncompliant facilities to cease operation, and prescribe civil fines
  up to $1,000,000 per day. **Status: introduced, not enacted.** Source:
  Data Center Water Tracker (summarizing legislature.mi.gov),
  https://savrn.com/data-center-water-tracker

### 1.3 What §1 does and does not establish

§1 establishes that heat removal is a first-order cost of computation at
civil scale and that Michigan is deciding, now, how much water that
cost may drink. It does not establish that any particular computing
technology changes the bill. That is §2's burden, and §2 does not
currently carry it.

---

## 2. The hypothesis, stated as a hypothesis

**H (T5).** *Representing computation at higher radix — concretely,
ternary weights and values in {−1, 0, +1} — can reduce the energy per
inference operation at fixed task accuracy by enough to matter at
facility scale, through the mechanisms below.*

H is a hypothesis. Each mechanism is listed with what actually supports
it and what cuts against it; the cuts are part of the charter, not
footnotes to it.

### 2.1 Mechanism (i): radix economy — a fact, and a small one

Mathematical fact (provable on one line; T4 as a classical result, and
elementary): if representing a range of N values costs radix × digits,
E(b) ≈ (b / ln b) · ln N, minimized over real b at **b = e ≈ 2.718**.
Over integers: 2/ln 2 ≈ 2.885, **3/ln 3 ≈ 2.731**, 4/ln 4 ≈ 2.885 —
base 3 is the most economical integer radix, ≈ **5.4%** below base 2 in
this model. Source: "Optimal radix choice,"
https://en.wikipedia.org/wiki/Optimal_radix_choice ; Brian Hayes,
"Third Base," *American Scientist*,
http://web.williams.edu/Mathematics/sjmiller/public_html/105Sp10/addcomments/Hayes_ThirdBase.htm

Two cuts, stated at full strength. First, 5.4% is the *entire* prize the
radix-economy argument offers — it cannot underwrite claims about
"saving" anything civil-scale. Second, the model prices digit-states ×
digit-count and is silent about the cost of a state: in a fixed voltage
window, three levels have roughly half the noise margin of two, and
per-state device cost, threshold generation, and interconnect physics
are exactly where ternary historically lost. Radix economy is a reason
the hypothesis is not absurd. It is not evidence that it is true.

Historical anchor (T4): **Setun**, developed 1958 at Moscow State
University under Sergei Sobolev and Nikolay Brusentsov — a working
balanced-ternary computer; ~50 units built (1959–1965), succeeded by
the Setun-70 (1970), then discontinued while binary machines it
out-priced were replaced by binary machines anyway. Ternary computing
is a real, built, abandoned technology — evidence that the radix is
implementable, and equally evidence that implementability was not
enough. Source: "Setun," https://en.wikipedia.org/wiki/Setun

### 2.2 Mechanism (ii): ternary weights at LLM scale — BitNet b1.58 (T4)

The strongest empirical leg, and it belongs to Microsoft Research, not
to us. Ma et al., "The Era of 1-bit LLMs: All Large Language Models are
in 1.58 Bits" (2024): every weight ternary {−1, 0, +1} (hence 1.58 =
log₂ 3 bits per weight), activations at 8 bits, trained from scratch.
The authors **report**: parity with FP16 LLaMA-style baselines in
perplexity and end-task accuracy at equal size and training tokens,
beginning at 3B parameters (3B perplexity 9.91 vs 10.04); at 3B, **2.71×
lower latency and 3.55× less memory** (measured, GPU, 2-bit kernel); at
70B, 4.1× lower latency and 8.9× throughput; and an **estimate** of
**71.4× less arithmetic energy for matrix multiplication on 7 nm** —
an estimate computed from a published per-operation energy model, *not*
a measurement of ternary silicon. Source (the paper):
https://arxiv.org/abs/2402.17764 and full text
https://arxiv.org/html/2402.17764

The cuts, at full strength:

- The baseline is FP16. The hypothesis must survive comparison against
  the best *binary low-precision* baselines (INT8/INT4/2-bit), which
  also shrink traffic and cheapen arithmetic. Against those, no
  published result known to this charter isolates a radix effect.
- The energy headline is modeled, not measured; it inherits every
  assumption of its op-energy table.
- Latency and memory *were* measured — on binary hardware, via packed
  2-bit kernels. They are real systems results about low-precision
  weights, obtained without any ternary device.
- Independent replication is partial: the inference kernels are open
  (Microsoft's bitnet.cpp; an official 2B model trained on 4T tokens
  followed in 2025), and third parties do run them; the at-scale
  *training-parity* claim rests mainly on the authors' reports.
- What does the work in BitNet is overwhelmingly mechanisms (iii) and
  "multiplication replaced by addition/selection" — i.e., *fewer bits
  moved, cheaper ops*. Whether the *ternary-ness* (as opposed to the
  *fewness of bits*) contributes anything separable is an open
  question, and it is the question §4 is designed to ask.

### 2.3 Mechanism (iii): fewer digit-moves per value (T4 mechanism, T5 sizing)

One trit carries log₂ 3 ≈ 1.585 bits, so a value needs ≈ 37% fewer
digits in base 3 than in base 2 — and data movement, not arithmetic, is
where the energy is. Horowitz's ISSCC 2014 accounting ("Computing's
Energy Problem"): a DRAM access costs **1–2 nJ**, against ~10 pJ for an
on-chip operation — a couple of orders of magnitude — with DRAM I/O
alone above 20 pJ/bit. Source (the paper):
https://pages.cs.wisc.edu/~markhill/restricted/isscc2014_horowitz_power_scaling.pdf

The cut: per-*bit* moved, a trit moved on binary wires costs exactly
what 1.585 bits cost — nothing is saved by renaming. The saving exists
only if values are stored, moved, and consumed *as trits* (packed or
native), and if the accuracy held fixed does not force wider values
elsewhere (BitNet's own activations sit at 8 bits). Mechanism (iii) is
therefore a claim about a full stack that does not exist, quantified by
an op/table model — which is why §4 prices a model, not a machine.

### 2.4 The hardware horizon (T4, honestly characterized)

Ternary logic hardware research exists and is laboratory-scale:
carbon-nanotube FET designs exploit chirality-set multiple thresholds,
and a 2025 *Science Advances* result demonstrates CNT source-gating
transistors switching among three states, with ternary inverters,
NMIN/NMAX gates, ternary SRAM cells, and a small ternary neural-network
demonstration. A larger literature is simulation-only (HSPICE against
the Stanford 32 nm CNTFET model), reporting power-delay improvements
*among ternary designs*, not against CMOS systems. There is no
commercial ternary processor, no foundry process, and no purchasable
device on which §4 could measure real energy. Sources:
https://www.science.org/doi/10.1126/sciadv.adt1909 ;
https://www.sciencedirect.com/science/article/pii/S2772671124000093

---

## 3. What we actually own — and what we do not

Verified by file inspection 2026-10-17. Everything here is **T1** and
narrower than its name will sound.

### 3.1 The ternary floor (algebra only)

`lean/ThetLogos/TritGrading.lean` (350 lines, **27 theorems**, zero
sorry): a three-element balanced-ternary type `Trit` = {neg, zero, pos}
with its integer reading into {−1, 0, +1}; the `ZMod 3` arithmetic of
trits (`Trit.addEquivZMod3`); submodule-valued `ZMod 3`-gradings of
matrix algebras; covariance of commutator and adjoint action under such
gradings; a squared-commutator trace bound for Hermitian matrices. The
file's own header: T1 background algebra, "not physics." It contains no
arithmetic circuits, no complexity bound, no statement about energy,
hardware, or computation cost of any kind.

`lean/ThetLogos/SexagesimalClock.lean`: the CRT decomposition
`ZMod 60 ≃+* ZMod 3 × ZMod 4 × ZMod 5`, and
`ClockGrading.reduceToTrit` — the reduction of a sexagesimal clock
grading along the mod-3 map (`toTritClock`) to a `TritGrading`.
Bookkeeping: the trit dial inside the base-60 clock. Algebra only.

### 3.2 The heat-flow floor (finite graphs only)

`lean/ThetLogos/BridgeLaplacian.lean` (466 lines, **29 theorems**, zero
sorry): on a finite weighted graph, the factorization **L = dᵀσd**
(boundary operator, Ohm factor, divergence), the dissipation identity
and its nonnegativity (`energy_nonneg`: for nonnegative weights,
0 ≤ Σᵢ Fᵢ (LF)ᵢ), Kirchhoff's voltage and current laws as theorems,
kernel = constants at positive weights, and a Fiedler variational
bound. This is the mathematics of diffusion — heat flow — on a finite
network: the same operator family that governs thermal spreading on
graphs. It is not a continuum heat equation, not a thermal model of any
building, and it has never met a measured temperature.

### 3.3 What we do not own

No ternary device, circuit, or simulation of one. No power model of any
computation. No benchmark, in
...[truncated 18333 chars] any language, run by anyone
here. No cooling model. No empirical result — not one measurement — in
this direction. And no bridge: nothing in §3.1 or §3.2 is *about*
computation cost or facility heat. The trit of `TritGrading` and the
trit of BitNet are the same three values and nothing more is currently
proved, modeled, or measured that connects them. A charter that implied
otherwise would be the exact failure this house exists to prevent.

---

## 4. The first honest experiment (priced)

**Design.** A software-emulation benchmark on one standard small
transformer family, run entirely on binary hardware, with two
independent energy proxies that must agree in sign before anything is
concluded:

- **Configurations:** FP16 baseline; binary INT8; binary INT4 (or 2-bit)
  as the *real* opponent; ternary 1.58-bit (official BitNet-class model
  and kernels where available). Post-training-quantized and
  trained-ternary variants are different objects and are reported
  separately, never pooled.
- **Fixed accuracy, defined in advance:** WikiText-2 perplexity within a
  pre-registered tolerance of the FP16 baseline, plus a small fixed
  end-task suite. A configuration that misses the band is not "less
  accurate but cheaper"; it is out of the comparison.
- **Proxy P1 (modeled):** an exact census per generated token — op
  counts by type, and bytes moved at each modeled level (weights,
  activations, KV) — multiplied by a published per-operation energy
  table (Horowitz-class, node stated). P1 is a model. It is labeled a
  model every time it is printed.
- **Proxy P2 (measured):** wall energy on the test machine (RAPL /
  package counters) for the *emulated* kernels. P2 measures what binary
  silicon spends emulating each configuration — a real measurement of
  an emulation, not of the represented arithmetic.
- **The question, sharp form:** at fixed accuracy, does the ternary
  configuration beat the best binary low-precision configuration in
  **both** proxies by more than the pre-registered margin (§5, K1)? A
  win over FP16 alone answers nothing — §2.2's cut — and is reported as
  nothing.

**Price.** The op/traffic census on existing open models and kernels:
**S** (days of desk work). The full benchmark — accuracy matching,
both proxies, dossier with the census tables: **M** (week scale). A
variant requiring training a ternary model from scratch: **L and out of
scope** (no GPU budget exists; if it is ever proposed, it is proposed
as its own scoping). Real energy on real ternary hardware: **FRONTIER**
— no device exists to measure; §2.4 is the whole horizon.

**Pre-registration.** The accuracy band, the margin in K1, the energy
table, and the token counts are fixed in the benchmark's dossier
*before* the runs. Changing a threshold after seeing a number converts
the experiment into marketing; the house rule is that the dossier's
first commit precedes the first run.

---

## 5. Kills, pre-named

- **K1 (no radix effect).** If, at fixed accuracy, the ternary
  configuration's modeled energy per token does not beat the best
  binary low-precision baseline by **≥ 10% in both proxies**, the radix
  direction dies in writing. What survives is a literature note:
  low precision helps; three-ness, at this scale of evidence, does not
  separably help.
- **K2 (anchor failure).** If BitNet-class parity or energy results
  fail independent replication in the literature — or the 71.4× class of
  figure is shown to be an artifact of its op-energy table — the T4
  anchor of §2.2 downgrades to T5, H loses its only empirical leg, and
  the direction is parked, not re-argued.
- **K3 (it's the bits, not the base).** If the traffic decomposition
  shows the ternary win, where one exists, is fully accounted for by
  bits moved per token — i.e., a binary scheme at equal bits/token
  matches it — the honest headline is "precision reduction, not radix,"
  and the trit framing of this direction is killed even though
  low-precision inference itself is vindicated.
- **K4 (proxy laundering).** Any public sentence that quotes a §4 proxy
  number as a hardware energy saving kills the claim, retroactively, in
  the same channel it was made. Emulation numbers are emulation
  numbers.
- **K5 (skipping the chain).** The only road from compute joules to
  water runs IT energy → heat rejected → cooling energy → evaporation
  at a stated WUE, at a stated facility. Any statement that skips a
  link — in a post, a pitch, or a headline — is out of charter,
  whatever §4 finds.

---

## 6. What this would make sayable — and what it would not

This charter, by itself, makes **nothing** sayable in public beyond:
*the question has been formulated, with its kills named.* The intended
audience for any eventual public word includes Michigan
decision-makers now weighing data-center water rules; the immediate
context is the outreach to Abdul El-Sayed (Democratic nominee for U.S.
Senate from Michigan; public-health background; general election
November 3, 2026) — noted here in one line, with no promises attached:
the existing draft post to him carries no solution claim, and this
charter changes nothing in it until a landing below is on record.

**If §4 lands positive** (ternary beats the best binary baseline at
fixed accuracy, both proxies, past the K1 margin), the sayable sentence
is exactly this shape and no larger:

> "In a pre-registered software model — labeled a model — ternary-weight
> inference used X% less modeled energy per token than the best binary
> low-precision baseline at matched accuracy. No ternary hardware
> exists yet; this is a reason to build the measurement, not a
> measurement."

**Not sayable after any §4 landing:** that ternary computing "saves the
data centers"; any gallon figure; any percentage applied to a Michigan
facility, the Saline campus, or the Great Lakes; any sentence in which
this program offers a solution to the water problem. Those sentences
require a chain — measured hardware energy, a facility model, a stated
WUE — of which this charter builds not one link.

**If §4 lands negative,** §5 executes: the kill is written, at proof
speed, in the same public register a success would have used. A clean
kill here is a deliverable, not an embarrassment: it is the difference
between a program that formulates and one that advertises.

---

## References

Problem (§1):

- Nature Forward, "Data Centers and Water Use" —
  https://natureforward.org/data-centers-and-water-use/
- FLOW Water Advocates, "Big tech data centers target Michigan's
  resources" —
  https://flowwateradvocates.org/big-tech-data-centers-target-michigans-resources/
- RocTel, "How Much Water Does a Data Center Use? The 2026 Numbers" —
  https://roctelecom.com/insights/data-center-water-usage/
- Uptime Institute, Global Data Center Survey 2025 —
  https://datacenter.uptimeinstitute.com/rs/711-RIA-145/images/2025.Annual.Survey.Report.pdf
- "Global Data Center PUE Stalls at 1.54" (Uptime survey summary) —
  https://mgrid.org/2025/10/01/uptime-institute-data-center-pue-stagnation-2025-liquid-cooling/
- Huawei Digital Power, "Demystifying PUE" —
  https://digitalpower.huawei.com/en/blogs/data-center-power-usage
- Alliance for the Great Lakes, *A Finite Resource* (Aug 2025) —
  https://greatlakes.org/wp-content/uploads/2025/08/AGL_WaterUse_Report_Aug2025_Final.pdf
- DataCenterDynamics, Saline Township settlement —
  https://www.datacenterdynamics.com/en/news/township-in-michigan-settles-lawsuit-allows-data-center-project-to-proceed/
- The Sun Times News, "Saline Township Data Center Draws Attention in
  Michigan Election Debates" —
  https://thesuntimesnews.com/saline-township-data-center-draws-attention-in-michigan-election-debates/
- Data Center Water Tracker, Michigan HB 6138 —
  https://savrn.com/data-center-water-tracker

Hypothesis anchors (§2):

- "Optimal radix choice" —
  https://en.wikipedia.org/wiki/Optimal_radix_choice
- Brian Hayes, "Third Base," *American Scientist* —
  http://web.williams.edu/Mathematics/sjmiller/public_html/105Sp10/addcomments/Hayes_ThirdBase.htm
- "Setun" — https://en.wikipedia.org/wiki/Setun
- Ma et al., "The Era of 1-bit LLMs: All Large Language Models are in
  1.58 Bits," arXiv:2402.17764 — https://arxiv.org/abs/2402.17764 ;
  full text https://arxiv.org/html/2402.17764
- Horowitz, "Computing's Energy Problem (and what we can do about it),"
  ISSCC 2014 —
  https://pages.cs.wisc.edu/~markhill/restricted/isscc2014_horowitz_power_scaling.pdf
- "Landauer's principle" —
  https://en.wikipedia.org/wiki/Landauer%27s_principle
- CNT source-gating ternary transistors, *Science Advances* 2025 —
  https://www.science.org/doi/10.1126/sciadv.adt1909
- CNTFET ternary arithmetic designs (simulation) —
  https://www.sciencedirect.com/science/article/pii/S2772671124000093

Corpus floor (§3): `lean/ThetLogos/TritGrading.lean`,
`lean/ThetLogos/SexagesimalClock.lean`,
`lean/ThetLogos/BridgeLaplacian.lean` — this repository, T1, verified by
inspection 2026-10-17.

---

*End of scoping. Decision left where this house leaves decisions: the
charter is formulated; §4 builds only on a greenlight, at the price
named, under the kills named.*
