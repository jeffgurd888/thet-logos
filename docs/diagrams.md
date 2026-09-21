# Diagrams

## The 10-rung chromatic ladder (organizational device)

```mermaid
flowchart TB
    R1["Rung 1 · Void ∅ · BLACK · T1"]
    R2["Rung 2 · Distinction ⟨a,b,c⟩=ab†c · COBALT · T2/T3"]
    R3["Rung 3 · Thet Primitive Θ=(θ,θ†) · PURPLE · T1"]
    R4["Rung 4 · LOGOS Engine K=−log ∆ · CRIMSON · T2/T3"]
    R5["Rung 5 · Tripotent Variety N₀³=N₀ · AMBER · T1/T5 withdrawn"]
    R6["Rung 6 · 32-State Spectrum H_F=ℂ³² · MAGENTA · T2/T3"]
    R7["Rung 7 · Spectral Triple D_F · CYAN · T2/T3"]
    R8["Rung 8 · Order Conditions · EMERALD · T3/T4"]
    R9["Rung 9 · Thet Engine ∆gap · INDIGO · T3 sim"]
    R10["Rung 10 · Epistemic Ledger · WHITE · meta"]
    R1 --> R2 --> R3 --> R4 --> R5 --> R6 --> R7 --> R8 --> R9 --> R10
    R6 -.->|"return loop<br/>(diagrammatic only)"| R4
```

> The ladder is an organizational/mnemonic device, not a formalized
> Möbius-bundle construction (Framework §2).

## The 32-state block structure

```mermaid
flowchart LR
    subgraph HF["H_F = ℂ³²"]
        HL["H_L · 0–7<br/>lepton 2 ⊕ quark 6"]
        HR["H_R · 8–15<br/>lepton 2 ⊕ quark 6"]
        HLc["H_L^c · 16–23<br/>anti-lepton 2 ⊕ anti-quark 6"]
        HRc["H_R^c · 24–31<br/>anti-lepton 2 ⊕ anti-quark 6"]
    end
    HL <-->|"p(k) = k ± 16"| HLc
    HR <-->|"J_F"| HRc
```

## D_F block matrix (Framework eq. 2)

```mermaid
flowchart TB
    subgraph DF["D_F : 32×32, self-adjoint, γ_F-odd"]
        direction LR
        A["A : H_L ↔ H_R<br/>Yukawa block"]
        B["B : H_L^c ↔ H_R^c<br/>conjugate block"]
        C["C : H_L ↔ H_L^c<br/>Majorana-type → 0"]
        E["E : H_R ↔ H_R^c<br/>Majorana-type → 0"]
    end
    DF -->|"order-one [[D,π],π°]=0"| Z["C = E = 0<br/>Yukawa form T4"]
```

## Order-zero vs order-one

```mermaid
flowchart LR
    pi["π(a)<br/>support: indices < 16"]
    piO["π°(b) = Jπ(b)*J⁻¹<br/>support: indices ≥ 16"]
    pi ---|"T3: [π(a), π°(b)] = 0<br/>disjoint support"| piO
    D["D_F"]
    D -->|"T4: [[D_F,π(a)],π°(b)]=0<br/>forces C,E → 0"| Y["Y_u Y_d Y_e Y_ν, Y_R"]
```

## Epistemic flow

```mermaid
flowchart LR
    T1["T1<br/>Assumed Primitives"]
    T2["T2<br/>Defined Operations"]
    T3["T3<br/>Proved / Checked"]
    T4["T4<br/>Emergent / Standard"]
    T5["T5<br/>Open / Withdrawn"]
    T1 --> T2 --> T3 --> T4
    T3 -.->|"failed / retracted"| T5
    note["Theorem ≠ Simulation ≠ Experiment ≠ Device"]
```

## Repository map

```mermaid
flowchart TB
    subgraph repo["thet-logos/"]
        ax["axioms/"]
        al["algebra/"]
        sp["spectral/"]
        ch["chromatic/"]
        ln["lean/ · ThetLogos"]
        py["python/ · thet_logos"]
        dc["docs/"]
        el["epistemic-ledger/"]
        ex["examples/"]
    end
    ax --> al --> sp --> ch
    sp --> ln
    sp --> py
    py --> ex
    ch --> el
    ln -.->|"tier labels"| el
    py -.->|"tier labels"| el
```
