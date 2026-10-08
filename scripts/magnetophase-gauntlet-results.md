# Magnetophase gauntlet — claim-2 extension test (T4)

Question: does `phi_{beta,A} = i[K_A, D_A] = 0` survive GENERAL (non-rho-real, non-structured, large, non-Hermitian) 1-forms?

- grid max ||phi||_F (abs): 2.276e-07
- grid max ||phi||_F (rel to beta*||D_A^2||*||D_A||): 1.580e-16
- Hermitian-D_A cases max: 0.000e+00
- non-Hermitian-D_A cases max: 2.276e-07

## (a) Dropping the Hermitian projection

The no-go does NOT break: [K_A, D_A] = 0 is a polynomial identity (K_A = f(D_A^2)) valid for ANY matrix D_A, Hermitian or not. What breaks is the STATE machinery:
- struct_noproj r=0.05: herm_resid(D_A)=1.03e+02; H=D_A^2 herm resid 2.24e+03, max|Im eig(H)|=5.59e+02, min Re eig(H)=-5.46e+02. eigh(H) is invalid input; rho = e^{-beta H}/Z is not a state (not positive/trace-1); entropy is complex/meaningless; the KMS derivation (unitary H-flow) is dead. Flux itself: 0.000e+00 — still zero by algebra.
- struct_noproj r=0.2: herm_resid(D_A)=4.14e+02; H=D_A^2 herm resid 3.58e+04, max|Im eig(H)|=8.94e+03, min Re eig(H)=-8.83e+03. eigh(H) is invalid input; rho = e^{-beta H}/Z is not a state (not positive/trace-1); entropy is complex/meaningless; the KMS derivation (unitary H-flow) is dead. Flux itself: 0.000e+00 — still zero by algebra.
- struct_noproj r=0.5: herm_resid(D_A)=1.03e+03; H=D_A^2 herm resid 2.24e+05, max|Im eig(H)|=5.59e+04, min Re eig(H)=-5.52e+04. eigh(H) is invalid input; rho = e^{-beta H}/Z is not a state (not positive/trace-1); entropy is complex/meaningless; the KMS derivation (unitary H-flow) is dead. Flux itself: 0.000e+00 — still zero by algebra.
- genAH_noproj r=0.05: herm_resid(D_A)=1.14e+02; H=D_A^2 herm resid 2.15e+04, max|Im eig(H)|=2.41e+03, min Re eig(H)=-1.53e+02. eigh(H) is invalid input; rho = e^{-beta H}/Z is not a state (not positive/trace-1); entropy is complex/meaningless; the KMS derivation (unitary H-flow) is dead. Flux itself: 2.276e-08 — still zero by algebra.
- genAH_noproj r=0.2: herm_resid(D_A)=4.56e+02; H=D_A^2 herm resid 8.62e+04, max|Im eig(H)|=9.44e+03, min Re eig(H)=-3.13e+03. eigh(H) is invalid input; rho = e^{-beta H}/Z is not a state (not positive/trace-1); entropy is complex/meaningless; the KMS derivation (unitary H-flow) is dead. Flux itself: 1.321e-08 — still zero by algebra.
- genAH_noproj r=0.5: herm_resid(D_A)=1.14e+03; H=D_A^2 herm resid 2.15e+05, max|Im eig(H)|=2.27e+04, min Re eig(H)=-2.17e+04. eigh(H) is invalid input; rho = e^{-beta H}/Z is not a state (not positive/trace-1); entropy is complex/meaningless; the KMS derivation (unitary H-flow) is dead. Flux itself: 1.583e-08 — still zero by algebra.
- nonAH_noproj r=0.05: herm_resid(D_A)=7.78e+01; H=D_A^2 herm resid 1.49e+04, max|Im eig(H)|=2.02e+03, min Re eig(H)=-2.17e+01. eigh(H) is invalid input; rho = e^{-beta H}/Z is not a state (not positive/trace-1); entropy is complex/meaningless; the KMS derivation (unitary H-flow) is dead. Flux itself: 1.866e-08 — still zero by algebra.
- nonAH_noproj r=0.2: herm_resid(D_A)=3.11e+02; H=D_A^2 herm resid 6.07e+04, max|Im eig(H)|=8.13e+03, min Re eig(H)=-6.01e+02. eigh(H) is invalid input; rho = e^{-beta H}/Z is not a state (not positive/trace-1); entropy is complex/meaningless; the KMS derivation (unitary H-flow) is dead. Flux itself: 1.785e-08 — still zero by algebra.
- nonAH_noproj r=0.5: herm_resid(D_A)=7.78e+02; H=D_A^2 herm resid 1.67e+05, max|Im eig(H)|=2.12e+04, min Re eig(H)=-3.89e+03. eigh(H) is invalid input; rho = e^{-beta H}/Z is not a state (not positive/trace-1); entropy is complex/meaningless; the KMS derivation (unitary H-flow) is dead. Flux itself: 1.549e-08 — still zero by algebra.

Mechanism: the lab's projection masks non-Hermiticity of D_A, not a flux effect. Theorem boundary = Hermiticity of D_A is needed for the *equilibrium-state* reading (T1 `thermal_flux_vanishes` assumes a self-adjoint Dirac); the *algebraic* commutator zero needs nothing.

## (b) Non-rho-real A1

- genAH (fully random anti-Hermitian, projected): worst flux 0.000e+00; rho-reality defect 1.390 (far from rho-real). Flux still zero: the proof only uses K_A = f(D_A^2).

## (c) Large fluctuations

- Ratios 0.05/0.2/0.5: relative residual stays ~1e-16 across all classes and beta in {0.1, 1, 10} — no numerical breakdown of the analytic identity; absolute residual scales as eps*beta*||D_A||^3 as expected.

## KMS at own beta (sample, Hermitian cases)

- struct r=0.2 beta=1.0: KMS resid 7.77e-16, S=1.3863 nats
- struct r=0.2 beta=10.0: KMS resid 8.88e-16, S=1.3863 nats
- struct r=0.5 beta=1.0: KMS resid 7.77e-16, S=1.3863 nats
- struct r=0.5 beta=10.0: KMS resid 8.88e-16, S=1.3863 nats
- genAH r=0.2 beta=1.0: KMS resid 0.00e+00, S=1.4029 nats
- genAH r=0.2 beta=10.0: KMS resid 8.88e-16, S=1.3863 nats
- genAH r=0.5 beta=1.0: KMS resid 0.00e+00, S=1.4029 nats
- genAH r=0.5 beta=10.0: KMS resid 8.88e-16, S=1.3863 nats

## Verdict

Claim-2 extension HOLDS across the wider class: with the analytic K_A, flux is identically zero for every tested 1-form (structured, random anti-Hermitian, fully random complex), with or without the Hermitian projection, at ||A1||/||D|| up to 0.5. The theorem's real boundary is Hermiticity of D_A: without it the Gibbs *state* (and hence entropy/KMS) is undefined, while the commutator stays zero. No case with flux != 0 found; nothing to add to the kill ledger.
