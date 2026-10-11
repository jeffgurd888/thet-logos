#!/usr/bin/env python3
"""Causality re-entry lab (T4) — the finite trace engine vs the continuum limit.

Span 5 killed the causal cone on the finite triple via trace-class collapse:
Tr[D,f] = 0 forces PSD i[D,f] to vanish (TwistedTriple.lean `dyn_comm_eq_zero`).
This lab tests whether that engine survives the almost-commutative product.

Continuum fact used: on S^1, [i*d/dx, f] = i*f' (multiplication), so
i[D, f] = -f' is a bounded NONZERO multiplication operator — not trace-class
(its singular values do not decay). We study its N-mode Fourier compression
M_N = P_N * (mult. by cos) * P_N (cos = -(-cos); sign is irrelevant here).

Table 1 — the finite engine fires per truncation:
  Tr_N([D_N, f_N]) = 0 EXACTLY for every N (finite cyclicity), where D_N is
  the N-point spectral i*d/dx (Fourier multiplier conjugated to the position
  basis) and f_N = diag(sin(2*pi*j/N)). This is `trace_comm_eq_zero` alive
  on each lattice truncation.

Table 2 — the engine cannot survive the limit (M_N = compression of the
continuum commutator, i.e. multiplication by cos, to N Fourier modes):
  Tr_N(M_N)       = 0 exactly (diagonal entries vanish: mean(cos) = 0),
  ||M_N||_1 / N   -> (1/2pi)∫|cos| = 2/pi ≈ 0.6366, so ||M_N||_1 ~ 0.6366*N
                    -> infinity: the continuum commutator is NOT trace-class,
                    hence `posSemidef_trace_eq_zero` cannot be invoked;
  ||M_N||_op      -> 1 = ||cos||_inf: bounded and NONZERO in the limit, so
                    the collapse conclusion (PSD => zero) is false;
  Tr_N((M_N)_+)/N -> (1/2pi)∫max(cos,0) = 1/pi ≈ 0.3183: the "PSD mass"
                    persists rather than vanishing.

Conclusion: the finite-trace hypothesis of `causalCone_obstruction`
(`trace_comm_eq_zero` + `posSemidef_trace_eq_zero`, typed over
`Matrix n n C` with `[Fintype n]`) provably fails on the product — the trace
over the manifold factor L^2(M,S) diverges. Tensoring with the finite
32-dim factor only multiplies ||.||_1 by a finite constant; the divergence
is purely manifold-side.

Deterministic (no seeds). numpy only.
"""

import numpy as np

TWO_PI = 2 * np.pi


def commutator_trace(N):
    """Tr_N([D_N, f_N]) with D_N the N-point spectral i*d/dx."""
    m = np.fft.fftfreq(N, d=1.0 / N)  # [0,1,...,N/2-1,-N/2,...,-1]
    Lam = np.diag(-m).astype(complex)      # i*d/dx has eigenvalues -m
    F = np.fft.fft(np.eye(N), norm="ortho")  # unitary DFT
    Dpos = F.conj().T @ Lam @ F            # position-basis Dirac
    j = np.arange(N)
    fpos = np.diag(np.sin(TWO_PI * j / N)).astype(complex)
    return float(abs(np.trace(Dpos @ fpos - fpos @ Dpos)))


def compression(N):
    """M_N = P_N (mult. by cos) P_N as an N x N Toeplitz matrix in the
    Fourier basis e_k, k = -N/2..N/2-1: <k|cos|l> = (d_{k,l+1}+d_{k,l-1})/2.
    (Note: fftfreq(N, d=1/N) already returns the integer mode labels.)"""
    ks = np.fft.fftfreq(N, d=1.0 / N)
    kidx = {k: i for i, k in enumerate(ks)}
    MN = np.zeros((N, N))
    for i, k in enumerate(ks):
        for dk in (1.0, -1.0):
            j = kidx.get(k + dk)
            if j is not None:
                MN[i, j] = 0.5
    return MN


def main():
    Ns = [8, 16, 32, 64, 128, 256]
    print("Table 1: |Tr_N([D_N, f_N])|  (finite cyclicity per truncation)")
    print(f"{'N':>6} {'|Tr[D,f]|':>12}")
    for N in Ns:
        print(f"{N:>6} {commutator_trace(N):>12.2e}")
    print()
    print("Table 2: M_N = compression of continuum commutator (mult. by cos)")
    print(f"{'N':>6} {'Tr(M_N)':>10} {'||M_N||_1/N':>12} {'||M_N||_op':>11} "
          f"{'Tr(M_N+ )/N':>12}")
    for N in Ns:
        MN = compression(N)
        tr = float(np.trace(MN))
        s = np.linalg.svd(MN, compute_uv=False)
        t1 = float(np.sum(s)) / N
        op = float(s[0])
        w = np.linalg.eigvalsh(MN)
        pp = float(np.sum(w[w > 0])) / N
        print(f"{N:>6} {tr:>10.2e} {t1:>12.6f} {op:>11.6f} {pp:>12.6f}")
    print()
    print("Analytic limits: ||M_N||_1/N -> 2/pi   = 0.636620")
    print("                 Tr(M_N+)/N  -> 1/pi   = 0.318310")
    print("                 ||M_N||_op  -> 1")
    print("                 Tr(M_N)      = 0 exactly, all N")
    print()
    print("Verdict: the finite trace engine fires on every finite truncation")
    print("(Table 1: Tr = 0 exactly) but cannot survive the continuum limit")
    print("(Table 2: ||.||_1 diverges linearly, operator norm stays nonzero).")
    print("The trace over the manifold factor is infinite; the obstruction's")
    print("trace-collapse hypothesis provably fails on the product.")


if __name__ == "__main__":
    main()
