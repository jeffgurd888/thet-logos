"""Engine #12 continuum-effective-theory tests: positive gates plus
deliberate-failure (kill) tests for K1-K5, schema validation, regulators,
and trajectory I/O.

Run:  cd ~/workspace/thet-logos/python && python3 -m pytest tests/ -x -q
"""
import numpy as np
import pytest

from thet_logos.engine12_cet import (
    AuditFailureException,
    AuditHarness,
    MetamaterialTargetData,
    SchemaValidationError,
    WetterichFlowEngine,
    calibration_run,
    drude_epsilon,
    lorentz_epsilon,
    point_group_generators,
    run_engine12,
    save_trajectories,
    synthetic_tio2_target,
)

N_OMEGA = 120
W = np.linspace(0.05, 30.0, N_OMEGA)
# K4's quadrature is resolution-limited (see audit_k4_causality docstring):
# K4-involving tests use the validated fine grid.
N_FINE = 400
W_FINE = np.linspace(0.05, 30.0, N_FINE)


def _tensor_from_diag(diag):
    """Build an (N_OMEGA, 3, 3) diagonal tensor from 3 length-N arrays."""
    t = np.zeros((len(W), 3, 3), dtype=complex)
    for a in range(3):
        t[:, a, a] = diag[a]
    return t


# ---------------------------------------------------------------------------
# Schema validation
# ---------------------------------------------------------------------------

def test_schema_accepts_synthetic_target():
    t = synthetic_tio2_target(n_omega=N_OMEGA)
    t.validate()  # must not raise


def test_schema_rejects_non_monotonic_omega():
    t = synthetic_tio2_target(n_omega=N_OMEGA)
    with pytest.raises(SchemaValidationError):
        MetamaterialTargetData(
            omega=t.omega[::-1], epsilon_exp=t.epsilon_exp, mu_exp=t.mu_exp,
            tan_delta_eps=t.tan_delta_eps, tan_delta_mu=t.tan_delta_mu,
            point_group_symmetry="Oh")


def test_schema_rejects_wrong_shape():
    t = synthetic_tio2_target(n_omega=N_OMEGA)
    with pytest.raises(SchemaValidationError):
        MetamaterialTargetData(
            omega=t.omega, epsilon_exp=t.epsilon_exp[:, :, :2],
            mu_exp=t.mu_exp, tan_delta_eps=t.tan_delta_eps,
            tan_delta_mu=t.tan_delta_mu, point_group_symmetry="Oh")


def test_schema_rejects_unknown_point_group():
    t = synthetic_tio2_target(n_omega=N_OMEGA)
    with pytest.raises(SchemaValidationError):
        MetamaterialTargetData(
            omega=t.omega, epsilon_exp=t.epsilon_exp, mu_exp=t.mu_exp,
            tan_delta_eps=t.tan_delta_eps, tan_delta_mu=t.tan_delta_mu,
            point_group_symmetry="C4v")


def test_schema_rejects_negative_loss_tangent():
    t = synthetic_tio2_target(n_omega=N_OMEGA)
    bad_td = t.tan_delta_eps.copy()
    bad_td[0] = -0.5
    with pytest.raises(SchemaValidationError):
        MetamaterialTargetData(
            omega=t.omega, epsilon_exp=t.epsilon_exp, mu_exp=t.mu_exp,
            tan_delta_eps=bad_td, tan_delta_mu=t.tan_delta_mu,
            point_group_symmetry="Oh")


def test_schema_rejects_nan():
    t = synthetic_tio2_target(n_omega=N_OMEGA)
    bad = t.epsilon_exp.copy()
    bad[3, 0, 0] = np.nan
    with pytest.raises(SchemaValidationError):
        MetamaterialTargetData(
            omega=t.omega, epsilon_exp=bad, mu_exp=t.mu_exp,
            tan_delta_eps=t.tan_delta_eps, tan_delta_mu=t.tan_delta_mu,
            point_group_symmetry="Oh")


# ---------------------------------------------------------------------------
# Regulators
# ---------------------------------------------------------------------------

def test_litim_threshold_is_exactly_three():
    eng = WetterichFlowEngine(1970.0, W, 1.0, [(81.0, 0.0, 0.07)],
                              regulator="litim")
    assert eng.threshold == 3.0


def test_exponential_threshold_is_finite_positive():
    eng = WetterichFlowEngine(1970.0, W, 1.0, [(81.0, 0.0, 0.07)],
                              regulator="exponential")
    assert np.isfinite(eng.threshold) and eng.threshold > 0.0


def test_bogus_regulator_rejected():
    with pytest.raises(ValueError):
        WetterichFlowEngine(1970.0, W, 1.0, [(81.0, 0.0, 0.07)],
                            regulator="pauli-villars")


def test_point_group_registry():
    assert len(point_group_generators("Oh")) == 4
    assert len(point_group_generators("D4h")) == 3
    with pytest.raises(SchemaValidationError):
        point_group_generators("C4v")


# ---------------------------------------------------------------------------
# K1-K5 positive gates
# ---------------------------------------------------------------------------

def test_k1_passes_on_structural_zero():
    assert AuditHarness().audit_k1_gauge_invariance(np.zeros(4))


def test_k1_fails_on_nonzero_longitudinal():
    assert not AuditHarness().audit_k1_gauge_invariance(
        np.array([0.0, 1e-6, 0.0, 0.0]))


def test_k2_calibration_passes_both_regulators():
    for reg in ("litim", "exponential"):
        cal = calibration_run(n_omega=N_FINE, n_steps=200, regulator=reg)
        assert cal["resid"] < 1e-6, (reg, cal["resid"])
        assert cal["k4_resid"] < 5e-3, (reg, cal["k4_resid"])


def test_k3_passes_isotropic_vs_oh():
    eps = lorentz_epsilon(W, 5.5, [(25.0, 12.0, 0.4)])
    t = _tensor_from_diag([eps, eps, eps])
    assert AuditHarness().audit_k3_symmetry(t, point_group_generators("Oh"))


def test_k3_passes_uniaxial_vs_d4h():
    exy = lorentz_epsilon(W, 5.0, [(20.0, 10.0, 0.3)])
    ez = lorentz_epsilon(W, 7.0, [(20.0, 10.0, 0.3)])
    t = _tensor_from_diag([exy, exy, ez])
    assert AuditHarness().audit_k3_symmetry(t, point_group_generators("D4h"))


def test_k3_fails_anisotropic_vs_oh():
    e1 = lorentz_epsilon(W, 5.0, [(20.0, 10.0, 0.3)])
    e2 = lorentz_epsilon(W, 6.0, [(20.0, 10.0, 0.3)])
    e3 = lorentz_epsilon(W, 7.0, [(20.0, 10.0, 0.3)])
    t = _tensor_from_diag([e1, e2, e3])
    assert not AuditHarness().audit_k3_symmetry(
        t, point_group_generators("Oh"))


def test_k4_passes_analytic_lorentz():
    eps = lorentz_epsilon(W_FINE, 5.5, [(25.0, 12.0, 0.4), (12.0, 18.0, 0.8)])
    ok, resid = AuditHarness().audit_k4_causality(W_FINE, eps, n_test=8)
    assert ok, resid


def test_k4_passes_analytic_drude():
    eps = drude_epsilon(W_FINE, 81.0, 0.07)
    ok, resid = AuditHarness().audit_k4_causality(W_FINE, eps, n_test=8)
    assert ok, resid


def test_k4_fails_acausal_model():
    # Im = 0 but Re varies: subtracted KK predicts zero variation.
    re = 5.0 + 0.5 * np.sin(W_FINE)
    eps = re + 0.0j * W_FINE
    ok, resid = AuditHarness().audit_k4_causality(W_FINE, eps, n_test=8)
    assert not ok, resid


def test_k4_rejects_underresolved_grid():
    # Coarse grids false-fail: the audit must refuse, not kill.
    eps = drude_epsilon(W, 81.0, 0.07)
    with pytest.raises(ValueError):
        AuditHarness().audit_k4_causality(W, eps)


def test_k5_passes_passive():
    eps = lorentz_epsilon(W, 5.5, [(25.0, 12.0, 0.4)])
    t = _tensor_from_diag([eps, eps, eps])
    mu = _tensor_from_diag([np.ones_like(W)] * 3)
    assert AuditHarness().audit_k5_passivity(t, mu)


def test_k5_fails_gain_medium():
    bad = (5.0 - 0.5j) * np.ones_like(W)
    t = _tensor_from_diag([bad, bad, bad])
    mu = _tensor_from_diag([np.ones_like(W)] * 3)
    assert not AuditHarness().audit_k5_passivity(t, mu)


# ---------------------------------------------------------------------------
# Hard-kill behaviour
# ---------------------------------------------------------------------------

def test_full_audit_raises_on_k5_violation():
    audit = AuditHarness()
    bad = (5.0 - 0.5j) * np.ones(N_FINE)
    t = np.zeros((N_FINE, 3, 3), dtype=complex)
    for a in range(3):
        t[:, a, a] = bad
    mu = np.zeros((N_FINE, 3, 3), dtype=complex)
    for a in range(3):
        mu[:, a, a] = 1.0
    eps = bad
    metrics = dict(longitudinal=np.zeros(2), eps_flow=eps,
                   eps_analytic=eps, eps_tensor=t, mu_tensor=mu,
                   eps_diag=eps, omega=W_FINE,
                   symm_ops=point_group_generators("Oh"))
    with pytest.raises(AuditFailureException):
        audit.execute_full_audit(metrics)


def test_full_audit_raises_without_symmetry_ops():
    # No silent cubic fallback: missing generators must kill, not default.
    audit = AuditHarness()
    eps = lorentz_epsilon(W, 5.5, [(25.0, 12.0, 0.4)])
    t = _tensor_from_diag([eps, eps, eps])
    mu = _tensor_from_diag([np.ones(N_OMEGA)] * 3)
    metrics = dict(longitudinal=np.zeros(2), eps_flow=eps,
                   eps_analytic=eps, eps_tensor=t, mu_tensor=mu,
                   eps_diag=eps, omega=W, symm_ops=None)
    with pytest.raises(AuditFailureException):
        audit.execute_full_audit(metrics)


def test_regulator_stability_audit():
    # The measured IR regulator dependence must match the threshold-number
    # prediction |T_exp - T_lit|/T_lit: this verifies the regulator enters
    # the flow exactly through the documented threshold number.
    cal_l = calibration_run(n_omega=N_FINE, n_steps=200, regulator="litim")
    cal_e = calibration_run(n_omega=N_FINE, n_steps=200,
                            regulator="exponential")
    resid = AuditHarness().audit_regulator_stability(
        cal_l["eps_flow"], cal_e["eps_flow"])
    predicted = abs(cal_e["engine"].threshold
                    - cal_l["engine"].threshold) / cal_l["engine"].threshold
    assert abs(resid - predicted) < 1e-3, (resid, predicted)
    assert resid > 0.0  # nonzero dependence is the honest expectation


# ---------------------------------------------------------------------------
# Trajectories
# ---------------------------------------------------------------------------

def test_trajectory_save_and_load(tmp_path):
    eng = WetterichFlowEngine(1970.0, W_FINE, 5.5,
                              [(25.0, 12.0, 0.4), (12.0, 18.0, 0.8)])
    _, logs = eng.flow_to(12.4, n_steps=200, audit=AuditHarness())
    assert len(logs) == 200
    p = str(tmp_path / "traj.npz")
    save_trajectories(p, logs, eng)
    d = np.load(p, allow_pickle=True)
    assert d["k"].shape == (200,)
    assert d["f"].shape == (200, 2)
    assert d["eps_diag"].shape == (200, N_FINE)
    assert str(d["regulator"]) == "litim"
    # k strictly decreasing along the trajectory
    assert np.all(np.diff(d["k"]) < 0)


def test_target_run_passes_all_gates():
    out = run_engine12(n_steps=200)
    r = out["residuals"]
    assert r["k2"] < 1e-6
    assert r["k4"] < 5e-3
    assert r["k5"] == 0.0
    assert out["steps"] == 200
