"""Tests for the finite thermal-flow probe (T4)."""
import numpy as np

from thet_logos.finite_thermal_flow import (
    VEV, Y_PHYS, build_H, sector_bases, sector_response, orthonormalize,
    gibbs_K, sanity_gibbs, verify_linearity, democratic_Y, shuffled_Y,
    all_responses,
)


def test_u1_exactly_inert():
    H = build_H(Y_PHYS)
    secs = sector_bases()
    g = sector_response(H, secs["u1"][0])
    assert g < 1e-9, f"u(1) must be exactly inert (diagonal in mass basis), got {g}"


def test_su3_embedding_artifact():
    secs = sector_bases()
    assert secs["su3"][1] is True, "su3 must carry the artifact flag"
    assert secs["_su3_max_entry"] == 0.0, "pi must kill every M_3(C) generator"
    H = build_H(Y_PHYS)
    assert sector_response(H, secs["su3"][0]) == 0.0


def test_su2_equals_doublet_mass_splitting():
    # analytic: orthonormal basis {i_m, j, k}/sqrt(2) on indices 0-1;
    # only j, k contribute, each giving |Ynu^2 - Ye^2| v^2.
    H = build_H(Y_PHYS)
    secs = sector_bases()
    g = sector_response(H, secs["su2"][0])
    pred = abs(Y_PHYS["Ynu"]**2 - Y_PHYS["Ye"]**2) * VEV**2
    assert abs(g - pred) < 1e-9 * max(pred, 1e-12), (g, pred)


def test_democratic_yukawas_all_inert():
    H = build_H(democratic_Y())
    r = all_responses(H)
    for name in ("u1", "su2", "su3"):
        assert r[name]["g_GeV2"] < 1e-9, (name, r[name]["g_GeV2"])


def test_shuffle_tracks_mass_splitting():
    H0 = build_H(Y_PHYS)
    for sd in (11, 22, 33):
        Y = shuffled_Y(sd)
        H = build_H(Y)
        secs = sector_bases()
        g = sector_response(H, secs["su2"][0])
        pred = abs(Y["Ynu"]**2 - Y["Ye"]**2) * VEV**2
        assert abs(g - pred) < 1e-9 * max(pred, 1e-12), (sd, g, pred)


def test_linearity_exact():
    H = build_H(Y_PHYS)
    assert verify_linearity(H, 1e-4) < 1e-6
    assert verify_linearity(H, 1.0) < 1e-6


def test_gibbs_flow_sanity():
    H = build_H(Y_PHYS)
    s = sanity_gibbs(H, 1e-4)
    assert s["group"] < 1e-8, s
    assert s["stationarity"] < 1e-8, s
    assert s["kms"] < 1e-6, s


def test_orthonormalize_drops_nulls():
    Z = [np.zeros((32, 32), complex)]
    assert orthonormalize(Z) == []
