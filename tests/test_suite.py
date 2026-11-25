"""Comprehensive 76-test suite for OMEGA94-LB-CERT-1.0.

Includes:
  - 1 aggregate canonical 16-certificate replay,
  - 3 raw-JSON zero-float / NaN / duplicate-key parser tests,
  - 2 exact arithmetic soundness regressions (exhaustive Tag(1,1) & tripod balanced peak),
  - 70 parametrized live adversarial forgery tests (12 schema/parser, 14 Mode 1,
    16 Mode 2, 14 Mode 3, 14 Mode 4), each asserting an exact regex match on its
    intended CertificateError branch — including the symbolic Mode 2 single-direction
    q=1 cheat and the Mode 4 forged zero-column-sum star matrix exploits.
"""

from __future__ import annotations

import copy
from fractions import Fraction
import json
from pathlib import Path
import pytest

from src.omega94_lb_certifier import (
    PROTOCOL_ID,
    verify_certificate_dict,
    verify_certificate_file,
    verify_certificate_str,
)
from src.omega94_lb_exact import (
    CertificateError,
    border_rank_lb_square,
    eval_tag_via_two_dw,
    frac_div,
    tripod_d_star,
)

ROOT = Path(__file__).resolve().parent.parent
CERT_DIR = ROOT / "certificates"


def _load(name: str) -> dict:
    return json.loads((CERT_DIR / f"{name}.cert.json").read_text(encoding="utf-8"))


def test_all_16_canonical_certificates_verify() -> None:
    files = sorted(CERT_DIR.glob("*.cert.json"))
    assert len(files) == 16
    for f in files:
        res = verify_certificate_file(f)
        assert res["protocol"] == PROTOCOL_ID


def test_raw_json_rejects_float_literal() -> None:
    raw = '{"protocol": "OMEGA94-LB-CERT-1.0", "certificate_id": "x", "mode": "rank_gate_and_tight_support_cert", "payload": {"n": 2.25}}'
    with pytest.raises(CertificateError, match="Floating-point literal rejected"):
        verify_certificate_str(raw)


def test_raw_json_rejects_nan_constant() -> None:
    raw = '{"protocol": "OMEGA94-LB-CERT-1.0", "certificate_id": "x", "mode": "rank_gate_and_tight_support_cert", "payload": {"n": NaN}}'
    with pytest.raises(CertificateError, match="Non-standard JSON constant rejected"):
        verify_certificate_str(raw)


def test_raw_json_rejects_duplicate_keys() -> None:
    raw = '{"protocol": "OMEGA94-LB-CERT-1.0", "protocol": "OMEGA94-LB-CERT-1.0"}'
    with pytest.raises(CertificateError, match="Duplicate JSON key rejected"):
        verify_certificate_str(raw)


def test_regression_tag_h1_exhaustive_64_inputs() -> None:
    for t0 in range(2):
        for t1 in range(2):
            for x0 in range(2):
                for x1 in range(2):
                    for y0 in range(2):
                        for y1 in range(2):
                            dw1, ssum, direct = eval_tag_via_two_dw([t0, t1], [x0, x1], [y0, y1], 1)
                            assert dw1 * ssum == direct


def test_regression_tripod_peak_and_sun_refutation() -> None:
    assert border_rank_lb_square(256) == 262144 > 131072
    ds_bal = tripod_d_star(Fraction(1), Fraction(1), Fraction(1))
    assert frac_div(Fraction(6), ds_bal) == Fraction(9, 4)
    ds_unbal = tripod_d_star(Fraction(1), Fraction(2), Fraction(3))
    assert frac_div(Fraction(12), ds_unbal) < Fraction(9, 4)


def _mutate_m2_q1_cheat(c: dict) -> None:
    """Build a fake q=1 single-direction cheat circuit for 2x2 MM over F_257."""
    c["payload"]["A0"] = [1, 0, 0, 1]
    c["payload"]["B0"] = [1, 0, 0, 1]
    # Wires 0..3 = A0 + u*X, wires 4..7 = B0 + v*Y
    # Fake circuit computes only ONE nonscalar product a00*b00 and reuses it on all outputs
    c["payload"]["gates"] = [
        {"op": "mul", "lhs": 0, "rhs": 4},  # wire 8: single nonscalar mul
    ]
    c["payload"]["output_wire_indices"] = [8, 8, 8, 8]
    c["payload"]["claimed_nonscalar_count"] = 1
    c["payload"]["claimed_rank_upper_bound"] = 2


def _build_70_forgeries() -> list[tuple[str, dict, str]]:
    m1 = _load("m1_bounds_n16_rect4x4x4")
    m2 = _load("m2_dual_strassen_div_2x2_f257")
    m3 = _load("m3_tag_h2_valid_and_collisions")
    m4 = _load("m4_tripod_balanced_unit_1_1_1")

    cases: list[tuple[str, dict, str]] = []

    def add(name: str, base: dict, mutator, regex: str) -> None:
        c = copy.deepcopy(base)
        mutator(c)
        cases.append((name, c, regex))

    # --- Schema / Top-Level (12) ---
    add("S01_bad_protocol", m1, lambda c: c.__setitem__("protocol", "FAKE-1.0"), "Unsupported protocol")
    add("S02_empty_cert_id", m1, lambda c: c.__setitem__("certificate_id", ""), "non-empty string")
    add("S03_unknown_mode", m1, lambda c: c.__setitem__("mode", "bogus_mode"), "Unknown certificate mode")
    add("S04_extra_top_key", m1, lambda c: c.__setitem__("rogue", 1), "Unexpected top-level keys")
    add("S05_bad_description", m1, lambda c: c.__setitem__("description", 99), "Optional field 'description' must be a string")
    add("S06_bad_note", m1, lambda c: c.__setitem__("note", False), "Optional field 'note' must be a string")
    add("S07_payload_not_obj", m1, lambda c: c.__setitem__("payload", "bad"), "must be a JSON object")
    add("S08_missing_protocol", m1, lambda c: c.pop("protocol"), "Missing required string field 'protocol'")
    add("S09_bool_as_int", m1, lambda c: c["payload"].__setitem__("n_square", True), "must be an exact integer")
    add("S10_float_in_dict", m1, lambda c: c["payload"].__setitem__("tight_B", 5.0), "must be an exact integer")
    add("S11_missing_key", m1, lambda c: c["payload"].pop("gate_lb"), "Missing keys in Mode 1 payload")
    add("S12_extra_key", m1, lambda c: c["payload"].__setitem__("extra", 1), "Unexpected keys in Mode 1 payload")

    # --- Mode 1 Forgeries (14) ---
    add("M1_01_n_too_small", m1, lambda c: c["payload"].__setitem__("n_square", 1), "n_square must lie in")
    add("M1_02_n_too_large", m1, lambda c: c["payload"].__setitem__("n_square", 50000), "n_square must lie in")
    add("M1_03_wrong_br_lb", m1, lambda c: c["payload"].__setitem__("border_rank_lb", c["payload"]["border_rank_lb"] - 1), "disagrees with exact ceil")
    add("M1_04_wrong_br_lb_hi", m1, lambda c: c["payload"].__setitem__("border_rank_lb", c["payload"]["border_rank_lb"] + 1), "disagrees with exact ceil")
    add("M1_05_wrong_gate_lb", m1, lambda c: c["payload"].__setitem__("gate_lb", c["payload"]["gate_lb"] - 1), "disagrees with exact ceil")
    add("M1_06_rect_bad_len", m1, lambda c: c["payload"].__setitem__("rect_dims", [4, 4]), "list of length in \\[3, 3\\]")
    add("M1_07_rect_zero_dim", m1, lambda c: c["payload"].__setitem__("rect_dims", [4, 0, 4]), "rect_dims must lie in")
    add("M1_08_wrong_rect_lb", m1, lambda c: c["payload"].__setitem__("rect_rank_lb", 15), "disagrees with Corollary 1.3")
    add("M1_09_tight_n_too_big", m1, lambda c: c["payload"].__setitem__("tight_n", 20), "tight_n must lie in")
    add("M1_10_tight_B_too_small", m1, lambda c: c["payload"].__setitem__("tight_B", 4), "tight_n < B <= 10000")
    add("M1_11_sun_n_invalid", m1, lambda c: c["payload"].__setitem__("sun_check_n", 1), "Invalid Sun conflict")
    add("M1_12_sun_not_refuted", m1, lambda c: c["payload"].__setitem__("sun_proposed_ub", 262144), "not strictly below Corollary 1.2")
    add("M1_13_sun_ub_zero", m1, lambda c: c["payload"].__setitem__("sun_proposed_ub", 0), "Invalid Sun conflict")
    add("M1_14_tight_B_dos_cap", m1, lambda c: c["payload"].__setitem__("tight_B", 100000), "tight_n < B <= 10000")

    # --- Mode 2 Forgeries (16) ---
    add("M2_01_composite_p", m2, lambda c: c["payload"].__setitem__("prime_p", 15), "prime modulus p")
    add("M2_02_tiny_p", m2, lambda c: c["payload"].__setitem__("prime_p", 3), "prime modulus p")
    add("M2_03_bad_side_s", m2, lambda c: c["payload"].__setitem__("side_s", 5), "matrix side s")
    add("M2_04_bad_A0_len", m2, lambda c: c["payload"]["A0"].pop(), "list of length in \\[4, 4\\]")
    add("M2_05_empty_gates", m2, lambda c: c["payload"].__setitem__("gates", []), "1\\.\\.256 arithmetic circuit gates")
    add("M2_06_bad_gate_op", m2, lambda c: c["payload"]["gates"][0].__setitem__("op", "xor"), "Unsupported gate op")
    add("M2_07_gate_wire_oob", m2, lambda c: c["payload"]["gates"][0].__setitem__("lhs", 999), "wire index out of range")
    add("M2_08_div_by_zero_base", m2, lambda c: (c["payload"]["A0"].__setitem__(0, 0), c["payload"]["B0"].__setitem__(3, 256)), "Division by non-unit")
    add("M2_09_wrong_nonscalar_cnt", m2, lambda c: c["payload"].__setitem__("claimed_nonscalar_count", 7), "Claimed nonscalar gate count")
    add("M2_10_wrong_rank_ub", m2, lambda c: c["payload"].__setitem__("claimed_rank_upper_bound", 15), "Claimed Lemma 2.4 rank upper bound")
    add("M2_11_wrong_output_wire", m2, lambda c: c["payload"]["output_wire_indices"].__setitem__(0, 0), "Output entry \\(0,0\\) symbolic dual expansion")
    add("M2_12_output_wire_oob", m2, lambda c: c["payload"]["output_wire_indices"].__setitem__(0, 999), "Output wire index out of range")
    add("M2_13_corrupted_gate_op", m2, lambda c: c["payload"]["gates"][-1].__setitem__("op", "sub"), "symbolic dual expansion")
    add("M2_14_single_dir_q1_cheat", m2, _mutate_m2_q1_cheat, "symbolic dual expansion")
    add("M2_15_noncanonical_A0", m2, lambda c: c["payload"]["A0"].__setitem__(0, 257), "outside canonical range")
    add("M2_16_noncanonical_const", m2, lambda c: c["payload"]["gates"][17].__setitem__("val", -1), "outside canonical range")

    # --- Mode 3 Forgeries (14) ---
    add("M3_01_h_bits_zero", m3, lambda c: c["payload"].__setitem__("h_bits", 0), "h_bits in \\[1, 3\\]")
    add("M3_02_h_bits_dos", m3, lambda c: c["payload"].__setitem__("h_bits", 10), "h_bits in \\[1, 3\\]")
    add("M3_03_empty_instances", m3, lambda c: c["payload"].__setitem__("instances", []), "1\\.\\.16 tagged-permutation")
    add("M3_04_inst_not_obj", m3, lambda c: c["payload"]["instances"].__setitem__(0, [1, 2]), "must be a JSON object")
    add("M3_05_inst_missing_key", m3, lambda c: c["payload"]["instances"][0].pop("tags"), "Missing keys in instances\\[0\\]")
    add("M3_06_tags_wrong_len", m3, lambda c: c["payload"]["instances"][0]["tags"].pop(), "list of length in \\[4, 4\\]")
    add("M3_07_tag_oob", m3, lambda c: c["payload"]["instances"][0]["tags"].__setitem__(0, 9), "out of range")
    add("M3_08_x_oob", m3, lambda c: c["payload"]["instances"][0]["x_payloads"].__setitem__(0, -1), "out of range")
    add("M3_09_y_oob", m3, lambda c: c["payload"]["instances"][0]["y_payloads"].__setitem__(0, 4), "out of range")
    add("M3_10_bad_exp_val", m3, lambda c: c["payload"]["instances"][0].__setitem__("expected_tag", 2), "expected_tag must be 0 or 1")
    add("M3_11_flipped_valid_tag", m3, lambda c: c["payload"]["instances"][0].__setitem__("expected_tag", 0), "expected_tag=0 != exact 1")
    add("M3_12_flipped_bad_payload", m3, lambda c: c["payload"]["instances"][2].__setitem__("expected_tag", 1), "expected_tag=1 != exact 0")
    add("M3_13_flipped_bad_perm", m3, lambda c: c["payload"]["instances"][3].__setitem__("expected_tag", 1), "expected_tag=1 != exact 0")
    add("M3_14_extra_inst_key", m3, lambda c: c["payload"]["instances"][0].__setitem__("rogue", 0), "Unexpected keys in instances\\[0\\]")

    # --- Mode 4 Forgeries (14) ---
    add("M4_01_star_wrong_rows", m4, lambda c: c["payload"]["star_slope_matrix"].pop(), "must have 5 arm rows")
    add("M4_02_star_wrong_cols", m4, lambda c: c["payload"]["star_slope_matrix"][0].pop(), "must have 4 site columns")
    add("M4_03_star_nonharmonic", m4, lambda c: c["payload"]["star_slope_matrix"][4].__setitem__(3, -3), "not harmonic")
    add("M4_04_star_bad_collision", m4, lambda c: (c["payload"]["star_slope_matrix"][0].__setitem__(0, 0), c["payload"]["star_slope_matrix"][3].__setitem__(0, 2)), "exact Figure 4 harmonic arm structure")
    add("M4_05_arms_wrong_len", m4, lambda c: c["payload"]["tripod_arms"].pop(), "3 \\[num, den\\] positive rationals")
    add("M4_06_arm_zero", m4, lambda c: c["payload"]["tripod_arms"].__setitem__(0, [0, 1]), "must be a positive rational")
    add("M4_07_arm_neg_den", m4, lambda c: c["payload"]["tripod_arms"].__setitem__(0, [1, -2]), "must be a positive rational")
    add("M4_08_wrong_D_star", m4, lambda c: c["payload"].__setitem__("claimed_D_star", [9, 3]), "claimed_D_star")
    add("M4_09_wrong_perimeter", m4, lambda c: c["payload"].__setitem__("claimed_perimeter", [7, 1]), "claimed_perimeter")
    add("M4_10_wrong_ratio", m4, lambda c: c["payload"].__setitem__("claimed_exponent_ratio", [2, 1]), "claimed_exponent_ratio")
    add("M4_11_wrong_amhm_margin", m4, lambda c: c["payload"].__setitem__("am_hm_margin", [1, 9]), "am_hm_margin")
    add("M4_12_asym_b_zero", m4, lambda c: c["payload"].__setitem__("asymptotic_b", 0), "asymptotic_b must lie in")
    add("M4_13_wrong_asym_D", m4, lambda c: c["payload"].__setitem__("claimed_asymptotic_D_star", [1, 1]), "claimed_asymptotic_D_star")
    add(
        "M4_14_star_forged_zero_colsum",
        m4,
        lambda c: c["payload"].__setitem__(
            "star_slope_matrix",
            [[100, -100, 0, 3], [-101, 99, 0, 0], [0, 0, -1, 0], [1, 1, 1, -3], [0, 0, 0, 0]],
        ),
        "exact Figure 4 harmonic arm structure",
    )

    assert len(cases) == 70
    return cases


FORGERIES = _build_70_forgeries()


@pytest.mark.parametrize("name,cert,expected_regex", FORGERIES, ids=[c[0] for c in FORGERIES])
def test_adversarial_forgery_rejected(name: str, cert: dict, expected_regex: str) -> None:
    with pytest.raises(CertificateError, match=expected_regex):
        verify_certificate_dict(cert)
