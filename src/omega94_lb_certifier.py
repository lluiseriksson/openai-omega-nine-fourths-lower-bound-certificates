"""Zero-float 4-mode certificate auditor for OMEGA94-LB-CERT-1.0.

Strictly parses JSON without floats (rejecting IEEE-754 decimals, NaN/Infinity,
and duplicate keys via object_pairs_hook) and verifies four canonical modes
aligned with OpenAI's November 24, 2026 matching lower bound omega_F = 9/4:
  1. rank_gate_and_tight_support_cert      (Corollaries 1.2, 1.3 & Section 2.4)
  2. dual_number_bilinearization_cert      (Lemma 2.4 over F_p[X, Y][u, v]/(u^2, v^2))
  3. tagged_perm_two_dw_reduction_cert     (Section 4.1 Tag(h, h) -> 2 D_w tests)
  4. tripod_harmonic_and_amhm_rigidity_cert (Sections 7.4, 8.2, 11.3 & Cor. 11.1)

NO floating-point operations or true division '/' on ints appear anywhere in this module.
"""

from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
from typing import Any, Dict, List, Mapping, Sequence, Tuple

from src.omega94_lb_exact import (
    CertificateError,
    SymDual,
    border_rank_lb_square,
    eval_tag_via_two_dw,
    frac_div,
    gate_lb_square,
    rect_border_rank_lb,
    sym_dual_add,
    sym_dual_const,
    sym_dual_div,
    sym_dual_is_nonconst,
    sym_dual_mul,
    sym_dual_sub,
    tripod_d_star,
)

PROTOCOL_ID = "OMEGA94-LB-CERT-1.0"
VALID_MODES = frozenset(
    {
        "rank_gate_and_tight_support_cert",
        "dual_number_bilinearization_cert",
        "tagged_perm_two_dw_reduction_cert",
        "tripod_harmonic_and_amhm_rigidity_cert",
    }
)


def _reject_float(val: str) -> Any:
    raise CertificateError(f"Floating-point literal rejected by zero-float policy: {val!r}")


def _reject_constant(val: str) -> Any:
    raise CertificateError(f"Non-standard JSON constant rejected: {val!r}")


def _no_duplicate_keys(pairs: List[Tuple[str, Any]]) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise CertificateError(f"Duplicate JSON key rejected: {k!r}")
        out[k] = v
    return out


def load_strict_json_str(raw: str) -> Dict[str, Any]:
    try:
        data = json.loads(
            raw,
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            object_pairs_hook=_no_duplicate_keys,
        )
    except CertificateError:
        raise
    except Exception as exc:
        raise CertificateError(f"Malformed JSON: {exc}") from exc
    if not isinstance(data, dict):
        raise CertificateError("Top-level certificate payload must be a JSON object")
    return data


def _req_int(obj: Mapping[str, Any], key: str) -> int:
    if key not in obj:
        raise CertificateError(f"Missing required integer field {key!r}")
    v = obj[key]
    if isinstance(v, bool) or not isinstance(v, int):
        raise CertificateError(f"Field {key!r} must be an exact integer")
    return v


def _req_str(obj: Mapping[str, Any], key: str) -> str:
    if key not in obj:
        raise CertificateError(f"Missing required string field {key!r}")
    v = obj[key]
    if not isinstance(v, str) or not v:
        raise CertificateError(f"Field {key!r} must be a non-empty string")
    return v


def _req_int_list(obj: Mapping[str, Any], key: str, min_len: int = 1, max_len: int = 64) -> List[int]:
    if key not in obj:
        raise CertificateError(f"Missing required integer list {key!r}")
    v = obj[key]
    if not isinstance(v, list) or not (min_len <= len(v) <= max_len):
        raise CertificateError(f"Field {key!r} must be a list of length in [{min_len}, {max_len}]")
    out: List[int] = []
    for item in v:
        if isinstance(item, bool) or not isinstance(item, int):
            raise CertificateError(f"Field {key!r} contains non-integer entry")
        out.append(item)
    return out


def _req_frac(obj: Mapping[str, Any], key: str) -> Fraction:
    pair = _req_int_list(obj, key, min_len=2, max_len=2)
    if pair[1] <= 0:
        raise CertificateError(f"Rational denominator in {key!r} must be positive")
    return Fraction(pair[0], pair[1])


def _check_keys(obj: Mapping[str, Any], expected: set[str], label: str) -> None:
    keys = set(obj.keys())
    missing = expected - keys
    extra = keys - expected
    if missing:
        raise CertificateError(f"Missing keys in {label}: {sorted(missing)}")
    if extra:
        raise CertificateError(f"Unexpected keys in {label}: {sorted(extra)}")


def _is_small_prime(p: int) -> bool:
    if p < 2:
        return False
    d = 2
    while d * d <= p:
        if p % d == 0:
            return False
        d += 1
    return True


# ---------------------------------------------------------------------------
# Mode 1: Rank/Gate Lower Bounds, Rectangular Bound & Strassen Tight Support
# ---------------------------------------------------------------------------

def _verify_mode1(payload: Mapping[str, Any]) -> Dict[str, Any]:
    expected = {
        "n_square",
        "border_rank_lb",
        "gate_lb",
        "rect_dims",
        "rect_rank_lb",
        "tight_n",
        "tight_B",
        "sun_check_n",
        "sun_proposed_ub",
    }
    _check_keys(payload, expected, "Mode 1 payload")

    n_sq = _req_int(payload, "n_square")
    br_lb = _req_int(payload, "border_rank_lb")
    gt_lb = _req_int(payload, "gate_lb")
    rect = _req_int_list(payload, "rect_dims", min_len=3, max_len=3)
    rect_lb = _req_int(payload, "rect_rank_lb")
    tight_n = _req_int(payload, "tight_n")
    tight_B = _req_int(payload, "tight_B")
    sun_n = _req_int(payload, "sun_check_n")
    sun_ub = _req_int(payload, "sun_proposed_ub")

    if not (2 <= n_sq <= 10_000):
        raise CertificateError("n_square must lie in [2, 10000]")
    br_calc = border_rank_lb_square(n_sq)
    gt_calc = gate_lb_square(n_sq)
    if br_lb != br_calc:
        raise CertificateError(f"border_rank_lb={br_lb} disagrees with exact ceil(n^(9/4))={br_calc}")
    if gt_lb != gt_calc:
        raise CertificateError(f"gate_lb={gt_lb} disagrees with exact ceil(n^(9/4)/2)={gt_calc}")
    # Direct integer power bracket checks
    if br_lb ** 4 < n_sq ** 9 or (br_lb - 1) ** 4 >= n_sq ** 9:
        raise CertificateError("border_rank_lb failed integer 4th-power bracket")
    if 16 * (gt_lb ** 4) < n_sq ** 9 or 16 * ((gt_lb - 1) ** 4) >= n_sq ** 9:
        raise CertificateError("gate_lb failed integer 4th-power bracket")

    a, b, c = rect
    if min(a, b, c) < 1 or max(a, b, c) > 10_000:
        raise CertificateError("rect_dims must lie in [1, 10000]")
    rect_calc = rect_border_rank_lb(a, b, c)
    if rect_lb != rect_calc:
        raise CertificateError(f"rect_rank_lb={rect_lb} disagrees with Corollary 1.3 bound {rect_calc}")

    # Exhaustive verification of Strassen tight-support weights on T_{tight_n} (Section 2.4)
    if not (2 <= tight_n <= 12):
        raise CertificateError("tight_n must lie in [2, 12] for exhaustive support audit")
    if not (tight_n < tight_B <= 10_000):
        raise CertificateError("Strassen tight-support base B must satisfy tight_n < B <= 10000")
    wA = set()
    wB = set()
    wC = set()
    for i in range(tight_n):
        for j in range(tight_n):
            wa = i - tight_B * j
            wA.add(wa)
            for k in range(tight_n):
                wb = tight_B * j - (tight_B ** 2) * k
                wc = (tight_B ** 2) * k - i
                wB.add(wb)
                wC.add(wc)
                if wa + wb + wc != 0:
                    raise CertificateError("Tight-support weights failed zero-sum identity")
    if len(wA) != tight_n * tight_n or len(wB) != tight_n * tight_n or len(wC) != tight_n * tight_n:
        raise CertificateError("Tight-support weights are not injective on all three factors")

    # Sun dyadic conflict check (Corollary 1.2): verify sun_proposed_ub < ceil(sun_n^(9/4))
    if not (2 <= sun_n <= 10_000) or sun_ub < 1:
        raise CertificateError("Invalid Sun conflict parameters")
    sun_lb = border_rank_lb_square(sun_n)
    if sun_ub >= sun_lb:
        raise CertificateError("Sun proposed upper bound is not strictly below Corollary 1.2 lower bound")

    return {
        "mode": "rank_gate_and_tight_support_cert",
        "n_square": n_sq,
        "border_rank_lb": br_lb,
        "gate_lb": gt_lb,
        "rect_rank_lb": rect_lb,
        "tight_triples_checked": tight_n ** 3,
        "sun_lb": sun_lb,
    }


# ---------------------------------------------------------------------------
# Mode 2: Exact Symbolic Dual-Number Bilinearization of Arithmetic Circuits
# ---------------------------------------------------------------------------

def _verify_mode2(payload: Mapping[str, Any]) -> Dict[str, Any]:
    expected = {
        "prime_p",
        "side_s",
        "A0",
        "B0",
        "gates",
        "output_wire_indices",
        "claimed_nonscalar_count",
        "claimed_rank_upper_bound",
    }
    _check_keys(payload, expected, "Mode 2 payload")

    p = _req_int(payload, "prime_p")
    s = _req_int(payload, "side_s")
    claimed_q = _req_int(payload, "claimed_nonscalar_count")
    claimed_r = _req_int(payload, "claimed_rank_upper_bound")

    if not (5 <= p <= 1009) or not _is_small_prime(p):
        raise CertificateError("Mode 2 requires a prime modulus p in [5, 1009]")
    if not (2 <= s <= 4):
        raise CertificateError("Mode 2 requires matrix side s in [2, 4]")

    s2 = s * s
    s4 = s2 * s2
    A0 = _req_int_list(payload, "A0", min_len=s2, max_len=s2)
    B0 = _req_int_list(payload, "B0", min_len=s2, max_len=s2)
    for label, mat in (("A0", A0), ("B0", B0)):
        for entry in mat:
            if not (0 <= entry < p):
                raise CertificateError(f"Field entry {entry} in {label} outside canonical range [0, {p - 1}]")
    out_wires = _req_int_list(payload, "output_wire_indices", min_len=s2, max_len=s2)

    raw_gates = payload.get("gates")
    if not isinstance(raw_gates, list) or not (1 <= len(raw_gates) <= 256):
        raise CertificateError("Mode 2 requires 1..256 arithmetic circuit gates")

    # Initial symbolic dual-number wires over F_p[X, Y][u, v]/(u^2, v^2):
    #   wires 0..s^2-1       are A0_{ij} + u * X_{ij}
    #   wires s^2..2*s^2-1   are B0_{jk} + v * Y_{jk}
    z1 = (0,) * s2
    z2 = (0,) * s4
    wires: List[SymDual] = []
    for idx in range(s2):
        e_vec = tuple(1 if t == idx else 0 for t in range(s2))
        wires.append((A0[idx], e_vec, z1, z2))
    for idx in range(s2):
        e_vec = tuple(1 if t == idx else 0 for t in range(s2))
        wires.append((B0[idx], z1, e_vec, z2))

    nonscalar_count = 0
    for idx, g in enumerate(raw_gates):
        if not isinstance(g, dict):
            raise CertificateError(f"Gate {idx} must be a JSON object")
        op = _req_str(g, "op")
        if op == "const":
            _check_keys(g, {"op", "val"}, f"gate[{idx}]")
            val = _req_int(g, "val")
            if not (0 <= val < p):
                raise CertificateError(f"Const gate[{idx}] value {val} outside canonical range [0, {p - 1}]")
            wires.append(sym_dual_const(val, p, s2))
        elif op in ("add", "sub", "mul", "div"):
            _check_keys(g, {"op", "lhs", "rhs"}, f"gate[{idx}]")
            lhs = _req_int(g, "lhs")
            rhs = _req_int(g, "rhs")
            if not (0 <= lhs < len(wires) and 0 <= rhs < len(wires)):
                raise CertificateError(f"Gate {idx} wire index out of range")
            wl, wr = wires[lhs], wires[rhs]
            if op == "add":
                wires.append(sym_dual_add(wl, wr, p))
            elif op == "sub":
                wires.append(sym_dual_sub(wl, wr, p))
            elif op == "mul":
                # Nonscalar iff both inputs are symbolically nonconstant
                if sym_dual_is_nonconst(wl) and sym_dual_is_nonconst(wr):
                    nonscalar_count += 1
                wires.append(sym_dual_mul(wl, wr, p, s2))
            else:  # div
                if sym_dual_is_nonconst(wr):
                    nonscalar_count += 1
                wires.append(sym_dual_div(wl, wr, p, s2))
        else:
            raise CertificateError(f"Unsupported gate op {op!r} at index {idx}")

    if nonscalar_count != claimed_q:
        raise CertificateError(
            f"Claimed nonscalar gate count {claimed_q} != exact count {nonscalar_count}"
        )
    if claimed_r != 2 * nonscalar_count:
        raise CertificateError(
            f"Claimed Lemma 2.4 rank upper bound {claimed_r} != 2*q = {2 * nonscalar_count}"
        )

    # Symbolically verify ALL s^2 output wires equal (A0 + u X)(B0 + v Y)
    # across all 1 + s^2 + s^2 + s^4 coordinates in F_p[X, Y][u, v]/(u^2, v^2).
    for i in range(s):
        for k in range(s):
            w_idx = out_wires[i * s + k]
            if not (0 <= w_idx < len(wires)):
                raise CertificateError("Output wire index out of range")
            got = wires[w_idx]
            exp00 = sum(A0[i * s + j] * B0[j * s + k] for j in range(s)) % p
            exp10 = [0] * s2
            exp01 = [0] * s2
            exp11 = [0] * s4
            for j in range(s):
                a_idx = i * s + j
                b_idx = j * s + k
                exp10[a_idx] = (exp10[a_idx] + B0[b_idx]) % p
                exp01[b_idx] = (exp01[b_idx] + A0[a_idx]) % p
                exp11[a_idx * s2 + b_idx] = 1
            expected_wire = (exp00, tuple(exp10), tuple(exp01), tuple(exp11))
            if got != expected_wire:
                raise CertificateError(
                    f"Output entry ({i},{k}) symbolic dual expansion disagrees with (A0+uX)(B0+vY)"
                )

    return {
        "mode": "dual_number_bilinearization_cert",
        "prime_p": p,
        "side_s": s,
        "total_gates": len(raw_gates),
        "nonscalar_gates": nonscalar_count,
        "lemma24_rank_ub": claimed_r,
    }


# ---------------------------------------------------------------------------
# Mode 3: Exact Tag(h, h) -> Two D_w List-Distinctness Reduction (Section 4.1)
# ---------------------------------------------------------------------------

def _verify_mode3(payload: Mapping[str, Any]) -> Dict[str, Any]:
    expected = {
        "h_bits",
        "instances",
    }
    _check_keys(payload, expected, "Mode 3 payload")

    h_bits = _req_int(payload, "h_bits")
    if not (1 <= h_bits <= 3):
        raise CertificateError("Mode 3 requires h_bits in [1, 3] for full exact 2^N signed-sum replay")
    N = 1 << h_bits

    raw_insts = payload.get("instances")
    if not isinstance(raw_insts, list) or not (1 <= len(raw_insts) <= 16):
        raise CertificateError("Mode 3 requires 1..16 tagged-permutation instances")

    accepted_cnt = 0
    for idx, inst in enumerate(raw_insts):
        if not isinstance(inst, dict):
            raise CertificateError(f"Instance {idx} must be a JSON object")
        _check_keys(inst, {"tags", "x_payloads", "y_payloads", "expected_tag"}, f"instances[{idx}]")
        tags = _req_int_list(inst, "tags", min_len=N, max_len=N)
        xs = _req_int_list(inst, "x_payloads", min_len=N, max_len=N)
        ys = _req_int_list(inst, "y_payloads", min_len=N, max_len=N)
        exp_val = _req_int(inst, "expected_tag")
        if exp_val not in (0, 1):
            raise CertificateError("expected_tag must be 0 or 1")
        dw1, signed_sum, direct = eval_tag_via_two_dw(tags, xs, ys, h_bits)
        combined = dw1 * signed_sum
        if combined != direct:
            raise CertificateError(f"Section 4.1 two-D_w reduction disagreed with direct Tag on instance {idx}")
        if combined != exp_val:
            raise CertificateError(f"Instance {idx} expected_tag={exp_val} != exact {combined}")
        accepted_cnt += combined

    return {
        "mode": "tagged_perm_two_dw_reduction_cert",
        "h_bits": h_bits,
        "N_records": N,
        "instances_verified": len(raw_insts),
        "accepted_instances": accepted_cnt,
    }


# ---------------------------------------------------------------------------
# Mode 4: Five-Arm Harmonic Star, Tripod D*(a), & AM-HM Rigidity (Secs. 7-11)
# ---------------------------------------------------------------------------

def _verify_mode4(payload: Mapping[str, Any]) -> Dict[str, Any]:
    expected = {
        "star_slope_matrix",
        "tripod_arms",
        "claimed_D_star",
        "claimed_perimeter",
        "claimed_exponent_ratio",
        "am_hm_margin",
        "asymptotic_b",
        "claimed_asymptotic_D_star",
    }
    _check_keys(payload, expected, "Mode 4 payload")

    # 1. Verify 5x4 harmonic star slope matrix (Figure 4, Section 7.4)
    raw_mat = payload.get("star_slope_matrix")
    if not isinstance(raw_mat, list) or len(raw_mat) != 5:
        raise CertificateError("star_slope_matrix must have 5 arm rows")
    mat: List[List[int]] = []
    for row in raw_mat:
        if not isinstance(row, list) or len(row) != 4:
            raise CertificateError("Each star_slope_matrix row must have 4 site columns")
        r_int: List[int] = []
        for x in row:
            if isinstance(x, bool) or not isinstance(x, int):
                raise CertificateError("star_slope_matrix entries must be integers")
            r_int.append(x)
        mat.append(r_int)
    for col in range(4):
        if sum(mat[r][col] for r in range(5)) != 0:
            raise CertificateError(f"Five-arm star column {col} is not harmonic (nonzero sum)")
    # Enforce exact Figure 4 five-arm harmonic star arm rows (up to positive integer scaling k >= 1)
    canonical_star = [
        [1, -1, -1, 1],
        [-1, 1, -1, 1],
        [-1, -1, 1, 1],
        [1, 1, 1, 1],
        [0, 0, 0, -4],
    ]
    scale_k = mat[0][0]
    if scale_k < 1 or mat != [[scale_k * v for v in row] for row in canonical_star]:
        raise CertificateError("Five-arm star slope rows do not match exact Figure 4 harmonic arm structure")

    # 2. Verify tripod arms a = (a1, a2, a3) > 0, D*(a), perimeter, and AM-HM margin
    raw_arms = payload.get("tripod_arms")
    if not isinstance(raw_arms, list) or len(raw_arms) != 3:
        raise CertificateError("tripod_arms must be 3 [num, den] positive rationals")
    arms: List[Fraction] = []
    for idx, pair in enumerate(raw_arms):
        if not isinstance(pair, list) or len(pair) != 2:
            raise CertificateError(f"tripod_arms[{idx}] must be [num, den]")
        if any(isinstance(v, bool) or not isinstance(v, int) for v in pair) or pair[0] <= 0 or pair[1] <= 0:
            raise CertificateError(f"tripod_arms[{idx}] must be a positive rational")
        arms.append(Fraction(pair[0], pair[1]))

    a1, a2, a3 = arms
    d_star_calc = tripod_d_star(a1, a2, a3)
    perim_calc = Fraction(2) * (a1 + a2 + a3)
    ratio_calc = frac_div(perim_calc, d_star_calc)
    am_hm_bound = Fraction(8, 9) * (a1 + a2 + a3)
    margin_calc = d_star_calc - am_hm_bound

    d_star_claimed = _req_frac(payload, "claimed_D_star")
    perim_claimed = _req_frac(payload, "claimed_perimeter")
    ratio_claimed = _req_frac(payload, "claimed_exponent_ratio")
    margin_claimed = _req_frac(payload, "am_hm_margin")

    if d_star_claimed != d_star_calc:
        raise CertificateError(f"claimed_D_star {d_star_claimed} != exact {d_star_calc}")
    if perim_claimed != perim_calc:
        raise CertificateError(f"claimed_perimeter {perim_claimed} != exact {perim_calc}")
    if ratio_claimed != ratio_calc:
        raise CertificateError(f"claimed_exponent_ratio {ratio_claimed} != exact {ratio_calc}")
    if margin_calc < 0:
        raise CertificateError("AM-HM inequality D*(a) >= (8/9) sum a_i violated")
    if margin_claimed != margin_calc:
        raise CertificateError(f"am_hm_margin {margin_claimed} != exact {margin_calc}")
    # Verify Corollary 11.1 rigidity: ratio == 9/4 iff a1 == a2 == a3
    is_balanced = (a1 == a2 == a3)
    if is_balanced and ratio_calc != Fraction(9, 4):
        raise CertificateError("Balanced tripod failed exact 9/4 ratio")
    if (not is_balanced) and ratio_calc >= Fraction(9, 4):
        raise CertificateError("Unbalanced tripod must satisfy perimeter / D*(a) < 9/4")

    # 3. Verify Section 8.2 asymptotic tripod D*(1, 1, b) = b + 3/2 + 1/(4b + 2)
    b_asym = _req_int(payload, "asymptotic_b")
    if not (1 <= b_asym <= 10_000):
        raise CertificateError("asymptotic_b must lie in [1, 10000]")
    asym_calc = tripod_d_star(Fraction(1), Fraction(1), Fraction(b_asym))
    asym_formula = Fraction(b_asym) + Fraction(3, 2) + Fraction(1, 4 * b_asym + 2)
    if asym_calc != asym_formula:
        raise CertificateError("Asymptotic tripod identity D*(1,1,b) = b + 3/2 + 1/(4b+2) failed")
    asym_claimed = _req_frac(payload, "claimed_asymptotic_D_star")
    if asym_claimed != asym_calc:
        raise CertificateError(f"claimed_asymptotic_D_star {asym_claimed} != exact {asym_calc}")

    return {
        "mode": "tripod_harmonic_and_amhm_rigidity_cert",
        "is_balanced": is_balanced,
        "D_star": f"{d_star_calc.numerator}/{d_star_calc.denominator}",
        "exponent_ratio": f"{ratio_calc.numerator}/{ratio_calc.denominator}",
        "am_hm_margin": f"{margin_calc.numerator}/{margin_calc.denominator}",
        "asymptotic_b": b_asym,
    }


# ---------------------------------------------------------------------------
# Public Entry Points
# ---------------------------------------------------------------------------

def verify_certificate_dict(data: Mapping[str, Any]) -> Dict[str, Any]:
    if not isinstance(data, Mapping):
        raise CertificateError("Certificate must be a mapping")
    allowed_top = {"protocol", "certificate_id", "mode", "payload", "description", "note"}
    extra_top = set(data.keys()) - allowed_top
    if extra_top:
        raise CertificateError(f"Unexpected top-level keys: {sorted(extra_top)}")
    for opt_k in ("description", "note"):
        if opt_k in data and not isinstance(data[opt_k], str):
            raise CertificateError(f"Optional field {opt_k!r} must be a string")

    proto = _req_str(data, "protocol")
    if proto != PROTOCOL_ID:
        raise CertificateError(f"Unsupported protocol {proto!r}; expected {PROTOCOL_ID!r}")
    cert_id = _req_str(data, "certificate_id")
    mode = _req_str(data, "mode")
    if mode not in VALID_MODES:
        raise CertificateError(f"Unknown certificate mode {mode!r}")

    payload = data.get("payload")
    if not isinstance(payload, Mapping):
        raise CertificateError("Field 'payload' must be a JSON object")

    try:
        if mode == "rank_gate_and_tight_support_cert":
            summary = _verify_mode1(payload)
        elif mode == "dual_number_bilinearization_cert":
            summary = _verify_mode2(payload)
        elif mode == "tagged_perm_two_dw_reduction_cert":
            summary = _verify_mode3(payload)
        else:
            summary = _verify_mode4(payload)
    except CertificateError:
        raise
    except ValueError as exc:
        raise CertificateError(f"Exact verification value error: {exc}") from exc

    summary["certificate_id"] = cert_id
    summary["protocol"] = PROTOCOL_ID
    return summary


def verify_certificate_str(raw: str) -> Dict[str, Any]:
    return verify_certificate_dict(load_strict_json_str(raw))


def verify_certificate_file(path: Path | str) -> Dict[str, Any]:
    return verify_certificate_str(Path(path).read_text(encoding="utf-8"))
