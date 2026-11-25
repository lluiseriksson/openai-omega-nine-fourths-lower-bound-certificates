"""Generate all 16 canonical OMEGA94-LB-CERT-1.0 certificates and 4 experiment JSONs.

Uses exact integer/Fraction arithmetic for all certificate generation and sweeps:
  - Exp 1: 16-certificate atlas & warm-up timing (4 per mode)
  - Exp 2: Square & rectangular border-rank / gate lower bounds (n=2..4096) & Sun refutation
  - Exp 3: Exact tripod AM-HM rigidity sweep D*(a1, a2, a3) & perimeter/D*(a) peak at 9/4
  - Exp 4: Exhaustive Tag(1, 1) -> two-D_w reduction verification across all 2^6 = 64 inputs
"""

from __future__ import annotations

from fractions import Fraction
import json
import math
from pathlib import Path
import sys
import time
from typing import Any, Dict, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.omega94_lb_certifier import PROTOCOL_ID, verify_certificate_dict
from src.omega94_lb_exact import (
    border_rank_lb_square,
    eval_tag_via_two_dw,
    frac_div,
    gate_lb_square,
    rect_border_rank_lb,
    tripod_d_star,
)

CERT_DIR = ROOT / "certificates"
RES_DIR = ROOT / "results"


# ---------------------------------------------------------------------------
# Certificate Builders (4 per Mode = 16 Total)
# ---------------------------------------------------------------------------

def build_mode1_cert(
    cert_id: str,
    n_sq: int,
    rect_dims: List[int],
    tight_n: int,
    tight_B: int,
    sun_n: int,
    sun_ub: int,
) -> Dict[str, Any]:
    br = border_rank_lb_square(n_sq)
    gt = gate_lb_square(n_sq)
    rlb = rect_border_rank_lb(rect_dims[0], rect_dims[1], rect_dims[2])
    return {
        "protocol": PROTOCOL_ID,
        "certificate_id": cert_id,
        "mode": "rank_gate_and_tight_support_cert",
        "description": f"Cors. 1.2-1.3 exact rank/gate lower bounds for n={n_sq}, rect={rect_dims}, tight T_{tight_n}",
        "payload": {
            "n_square": n_sq,
            "border_rank_lb": br,
            "gate_lb": gt,
            "rect_dims": rect_dims,
            "rect_rank_lb": rlb,
            "tight_n": tight_n,
            "tight_B": tight_B,
            "sun_check_n": sun_n,
            "sun_proposed_ub": sun_ub,
        },
    }


def _build_strassen_2x2_gates(use_div_trick: bool = False) -> Tuple[List[Dict[str, Any]], List[int], int]:
    """Build exact Strassen 7-product circuit for 2x2 matrix multiplication.
    Wires 0..3: A = (a00, a01, a10, a11); Wires 4..7: B = (b00, b01, b10, b11).
    If use_div_trick=True, routes M1 through a nonscalar division gate (M1 * d) / d
    where d = a00 + b11 + 1 (nonconstant, regular at A0, B0) to exercise Lemma 2.4's
    quotient gate bilinearization!
    """
    gates: List[Dict[str, Any]] = []

    def add_g(op: str, **kw: Any) -> int:
        idx = 8 + len(gates)
        gates.append({"op": op, **kw})
        return idx

    # Linear combinations
    s1 = add_g("add", lhs=0, rhs=3)  # a00 + a11
    s2 = add_g("add", lhs=4, rhs=7)  # b00 + b11
    s3 = add_g("add", lhs=2, rhs=3)  # a10 + a11
    s4 = add_g("sub", lhs=5, rhs=7)  # b01 - b11
    s5 = add_g("sub", lhs=6, rhs=4)  # b10 - b00
    s6 = add_g("add", lhs=0, rhs=1)  # a00 + a01
    s7 = add_g("sub", lhs=2, rhs=0)  # a10 - a00
    s8 = add_g("add", lhs=4, rhs=5)  # b00 + b01
    s9 = add_g("sub", lhs=1, rhs=3)  # a01 - a11
    s10 = add_g("add", lhs=6, rhs=7)  # b10 + b11

    # 7 Strassen nonscalar multiplications
    m1 = add_g("mul", lhs=s1, rhs=s2)
    m2 = add_g("mul", lhs=s3, rhs=4)
    m3 = add_g("mul", lhs=0, rhs=s4)
    m4 = add_g("mul", lhs=3, rhs=s5)
    m5 = add_g("mul", lhs=s6, rhs=7)
    m6 = add_g("mul", lhs=s7, rhs=s8)
    m7 = add_g("mul", lhs=s9, rhs=s10)

    nonscalar = 7
    if use_div_trick:
        c1 = add_g("const", val=1)
        d_pre = add_g("add", lhs=0, rhs=7)
        d_wire = add_g("add", lhs=d_pre, rhs=c1)  # nonconstant regular divisor
        m1_num = add_g("mul", lhs=m1, rhs=d_wire)
        m1 = add_g("div", lhs=m1_num, rhs=d_wire)
        nonscalar = 9  # +1 mul +1 div

    # Recombine C = A*B
    c00_a = add_g("add", lhs=m1, rhs=m4)
    c00_b = add_g("sub", lhs=c00_a, rhs=m5)
    c00 = add_g("add", lhs=c00_b, rhs=m7)

    c01 = add_g("add", lhs=m3, rhs=m5)
    c10 = add_g("add", lhs=m2, rhs=m4)

    c11_a = add_g("sub", lhs=m1, rhs=m2)
    c11_b = add_g("add", lhs=c11_a, rhs=m3)
    c11 = add_g("add", lhs=c11_b, rhs=m6)

    return gates, [c00, c01, c10, c11], nonscalar


def _build_schoolbook_gates(s: int, use_div: bool = False) -> Tuple[List[Dict[str, Any]], List[int], int]:
    """Build exact s x s matrix multiplication circuit (optionally with nonscalar division)."""
    s2 = s * s
    gates: List[Dict[str, Any]] = []

    def add_g(op: str, **kw: Any) -> int:
        idx = 2 * s2 + len(gates)
        gates.append({"op": op, **kw})
        return idx

    out_wires: List[int] = []
    nonscalar = 0
    for i in range(s):
        for k in range(s):
            acc = None
            for j in range(s):
                prod = add_g("mul", lhs=i * s + j, rhs=s2 + j * s + k)
                nonscalar += 1
                if acc is None:
                    acc = prod
                else:
                    acc = add_g("add", lhs=acc, rhs=prod)
            assert acc is not None
            if use_div and i == 0 and k == 0:
                c3 = add_g("const", val=3)
                d_w = add_g("add", lhs=0, rhs=c3)
                num_w = add_g("mul", lhs=acc, rhs=d_w)
                acc = add_g("div", lhs=num_w, rhs=d_w)
                nonscalar += 2
            out_wires.append(acc)
    return gates, out_wires, nonscalar


def build_mode2_cert(
    cert_id: str,
    p: int,
    s: int,
    A0: List[int],
    B0: List[int],
    kind: str,
) -> Dict[str, Any]:
    if kind == "strassen":
        gates, out_w, q = _build_strassen_2x2_gates(use_div_trick=False)
    elif kind == "strassen_div":
        gates, out_w, q = _build_strassen_2x2_gates(use_div_trick=True)
    elif kind == "schoolbook_div":
        gates, out_w, q = _build_schoolbook_gates(s, use_div=True)
    else:
        gates, out_w, q = _build_schoolbook_gates(s, use_div=False)

    return {
        "protocol": PROTOCOL_ID,
        "certificate_id": cert_id,
        "mode": "dual_number_bilinearization_cert",
        "description": f"Lem. 2.4 symbolic dual-number bilinearization over F_{p}[X,Y][u,v]/(u^2,v^2) for {s}x{s} ({kind})",
        "payload": {
            "prime_p": p,
            "side_s": s,
            "A0": A0,
            "B0": B0,
            "gates": gates,
            "output_wire_indices": out_w,
            "claimed_nonscalar_count": q,
            "claimed_rank_upper_bound": 2 * q,
        },
    }


def build_mode3_cert(cert_id: str, h_bits: int, raw_cases: List[Tuple[List[int], List[int], List[int]]]) -> Dict[str, Any]:
    instances = []
    for tags, xs, ys in raw_cases:
        dw1, ssum, direct = eval_tag_via_two_dw(tags, xs, ys, h_bits)
        assert dw1 * ssum == direct
        instances.append(
            {
                "tags": tags,
                "x_payloads": xs,
                "y_payloads": ys,
                "expected_tag": direct,
            }
        )
    return {
        "protocol": PROTOCOL_ID,
        "certificate_id": cert_id,
        "mode": "tagged_perm_two_dw_reduction_cert",
        "description": f"Sec. 4.1 exact Tag({h_bits},{h_bits}) reduction to two D_w tests ({len(instances)} instances)",
        "payload": {
            "h_bits": h_bits,
            "instances": instances,
        },
    }


def build_mode4_cert(cert_id: str, arms_frac: List[Fraction], asym_b: int) -> Dict[str, Any]:
    star_mat = [
        [1, -1, -1, 1],
        [-1, 1, -1, 1],
        [-1, -1, 1, 1],
        [1, 1, 1, 1],
        [0, 0, 0, -4],
    ]
    a1, a2, a3 = arms_frac
    d_star = tripod_d_star(a1, a2, a3)
    perim = Fraction(2) * (a1 + a2 + a3)
    ratio = frac_div(perim, d_star)
    margin = d_star - Fraction(8, 9) * (a1 + a2 + a3)
    asym_d = tripod_d_star(Fraction(1), Fraction(1), Fraction(asym_b))
    return {
        "protocol": PROTOCOL_ID,
        "certificate_id": cert_id,
        "mode": "tripod_harmonic_and_amhm_rigidity_cert",
        "description": f"Secs. 7.4/8.2/11.3 five-arm harmonic star & tripod AM-HM rigidity for arms {arms_frac}",
        "payload": {
            "star_slope_matrix": star_mat,
            "tripod_arms": [[a.numerator, a.denominator] for a in arms_frac],
            "claimed_D_star": [d_star.numerator, d_star.denominator],
            "claimed_perimeter": [perim.numerator, perim.denominator],
            "claimed_exponent_ratio": [ratio.numerator, ratio.denominator],
            "am_hm_margin": [margin.numerator, margin.denominator],
            "asymptotic_b": asym_b,
            "claimed_asymptotic_D_star": [asym_d.numerator, asym_d.denominator],
        },
    }


def main() -> None:
    CERT_DIR.mkdir(parents=True, exist_ok=True)
    RES_DIR.mkdir(parents=True, exist_ok=True)

    certs: List[Dict[str, Any]] = [
        # Mode 1 (4 certs)
        build_mode1_cert("m1_bounds_n16_rect4x4x4", 16, [4, 4, 4], 4, 5, 256, 1 << 17),
        build_mode1_cert("m1_bounds_n256_sun_refute", 256, [16, 4, 16], 6, 7, 256, 1 << 17),
        build_mode1_cert("m1_bounds_n1024_rect64x16x64", 1024, [64, 16, 64], 8, 10, 256, 1 << 17),
        build_mode1_cert("m1_bounds_n4096_rect256x64x256", 4096, [256, 64, 256], 10, 11, 4096, (1 << 27) - 1),
        # Mode 2 (4 certs)
        build_mode2_cert("m2_dual_strassen_2x2_f101", 101, 2, [2, 3, 5, 7], [11, 13, 17, 19], "strassen"),
        build_mode2_cert("m2_dual_strassen_div_2x2_f257", 257, 2, [3, 5, 7, 11], [2, 13, 17, 19], "strassen_div"),
        build_mode2_cert("m2_dual_schoolbook_div_3x3_f509", 509, 3, [1, 2, 3, 4, 5, 6, 7, 8, 9], [2, 3, 5, 7, 11, 13, 17, 19, 23], "schoolbook_div"),
        build_mode2_cert("m2_dual_schoolbook_4x4_f1009", 1009, 4, list(range(1, 17)), list(range(17, 33)), "schoolbook"),
        # Mode 3 (4 certs)
        build_mode3_cert(
            "m3_tag_h1_exhaustive_4cases",
            1,
            [
                ([0, 1], [0, 1], [0, 1]),
                ([1, 0], [1, 0], [0, 1]),
                ([1, 0], [0, 0], [0, 1]),
                ([0, 0], [0, 1], [0, 1]),
            ],
        ),
        build_mode3_cert(
            "m3_tag_h2_valid_and_collisions",
            2,
            [
                ([2, 0, 3, 1], [1, 3, 2, 0], [3, 0, 1, 2]),
                ([3, 2, 1, 0], [0, 1, 2, 3], [3, 2, 1, 0]),
                ([2, 0, 3, 1], [1, 3, 2, 1], [3, 0, 1, 2]),
                ([2, 0, 2, 1], [1, 3, 2, 0], [3, 0, 1, 2]),
            ],
        ),
        build_mode3_cert(
            "m3_tag_h3_cyclic_perm_n8",
            3,
            [
                ([1, 2, 3, 4, 5, 6, 7, 0], [5, 2, 7, 0, 4, 1, 6, 3], [3, 5, 2, 7, 0, 4, 1, 6]),
                ([1, 2, 3, 4, 5, 6, 7, 0], [5, 2, 7, 0, 4, 1, 6, 2], [3, 5, 2, 7, 0, 4, 1, 6]),
            ],
        ),
        build_mode3_cert(
            "m3_tag_h3_involution_n8",
            3,
            [
                ([7, 6, 5, 4, 3, 2, 1, 0], [0, 1, 2, 3, 4, 5, 6, 7], [7, 6, 5, 4, 3, 2, 1, 0]),
                ([7, 6, 5, 4, 3, 2, 0, 0], [0, 1, 2, 3, 4, 5, 6, 7], [7, 6, 5, 4, 3, 2, 1, 0]),
            ],
        ),
        # Mode 4 (4 certs)
        build_mode4_cert("m4_tripod_balanced_unit_1_1_1", [Fraction(1), Fraction(1), Fraction(1)], 5),
        build_mode4_cert("m4_tripod_maximal_scale1_3_8", [Fraction(3, 8), Fraction(3, 8), Fraction(3, 8)], 20),
        build_mode4_cert("m4_tripod_asymmetric_1_2_3", [Fraction(1), Fraction(2), Fraction(3)], 50),
        build_mode4_cert("m4_tripod_stretched_1_1_100", [Fraction(1), Fraction(1), Fraction(100)], 100),
    ]

    atlas_rows: List[Dict[str, Any]] = []
    for cert in certs:
        cid = cert["certificate_id"]
        path = CERT_DIR / f"{cid}.cert.json"
        path.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8", newline="\n")
        summary = verify_certificate_dict(cert)
        times_ms: List[float] = []
        for _ in range(7):
            t0 = time.perf_counter()
            verify_certificate_dict(cert)
            times_ms.append((time.perf_counter() - t0) * 1000.0)
        mean_ms = sum(times_ms) / len(times_ms)
        atlas_rows.append(
            {
                "certificate_id": cid,
                "mode": cert["mode"],
                "mean_ms": round(mean_ms, 3),
                "summary": summary,
            }
        )
        print(f"[OK] {cid:38s} | {mean_ms:7.3f} ms | {summary}")

    (RES_DIR / "exp1_certificate_atlas.json").write_text(
        json.dumps({"protocol": PROTOCOL_ID, "count": len(atlas_rows), "certificates": atlas_rows}, indent=2) + "\n",
        encoding="utf-8",
        newline="\n",
    )

    # Exp 2: Exact Square Rank / Gate Lower Bounds vs Historical Lower Bounds (Blaser, Landsberg-Michalek)
    exp2_rows = []
    for n in [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096]:
        br_94 = border_rank_lb_square(n)
        gate_94 = gate_lb_square(n)
        lm_br = 2 * n * n - math.ceil(math.log2(n)) - 1  # Landsberg-Michalek border rank LB
        blaser_r = (5 * n * n) // 2 - 3 * n              # Blaser ordinary rank LB
        exp2_rows.append(
            {
                "n": n,
                "border_rank_lb_9_4": br_94,
                "gate_lb_9_4": gate_94,
                "landsberg_michalek_br_lb": lm_br,
                "blaser_rank_lb": blaser_r,
                "ratio_94_over_lm": round(br_94 / max(1, lm_br), 3),
            }
        )
    (RES_DIR / "exp2_rank_gate_bounds.json").write_text(
        json.dumps({"rows": exp2_rows}, indent=2) + "\n", encoding="utf-8", newline="\n"
    )

    # Exp 3: Exact Tripod AM-HM Rigidity Profile along (1, 1, b) for b in [1/8 .. 32]
    exp3_rows = []
    b_grid = [
        Fraction(1, 8), Fraction(1, 4), Fraction(1, 2), Fraction(3, 4),
        Fraction(1), Fraction(3, 2), Fraction(2), Fraction(3),
        Fraction(4), Fraction(8), Fraction(16), Fraction(32),
    ]
    for b in b_grid:
        ds = tripod_d_star(Fraction(1), Fraction(1), b)
        perim = Fraction(2) * (Fraction(2) + b)
        ratio = frac_div(perim, ds)
        margin = ds - Fraction(8, 9) * (Fraction(2) + b)
        exp3_rows.append(
            {
                "b_str": f"{b.numerator}/{b.denominator}",
                "b_float": float(b),
                "D_star_float": round(float(ds), 6),
                "exponent_ratio_float": round(float(ratio), 6),
                "am_hm_margin_float": round(float(margin), 6),
                "gap_below_9_4": round(2.25 - float(ratio), 6),
            }
        )
    (RES_DIR / "exp3_tripod_rigidity.json").write_text(
        json.dumps({"rows": exp3_rows}, indent=2) + "\n", encoding="utf-8", newline="\n"
    )

    # Exp 4: Exhaustive Tag(1,1) (all 2^6 = 64 inputs) exact agreement
    t1_total = 0
    t1_accept = 0
    for t0 in range(2):
        for t1 in range(2):
            for x0 in range(2):
                for x1 in range(2):
                    for y0 in range(2):
                        for y1 in range(2):
                            dw1, ssum, direct = eval_tag_via_two_dw([t0, t1], [x0, x1], [y0, y1], 1)
                            assert dw1 * ssum == direct
                            t1_total += 1
                            t1_accept += direct
    exp4 = {
        "tag_h1_exhaustive_total": t1_total,
        "tag_h1_accepted": t1_accept,
        "tag_h1_exact_matches": t1_total,
        "note": "All 64 combinations of (tags, x, y) in {0,1}^6 for Tag(1,1) match Section 4.1 two-D_w signed-sum identically.",
    }
    (RES_DIR / "exp4_tag_exhaustive.json").write_text(
        json.dumps(exp4, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print("All 16 certificates and 4 experiment JSON files generated successfully.")


if __name__ == "__main__":
    main()
