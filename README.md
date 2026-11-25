# Constructive Lean 4 Kernel and Exact Zero-Float Certificates for OpenAI's Matching Matrix Multiplication Lower Bound $\omega_F = 9/4$

**Author:** Lluis Eriksson  
**Protocol:** `OMEGA94-LB-CERT-1.0`  
**Licenses:** MIT (code, Lean 4 proofs, certificates) / CC-BY-4.0 (manuscript & figures)

## Overview

Independent, explicitly scoped, zero-floating-point two-layer verification companion for the discrete algebraic, dual-number bilinearization, tight-tensor support, tagged-permutation two-$D_w$ reduction, five-arm harmonic star, and tripod AM–HM rigidity mechanisms of OpenAI's November 24, 2026 preprint *"The matrix multiplication exponent is nine fourths"*.

- **Layer 1 (`lean/OpenAIOmegaLowerBound.lean`):** 18 standalone constructive Lean 4.35.0 sub-lemmas (`0` `sorry`, `0` custom `axiom`, `0` `Classical.choice`, `0` warnings; `4 none` + `14 [propext, Quot.sound]`).
- **Layer 2 (`src/omega94_lb_exact.py`, `src/omega94_lb_certifier.py`):** Pure-stdlib Python `int`/`Fraction` zero-float auditor across 4 modes (`rank_gate_and_tight_support_cert`, `dual_number_bilinearization_cert`, `tagged_perm_two_dw_reduction_cert`, `tripod_harmonic_and_amhm_rigidity_cert`).
- **Canonical Atlas & Red-Team Audit:** 16 canonical certificates verified ($0.027$–$2.466$ ms), `76/76` pytest checks (`70/70` live adversarial forgeries rejected with exact branch regexes), and full 41-file SHA-256 integrity manifest.

## Reproducibility (5-Gate Verification)

```bash
python scripts/run_all_experiments.py
python scripts/make_figures.py
python scripts/verify_all.py
```
