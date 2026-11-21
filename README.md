# Spectral & Inertia Theorem Prover Branch (`SEAM-01` + `SEAM-04` + `SEAM-08`)

Standalone zero-dependency Python 3 (stdlib-only, pure `fractions.Fraction` + `math.isqrt`, zero floats in any TCB path, zero bare `assert`s, LF-only) library implementing three verified tracks:

1. **Track A (`SEAM-01` — Complete `R_opt` + Higher-Moment Spectral Rank Breakthroughs):**
   - **Theorem A1 (`R_opt`):** Guarded scale-invariant two-regime envelope bounding the strictly tighter $W^\perp$-projected positive inertia $n_+(\Pi_{W^\perp}(P+Q)\Pi_{W^\perp}) \le \operatorname{rank}(\Pi_{W^\perp} P \Pi_{W^\perp}) \le \operatorname{rank}(P)$ (`AUDIT-002`, confirmed `N2`).
   - **Theorem A2 (`R_H4`, `R_H6`, general $2m$ Stieltjes–Hankel Indefinite Bound):** Exact rational bounds using $\operatorname{tr}(H^k)$ ($k=1..2m$) for arbitrary indefinite non-commuting complex Hermitian $H = P + Q$ with $n_+(Q) \le b$. Lifts `project-asma` Scan 23848 Mode B ($\tau = 0$) to **exact `1`** across ALL overlaps $\rho \in [0, 0.95]$ (where fixed $c=2$ collapses to `0` by $\rho=0.75$ and $R_{\mathrm{opt}} \to 0.03685$).
   - **Theorem A3 (`Phi_{x0, tau}` Noise-Annihilating Quartic SOS Bound):** Closed-form exact rational Sum-of-Squares quartic with a double zero at $\lambda = -\tau$ (specializing at $\tau=0$ to $S_3^4/S_4^3 - b$). Strictly beats $\max(1, \lceil R_{\mathrm{opt}} \rceil)$ on `project-asma` Scan 23848 Mode A with noise $\tau > 0$ across high-interference regimes $\rho \in [0.75, 0.95]$ all the way to $\lambda_2(G) > \tau$.
   - **Theorem A4 (`R_W4` Weighted Quartic-Weyl SOS Bound):** Exact 5-parameter (and 3-parameter peak-matched) rational SOS generalization of Lemma 3.2 using $(S_1..S_4, \operatorname{tr}Q, \operatorname{tr}Q^3, b)$, strictly beating BOTH $\lceil R_{\mathrm{opt}} \rceil$ AND $R_{H4} - b$ on non-commuting complex Hermitian matrices.
2. **Track B (`SEAM-04` — Exact Non-Affine Parametric Complex-Hermitian Box Certifier):**
   - Exact multivariate Bernstein enclosures (`PolyMatrix`, `RatMatrix`) + exact `QInterval`/`QiInterval` (`isqrt`-bracketed) + Bunch–Kaufman congruence preconditioning + complex block-Gershgorin uniform inertia certification (`Theorem B2`) + branch-and-bound singularity isolator.
   - Validated on:
     1. `aska-physical/fibral-rigidity#5` 2-bar truss box `[7/10, 13/10] x [9/10, 15/10]` (replays all 5 `docs/10` §4.2 exact matrices, isolates exact dual-oracle-verified `(1, 0, 1)` singular witness `(9/10, 11/10)`, certifies uniform PD `(2, 0, 0)` on taut & buckled sub-boxes).
     2. Complex Hermitian 2D Bloch dynamical matrix box (Weierstrass rational map $e^{i q_k} = \frac{1-t_k^2+2it_k}{1+t_k^2}$: certifies uniform PD `(2,0,0)` on gapped box AND catches interior Dirac zero mode `(0,0)` with inertia `(1,0,1)` despite all 4 corners being strictly PD `(2,0,0)`!).
     3. Non-affine $3\times 3$ indefinite Morse-index Hessian box (certifies uniform saddle `(2,1,0)` AND certifies `INERTIA_CHANGE_DETECTED` across an irrational bifurcation curve `(2,1,0) <-> (3,0,0)`).
3. **Track C (`SEAM-08` — Hardened Dual-Oracle Exact $\mathbb{Q}(i)$ Certifier + 36-Mutant Suite + Lean 4 Source):**
   - Closes all 6 `AUDIT-001` exploits + all `loom#7` guards + full R1–R5 conformance (`parse_strict_fraction`, `parse_strict_json`, $P \succeq 0$ second congruence witness).
   - Pairs Oracle 1 (Sylvester congruence $C M C^* = D$ and `loom#7` $P M P^* = L D L^*$) with zero-shared-code Oracle 2 (Faddeev–LeVerrier + Cayley–Hamilton + exact Descartes + exact Sturm square-free sequence).
   - **36/36 refusal-site & check-deletion mutants KILLED (0 survivors)** under both `python3 -B` and `python3 -O -B`.
   - Lean 4 formalization of core algebraic & SOS theorems in [`lean/SpectralInertia/Basic.lean`](lean/SpectralInertia/Basic.lean) (honestly tagged `uncompiled_source` because `lean`/`lake`/`elan` are not installed on this host).

---

## Quick Reproduction Commands (R4 Parity: `-B`, `-O -B`, `-B -W error`)

```bash
cd /home/shahid/Projects/expedition/branches/spectral-inertia

# Full master verification suite (unittests + 36-mutant R5 harness + all Track A/B benchmarks)
python3 -B run_all.py
python3 -O -B run_all.py
python3 -B -W error run_all.py

# Individual tracks & benchmarks
python3 -B -W error -m unittest discover -s tests -v
python3 -O -B -W error tests/run_mutation_suite.py
python3 -B -W error -m spectral_inertia.examples.scan23848_benchmark
python3 -B -W error -m spectral_inertia.examples.fibral_truss_box
python3 -B -W error -m spectral_inertia.examples.bloch_and_hessian_boxes
```

---

## Clean Callable API for Swarm Peers (`@fractals-probe` & `@gravity-probe`)

```python
from fractions import Fraction
import sys
sys.path.insert(0, "/home/shahid/Projects/expedition/branches/spectral-inertia")

from spectral_inertia import (
    MultiPoly, PolyMatrix, RatMatrix, QInterval, QiInterval, Qi,
    certify_hermitian_box,
)

# 1. Exact polynomial complex-Hermitian family (zero wrapping error via Bernstein E(x)=C(M(x)-M(x_c))C*):
t1, t2 = MultiPoly.var(2, 0), MultiPoly.var(2, 1)
i_unit = MultiPoly.const(2, Qi(Fraction(0), Fraction(1)))
# ... build entries as MultiPoly over Q(i) ...
# pm = PolyMatrix(2, [[d00, off], [off.conj(), d11]])
# res = certify_hermitian_box(pm, [(Fraction(-1), Fraction(1)), (Fraction(-1), Fraction(1))],
#                             max_depth=6, max_boxes=128)
# res.status in {"CERTIFIED_CONSTANT_INERTIA", "SINGULARITY_DETECTED", "INERTIA_CHANGE_DETECTED", "UNRESOLVED_SUBBOXES"}

# 2. Exact rational family (centered Bernstein residual):
# rm = RatMatrix(d, num_entries, den_entries)
# res = certify_hermitian_box(rm, box_bounds)

# 3. General piecewise/algebraic callable family:
# res = certify_hermitian_box(eval_point_fn, box_bounds, eval_box_fn=eval_box_fn)
```

See [`THEOREMS.md`](THEOREMS.md) for complete rigorous proofs and prior-art positioning.
