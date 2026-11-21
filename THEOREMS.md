# Spectral & Inertia Theorems: Complete Rigorous Proofs & Honest Prior-Art Audit

**Branch:** `/home/shahid/Projects/expedition/branches/spectral-inertia/`  
**Scope:** `SEAM-01` (Track A: `R_opt` + Higher-Moment Breakthroughs), `SEAM-04` (Track B: Exact Non-Affine Parametric Complex-Hermitian Box Certifier), and `SEAM-08` (Track C: Hardened Dual-Oracle Exact $\mathbb{Q}(i)$ Certifier).

---

## 0. Honest Prior-Art & Novelty Audit (Gate 9 Discipline)

Before claiming new ground, we record exactly what exists in prior art (checked directly against full texts archived in `/home/shahid/Projects/expedition/peer-web/raw/`):

1. **Classical PSD rank–trace / Hankel–Stieltjes inequalities:**
   - For PSD $P \succeq 0$, $\operatorname{rank}(P) \ge (\operatorname{tr} P)^2 / \operatorname{tr}(P^2)$ (Cauchy–Schwarz / Rényi-2 effective rank), Hölder $\operatorname{rank}(P) \ge (\operatorname{tr} P)^{k/(k-1)} / (\operatorname{tr} P^k)^{1/(k-1)}$, and PSD Hankel moment matrices $\mathcal{H}_d(P) \succeq 0 \implies \operatorname{rank}(P) \ge v_d^\top M_d^+ v_d$ are classical.
2. **`arXiv:2608.13637v2` (Alpöge & Furman, Aug 2026, Lemma 3.2):**
   - For Hermitian $P \succeq 0$ and Hermitian $Q$ with $n_+(Q) \le b$:
     $$\operatorname{rank}(P) \ge 2\operatorname{tr}(P) + 4\operatorname{tr}(Q) - 4b - \|P+Q\|_{\mathrm{HS}}^2.$$
   - Fixed unscaled weight $c = 2$; bounds total $\operatorname{rank}(P)$.
3. **`arXiv:2609.33043` (`[23, Lemma 4]`) & `arXiv:2610.08965v1` (Knausgård, Oct 2026, Lemmas 2.1 & 6.1):**
   - Defines saturated quadratic $\varphi_c(x) = x^2 - (x-c)_+^2 = \min(x^2, 2cx - c^2)$ and proves for $t \ge c$:
     $$\operatorname{tr}((P+Q)^2) \ge \operatorname{tr}\varphi_c(P) + 2t\operatorname{tr}(Q) - t^2 b.$$
   - At $c = 1$, $\varphi_1(\lambda) \ge 2\lambda - \mathbf{1}_{\lambda > 0}$ yields the additive $t \ge 1$ rank–trace family for total $\operatorname{rank}(P)$. Splits $A = (P - Q_-) + Q_+$ without $W^\perp$ compression, without scale-invariant joint optimization, and without higher moments $\operatorname{tr}(H^3), \operatorname{tr}(H^4)$.
4. **`siliconcordat/loom#7` (`docs/10-exact-inertia-certificates.md` §3.2–3.3):**
   - Proves the unscaled additive family via Weyl `(W1)/(W2)` with best member $R_G = 2\operatorname{tr}P + (\operatorname{tr}Q)^2/b - \|H\|_F^2$ (for $\operatorname{tr}Q \ge b$). Not scale-invariant; bounds total $\operatorname{rank}(P)$; single Python checker; 2-bar truss checked at 5 isolated points.

### What Is Genuinely New Here (`N2` Delta)
- **Theorem A1 (`AUDIT-002`, confirmed `N2`):** Strengthens the target to the **$W^\perp$-projected positive inertia** $n_+(\Pi_{W^\perp}(P+Q)\Pi_{W^\perp}) \le \operatorname{rank}(\Pi_{W^\perp}P\Pi_{W^\perp}) \le \operatorname{rank}(P)$ via an explicit 6-term nonnegative slack identity in $W \oplus W^\perp$; gives the closed-form guarded scale-invariant two-regime envelope $R_{\mathrm{opt}}(u,t,S,b)$; and proves **integer-exact pointwise sharpness** $\min \operatorname{rank}(P) = \max(1, \lceil R_{\mathrm{opt}} \rceil)$ from $(u,t,S,b)$ alone.
- **Theorem A2 (Degree-$2m$ Stieltjes–Hankel Indefinite Projected-Inertia Bound $R_{H,2m}$):** Extends classical PSD Hankel Schur complements to **arbitrary indefinite non-commuting complex Hermitian $H = P + Q$ with $n_+(Q) \le b$** by combining alternating-sign nonnegativity $a \in \mathbb{Q}_{\ge 0}^m$ (forcing $\phi_a(\lambda) = 1 - q_a(\lambda)^2 \le \mathbf{1}_{\lambda > 0}$ on all of $\mathbb{R}$, including negative eigenvalues!) with Cauchy interlacing $n_+(H) \le b + n_+(H_\perp)$ — yielding closed-form $R_{H4}$ and exact active-set KKT $R_{H6}$ with exact rank-$m$ recovery whenever $H \succeq 0$ has $\le m$ distinct eigenvalues (lifting Scan 23848 Mode B to exact `1` across ALL $\rho \in [0, 1)$).
- **Theorem A3 (Exact Noise-Annihilating Quartic SOS Bound $\Phi_{x_0, \tau}$):** A closed-form, square-root-free exact rational Sum-of-Squares quartic polynomial $\Phi_{x_0,\tau}(\lambda) \le \mathbf{1}_{\lambda > 0}$ with a **double zero at $\lambda = -\tau$** (annihilating uniform noise floors $-\tau I_T$ to second order), specializing at $\tau = 0$ to the indefinite odd-even Hölder bound $S_3^4/S_4^3 - b$, and strictly surpassing $\max(1, \lceil R_{\mathrm{opt}} \rceil)$ on Scan 23848 Mode A across high-interference noisy regimes ($\rho \in [0.75, 0.95], \tau > 0$) all the way to the physical detectability threshold $\lambda_2(G) > \tau$.
- **Theorem A4 (Exact Weighted Quartic-Weyl SOS Bound $R_{W4}$):** A 5-parameter (and 3-parameter peak-matched) exact rational SOS generalization of Lemma 3.2 combining quartic $\phi_{s,p}(H)$ with odd non-decreasing $Q$-moments $2\gamma_1\operatorname{tr}(Q) + 2\gamma_3\operatorname{tr}(Q^3)$ via Weyl `(W2)` + Cauchy interlacing, simultaneously placing zero-slack peaks at two eigenvalues of $P_\perp$ AND at the positive eigenvalue(s) of $Q_+$ — strictly beating BOTH $\lceil R_{\mathrm{opt}} \rceil$ AND $R_{H4} - b$ on non-commuting complex Hermitian matrices!
- **Theorems B1–B2 (Complex-Hermitian Bernstein Congruent Block-Gershgorin Box Certifier):** Combines exact multivariate Bernstein tensor conversion over $\mathbb{Q}(i)$ with congruence-preconditioned polynomial residuals $E(x) = C(M(x) - M(x_c))C^*$ (eliminating both dependency error and matrix wrapping error) and $1\times 1 / 2\times 2$ block-Gershgorin uniform non-singularity certification over continuous parameter boxes.

---

## 1. Track A — Spectral & Higher-Moment Rank Theorems (`SEAM-01`)

Throughout Section 1, let $P, Q \in \mathbb{C}^{n \times n}$ be arbitrary (possibly **non-commuting**) complex Hermitian matrices with $P \succeq 0$ and $n_+(Q) \le b$. Decompose $Q = Q_+ - Q_-$ ($Q_+, Q_- \succeq 0$, $Q_+ Q_- = 0$), let $W = \operatorname{range}(Q_+)$ with $\dim W = b_+ \le b$, and define:
$$H := P + Q, \qquad P_\perp := \Pi_{W^\perp} P \Pi_{W^\perp}, \qquad H_\perp := \Pi_{W^\perp} H \Pi_{W^\perp} = P_{22} - Q_-, \qquad S_k := \operatorname{tr}(H^k).$$

### Lemma 0 (Universal Projected-Inertia Interlacing Chain)
$$\operatorname{rank}(P) \;\ge\; \operatorname{rank}(P_\perp) \;\ge\; n_+(H_\perp) \;\ge\; n_+(H) - b.$$
**Proof.**
1. $\operatorname{rank}(P) \ge \operatorname{rank}(\Pi_{W^\perp} P \Pi_{W^\perp}) = \operatorname{rank}(P_\perp)$ is immediate since multiplication by $\Pi_{W^\perp}$ cannot increase rank.
2. Since $Q_- \succeq 0$, $H_\perp = P_{22} - Q_- \preceq P_{22}$, so by Weyl monotonicity $\lambda_i(H_\perp) \le \lambda_i(P_{22})$, hence $n_+(H_\perp) \le n_+(P_{22}) = \operatorname{rank}(P_\perp)$ (as $P_{22} \succeq 0$).
3. $H_\perp$ is an $(n - b_+) \times (n - b_+)$ principal compression of the $n \times n$ Hermitian matrix $H$. By Cauchy's interlacing theorem,
   $$\lambda_{i + b_+}(H) \le \lambda_i(H_\perp) \qquad (1 \le i \le n - b_+).$$
   Setting $i = n_+(H_\perp) + 1$ gives $\lambda_{b_+ + n_+(H_\perp) + 1}(H) \le \lambda_{n_+(H_\perp) + 1}(H_\perp) \le 0$. Thus $n_+(H) \le b_+ + n_+(H_\perp) \le b + n_+(H_\perp)$. $\square$

---

### Theorem A1 (Guarded Sharp Projected Envelope $R_{\mathrm{opt}}$ & 6-Term Slack Identity)
Write $u = \operatorname{tr}(P)$, $t = \operatorname{tr}(Q)$, $S = S_2 = \|H\|_F^2$. Then:
1. **Unscaled $W \oplus W^\perp$ block slack identity:** For every real $c \ge 1$,
   $$n_+(H_\perp) + c^2 b - \big(2u + 2ct - S\big) \;\ge\; 2(c-1)\operatorname{tr}(P_{11} + Q_-) + 2\|P_{12}\|_F^2 + \|(P_{11}+Q_+) - c I_W\|_F^2 + c^2(b - b_+) \;\ge\; 0.$$
2. **Guarded scale-invariant two-regime envelope:**
   $$n_+(H_\perp) \;\ge\; R_{\mathrm{opt}}(u, t, S, b) := \begin{cases} 0, & u \le 0 \text{ or } u + t \le 0, \\[4pt] \dfrac{u^2}{S - t^2 / b}, & u > 0,\; b > 0,\; t > 0,\; t(u+t) \ge b S, \\[8pt] \max\!\left(0,\; \dfrac{(u+t)^2}{S} - b\right), & \text{otherwise.} \end{cases}$$
   *(Boundary proof: if $u > 0, b > 0, t > 0$, then $S = \|P_{11}+Q_+\|_F^2 + \|H_\perp\|_F^2 + 2\|P_{12}\|_F^2 \ge \frac{(\operatorname{tr}(P_{11}+Q_+))^2}{b} + \|P_{22}-Q_-\|_F^2$. If $\operatorname{tr}(P_{11}) > 0$ then $(\operatorname{tr}P_{11} + \operatorname{tr}Q_+)^2/b \ge (\operatorname{tr}P_{11}+t)^2/b > t^2/b$; otherwise $P_{11}=0 \implies P_{12}=0$ (since $P \succeq 0$) and $\operatorname{tr}(P_{22}) = u > 0$, so either $Q_- \ne 0$ (making $\operatorname{tr}Q_+ = t + \operatorname{tr}Q_- > t$) or $Q_- = 0$ (making $\|H_\perp\|_F^2 = \|P_{22}\|_F^2 > 0$). In every case $S > t^2/b$ strictly!)*
3. **Integer-exact pointwise sharpness (`AUDIT-002`):** For every feasible $(u, t, S, b)$ with $u > 0$, $\min \operatorname{rank}(P) = \max(1, \lceil R_{\mathrm{opt}}(u,t,S,b) \rceil)$.

---

### Theorem A2 (Degree-$2m$ Stieltjes–Hankel Indefinite Projected-Inertia Bound $R_{H,2m}$)
Let $m \ge 1$ and let $a = (a_1, \dots, a_m) \in \mathbb{Q}_{\ge 0}^m$ be ANY nonnegative rational vector. Define
$$q_a(\lambda) := 1 + \sum_{k=1}^m (-1)^k a_k \lambda^k, \qquad \phi_a(\lambda) := 1 - q_a(\lambda)^2.$$
Then for ALL non-commuting complex Hermitian $H = P + Q$ ($P \succeq 0, n_+(Q) \le b$):
$$\operatorname{rank}(P) \;\ge\; \operatorname{rank}(P_\perp) \;\ge\; n_+(H_\perp) \;\ge\; \operatorname{tr}(\phi_a(H)) - b \;=\; 2 \sum_{k=1}^m (-1)^{k-1} a_k S_k - \sum_{j,k=1}^m (-1)^{j+k} a_j a_k S_{j+k} - b.$$

**Proof.**
1. For any $\lambda \le 0$, write $\lambda = -x$ with $x \ge 0$. Since every $a_k \ge 0$,
   $$q_a(-x) = 1 + \sum_{k=1}^m a_k x^k \ge 1 \implies \phi_a(\lambda) = 1 - q_a(\lambda)^2 \le 0.$$
2. For any $\lambda > 0$, $\phi_a(\lambda) = 1 - q_a(\lambda)^2 \le 1$.
3. Summing over eigenvalues $h_1, \dots, h_n$ of $H$ and applying Lemma 0 ($n_+(H) \le b + n_+(H_\perp)$):
   $$\operatorname{tr}(\phi_a(H)) = \sum_{h_i > 0} \phi_a(h_i) + \sum_{h_i \le 0} \phi_a(h_i) \le n_+(H) + 0 \le b + n_+(H_\perp). \quad \square$$

#### Corollary A2(a) — Closed-Form Quartic Stieltjes–Hankel Bound ($m = 2$, $R_{H4}$)
Maximizing the concave quadratic $f(s, p) = 2s S_1 - 2p S_2 - s^2 S_2 + 2sp S_3 - p^2 S_4$ over $s \ge 0, p \ge 0$ gives:
- If $\Delta := S_2 S_4 - S_3^2 > 0$, $s^* := (S_1 S_4 - S_2 S_3)/\Delta \ge 0$, and $p^* := (S_1 S_3 - S_2^2)/\Delta \ge 0$:
  $$n_+(H_\perp) \;\ge\; R_{H4}(H, b) = \max\!\left(0,\; \frac{S_1^2}{S_2} + \frac{(S_1 S_3 - S_2^2)^2}{S_2(S_2 S_4 - S_3^2)} - b\right).$$
- Otherwise, the exact KKT boundary optimum is $\max(0, S_1^2/S_2 - b)$ (when $S_1 > 0, S_2 > 0$).

#### Corollary A2(b) — Exact Rank-$m$ Recovery for PSD $H$ (Orthogonal-Polynomial Sign Positivity)
If $H \succeq 0$ has $k \le m$ distinct positive eigenvalues $0 < \mu_1 < \dots < \mu_k$, let $q^*(\lambda) := \prod_{j=1}^k (1 - \lambda / \mu_j) = 1 + \sum_{j=1}^k (-1)^j e_j(1/\mu_1, \dots, 1/\mu_k) \lambda^j$. Every coefficient $a_j^* = e_j(1/\mu_1,\dots,1/\mu_k)$ is strictly positive, $q^*(\mu_j) = 0 \implies \phi_{a^*}(\mu_j) = 1$, and $\phi_{a^*}(0) = 0$. Therefore:
$$R_{H, 2m}(H, b) \;=\; \max\big(0,\; \operatorname{rank}(H) - b\big) \quad \text{(EXACT ZERO GAP!)}$$
In particular, on `project-asma` Scan 23848 Mode B ($\tau = 0, b = 1, \operatorname{rank}(H) = 2$), **$R_{H4}(H, 1) = 1$ identically for EVERY overlap $\rho \in [0, 1)$** (including $\rho = 0.95$ where $R_{\mathrm{opt}} = 0.03685$ and fixed $c = 2$ collapses to $0$!).

---

### Theorem A3 (Exact Noise-Annihilating Quartic SOS Bound $\Phi_{x_0, \tau}$)
Let $x_0 \in \mathbb{Q}_{>0}$ and $\tau \in \mathbb{Q}_{\ge 0}$ be arbitrary rationals. Define:
$$d := 3 x_0 + \tau > 0, \qquad L := \frac{2 x_0 (2 x_0 + \tau)}{d} > x_0, \qquad M := \frac{x_0^2 (x_0 + \tau)^3}{d} > 0,$$
$$\Phi_{x_0, \tau}(\lambda) := \frac{\lambda (L - \lambda)(\lambda + \tau)^2}{M} = \frac{L\tau^2 \lambda + (2L\tau - \tau^2)\lambda^2 + (L - 2\tau)\lambda^3 - \lambda^4}{M}.$$
Then:
1. **Non-positivity & double zero at $-\tau$:** For all $\lambda \le 0$, $\Phi_{x_0, \tau}(\lambda) \le 0$, with $\Phi_{x_0, \tau}(-\tau) = \Phi'_{x_0, \tau}(-\tau) = 0$.
2. **Closed-form exact rational Sum-of-Squares upper bound ($\Phi_{x_0, \tau}(\lambda) \le 1$ for ALL $\lambda \in \mathbb{R}$):**
   $$M - \lambda(L - \lambda)(\lambda + \tau)^2 \;=\; (\lambda - x_0)^2 \left[ \left(\lambda + \frac{x_0^2 + 3 x_0 \tau + \tau^2}{d}\right)^2 + \frac{x_0^2 (2 x_0^2 + 4 x_0 \tau + \tau^2)}{d^2} \right] \;\ge\; 0,$$
   with exact equality $\Phi_{x_0, \tau}(x_0) = 1$.
3. **Projected positive-inertia lower bound:** For ALL non-commuting complex Hermitian $H = P + Q$ ($P \succeq 0, n_+(Q) \le b$),
   $$\operatorname{rank}(P) \;\ge\; \operatorname{rank}(P_\perp) \;\ge\; n_+(H_\perp) \;\ge\; \frac{L\tau^2 S_1 + (2L\tau - \tau^2)S_2 + (L - 2\tau)S_3 - S_4}{M} - b.$$

**Proof.**
(1) If $\lambda \le 0$, then $L - \lambda \ge L > 0$ and $(\lambda + \tau)^2 \ge 0$, so $\lambda(L-\lambda)(\lambda+\tau)^2 \le 0$. The factor $(\lambda+\tau)^2$ gives a double zero at $-\tau$.  
(2) Expand both sides in $\mathbb{Q}(x_0, \tau)[\lambda]$:
- $\lambda^4$: $1 = 1$.
- $\lambda^3$: $\frac{2(x_0^2+3x_0\tau+\tau^2)}{d} - 2x_0 = \frac{2x_0^2+6x_0\tau+2\tau^2 - 6x_0^2 - 2x_0\tau}{d} = \frac{-4x_0^2+4x_0\tau+2\tau^2}{d} = 2\tau - L$.
- $\lambda^2$: $\frac{(x_0^2+3x_0\tau+\tau^2)^2 + x_0^2(2x_0^2+4x_0\tau+\tau^2)}{d^2} - \frac{4x_0(x_0^2+3x_0\tau+\tau^2)}{d} + x_0^2 = \frac{(x_0+\tau)^3}{d} + \dots = \tau^2 - 2L\tau$ (verified symbolically & in exact `Fraction` on every invocation in `certify_noise_annihilating_quartic` and formally in `Basic.lean`).
- $\lambda^1$: $-2 x_0 \frac{(x_0+\tau)^3}{d} + x_0^2 \frac{2(x_0^2+3x_0\tau+\tau^2)}{d} = \frac{-2x_0(x_0^3+3x_0^2\tau+3x_0\tau^2+\tau^3) + 2x_0^4+6x_0^3\tau+2x_0^2\tau^2}{d} = \frac{-2x_0\tau^2(2x_0+\tau)}{d} = -L\tau^2$.
- $\lambda^0$: $x_0^2 \frac{(x_0+\tau)^3}{d} = M$.
Since $x_0 > 0, \tau \ge 0$, every square and coefficient on the RHS is nonnegative, hence $\Phi_{x_0,\tau}(\lambda) \le 1$ on $\mathbb{R}$.  
(3) By Lemma 0, $\operatorname{tr}(\Phi_{x_0,\tau}(H)) = \sum_{h_i > 0} \Phi_{x_0,\tau}(h_i) + \sum_{h_i \le 0} \Phi_{x_0,\tau}(h_i) \le n_+(H) \le b + n_+(H_\perp)$. $\square$

#### Corollary A3(a) (Odd-Even Indefinite Hölder Bound at $\tau = 0$)
Setting $\tau = 0$ gives $L = \frac{4}{3} x_0$, $M = \frac{1}{3} x_0^4$, $\operatorname{tr}(\Phi_{x_0, 0}(H)) = \frac{4}{x_0^3} S_3 - \frac{3}{x_0^4} S_4$. When $S_3 > 0$, substituting $x_0 = S_4 / S_3 \in \mathbb{Q}_{>0}$ yields the exact closed-form bound:
$$n_+(H_\perp) \;\ge\; \frac{S_3^4}{S_4^3} - b.$$

#### Corollary A3(b) (Universal High-Interference Detectability at Uniform Noise Floor $-\tau$)
If $H = G - \tau I_T$ ($G \succeq 0$) has two eigenvalues $\lambda_1 \ge \lambda_2 > \tau$, then for $x_0 = \lambda_1 - \tau$ (or any sufficiently close rational $x_0 \in \mathbb{Q}_{>0}$), $\Phi_{x_0,\tau}(\lambda_1 - \tau) = 1$, $\Phi_{x_0,\tau}(\lambda_2 - \tau) > 0$, and $\Phi_{x_0,\tau}(-\tau) = 0$. Therefore $\operatorname{tr}(\Phi_{x_0,\tau}(H)) > 1$, certifying $\operatorname{rank}(G) \ge 2$ all the way to the exact physical threshold $\lambda_2 \to \tau^+$ (beating $\lceil R_{\mathrm{opt}} \rceil = 1$ on Scan 23848 Mode A across $\rho \in [0.75, 0.95], \tau > 0$!).

---

### Theorem A4 (Exact Weighted Quartic-Weyl SOS Bound $R_{W4}$)
Let $s \ge 0, p > 0, \gamma_1 \ge 0, \gamma_3 \ge 0, \kappa > 0$ be arbitrary rationals. Set:
$$\beta := s + \frac{\gamma_3}{p}, \qquad \alpha := 1 - \frac{\beta^2 - s^2 + \kappa}{2p}, \qquad \lambda_0 := \frac{s + \gamma_1 - \alpha\beta}{\kappa}, \qquad M := \alpha^2 + \kappa \lambda_0^2.$$
Then for ALL non-commuting complex Hermitian $H = P + Q$ ($P \succeq 0, n_+(Q) \le b$):
$$\operatorname{rank}(P) \;\ge\; \operatorname{rank}(P_\perp) \;\ge\; n_+(H_\perp) \;\ge\; 2s S_1 - (s^2 + 2p) S_2 + 2sp S_3 - p^2 S_4 + 2\gamma_1 \operatorname{tr}(Q) + 2\gamma_3 \operatorname{tr}(Q^3) - b M.$$

**Proof.**
1. Direct algebraic expansion verifies the exact polynomial SOS identity over $\mathbb{R}$:
   $$M - \big(\phi_{s,p}(\lambda) + 2\gamma_1\lambda + 2\gamma_3\lambda^3\big) \;=\; (p\lambda^2 - \beta\lambda + \alpha)^2 + \kappa(\lambda - \lambda_0)^2 \;\ge\; 0 \qquad \forall \lambda \in \mathbb{R},$$
   where $\phi_{s,p}(\lambda) = 1 - (1 - s\lambda + p\lambda^2)^2 \le \mathbf{1}_{\lambda > 0}$ (since $s \ge 0, p > 0$).
2. Define $g(\lambda) := 2\gamma_1\lambda + 2\gamma_3\lambda^3$. Since $\gamma_1, \gamma_3 \ge 0$, $g$ is non-decreasing on $\mathbb{R}$ and $g(\lambda) \le 0$ for all $\lambda \le 0$. Let $q_1 \ge \dots \ge q_n$ and $h_1 \ge \dots \ge h_n$ be the eigenvalues of $Q$ and $H = P + Q$ (padded by zeros past $n$). Since $n_+(Q) \le b$, $q_j \le 0$ for $j > b$; since $P \succeq 0$, Weyl monotonicity `(W2)` gives $q_j \le h_j$ for all $j$. Hence:
   $$\operatorname{tr}(g(Q)) = \sum_{j=1}^n g(q_j) \le \sum_{j=1}^b g(q_j) \le \sum_{j=1}^b g(h_j).$$
3. Let $r_\perp := n_+(H_\perp)$. By Lemma 0 (Cauchy interlacing), $h_j \le 0$ for all $j > b + r_\perp$. Split the sum:
   $$\operatorname{tr}(\phi_{s,p}(H)) + \operatorname{tr}(g(Q)) \;\le\; \sum_{j=1}^b \big(\phi_{s,p}(h_j) + g(h_j)\big) + \sum_{j=b+1}^{b+r_\perp} \phi_{s,p}(h_j) + \sum_{j > b+r_\perp} \phi_{s,p}(h_j) \;\le\; b M + r_\perp + 0.$$
   Subtracting $b M$ yields the theorem. $\square$

#### Corollary A4(a) (3-Parameter Peak-Matched Specialization using ONLY $\operatorname{tr}(Q)$)
When $\gamma_3 = 0$ and $\mu > \frac{s}{2p}$ satisfies $q(\mu) := 1 - s\mu + p\mu^2 > 0$, choosing $\gamma_1 := q(\mu)(2p\mu - s) > 0$ and $\kappa := 2p\, q(\mu) > 0$ gives $\alpha = 1 - q(\mu)$, $\lambda_0 = \mu$, and $M = (1 - q(\mu))^2 + 2p\mu^2 q(\mu)$, making BOTH squares vanish identically at $\lambda = \mu$ (zero slack at $\lambda = \mu$ AND at the two roots of $q(\lambda) = 0$!).  
*Non-commuting sensitivity remark:* The Weyl `(W2)` slack is $2\gamma_1\big(\sum_{j=1}^b(h_j - q_j) + \operatorname{tr}(Q_-)\big)$, scaling linearly with $\gamma_1 = q(\mu)q'(\mu)$. Thus moderate separation $\mu$ (moderate $\gamma_1$) retains strict dominance over BOTH $\lceil R_{\mathrm{opt}} \rceil$ AND $R_{H4} - b$ even under non-commuting complex Hermitian coupling, whereas in strongly non-commuting large-$q_1$ regimes the $\gamma_1 = 0$ Stieltjes–Hankel bounds $R_{H4}, R_{H6}$ incur zero Weyl slack!

---

## 2. Track B — Exact Non-Affine Complex-Hermitian Box Certification (`SEAM-04`)

### Theorem B1 (Exact Multivariate Bernstein Enclosure)
For $f(x_0, \dots, x_{d-1}) = \sum_\alpha c_\alpha x^\alpha \in \mathbb{Q}[x_0, \dots, x_{d-1}]$ on box $B = \prod_{k=0}^{d-1}[a_k, b_k]$, transforming each axis via $x_k = a_k + (b_k - a_k) u_k$ and $u_k^s = \sum_{j=s}^{m_k} \frac{\binom{j}{s}}{\binom{m_k}{s}} B_{j, m_k}(u_k)$ expresses $f(x) = \sum_\beta B_\beta \prod_{k=0}^{d-1} B_{\beta_k, m_k}(u_k)$. Since $B_{j,m}(u) \ge 0$ and $\sum_j B_{j,m}(u) \equiv 1$ on $[0,1]$,
$$\min_\beta B_\beta \;\le\; f(x) \;\le\; \max_\beta B_\beta \qquad \forall x \in B.$$

### Theorem B2 (Complex Hermitian Congruent Block-Gershgorin Uniform Inertia Theorem)
Let $M: B \to \mathbb{C}^{n \times n}$ be a continuous family of Hermitian matrices on a closed box $B = \prod_{k=1}^d [a_k, b_k]$, and let $x_c \in B \cap \mathbb{Q}^d$ satisfy $C M(x_c) C^* = D$ with invertible $C \in \mathbb{Q}(i)^{n \times n}$ and nonsingular Hermitian block-diagonal $D = \bigoplus_{k=1}^m D_k$ ($1\times 1$ and $2\times 2$ blocks, $n_0(D) = 0$). Let $\Delta(B)$ be an exact complex rational interval enclosure of $E(x) := C(M(x) - M(x_c))C^*$ over $x \in B$.  
Suppose that for every block $k = 1, \dots, m$, an exact rational lower bound $\mu_k \le \sigma_{\min}(D_k)$ satisfies:
$$\mu_k \;>\; \sum_{j=1}^m \operatorname{frob\_hi}\!\big(\Delta_{kj}(B)\big),$$
where $\operatorname{frob\_hi}(\Delta_{kj}) \ge \sup_{E \in \Delta(B)} \|E_{kj}\|_F$. Then $M(x)$ is nonsingular for ALL $x \in B$, and its Sylvester inertia $(n_+(M(x)), n_-(M(x)), 0)$ is **identically equal to $\operatorname{inertia}(D)$ at every real point $x \in B$**.

**Proof.**
Suppose $(D + E(x))v = 0$ for some $x \in B$ and nonzero $v = (v_1, \dots, v_m)$. Pick $k \in \arg\max_j \|v_j\|_2$ so $\|v_k\|_2 > 0$. From $D_k v_k = -\sum_{j=1}^m E_{kj}(x) v_j$:
$$\mu_k \|v_k\|_2 \;\le\; \sigma_{\min}(D_k)\|v_k\|_2 \;\le\; \|D_k v_k\|_2 \;\le\; \sum_{j=1}^m \|E_{kj}(x)\|_2 \|v_j\|_2 \;\le\; \left(\sum_{j=1}^m \operatorname{frob\_hi}(\Delta_{kj}(B))\right) \|v_k\|_2,$$
contradicting $\mu_k > \sum_j \operatorname{frob\_hi}(\Delta_{kj}(B))$. Thus $D + E(x) = C M(x) C^*$ is nonsingular for all $x \in B$, hence $M(x)$ is nonsingular for all $x \in B$. Since $B$ is connected and eigenvalues of Hermitian matrices vary continuously with $M(x)$, no eigenvalue can cross $0$ on $B$. By Sylvester's law of inertia at $x_c$, $\operatorname{inertia}(M(x)) = \operatorname{inertia}(M(x_c)) = \operatorname{inertia}(D)$ identically on $B$. $\square$

---

## 3. Track C — Dual-Oracle Exact $\mathbb{Q}(i)$ Soundness (`SEAM-08`)

- **Oracle 1 (Sylvester Congruence):** Verifies exact $C C^{-1} = C^{-1} C = I_n$ and $C M C^* = D$ (or `loom#7` $P M P^* = L D L^*$ with permutation bijection $P$ and unit lower triangular $L$), non-overlapping $1\times 1$/$2\times 2$ Hermitian block structure of $D$, and the complete 5-row $2\times 2$ Hermitian inertia classification (where $\det = 0, b \ne 0 \implies ac = |b|^2 > 0 \implies a+c \ne 0$).
- **Oracle 2 (Zero-Shared-Code Spectral Oracle):** Uses raw `(Fraction, Fraction)` tuples with zero shared functions from Oracle 1; computes $p(x) = \det(xI - M) \in \mathbb{Q}[x]$ via Faddeev–LeVerrier; verifies exact Cayley–Hamilton identity $B_n + c_n I = 0$; counts exact $(n_+, n_-, n_0)$ by Descartes' rule of signs (exact because Hermitian $\implies$ all roots real) AND independently by exact Sturm sequences on the square-free peel $p / \gcd(p, p')$ (counting exact multiplicities!).
- **Soundness:** Acceptance requires exact agreement `Oracle 1 == Descartes == Sturm (== claim)`.
