# Findings of the formalization

Findings of the formalization of *Tight Sample Complexity Bounds for Entropic Best Policy
Identification* (Essakine, Vernade, COLT 2026, arXiv:2605.13717v1) that are not errors of the
paper: hypotheses that are not needed, slack in the constants, implicit assumptions of the
paper's proofs. The errors of the paper are in `notes/paper-errata.md` (`E1`, `E2`, …).

## Phase 1 (statements)

* The concentration events of Lemma 5 hold for *any* algorithm, not only Entropic-BPI (used
  as such in the blueprint).
* The bonus with the KL rate $\alpha$ (E4) does not change the order of the sample
  complexity: the $\alpha$-term is absorbed by the additive $84H$ term, which is already in $\alpha$.
* The asymptotic form of the corrected Theorem 4 has $e^{4|\beta|\varepsilon}$ instead of the paper's
  $e^{2\max\{\beta,0\}\varepsilon}$, because a single progress constant
  $\kappa = (e^{|\beta|\varepsilon}-1)e^{-2|\beta|\varepsilon}/2$ is used for both signs; under
  $\varepsilon \le 2/(|\beta|HS)$ this factor is at most $e^8$.
* The Lean model needs no conditioning on null events: the entropic variance
  $\sigma Q^\pi_h(s,a)$ is defined through the law "play $a$ at $(s,h)$, then $\pi$", and the
  filtration of the empirical chapter is $\sigma(\mathrm{hist}_t, \pi^{t+1})$.
* Comparator (the tool that checks the headline statements) forced a coding discipline on the
  definitions: no nested proofs, no matchers, no real numerals $\ge 2$ (see
  `notes/lean-design.md`); this is a property of Lean's auxiliary declarations, not of the paper.

## Phase 2 (proofs)

* **Chapter "Elementary inequalities" (2026-09-16).** Mathlib already has the Bhatia–Davis
  inequality (`ProbabilityTheory.variance_le_sub_mul_sub`), so the paper's Lemma 24 reduces to
  the algebraic maximization `sub_mul_sub_div_sq_le`, which needs no restriction of the mean to
  $[m, M]$. The root of the quadratic inequality $x^2 \le bx + c$ needs no sign assumption on
  $x$. The self-bounding inequality (Lemma 29) is proved in the sharp form
  $\tau \le K(\tfrac85\log M)^2 + 1$ for every $M \ge 4\alpha K$, from which both the
  $(C + \sqrt D)^2$ and the $(C + D)^2$ forms of $C_1$ follow; the bound
  $\log y \le y^\gamma/(e\gamma)$ used for it sharpens Mathlib's `Real.log_le_rpow_div` by a
  factor $e$. The logarithmic sum bound (Lemma 28) is stated for sums over $t < T$ with the
  bound $3\log(U_T + 1)$ (and $4\log(U_T + 1)$).
* **Chapter "Model" (`chap:mdp`, 2026-09-16).** The exponential Bellman equation
  $Z^\pi_h(s) = U^\pi_h(s, \pi_h(s))$ is *false* for general reward kernels when the value is a
  Bochner integral: if the exponential return is not integrable its integral is $0$ while the
  right-hand side can be positive. The formalization proves the identity for the Lebesgue
  integrals without hypothesis and for the values under the hypothesis that the rewards have
  finite exponential moments of order $\beta$ (automatic for the paper's deterministic rewards in
  $[0, 1]$). The ranges of $Z^\pi$, $U^\pi$, $Z^*$, $U^*$ follow analytically from the Bellman
  equation; the optimal Bellman equation and the optimality of the greedy policy need only finite
  exponential moments (not a reward function in $[0, 1]$), and the value-gap identities only
  $Z^\pi_h(s) > 0$. The Markov property of the trajectory law of a stationary policy
  (not in LML) is proved by uniqueness of the Ionescu–Tulcea measure.
* **Chapter "Change of measure" (`chap:pre_info`, 2026-09-16).** The one-sided change of measure
  (the paper's Lemma 17 with $\tau$ almost surely finite under the first environment only) is
  proved; mutual absolute continuity of the arm distributions is not needed ($0 \cdot \infty = 0$
  in $[0, \infty]$). The convexity step of the proof only needs the bound
  $\klbin(x, y) \le \max\{\klbin(x, y_1), \klbin(x, y_2)\}$ for $y \in [y_1, y_2]$, proved by
  unimodality ($\partial_y \klbin(x, y) = (y - x)/(y(1 - y))$), and the lower bound
  $\klbin(x, y) \ge (1 - x)\log\frac1{1 - y} - \log 2$ does not need $x \le 1$. The proof avoids
  auxiliary truncated algorithms: the stopping rule itself separates $\{\tau \le M\}$ from
  $\{\tau > M\}$ on the law of the history stopped at $M$. The lower bound needs the form of the
  theorem in which the alternative instance appears only through the law of the output
  (`IdentAlg.outputMeasure`), since PAC is a property of that law and no run in the alternative
  instance is given.
* **Chapter "Concentration inequalities" (`chap:pre_concentration`, 2026-09-16).** Lemma 19
  (Sanov) is proved with $(n+1)^{m-1}$, confirming the correction of E22. Lemma 20 (Bernoulli
  maximal inequality) and Lemma 21 (self-normalized Bernstein, with the smaller term
  $\log(8(1+\sqrt{2t}))$) hold for every $\delta > 0$ and all $t \ge 0$; the explicit form of
  Lemma 21 already holds at $t = 0$ ($L_0 = \log(4e/\delta) > 2$). Lemma 22 (KL–Bernstein) and
  Lemmas 25–26 (variance transport) hold for arbitrary probability measures, not only on finite
  sets, and the second inequality of Lemma 26 holds with the constant $1$ in place of $3$. The
  inequality $h(x) \ge x^2/(2(1+x/3))$ for the Poisson Cramér transform follows from the Padé
  bound $\log(1+x) \ge (6x + 5x^2)/(6 + 8x + 2x^2)$ with a single derivative; Ville's inequality
  holds with the bound $\mathbb E[M_0]/c$.
* **Chapter "Algorithm" (`chap:algorithm`, 2026-09-16).** The ranges of the backups and of the
  certificate need $\delta \le 1$ (for the nonnegativity of the rates $\log(3SAH/\delta)$) and
  hold uniformly in the sign of $\beta$ when written between $\min\{1, e^{\beta j}\}$ and
  $\max\{1, e^{\beta j}\}$; the run properties of Entropic-BPI hold in any environment.
* **Chapter "Finite-horizon MDP theory" (`chap:pre_mdp`, agent D, 2026-09-16).** No error in the
  paper for this chapter. The entropic-variance identities (the Bellman recursion of the entropic
  variance and its telescoping sum) need finite exponential moments of order $2\beta$ of the
  rewards, automatic for a reward function in $[0, 1]$. The bound on the normalized variance of
  the exponential return by $G_{\max}$ needs only rewards in $[0, 1]$ (not deterministic rewards)
  and holds at every starting pair $(s, h)$. The Cauchy–Schwarz inequality along a trajectory
  holds for weights of any sign, under integrability in place of boundedness, and the unrolling
  of a backward recursive inequality only needs a nonnegative multiplier. The visits of a
  state-action pair are dominated by an i.i.d. sample in the form used by the concentration
  events (probability of a set of next-state sequences at the first $n$ visits at most its
  product-measure probability); the independence statement with a general test function is not
  needed.
* **Rates and counting argument (`chap:sample_complexity`, main thread, 2026-09-16).** The
  monotonicity of $x \mapsto \alpha(x)/x$ holds on $(0, \infty)$, with a proof by
  $\log(1 + u) \le u$ instead of derivatives. Lemma 27 holds on the counts event under the
  corrected hypotheses of `rem:sc_lemma27` (the rate dominates $\alpha^{\mathrm{cnt}}(\delta) > 1$,
  i.e.\ $\delta \le 1$), and the counting argument (Lemma 28 summed over the triples) holds with
  the constant $16$ of `rem:sc_counting_constant` for every $T \ge 0$.
* **Time-uniform KL concentration (`lem:empirical_kl_time_uniform`, agent F, 2026-09-16).** The
  bound $\Prob(\exists n \ge 1, n\KL(\hat q_n \| p) \ge \log(1/\delta') + (m-1)\log(n+1) + 1 +
  \frac12\log n) \le \delta'$ is proved with the exact constants of the blueprint, for an arbitrary
  law on a finite set and every $\delta' > 0$. The Dirichlet mixture over the simplex is replaced
  by the Laplace (rule of succession) product
  $M_n = \prod_{k<n} \frac{(N_k(\xi_k) + 1)/(k + m)}{p(\xi_k)}$, which has the same value
  $(m-1)!\prod_x N_n(x)!/(n + m - 1)!$ and is a nonnegative supermartingale without restricting
  to the support of $p$; no integral over the simplex is needed. This confirms that the rate
  $\alpha(n, \delta) = \log(3SAH/\delta) + S\log(8e(n+1))$ of the paper is valid time-uniformly,
  while a union bound over $n$ of Sanov's bound is not (`rem:empirical_sanov_union`).
* **Analysis on the good event (`chap:analysis_pos`, `chap:analysis_neg`, agent E, 2026-09-16).**
  No new error: the blueprint statements (with the corrected bonus, whose third term carries the
  KL rate $\alpha$, the clips, and the constants $3$, $3/H$, $36$, $13$, $84$) are proved for both
  signs of $\beta$. The proofs have slack: the concentration lemma gives
  $(2H + 2\sqrt2 + 3)B\alpha \le (4H + 5)B\alpha$, the third term of Lemmas 11 and 16 gives
  $(H + 2\sqrt2 + 2/3)B\alpha$, and the certificate recursion holds with $1 + 10/H$ and $77H$ in
  place of $1 + 13/H$ and $84H$. All the lemmas hold for $\delta \in (0, 1]$ and are statements
  about a fixed history satisfying the pointwise consequences of the good event: they need no
  run hypothesis. The ranges of the auxiliary values $\mathring Z$, $\mathring U$ hold for every
  number of remaining steps without any event. The KL–Bernstein and variance-transport
  inequalities are used in vector form for functions with values in $[c, c + b]$, $b \ge 0$, so
  the case of a zero range needs no special treatment.
* **Probabilities of the concentration events (`chap:empirical`, agent G, 2026-09-16).** The
  three events of the analysis and the good event have the probabilities of the paper's
  Lemma 5, in every run of every algorithm, with the corrected union bound
  $\delta/(3SAH)$ per triple (`rem:empirical_bernstein_index`) and the Bernstein inequality
  indexed by the number of visits. The KL and counts events hold for every $\delta > 0$, the
  Bernstein event for $\delta \in (0, 1]$, and the good event for every $\beta$ (including
  $\beta = 0$). The Bernoulli maximal inequality already covers $t = 0$, so the counts event
  needs no separate case. The KL event only needs the rate $\log(3SAH/\delta) + S\log(e(n+1))$:
  the factor $8$ of the paper's $\alpha(n, \delta)$ is slack there, and is used only by
  $\alpha^*$ (through $4e(2n+1) \le 8e(n+1)$). No measurability of the events is needed: the
  proofs are countable union bounds on complements.
* **Tail of the analysis and Theorem 4 (agent H, 2026-09-16).** Both conclusions of Theorem 4
  are proved for the frozen statements. Neither uses the hypothesis $\eps \le 2/(|\beta|HS)$ nor
  $\delta < 1$: $\delta \in (0, 1]$ and $\eps > 0$ suffice (`rem:sc_hypotheses`). The constants
  $10^9$ and $10^{10}$ of the upper bound have a slack of a factor about $16$; even the crude
  bound $e^{13} \le 3^{13}$ suffices. The claim that the stopping-time bound holds pointwise on the
  good event silently uses that the policy played in each episode is the greedy policy of the
  history, which holds almost surely in a run: the counting argument is about the policies
  played, the certificate bound about the greedy policies. The degenerate horizon $H = 0$, where
  the blueprint's $D \ge 1$ fails, is handled separately (the progress hypothesis is then
  contradictory). The PAC property is transferred from one run to the law of the output with
  LML's canonical run.
