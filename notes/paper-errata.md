# Errata of Tight Sample Complexity Bounds for Entropic Best Policy Identification

Errors found in the paper while formalizing it, with their corrections. Each entry gives where the
error is (the revision of the paper, the result, the page or equation), the error, the correction,
the declarations that state the corrected form, the kind of error and when it was found. Entries
are numbered `E1`, `E2`, … and never renumbered.

The revision is arXiv:2605.13717v1, identical to the COLT 2026 submission (`source/`). Results
carry the paper's numbers (one counter for all environments; the appendix restatements of
Theorems 4 and 3 are Theorems 6 and 18); the appendices are A (concentration events), B (algorithm
analysis: B.1 for $\beta > 0$, B.2 for $\beta < 0$), C (lower bound), E (concentration
inequalities) and F (technical results). E1–E10 concern the formalized statements and the
definitions they rest on; E11–E25 only proofs or constants. Blueprint labels refer to
`blueprint/src/chapters/`, and Lean names without a namespace are in `Essakine2026Tight`. Findings
of the formalization that are not errors of the paper are in `notes/formalization-findings.md`.

## E1. Theorem 3: the bound on the binary divergence is false

- **Where:** arXiv:2605.13717v1, Theorem 3, its proof in Appendix C (Theorem 18): the bound
  $d(p_-, p_+) \le (p_+ - p_-)^2 / (p_-(1 - p_-))$.
- **Error:** the elementary bound $d(x, y) \le (x - y)^2 / (y (1 - y))$ has the *second* argument
  in the denominator, so the displayed inequality bounds $d(p_+, p_-)$, not $d(p_-, p_+)$; and
  $d(p_-, p_+) \to \infty$ as $p_+ \to 1$ while Condition A only guarantees $p_+ < 1$, with no
  margin. Counterexample, admissible for the paper's Condition A: $c = 1$,
  $e^{\beta\varepsilon} = 1.23$, $p_- = 1/4$, $p_+ \approx 0.99675$, for which
  $d(p_-, p_+) \approx 3.7 > 1.61$ (the paper's bound).
- **Correction:** Condition A is restated with a margin equivalent to $p_+ \le (1 + p_-)/2$:
  $e^{|\beta|\varepsilon} - 1 \le c(2c+1)/(4(3c+2))$ for $\beta > 0$ and
  $e^{|\beta|\varepsilon} - 1 \le c/(10c + 8)$ for $\beta < 0$ (for $\beta < 0$ this is exactly
  the paper's $e^{|\beta|\varepsilon} \le (11c+8)/(10c+8)$; the paper's caps $16/13$ and $11/10$
  are not needed). Then
  $d(p_-, p_+) \le \Delta^2 / (p_+(1-p_+)) \le 72 (c+1)(e^{|\beta|\varepsilon}-1)^2 / c^2$ for
  both signs. Blueprint `def:condition_a`, `lem:hard_params_valid`, `lem:hard_kl_params`,
  `rem:lb_kl_paper`.
- **Lean:** `ConditionA` states the corrected condition, a hypothesis of
  `exists_hardMDP_lowerBound_le_lintegral_stoppingTime`; the bound is
  `klBerReal_hardPMinus_hardPPlus_le`.
- **Kind:** false statement.
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E2. Theorem 3: Condition A is stated with the wrong horizon

- **Where:** arXiv:2605.13717v1, Theorem 3 (Condition A), and its proof in Appendix C.
- **Error:** Condition A is stated with $c = e^{|\beta| H} - 1$, but the construction uses
  $c' = e^{|\beta| H'} - 1$ with the effective horizon $H' = H - \bar H - d \le H$. The
  admissibility thresholds ($0 < p_- < p_+ < 1$) are increasing in $c$, so the condition with $H$
  does not imply admissibility with $H'$.
- **Correction:** Condition A is assumed for $H' = H - \lfloor H/3 \rfloor - d$.
- **Lean:** `effHorizon`, and the hypothesis `ConditionA β (effHorizon S A H) ε` of
  `exists_hardMDP_lowerBound_le_lintegral_stoppingTime`.
- **Kind:** missing hypothesis.
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E3. Theorem 3: the gap Δ of the hard instances

- **Where:** arXiv:2605.13717v1, proof of Theorem 3 in Appendix C, the choice of $\Delta$.
- **Error:** for $\beta < 0$ the gap $\Delta$ is off by a factor 2 from the equation
  $V^{\mathcal M_u,*} - V^{\mathcal M_u}(\pi) = \varepsilon$ it is supposed to solve, and for both
  signs the exact-$\varepsilon$ choice does not give the *strict* suboptimality that the PAC bad
  event ($V^* - V^{\hat\pi} > \varepsilon$) requires.
- **Correction:** $\Delta = (q-1)(3c+2)/(c(c+1))$ for $\beta > 0$ and
  $(q-1)(3c+2)/(c(c+1)(2q-1))$ for $\beta < 0$, with $q = e^{|\beta|\varepsilon}$, so that a
  non-realizing policy is $|\beta|^{-1}\log(2q-1) > \varepsilon$ suboptimal. Blueprint
  `def:hard_params`, `lem:hard_eps_suboptimal`, `rem:lb_params`.
- **Lean:** `hardDelta`, `lt_optEntropicValue_sub_entropicValue_hardMDP`.
- **Kind:** wrong constant.
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E4. Exploration bonus: the third term must carry the KL rate α, not α*

- **Where:** arXiv:2605.13717v1, Section 4, equations (bonus positive) and (bonus_negative), and
  the proof of Lemma 11.
- **Error:** the bonus has the third term $4H e^{\beta(H-h)}\alpha^*(n)/n$, while the statement of
  Lemma 7 has $\alpha$. The proof of Lemma 11 needs
  $(2H + 2/3) e^{\beta(H-h)} \alpha(n)/n \le b_h^t$, which fails with $\alpha^*$ (as small as
  $\alpha/S$).
- **Correction:** the bonus uses $\alpha$ in its third term. Blueprint `def:bonus`,
  `rem:pos_constants_bonus`. This does not change the order of the sample complexity: the
  $\alpha$-term is absorbed by the additive $84H$ term, which is already in $\alpha$.
- **Lean:** `bonus`, in the definition of `entropicBPI`.
- **Kind:** wrong constant (the rate of a term of the algorithm).
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E5. The clips of the optimistic backups and of the certificate are off by one

- **Where:** arXiv:2605.13717v1, Section 4 and equation (optimism_equation_positive) (the clip of
  $\widetilde U_h^t$), and Appendix B (the clip of the certificate).
- **Error:** $\widetilde U_h^t$ is clipped at $e^{\beta(H-h-1)}$; with the paper's 1-indexed $h$,
  $U^*_h$ ranges in $[1, e^{\beta(H+1-h)}]$, so optimism $U^* \le \widetilde U$ fails at $h = H$
  ($e^{-\beta} < 1 \le U^*_H$). The certificate clip $e^{\beta(H-h)}$ does not dominate
  $\widetilde Z_H - \mathring Z_H \le e^{\beta} - 1$ when $\beta > \log 2$.
- **Correction:** the clip $e^{\beta(H+1-h)}$ for both. Blueprint `def:backups`,
  `def:certificate`, `rem:algorithm_clips`, `rem:algorithm_cert_clip`.
- **Lean:** `stepU`, `certStep` (the clip `Real.exp (β * (k + 1))`, with `k = H - h` the number
  of steps after the step).
- **Kind:** typo (off by one or two).
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E6. Algorithm 1: the greedy policy for β < 0

- **Where:** arXiv:2605.13717v1, Algorithm 1, the greedy policy for $\beta < 0$.
- **Error:** Algorithm 1 writes $\arg\min_a \widetilde U$, while the analysis of Appendix B.2
  (Lemmas 14, 16) needs $\arg\min_a \underline U$.
- **Correction:** $\arg\min_a \underline U$. Blueprint `def:greedy`, `rem:algorithm_greedy_neg`.
- **Lean:** `greedy`.
- **Kind:** typo.
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E7. The stopping condition for β < 0

- **Where:** arXiv:2605.13717v1, Appendix B.2, the stopping condition.
- **Error:** the threshold is written $(e^{\beta\varepsilon} - 1)\underline Z_1$, which is negative:
  the algorithm would never stop.
- **Correction:** $(1 - e^{\beta\varepsilon})\underline Z_1$, as in the box of Algorithm 1.
- **Lean:** `stopCond`.
- **Kind:** typo.
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E8. Lemma 29 (self-bounding inequality) is false as stated

- **Where:** arXiv:2605.13717v1, Lemma 29 (Appendix F, from Ménard et al. 2021), the constant
  $C_1$.
- **Error:** counterexample: $\alpha = e$, $B = E = 1$, $C = 1000$, $A = D = 10^{-6}$,
  $\tau = 4\cdot 10^8$ satisfies the hypothesis but violates the conclusion with
  $C_1 = \frac85\log(11\alpha^2(A+E)(C+D))$.
- **Correction:** the factor $(C + D)$ in $C_1$ must be squared:
  $C_1 = \frac85 \log(11 \alpha^2 (A+E)(C+D)^2)$, proved for $A, B, C, D \ge 0$, $E \ge B$,
  $\alpha \ge e$, $D \ge 1$; the form with $(C + \sqrt D)^2$ holds without $D \ge 1$. Through the
  constant of Theorem 4, this changes the statement of Theorem 4. Blueprint `lem:self_bounding`,
  `lem:pana_self_bounding_core`, `rem:pana_self_bounding_paper`.
- **Lean:** `Real.le_of_le_sqrt_mul_add`, `Real.le_of_le_sqrt_mul_add'`, and `logFactor` in
  `upperBound`.
- **Kind:** false statement.
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E9. Theorem 4: the final bound

- **Where:** arXiv:2605.13717v1, Theorem 4 (and Theorem 6, its restatement in Appendix B), the
  two-term bound and its "in particular" single-term form.
- **Error:** the "in particular" single-term form assumes that the first term of the two-term bound
  dominates, which the hypothesis $\varepsilon \le 2/(|\beta| H S)$ does not guarantee (the second
  term can dominate when $G_{\max}$ is small). The displayed two-term bound omits the absolute
  constants of its own $C$ and $D$ (e.g. $(36 e^{13})^2$), and its $C_1$ is not Lemma 29's $C_1$
  at its $C$, $D$. Its constant $C_2$ contains the typos $e^{\beta\varepsilon}$ (for
  $e^{|\beta|\varepsilon}$) and $e^{|\beta H}$.
- **Correction:** the bound obtained by applying the corrected Lemma 29 (E8) to the recursive
  inequality of the analysis, in its two-term form, with generous absolute constants ($10^9$ and
  $10^{10}$ in $C$ and $D$; the proof gives $144 e^{13}$ and $1344 e^{13}$). The hypothesis
  $\varepsilon \le 2/(|\beta| H S)$ is not used by the proof (kept for fidelity). Blueprint
  `def:upper_bound_const`, `rem:sc_constants`, `rem:sc_hypotheses`.
- **Lean:** `coeffSqrt`, `coeffLin`, `upperBound`, in
  `probReal_stoppingTime_entropicBPI_le_ge`.
- **Kind:** gap in the proof (and typos).
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E10. The Bernstein concentration event must be non-strict

- **Where:** arXiv:2605.13717v1, Appendix A, the Bernstein event $\mathcal E^-$.
- **Error:** with the strict inequality, the event $\mathcal E^-$ is empty: at $h = H$,
  $Z^*_{H+1} \equiv 1$ and the range factor $1 - e^{\beta(H - H)} = 0$ make both sides $0$.
- **Correction:** "$\le$", which is what the Bernstein inequality gives anyway. Blueprint
  `def:event_bern`, `rem:empirical_bern_event`.
- **Lean:** `eventBern`.
- **Kind:** typo.
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E11. Lemma 27 (pseudo-counts): the hypotheses do not suffice

- **Where:** arXiv:2605.13717v1, Lemma 27 (Appendix F).
- **Error:** its two monotonicity hypotheses do not suffice ($\alpha \equiv 1/8$, $n = 0$,
  $\bar n = 1/2$ is a counterexample); the proof needs $\alpha \ge \alpha^{\mathrm{cnt}} \ge 1$.
  Moreover the paper's pseudo-count $\bar n = \mathbb E[n]$ is a deterministic quantity, while
  Lemma 20 controls, and the counting argument telescopes, the random pseudo-counts
  $\bar n_h^t = \sum_{i \le t} p^{\pi^i}_h(s,a)$ (conditional visit probabilities).
- **Correction:** the lemma under $\alpha \ge \alpha^{\mathrm{cnt}} \ge 1$, which the rates of the
  paper satisfy ($\log(3SAH/\delta) \ge \log 3 > 1$), for the random pseudo-counts. Blueprint
  `lem:pseudo_counts_bound`, `def:pseudo_counts`, `rem:sc_lemma27`.
- **Lean:** `pseudoCount`, `rateMin_le_of_mem_eventCnt`.
- **Kind:** missing hypothesis.
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E12. The counting argument: the constant is 16

- **Where:** arXiv:2605.13717v1, Appendix B.1, the counting argument.
- **Error:** the constant is $16$ ($4$ from Lemma 27 and $4$ from Lemma 28), not $3$; the paper
  also writes $\alpha(\tilde n \vee 1)$ for $4\alpha(\tilde n)/(\tilde n \vee 1)$.
- **Correction:** the constant $16$. Blueprint `lem:sum_counts_bound`.
- **Lean:** `sum_sum_occupancy_mul_rateMin_le`.
- **Kind:** wrong constant.
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E13. Lemma 5 (good event): the union bounds

- **Where:** arXiv:2605.13717v1, Lemma 5 and its proof (Appendix A).
- **Error:** (a) the KL event cannot be obtained from Sanov's bound (Lemma 19) by a union bound
  over $n$: with the rate $\alpha(n) = \log(3SAH/\delta) + S\log(8e(n+1))$ the terms
  $(n+1)^{S-1} e^{-\alpha(n)}$ form a harmonic series. (b) The Bernstein inequality is applied
  with the episode index $t$ while the rate is in the number of visits $n$. (c) The union bound
  needs $\delta_{h,s,a} = \delta/(3SAH)$, not $\delta/(SAH)$, to get $\delta/3$.
- **Correction:** (a) the time-uniform bound is proved by a mixture martingale and Ville's
  inequality, with a threshold below $\alpha(n)/n$; (b) the Bernstein inequality is indexed by the
  visits; (c) $\delta/(3SAH)$ per triple. Blueprint `lem:event_kl_prob`,
  `lem:empirical_kl_time_uniform`, `rem:empirical_sanov_union`, `rem:empirical_bernstein_index`.
- **Lean:** `measure_compl_eventKL_le`,
  `InformationTheory.measure_exists_le_klDiv_empiricalFreq_le`.
- **Kind:** gap in the proof.
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E14. Lemmas 11 and 16: a missing variance transport

- **Where:** arXiv:2605.13717v1, proofs of Lemmas 11 (Appendix B.1) and 16 (Appendix B.2).
- **Error:** the proof applies the KL-Bernstein inequality with the variance under $\hat p$, but
  $\mathrm{KL}(\hat p \| p_h) \le \alpha/n$ controls $|(\hat p - p_h) f|$ with the variance under
  $p_h$.
- **Correction:** a transport step (Lemmas 25, 26). Together with E4, the constants $3$ and $3/H$
  are then correct. Blueprint `lem:certificate_pos`, `rem:pos_constants_certificate`.
- **Lean:** `UtildeAt_sub_ringUAt_le_of_pos`, `ringUAt_sub_UlowerAt_le_of_neg`.
- **Kind:** gap in the proof.
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E15. Lemmas 7 and 12: a dropped factor √2

- **Where:** arXiv:2605.13717v1, Lemmas 7 (Appendix B.1) and 12 (Appendix B.2) and their proofs.
- **Error:** the proof takes $\sqrt{\mathrm{Var}\,\alpha^*/n}$ instead of
  $\sqrt{2\,\mathrm{Var}\,\alpha^*/n}$ (a $\sqrt2$ is dropped twice). Lemma 12's statement misses
  a $/n$ and has the exponent $H - hH$.
- **Correction:** the constants $2\sqrt2$, $5$ and $4H$ are nevertheless correct, through
  $\sqrt{\alpha\alpha^*} \le (\alpha+\alpha^*)/2$ and a different AM–GM weight. Blueprint
  `lem:concentration_pos`, `lem:concentration_neg`.
- **Lean:** `abs_vecExp_sub_le_bonusAt_add_of_pos`, `abs_vecExp_sub_le_bonusAt_add_of_neg`.
- **Kind:** gap in the proof (and typos).
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E16. Lemmas 10 and 15: a sign in a factor

- **Where:** arXiv:2605.13717v1, proofs of Lemmas 10 (Appendix B.1) and 15 (Appendix B.2).
- **Error:** the difference of the two max/min arguments is
  $e^{\beta r}(1 + 1/H)\hat p(\underline Z - \mathring Z)$, not $(1 - 1/H)$.
- **Correction:** $(1 + 1/H)$; only the sign matters for the proof. Blueprint `lem:ring_pos`,
  `lem:ring_neg`.
- **Lean:** `ringU_le_stepUAt_snd_of_pos`, `stepUAt_fst_le_ringU_of_neg`.
- **Kind:** typo.
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E17. The true-kernel recursion of the certificate

- **Where:** arXiv:2605.13717v1, Appendix B.1, "Sample complexity", and its counterpart for
  $\beta < 0$ in Appendix B.2.
- **Error:** the paper's steps give $1 + 15.5/H$ (not $13/H$), and $81H + (1 + 3/H)3H \ne 84H$.
  For $\beta < 0$, the additive term $84H(1 - e^{\beta(H-h)})$ vanishes at $h = H$, and
  $e^{\beta r} \le 1$ cannot absorb the clip $1$ of an unvisited pair. Unvisited pairs (the
  paper's $\alpha(0)/0 = \infty$, "$\alpha(n) \wedge 1$") need the term
  $84H e^{\beta(H+1-h)}\rho$ to dominate the clip.
- **Correction:** the constants $36$, $13$ and $84$ hold with a sharper AM–GM step; for
  $\beta < 0$ the additive term is $84 H\,\rho$, outside the factor $e^{\beta r}$. Blueprint
  `lem:cert_true_recursion_pos`, `lem:cert_true_recursion_neg`, `rem:neg_additive_term`.
- **Lean:** `cert_le_of_pos`, `cert_le_of_neg`.
- **Kind:** gap in the proof.
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E18. ε-optimality at stopping for β < 0

- **Where:** arXiv:2605.13717v1, Appendix B.2, the ε-optimality of the output at the stopping
  time.
- **Error:** the proof uses $Z^\pi_1 \ge \underline Z_1$ without proof, and its last display has a
  sign error.
- **Correction:** $Z^\pi_1 \ge Z^*_1 \ge \underline Z_1$ for $\beta < 0$. Blueprint
  `lem:pac_at_stopping_neg`, `rem:neg_stopping`.
- **Lean:** `optEntropicValue_sub_entropicValue_le_of_stopCond_of_neg`.
- **Kind:** gap in the proof (and a sign typo).
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E19. Lemma 28: the constant

- **Where:** arXiv:2605.13717v1, Lemma 28 (Appendix F).
- **Error:** none: the lemma is stated with the constant $4$ and holds with $3$.
- **Correction:** the constant $3$ (and the stated $4$). Blueprint `lem:log_sum_bound`.
- **Lean:** `Real.sum_div_max_one_le_three_mul_log`, `Real.sum_div_max_one_le_four_mul_log`.
- **Kind:** no error (a sharper constant).
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E20. Theorem 3: the counting of the hard instances

- **Where:** arXiv:2605.13717v1, proof of Theorem 3 in Appendix C, the tree of states and the
  final constant.
- **Error:** $L \ge S/4$ is proved only for full trees ($S - 3 = (A^d - 1)/(A-1)$);
  $\bar H = H/3$ is not an integer; the factor $e^{2\min\{\beta,0\}\varepsilon}$ is an artifact of
  a loose bound; the paper's constant $1/1650$ is not derivable.
- **Correction:** for the first $S - 3$ nodes of the $A$-ary tree in breadth-first order (leaves =
  childless nodes), $L = (S-3) - \lceil (S-4)/A \rceil \ge (S-3)/2 \ge S/4$;
  $\bar H = \lfloor H/3 \rfloor \ge H/6$; the factor $e^{2\min\{\beta,0\}\varepsilon} \le 1$ is
  kept; with the corrected divergence bound (E1) the constant is $1/3456$, stated as $1/5000$.
  Blueprint `lem:tree_leaves`, `thm:lower_bound`, `rem:lb_constant`.
- **Lean:** `card_leafFinset`, `lowerBound`, `exists_hardMDP_lowerBound_le_lintegral_stoppingTime`.
- **Kind:** gap in the proof (and wrong constant).
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E21. Appendix A, Lemma 14 and Definition 2: imprecisions

- **Where:** arXiv:2605.13717v1, Appendix A (the KL event), Lemma 14 (Appendix B.2) and
  Definition 2.
- **Error:** the KL event is written with the threshold $\alpha(n)$ instead of $\alpha(n)/n$; the
  last sentence of Lemma 14 mixes $V$ and $Z$; Definition 2 does not require $\tau < \infty$.
- **Correction:** the threshold $\alpha(n)/n$. The formalization's PAC property is about the law
  of the output, and the sample complexity theorem gives $\tau < \infty$ with probability
  $1 - \delta$.
- **Lean:** `eventKL`, `Learning.MDP.Episodic.IsEntropicPAC`.
- **Kind:** typo.
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E22. Lemma 19 (Sanov): the exponent

- **Where:** arXiv:2605.13717v1, proof of Lemma 19 (Appendix E.1).
- **Error:** the proof writes $(n+1)^m$ where the method of types gives $(n+1)^{m-1}$ (harmless).
- **Correction:** $(n+1)^{m-1}$. Blueprint `thm:sanov_hp`, `rem:pconc_sanov_paper`.
- **Lean:** `InformationTheory.measure_lt_klDiv_empiricalFreq_le`.
- **Kind:** typo.
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E23. Lemma 21 (self-normalized Bernstein): the supermartingale and the constants

- **Where:** arXiv:2605.13717v1, Lemma 21 and its proof (Appendix E.3).
- **Error:** the exponential-supermartingale lemma holds for $\lambda \ge 0$ only, not for all real
  $\lambda$; the inversion of the Poisson Cramér transform gives $s \le \sqrt{2c\ell} + \frac23\ell$
  (constant $2/3$, not $1/3$).
- **Correction:** the negative side is obtained from $-Y$. The blueprint proves the inequality by
  the method of mixtures, with the sharper threshold $\log(1/\delta) + \log(8(1 + \sqrt{2t}))$,
  from which the paper's $\log(4e(2t+1))$ form follows; the explicit form has $\frac53 b L_t$,
  stated with $3b$. Blueprint `thm:bernstein_self_normalized`, `cor:bernstein_explicit`,
  `rem:pconc_bernstein_constants`.
- **Lean:** `ProbabilityTheory.measure_exists_log_le_selfNorm_poissonCramer_le`,
  `ProbabilityTheory.measure_exists_sqrt_add_lt_abs_selfNormSum_le`.
- **Kind:** false statement (an intermediate lemma) and wrong constant.
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E24. Lemmas 22, 25 and 26: the constants and the range of α

- **Where:** arXiv:2605.13717v1, Lemmas 22 (Appendix E.4), 25 and 26 (Appendix F).
- **Error:** none: Lemma 25 is stated with $4$ and holds with $10/3$ and $5/3$, Lemma 26 is stated
  with $3$ and holds with $1$, and Lemmas 22 and 25 hold for every $\alpha \ge 0$.
- **Correction:** the sharper constants. Blueprint `lem:kl_transport_var`, `lem:transport_var`.
- **Lean:** `InformationTheory.variance_le_two_mul_variance_add_of_klDiv_le`,
  `ProbabilityTheory.variance_le_two_mul_variance_add`.
- **Kind:** no error (sharper constants).
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).

## E25. Lemma 17 (change of measure): a missing finiteness

- **Where:** arXiv:2605.13717v1, Lemma 17 (Appendix C), cited from Kaufmann, Cappé and Garivier.
- **Error:** the cited proof silently needs the event to lie in $\{\sigma < \infty\}$ under the
  second model too.
- **Correction:** a one-sided version, with the almost sure finiteness under the first
  environment only, which is all the lower bound has ($\mathbb E_0[\tau] < \infty$), proved
  through the bounded stopping rules $\tau \wedge M$, the lower semicontinuity and the convexity
  of the binary divergence. Blueprint `thm:change_of_measure`, `rem:pinfo_one_sided`.
- **Lean:** `Learning.IdentAlg.IsRun.klBer_measureReal_le_sum_pullCount`,
  `Learning.IdentAlg.IsRun.klBer_measureReal_outputMeasure_le_sum_pullCount`.
- **Kind:** gap in the proof.
- **Found:** phase-1 statement check (blueprint, 2026-09-16, commit aa2c56c).
