# Paper roadmap: Tight Sample Complexity Bounds for Entropic Best Policy Identification

Paper: RemyDegenne/Essakine2026Tight · LMLExplore afd365492580 · LMLRoadmaps 468f19f45fae · Refreshed 2026-11-12

## Items

| Id | Item | Tag | Link | Status | Files |
|---|---|---|---|---|---|
| R1 | MDPs, their environment and stationary deterministic policies (`MDP`, `MDP.env`, `policyAlg`, `policyMeasure`, `stateLaw`, `meanReward`) | exists | `Learning.MDP.env` | – | |
| R2 | Episodic MDPs and the time-augmented MDP (`EpisodicMDP`, `ofDet`, `meanReward`, `RewardsIn`, `HasRewardFn`, `augmented`) | exists | `Learning.MDP.Episodic.EpisodicMDP` | – | `ForLMLExplore/MarkovDecisionProcess/Episodic/Basic.lean` |
| R3 | State marginals and occupancy measures of an episodic MDP | exists | `Learning.MDP.Episodic.EpisodicMDP.occupancy` | – | `ForLMLExplore/MarkovDecisionProcess/Episodic/Occupancy.lean` |
| R4 | Conditional distributions: integrals and conditional expectations against `HasCondDistrib`, restrictions, compositions with laws | target | ReinforcementLearning 7.6 | proved | `ForLMLExplore/Probability/HasCondDistribIntegral.lean`, `ForLMLExplore/Probability/HasCondDistribCondExp.lean`, `ForLMLExplore/Probability/CondDistrib.lean` |
| R5 | Markov property of the trajectory of a stationary deterministic policy (`policyKernel` through `Kernel.traj`, shifted trajectories) | target | ReinforcementLearning 7.2 | proved | `ForLMLExplore/MarkovDecisionProcess/Markov.lean` |
| R6 | `H`-step policies and episode trajectories (`Policy`, `Policy.extend`, `stepLaw`, `episodeReturn`, `episodeStates`), with the Markov property along an episode | target | ReinforcementLearning 7.6 | proved | `ForLMLExplore/MarkovDecisionProcess/Episodic/Basic.lean`, `ForLMLExplore/MarkovDecisionProcess/Episodic/StepLaw.lean` |
| R7 | Episodes as rounds: the law of the state sequence of an episode, `statesEnv` and best policy identification algorithms `BPIAlg` | target | ReinforcementLearning 7.7 | proved | `ForLMLExplore/MarkovDecisionProcess/Episodic/Basic.lean`, `ForLMLExplore/MarkovDecisionProcess/Episodic/StateSeq.lean` |
| R8 | Exponential and entropic values: Bellman equations, ranges, optimal entropic values and a greedy optimal policy, maximal return, entropic PAC property | staged | S1 | proved | `ForLMLExplore/MarkovDecisionProcess/Vec.lean`, `ForLMLExplore/MarkovDecisionProcess/Episodic/Entropic.lean`, `ForLMLExplore/MarkovDecisionProcess/Episodic/Values.lean`, `ForLMLExplore/Probability/Moments/Variance.lean`, `ForLMLExplore/Algebra/Order/Field/Basic.lean` |
| R9 | Entropic variances and backward recursions along the trajectory: variance recursion and telescoping, weighted unrolling, Cauchy–Schwarz bounds | staged | S1 | proved | `ForLMLExplore/MarkovDecisionProcess/Episodic/EntropicVariance.lean`, `ForLMLExplore/MarkovDecisionProcess/Episodic/Unroll.lean`, `ForLMLExplore/MarkovDecisionProcess/Episodic/UnrollBounds.lean`, `ForLMLExplore/MeasureTheory/Integral/CauchySchwarz.lean`, `ForLMLExplore/Analysis/SpecialFunctions/Exp.lean` |
| R10 | Empirical models of episodes: visit counts, reward sums, transition counts and empirical transitions | target | ReinforcementLearning 14.1 | proved | `ForLMLExplore/ReinforcementLearning/Episodic/Empirical.lean`, `ForLMLExplore/ReinforcementLearning/Episodic/EmpiricalCounts.lean` |
| R11 | Visits of a step–state–action pair across episodes, the next states observed at them and their domination by i.i.d. samples | target | ReinforcementLearning 14.2 | proved | `ForLMLExplore/ReinforcementLearning/Episodic/Visits.lean`, `ForLMLExplore/ReinforcementLearning/Episodic/VisitConcentration.lean`, `ForLMLExplore/Probability/Process/FirstEntrance.lean` |
| R12 | Counts versus pseudo-counts: the Bernoulli maximal inequality | target | ReinforcementLearning 19.2 | proved | `ForLMLExplore/Probability/Martingale/Ville.lean` |
| R13 | Ville's inequality | exists | `MeasureTheory.Supermartingale.measure_exists_le_le` | – | |
| R14 | Weighted measures of probability vectors | exists | `LMLExplore.weightedMeasure` | – | |
| R15 | Bernoulli measures, the binary relative entropy, Pinsker's inequality and data processing to an event | exists | `LMLExplore.klBer` | – | `ForLMLExplore/InformationTheory/KullbackLeibler/Bernoulli.lean`, `ForLMLExplore/Probability/Distributions/Bernoulli.lean` |
| R16 | The divergence of two Bernoulli measures on any two distinct points | refactor | `LMLExplore.klDiv_bernoulliMeasure` | proved | `ForLMLExplore/InformationTheory/KullbackLeibler/Bernoulli.lean` |
| R17 | Canonical runs of identification algorithms and their transport | exists | `LMLExplore.Identification.runMeasure` | – | |
| R18 | Change of measure at a stopping time for identification algorithms | exists | `LMLExplore.Identification.klBer_measureReal_histOutputMeasure_le` | – | `ForLMLExplore/Identification/ChangeOfMeasure.lean` |
| R19 | Chain rule for the KL divergence at a stopping time, with equality: prefix filtrations, stopped histories, regrouping by action counts | target | Identification 2.1 | proved | `ForLMLExplore/Probability/Process/SigmaPrefix.lean`, `ForLMLExplore/MeasureTheory/MeasurableSpace/PiFinSuccProd.lean`, `ForLMLExplore/InformationTheory/KLStoppedPrefix.lean`, `ForLMLExplore/SequentialLearning/StoppedHistory.lean`, `ForLMLExplore/SequentialLearning/DivergenceDecomposition.lean` |
| R20 | Method of types and Sanov's bound on a finite set | target | ReinforcementLearning 3.4 | proved | `ForLMLExplore/InformationTheory/MethodOfTypes.lean`, `ForLMLExplore/InformationTheory/KullbackLeibler/Fintype.lean` |
| R21 | Time-uniform KL concentration of the empirical distribution by the Laplace mixture | target | ReinforcementLearning 3.4 | proved | `ForLMLExplore/InformationTheory/KLTimeUniform.lean` |
| R22 | Donsker–Varadhan inequality and the Bernstein bound on the log-moment generating function | exists | `TauCeti.ofReal_integral_sub_log_integral_exp_le_klDiv` | – | |
| R23 | KL-to-Bernstein transport and variance transport under a KL constraint | target | ReinforcementLearning 19.2 | proved | `ForLMLExplore/InformationTheory/KLBernstein.lean`, `ForLMLExplore/Probability/Moments/VarianceTransport.lean` |
| R24 | Square roots, logarithms against powers and the self-bounding inequality | target | ReinforcementLearning 19.2 | proved | `ForLMLExplore/Analysis/Real/Sqrt.lean`, `ForLMLExplore/Analysis/SpecialFunctions/Pow/Real.lean`, `ForLMLExplore/Analysis/SpecialFunctions/Log/SelfBounding.lean` |
| R25 | Logarithmic sum bound | target | ReinforcementLearning 19.2 | proved | `ForLMLExplore/Analysis/SpecialFunctions/Log/Basic.lean` |
| R26 | Time-uniform self-normalized Bernstein inequality, for martingale differences and for i.i.d. sequences, with the Poisson Cramér transform | staged | S2 | proved | `ForLMLExplore/Probability/Moments/SelfNormalizedBernstein.lean`, `ForLMLExplore/Probability/Moments/SelfNormalizedBernsteinIID.lean`, `ForLMLExplore/Analysis/SpecialFunctions/PoissonCramer.lean`, `ForLMLExplore/Probability/Independence/NaturalPast.lean` |
| R27 | Measurable singletons of dependent sums; bounding an extended natural number by a real number | staged | S3 | proved | `ForLMLExplore/MeasureTheory/MeasurableSpace/Sigma.lean`, `ForLMLExplore/Basic/Real/ENatENNReal.lean` |
| R28 | Tree of the hard instances: breadth-first `A`-ary trees, depths, leaves and walks | target | ReinforcementLearning 19.3 | proved | `EV2026/HardTree.lean` |
| R29 | Entropic-BPI: exploration rates, constants, bonuses and backups, the algorithm, its runs and its visit counts | paper | | proved | `EV2026/Rates.lean`, `EV2026/Constants.lean`, `EV2026/Backups.lean`, `EV2026/Algorithm.lean`, `EV2026/Run.lean`, `EV2026/EntropicBPIRun.lean`, `EV2026/VisitCounts.lean` |
| R30 | Concentration events of Entropic-BPI and the probability of the good event | paper | | proved | `EV2026/Events.lean` |
| R31 | Analysis of Entropic-BPI on the good event for both signs of β: optimism, certificates, rate bounds, the tail | paper | | proved | `EV2026/AnalysisCommon.lean`, `EV2026/AnalysisPos.lean`, `EV2026/AnalysisNeg.lean`, `EV2026/RateBounds.lean`, `EV2026/TailCommon.lean`, `EV2026/TailPos.lean`, `EV2026/TailNeg.lean` |
| R32 | Hard instances of the lower bound: parameters and MDPs | paper | | proved | `EV2026/HardParams.lean`, `EV2026/HardMDP.lean` |

## Notes

- R1: the project uses LMLExplore's `MDP`, `MDP.env`, `MDP.policyAlg`, `MDP.policyMeasure`,
  `MDP.stateLaw` and `MDP.meanReward`; the local copy is deleted (2026-11-12). LMLExplore's
  `MDP.env` needs `[Nonempty 𝓢]`, which the headline statements do not assume: `stepLaw` takes the
  instance from its initial state through the named lemma `nonempty_augState`, so that its
  definition has no nested proof. The closure of the three headline statements imports these
  definitions instead of copying them.
- R2: the project uses LMLExplore's `EpisodicMDP`, `ofDet`, `meanReward`, `RewardsIn`,
  `HasRewardFn` (with `HasRewardFn.rewardsIn`) and `augmented` (with `augmented_P_apply`,
  `augmented_R_apply`); the local copies are deleted (2026-11-12). Their bodies are not exposed:
  the proofs go through `rewardsIn_def`, `hasRewardFn_def`, `meanReward_def` and `ofDet_trans`.
  `transVec` and `measurable_rewardFn` remain in `Episodic/Basic.lean`.
- R3: the local `occupancyMeasure M π s₁ h`, the law of the state-action pair at the step `h`
  under `stepLaw`, is LMLExplore's `M.occupancy (detPolicy hπ) (Measure.dirac s₁) h` for the
  deterministic kernels of `π` (`occupancyMeasure_eq_occupancy`, through
  `isAlgEnvSeq_markov_stepLaw` and `EpisodicMDP.hasLaw_obs_fst_action_markov`). The local state
  laws and their forward recursion are gone in favour of LMLExplore's `stateMarginal` and
  `EpisodicMDP.stateMarginal_trans_add_one`; the finite pointwise forms (`occupancy_eq`,
  `occupancy_succ`, `sum_occupancy`) and the `stepLaw` forms remain, re-proved on LMLExplore's.
- R4: a direct prerequisite of R5, R6, R11 and R19, ported with the first of them. The
  duplicates are deleted (2026-11-12): LMLExplore's `hasCondDistrib_snd_compProd_comap` (also for
  `f = id`) and `HasCondDistrib.lintegral_comp_prodMk_eq_lintegral_lintegral`, LML's
  `HasCondDistrib.comp_hasLaw`, Tau Ceti's `Measure.compProd_restrict_left`, and
  `HasCondDistrib.compProd_left` is `HasCondDistrib.compProd_left_of_sectR` with
  `Kernel.sectR_prodMkLeft`. New: `HasCondDistrib.integral_prodMk`,
  `hasCondDistrib_of_lintegral_eq`, `HasCondDistrib.compProd_left_of_sectR`, `restrict_preimage`,
  `of_comp_hasLaw`, and `condExp_comap_ae_eq_integral` without a standard Borel space.
- R5: Layer 7.2 asks for stochastic Markov policies (`Algorithm.markov`) and for the law of the
  state process as Tau Ceti's `markovChainLaw`, whose shift Markov property Tau Ceti has
  (`condExp_shift_iterate_markovChainLaw`). The port states the Markov property of runs for
  `Algorithm.markov`, on LMLExplore's `MDP.env` (R1), and gets the deterministic case through
  LMLExplore's `policyAlg_eq_markov`. The local file is on LMLExplore's `MDP.env` since
  2026-11-12; `Kernel.traj_congr` is gone (`congr`), and `measurable_finCons` and
  `measurable_finSnoc` are proved from Mathlib's `MeasurableEquiv.piFinSuccAbove` and LML's
  `MeasurableEquiv.finSuccProd`.
- R6: Layer 7.6 takes the `H`-step policies `Policy 𝓢 𝓐 H = Fin H → 𝓢 → 𝓐` and `Policy.extend`
  from here, with measurability as a separate hypothesis. LMLExplore has the Markov-policy side
  (`augMarkovPolicy`, `EpisodicMDP.value`, `runReturn_augmented_markov`, the one-step laws
  `hasCondDistrib_obs_fst_add_one` and `hasCondDistrib_action_obs_fst_markov`). The port defines
  `stepLaw` as the trajectory law of `Algorithm.markov` of the deterministic kernels in
  `M.augmented`, with `augMarkovPolicy` in place of `augPolicy`, and adds what LMLExplore lacks:
  the iterated Markov property along an episode (`hasCondDistrib_shiftRounds_stepLaw`,
  `integral_mul_obs_succ_stepLaw`).
- R7: Layer 7.7 asks for `statesEnv M H μ` with an initial law μ, for finite `𝓢` and countable
  `𝓐`; the local `statesEnv M H s₁` is the case `μ = δ_{s₁}`. Layer 19.1 defines best policy
  identification algorithms as `BPIAlg`. The law of the state sequence (`stateSeqLaw`, with its
  backward recursion `stateSeqLaw_succ`) gives the kernel of `statesEnv`; `hasCondDistrib_statesLaw`
  and the laws of `statesEnv` are in `StepLaw.lean` (R6).
- R8: risk-sensitive MDPs are outside the scope of the ReinforcementLearning roadmap, hence S1.
  `expValue` is Mathlib's `mgf (episodeReturn (H - h)) (stepLaw M π (s, h)) β` and `entropicValue`
  is `β⁻¹ * cgf …`: the port states them through `mgf` and `cgf`. `vecExp` is Mathlib's
  `dotProduct`: the tabular forms go through `integral_fintype` and LMLExplore's `simplex`.
  `rewardsIn_of_hasRewardFn` is LMLExplore's `EpisodicMDP.HasRewardFn.rewardsIn`, and the local
  `optPolicy` would collide with `EpisodicMDP.optPolicy` under dot notation.
  `integral_mem_Icc_of_ae_mem_Icc` generalizes LMLExplore's
  `MeasureTheory.integral_id_mem_Icc_of_ae_mem_Icc`.
- R9: in S1. LMLExplore has the risk-neutral analogues: the unweighted unrolling
  `EpisodicMDP.integral_eq_sum_integral_occupancy_add` and the discounted total-variance identities
  (`Learning.MDP.returnVariance_eq_add`). The telescoping of the entropic variances is the
  multiplicative analogue of the finite-horizon total-variance identity of ReinforcementLearning
  1.9, and takes its statement shape. The Cauchy–Schwarz bound follows from Mathlib's
  `integral_mul_le_Lp_mul_Lq_of_nonneg`.
- R10: Layer 14.1 asks for the episodic counts before episode `k` as LML `pullCount`s of the
  step–state–action process, for an empirical kernel that is a probability measure (the uniform
  law on `𝓢` at an unvisited pair, where the local `empTrans` is `0`) and for measurability in the
  history. The additive-monoid `EmpiricalModel` is what the paper's algorithm updates.
- R11: Layer 14.2 cites `Visits.lean`. It asks for per-`(h, s, a)` streams of law `P_h(s, a)` read
  at the visits, with the stream representation and the keyed transfer of ReinforcementLearning
  6.1; the local results are the conclusion of that transfer, as a domination of the next states
  at the visits by an i.i.d. sample on the original space (`measure_visitNextState_mem_le_pi`,
  `measure_exists_le_pullCount_visitNextState_mem_le`). The port goes through Layer 6.1 once it
  exists. `exists_le_pullCount_iff_stepsUntil_ne_top` and
  `exists_pullCount_eq_iff_exists_le_pullCount` belong in `SequentialLearning/FiniteActions.lean`.
  `VisitConcentration.lean` also holds the instance of R12 at the visits,
  `measure_exists_pullCount_lt_le`, with the random pseudo-counts of `notes/paper-errata.md` E11.
- R12: Layer 19.2 asks for counts versus pseudo-counts, `n ≥ n̄/2 - log(3SAH/δ)`: the Bernoulli
  maximal inequality `measure_exists_sum_lt_half_mul_sum_sub_le` (Dann, Lattimore and Brunskill
  2017, Lemma F.4). LMLExplore's fixed-η Freedman inequality
  (`LMLExplore.measure_exists_mul_sum_condExp_sq_add_log_div_le_sum_le`) gives only
  `- 2 log(1/δ)`. Port it on LMLExplore's Ville inequality (R13) and
  `LMLExplore.supermartingale_exp_sum_of_condExp_exp_le_one`.
- R13: the project uses LMLExplore's Ville inequality
  (`MeasureTheory.Supermartingale.measure_exists_le_le`, which needs only almost-everywhere
  nonnegativity) and its finite-horizon form `Supermartingale.maximal_ineq`; the local copies are
  deleted (2026-11-12). `Ville.lean` holds only R12; `condExp_exp_sub_le_one` stays there, since
  LMLExplore's conditional Bennett bound does not give `e^{-P/2}`.
- R14: the project uses LMLExplore's `weightedMeasure` and its API; the local copy is deleted
  (2026-11-12). LMLExplore's `isProbabilityMeasure_weightedMeasure` takes `p ∈ simplex ι`.
- R15: the project uses LMLExplore's `klBer` (the divergence of the Bernoulli laws at the
  parameters clipped to `[0, 1]`, which is the binary divergence on `[0, 1]²`, where every use
  lies), `klBerReal` and their API, LMLExplore's `klBer_measureReal_le_klDiv`, Tau Ceti's
  `TauCeti.two_mul_sq_measureReal_sub_le_klDiv` and Mathlib's
  `hasLaw_indicator_one_bernoulliMeasure`; `KLBer.lean` and `Pinsker.lean` are deleted
  (2026-11-12). What LMLExplore lacks is in `InformationTheory/KullbackLeibler/Bernoulli.lean`
  (LMLExplore's path), re-proved on LMLExplore's definitions: `sub_log_two_le_klBerReal`,
  `mul_log_sub_log_two_le_klBerReal`, `exp_neg_le_of_klBer_le` (namespace `LMLExplore`) and
  `abs_sub_le_sqrt_klDiv`; and in `Probability/Distributions/Bernoulli.lean`: the `lintegral`,
  `withDensity` and `rnDeriv` forms of `bernoulliMeasure` and `ae_bernoulliMeasure` (used by
  `EV2026/HardParams.lean` and `EV2026/HardMDP.lean`).
- R16: LMLExplore's `klDiv_bernoulliMeasure` is stated for the Bernoulli laws on `{1, 0} ⊆ ℝ`; the
  local `InformationTheory.klDiv_bernoulliMeasure` holds for `Ber(x, y, ·)` with `x ≠ y` in any
  measurable space with measurable singletons, and `EV2026/HardMDP.lean` uses it for the good and
  bad absorbing states. The refactor restates LMLExplore's lemma in that generality and updates
  its uses (the current statement is the case `x = 1`, `y = 0`). The local lemma now reads
  `klDiv Ber(x, y, p) Ber(x, y, q) = LMLExplore.klBer p q`, proved by data processing both ways
  from LMLExplore's.
- R17: the project uses LMLExplore's `Identification.runMeasure`, `isRun_runMeasure`,
  `snd_runMeasure`, `IsAlgEnvSeq.comp_hasLaw`, `IdentAlg.IsRun.comp_hasLaw` and
  `IdentAlg.measurable_stoppedHist`; the local file is deleted (2026-11-12).
- R18: the local truncation (`truncSet` and the time-`M` lemmas) is deleted (2026-11-12):
  `IsRun.klBer_measureReal_le_sum_pullCount` is re-proved from LMLExplore's
  `Identification.klBer_measureReal_histOutputMeasure_le` (almost-sure stopping under the first
  model only, through `Learning.klDiv_stoppedHistMeasure_le`) and
  `Learning.IdentAlg.IsRun.hasLaw_stoppedHist_output`, and `stoppedHist_mem_stopSet_iff`,
  `fst_stoppedHist` are LMLExplore's. The run-level forms that `EV2026/LowerBound.lean` uses
  remain (`IsRun.klBer_measureReal_outputMeasure_le_sum_pullCount`,
  `IsRun.klDiv_bernoulliMeasure_le_sum_pullCount`,
  `IsRun.klBerReal_measureReal_le_toReal_sum_pullCount`): LMLExplore states the measure-level
  forms only. The two-sided equality `IsRun.klDiv_map_stoppedHist_out_eq_sum_pullCount` belongs
  to R19.
- R19: Identification 2.1 asks for the equality case, when τ is almost surely finite under both
  pairs, which the Generalization roadmap leaves to it; LMLExplore has the inequalities for any two
  pairs (`Learning.klDiv_stoppedHistMeasure_le_tsum`, `Learning.klDiv_stoppedHistMeasure_le_lintegral`),
  stated with `stoppedHistMeasure` and `notStoppedSet`, which the port follows. The local chain
  rule along the prefix filtration of any process (`klDiv_map_stoppedValue_sigmaPrefix_compProd`,
  with bounded-time forms) proves it, and the regrouping by action counts gives the bandit
  equality. The drops are done (2026-11-12): `hittingValue`, `hittingProcess` and
  `HittingTime.lean` are gone in favour of Mathlib's `stoppedValue`/`stoppedProcess` at
  `hittingAfter` (the lemmas are renamed `…stoppedValue…`/`…stoppedProcess…`, with the suffix
  `_hittingAfter` in `KLStoppedPrefix.lean`), and the project uses LMLExplore's
  `natCast_pullCount_toNat_le`, `IsAlgEnvSeq.klDiv_map_history_eq_sum_pullCount`,
  `sum_lintegral_pullCount_mul` and `tsum_indicator_natCast_lt_eq_sum_range` and LML's
  `Learning.sum_pullCount_mul`. `piFinSuccProd` stays: for a family `X : ℕ → Type*`, Mathlib's
  `MeasurableEquiv.piFinSuccAbove` at `Fin.last n` has the factor
  `Π j, X ((Fin.last n).succAbove j)`, equal to `Π j : Fin n, X j` only propositionally, and LML's
  `MeasurableEquiv.finSuccProd` is for one space.
- R20: Layer 3.4 states `(n+1)^m e^{-nε}`; the local `measure_lt_klDiv_empiricalFreq_le` has
  `(n+1)^{m-1}` (`notes/paper-errata.md` E22). `toReal_klDiv_eq_sum` is close to Tau Ceti's
  `TauCeti.klDiv_eq_ofReal_sum_log_singleton` (which assumes full support; the local one needs
  only absolute continuity) and is proved from Tau Ceti's
  `Measure.rnDeriv_eq_measure_singleton_div`; `rnDeriv_apply_eq_div`, `measure_typeCount_eq` and
  `iIndepFun.measure_prefix_mem_eq_pi` are deleted (2026-11-12) in favour of it and of Mathlib's
  `iIndepFun.hasLaw_pi`.
- R21: Layer 3.4 asks for the martingale property of the likelihood ratio of every predictable
  predictor and, for Laplace's predictor, the threshold `log(1/δ) + (m-1) log(e(1 + n/(m-1)))` of
  [JKMDLV20, Proposition 1]. The local threshold `log(1/δ) + (m-1) log(n+1) + 1 + log(n)/2` is
  another bound on the same mixture (`laplaceRatio`): the port proves the roadmap's form and may
  keep this one. `Stirling.factorial_le_exp_one_mul_sqrt_mul_div_pow`,
  `Nat.ascFactorial_le_factorial_mul_add_one_pow` and
  `Measure.absolutelyContinuous_of_forall_singleton` are Mathlib-shaped helpers.
- R22: the project uses Tau Ceti's `TauCeti.ofReal_integral_sub_log_integral_exp_le_klDiv`;
  the local copy is deleted (2026-11-12), and `log_integral_exp_mul_sub_le` is proved from
  LMLExplore's `MeasureTheory.MemLp.mgf_le_exp_mul_exp_sub_one_sub_of_ae_le`.
- R23: Layer 19.2 asks for the KL-to-Bernstein transport `|pf - qf| ≤ √(2 Var_q(f) α) + (2/3) b α`
  for `f ∈ [0, b]`, which is `abs_integral_sub_integral_le_of_klDiv_le` on any measurable space,
  and for the variance transfers [MDJKLV21, Lemmas 10–12], toward which go
  `variance_le_two_mul_variance_add_of_klDiv_le`, `variance_le_two_mul_variance_add` and
  `variance_le_variance_add_sum_abs_sub` (with the sharper constants of `notes/paper-errata.md`
  E24); check them against the source. `integrable_of_ae_mem_Icc` and `integrable_of_ae_abs_le`
  are deleted (2026-11-12) in favour of Mathlib's `Integrable.of_mem_Icc` and
  `Integrable.of_bound`, and `variance_le_mul_integral` is proved from Mathlib's
  `variance_le_sub_mul_sub`.
- R24: Layer 19.2 asks for the inversion of the implicit inequality on τ [MDJKLV21, Lemma 13]:
  `Real.le_of_le_sqrt_mul_add`, with the constant corrected (`notes/paper-errata.md` E8: the factor
  `C + D` of `C₁` is squared) and without the hypotheses `A, B, C, D > 0` and `B ≥ 1`. Check the
  constant `C₁` of Layer 19.2 against it. `Real.sqrt_add_le` is deleted (2026-11-12) in favour
  of Tau Ceti's `Real.sqrt_le_sqrt_add_sqrt_abs_sub`; the weighted AM–GM inequalities and
  `Real.le_add_sqrt_of_sq_le` are new, for LMLExplore's `Analysis/Real/Sqrt.lean`.
- R25: Layer 19.2 asks for `∑_t u_{t+1}/max(1, U_t) ≤ 4 log(U_{T+1} + 1)` [MDJKLV21, Lemma 9]:
  `Real.sum_div_max_one_le_four_mul_log`, from the constant `3` of
  `Real.sum_div_max_one_le_three_mul_log` (`notes/paper-errata.md` E19). Check the indexing of the
  sum against the roadmap's.
- R26: the one-step bound and the exponential supermartingale are LMLExplore's
  `condExp_exp_mul_sub_mul_condExp_sq_le_one` and
  `supermartingale_exp_mul_sum_sub_mul_sum_condExp_sq` (Freedman, one-sided, more general), and
  the mixture step is `LMLExplore.supermartingale_integral`: the local proof rests on them since
  2026-11-12 (`condExp_exp_mul_sub_le_one` and `setLIntegral_selfNorm_mixture_le` are deleted, the
  mixture is a Bochner integral, `selfNormMixture_eq_integral`), and the port keeps the mixture
  bound, its explicit forms and the i.i.d. corollary. `exp u - 1 - u` has its API inline in
  LMLExplore's `Analysis/SpecialFunctions/Exp.lean`: `Real.exp_mul_le_of_abs_le`,
  `Real.expSubOneSub_mul_le` and `Real.expSubOneSub_eq_tsum` are deleted in favour of
  `Real.exp_mul_le_one_add_mul_add_mul_sq` and `Real.hasSum_pow_add_two_div_factorial`, and the
  local `Real.expSubOneSub` remains in statements; `x²/(2(1 + x/3)) ≤ h(x)`, the Padé bound
  `div_le_log_one_add` and the inversion `le_sqrt_add_of_mul_poissonCramer_le` are new.
  `Filtration.naturalPast` is built inline in LMLExplore's `Probability/Martingale/RateFunction.lean`
  and `Probability/Martingale/SubGaussian.lean`. Constants: `notes/paper-errata.md` E23.
- R27: Mathlib-shaped facts with no target, see S3.
- R28: in the paper's folder but library-shaped: combinatorics on `ℕ` of the first `n` nodes of the
  `A`-ary tree in breadth-first order, whose only tie to the paper is `treeDepth`
  (`EV2026/Constants.lean`). Layers 18.4 and 19.3 build the hard instances of [DMKV21, Theorems 7,
  9] on the full tree, `S = 3 + (A^d - 1)/(A - 1)`; this file covers every `S ≥ 6`
  (`notes/paper-errata.md` E20). The port moves it, with `treeDepth`, to
  `LMLExplore/ReinforcementLearning/`.
- R29–R32: the paper's own material. `EV2026/TailCommon.lean` (`measureReal_bad_le`,
  `one_sub_le_measureReal_stoppingTime_le`) follows a library-shaped pattern that a later item can
  extract: an event of probability at least `1 - δ` on which the algorithm stops in time with a
  good answer gives the PAC property and a high-probability bound on the stopping time.

## Proposed targets

### S1. Entropic risk in finite-horizon MDPs

Values and optimality for the entropic risk measure of the return, the risk-sensitive criterion of
[HM72], [FYCWX20], [FYCW21] and [EV26]. Let `M : EpisodicMDP 𝓢 𝓐` (ReinforcementLearning 7.1) have
rewards in `[c, d]`, horizon `H`, and `β ≠ 0` (β > 0 risk-seeking, β < 0 risk-averse; one set of
definitions serves both signs).

1. **Exponential and entropic values.** For a Markov policy `π : ℕ → Kernel 𝓢 𝓐`, define the
   exponential value `Z^π_h(s)`, the moment generating function at β of the return of the `H - h`
   remaining steps of the run of π from `(s, h)` in `M.augmented` (Mathlib's `mgf`), the entropic
   value `V^π_h = β⁻¹ log Z^π_h` (`cgf`), and the action values `U^π_h(s, a)`, `Q^π_h(s, a)`.
   Deterministic policies are the `H`-step policies of ReinforcementLearning 7.6.
   - Prove the exponential Bellman equation
     `Z^π_h(s) = ∫ (∫ e^{βr} dR_h(s, a)) (∫ Z^π_{h+1} dP_h(s, a)) dπ_h(s)(a)`, `Z^π_H = 1`, its
     Lebesgue form without boundedness, and the ranges
     `Z^π_h ∈ [min(1, e^{β(H-h)}), max(1, e^{β(H-h)})]` for rewards in `[0, 1]`.
   - State the tabular forms for finite `𝓢` with `dotProduct` and LMLExplore's `simplex`.
2. **Optimal entropic values** [FYCW21]. Define the optimal entropic value as the supremum of the
   entropic value of the return over all algorithms in `M.augmented` from `(s, h)`. Prove the
   optimal exponential Bellman equation by backward induction for countable `𝓐` (through
   measurable ε-greedy policies, as ReinforcementLearning 8.2), its attainment by the greedy
   deterministic Markov policy for finite `𝓐`, and `V^π_h ≤ V^*_h` for every algorithm, with the
   reduction to Markov deterministic policies.
3. **Entropic variances.** Define `Var_{P_h(s,a)}(Z^π_{h+1})` and the variance of `Z^π_h` under the
   law of the next reward and state. Prove their recursion and the telescoping of the variance of
   the exponentiated return,
   `Var(e^{βG}) = ∑_{h<H} E[e^{2β ∑_{i≤h} r_i(S_i, A_i)} Var_{P_h(S_h, A_h)}(Z^π_{h+1})]` for
   deterministic rewards (the multiplicative analogue of the finite-horizon total-variance identity
   of ReinforcementLearning 1.9), the normalized bound `Var(X)/(E X)² ≤ (M - m)²/(4Mm)` for
   `X ∈ [m, M]` with `m > 0` (normalized Bhatia–Davis), and the unrolling of backward recursive
   inequalities with multiplicative weights along the trajectory.
4. **Entropic best policy identification.** An algorithm in `statesEnv` (ReinforcementLearning 7.7)
   is `(ε, δ)`-PAC for the entropic risk on a class of MDPs if its output is ε-optimal for `V_0`
   with probability at least `1 - δ` on every MDP of the class, as LML's `IdentAlg.IsPAC`. Define
   the maximal return `G_max` and prove its bounds.

ReinforcementLearning lists risk-sensitive MDPs outside its scope: S1 would be a new layer of that
roadmap, after Layers 7, 8 and 12, or a roadmap of its own.

References: [HM72] R. A. Howard and J. E. Matheson, Risk-sensitive Markov decision processes,
Management Science 18(7), 1972. [FYCWX20] Y. Fei, Z. Yang, Y. Chen, Z. Wang and Q. Xie,
Risk-sensitive reinforcement learning: near-optimal risk-sample tradeoff in regret, NeurIPS 2020.
[FYCW21] Y. Fei, Z. Yang, Y. Chen and Z. Wang, Exponential Bellman equation and improved regret
bounds for risk-sensitive reinforcement learning, NeurIPS 2021. [EV26] A. Essakine and C. Vernade,
Tight sample complexity bounds for entropic best policy identification, COLT 2026,
arXiv:2605.13717.

### S2. Time-uniform self-normalized Bernstein inequality

The self-normalized Bernstein inequality of [MDJKLV21], by the method of mixtures [HRMS20], at every
time simultaneously. Let `(ℱ_t)` be a filtration, `X_t` be `ℱ_{t+1}`-measurable with `|X_t| ≤ b`
(`b > 0`) and `E[X_t | ℱ_t] = 0`, and `w_t ∈ [0, 1]` be `ℱ_t`-measurable. Write
`S_n = ∑_{t<n} w_t X_t`, `V_n = ∑_{t<n} w_t² E[X_t² | ℱ_t]` and `h(x) = (1 + x) log(1 + x) - x`,
the Cramér transform of the Poisson law of parameter 1.

1. **The Poisson Cramér transform.** Prove `h(x) ≥ x²/(2(1 + x/3))` for `x ≥ 0`, the value
   `c h(s/c)` of `λ ↦ λ b s - c(e^{λb} - 1 - λb)` at `λ = log(1 + s/c)/b`, and the inversion
   `c h(s/c) ≤ ℓ ⇒ s ≤ √(2cℓ) + (2/3)ℓ`.
2. **Mixture bound.** Mix the exponential supermartingales `exp(λ S_n - ψ_b(λ) V_n)` of
   ReinforcementLearning 3.1 (LMLExplore's `Probability/Martingale/Freedman.lean`) over λ, for `X`
   and `-X`, and prove with Ville's inequality: for `δ ∈ (0, 1)`,
   `P(∃ n ≥ 1, (V_n/b² + 1) h(b|S_n|/(V_n + b²)) ≥ log(1/δ) + log(8(1 + √(2n)))) ≤ δ`, and the
   weaker threshold `log(1/δ) + log(4e(2n + 1))` of [MDJKLV21].
3. **Explicit forms.** With probability at least `1 - δ`, for all `n ≥ 1`,
   `|S_n| ≤ √(2(V_n + b²)L_n) + (2/3) b L_n` and `|S_n| ≤ √(2 V_n L_n) + 3 b L_n`, with
   `L_n = log(4e(2n + 1)/δ)`; and the i.i.d. corollary: for i.i.d. `Y_i` with `|Y_i - E Y_i| ≤ b`
   and variance σ², `|∑_{i<n}(Y_i - E Y_i)| ≤ √(2nσ²L_n) + 3bL_n` for all `n`.

ReinforcementLearning 3.1 (Freedman's inequality, peeled up to a horizon) and 3.2 (empirical
Bernstein at a fixed `n`) do not contain this time-uniform form: S2 would be an item of
ReinforcementLearning Layer 3, stated through the conditional domination of Identification 4.2.

References: [MDJKLV21] P. Ménard, O. D. Domingues, A. Jonsson, E. Kaufmann, E. Leurent and
M. Valko, Fast active learning for pure exploration in reinforcement learning, ICML 2021.
[HRMS20] S. R. Howard, A. Ramdas, J. McAuliffe and J. Sekhon, Time-uniform Chernoff bounds via
nonnegative supermartingales, Probability Surveys 17, 2020. [EV26, Lemma 21].

### S3. Measurable singletons of dependent sums and bounds on extended natural numbers

`MeasurableSingletonClass (Σ i, α i)` when every `α i` has measurable singletons, next to
Mathlib's `Sigma.instMeasurableSpace` and LML's `measurableSet_sigma_iff`; and
`ENat.toENNReal_le_ofReal_of_forall_natCast_le`: if every natural number `T ≤ τ` is at most the
real `U`, then `(τ : ℝ≥0∞) ≤ ENNReal.ofReal U`, next to Mathlib's `ENat.forall_natCast_le_iff_le`.
Both are Mathlib-shaped. A target would only place them in LMLExplore
(`MeasureTheory/MeasurableSpace/Constructions.lean`, `Basic/`) until Mathlib has them.
