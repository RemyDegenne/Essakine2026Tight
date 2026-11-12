# Deduplication against LMLExplore (2026-11-12)

Until 2026-11-12 the project imported none of LMLExplore or Tau Ceti: `ForLMLExplore/` held local
copies of material that LMLExplore, Tau Ceti, LML or Mathlib already had at the pinned versions
(LMLExplore `afd365492580`), some of them with the same full names, so that the two could not be
imported together. This deduplication deleted every such copy, moved each use to the upstream
declaration and kept, re-proved on top of upstream, what is additional. It follows the items of
`PAPER_ROADMAP.md` tagged `exists` and the duplicates listed in its notes. The LMLExplore pin did
not move.

Decisions:

- LMLExplore's `MDP.env` needs `[Nonempty 𝓢]` (the fallback initial law when `μ₀` is not a
  probability measure), which the headline statements do not assume. `stepLaw` takes the instance
  `Nonempty (S × ℕ)` from its initial state through the named lemma `nonempty_augState`: an
  anonymous constructor `⟨p₀⟩` would be a nested proof with a non-atomic argument, abstracted as
  `stepLaw._proof_1`, which comparator cannot match.
- LMLExplore's definitions do not expose their bodies (no `@[expose]`): `rfl` proofs and
  applications such as `hM h s a` for `hM : M.HasRewardFn r` go through LMLExplore's `_def` and
  `_apply` lemmas (`hasRewardFn_def`, `rewardsIn_def`, `policyMeasure_def`, `env_obs_add_one_apply`,
  `augmented_P_apply`, …).
- Kept although they duplicate Mathlib in substance, because the change would rewrite the closure
  of the headline statements and many proofs: `vecExp` (Mathlib's `dotProduct`, about 300 uses)
  and the definitions of `expValue`, `entropicValue` (Mathlib's `mgf`, `cgf`). The roadmap notes
  (R8) leave these restatements to the port.

The headline statements are unchanged; the regenerated comparator challenges import LMLExplore's
`MDP`, `MDP.env`, `EpisodicMDP` and `EpisodicMDP.augmented` instead of copying local definitions.

The removed or renamed public declarations, with what replaces them, follow.

## Conditional distributions and identification runs (R4, R17, name clashes)

- `ProbabilityTheory.hasCondDistrib_snd_compProd_comap` (`Probability/CondDistrib.lean`) →
  LMLExplore's, same name.
- `MeasureTheory.Measure.restrict_compProd_prod_univ` → Tau Ceti
  `MeasureTheory.Measure.compProd_restrict_left` (symm).
- `ProbabilityTheory.HasCondDistrib.comp_of_hasLaw` → LML
  `ProbabilityTheory.HasCondDistrib.comp_hasLaw`.
- `ProbabilityTheory.hasCondDistrib_snd_compProd` → LMLExplore `hasCondDistrib_snd_compProd_comap`
  with `f = id`.
- `ProbabilityTheory.HasCondDistrib.compProd_left` → `HasCondDistrib.compProd_left_of_sectR` with
  `Kernel.sectR_prodMkLeft`.
- `ProbabilityTheory.HasCondDistrib.lintegral_prodMk` → LMLExplore
  `HasCondDistrib.lintegral_comp_prodMk_eq_lintegral_lintegral`.
- File `ForLMLExplore/Probability/HasCondDistrib.lean` deleted.
- File `ForLMLExplore/Identification/IdentificationAlg.lean` deleted:
  `Learning.IsAlgEnvSeq.comp_hasLaw` (LMLExplore, same name), `Learning.IdentAlg.IsRun.comp_hasLaw`
  (LMLExplore, same name), `Learning.IdentAlg.measurable_stoppedHist_traj` →
  `Learning.IdentAlg.measurable_stoppedHist`, `Learning.IdentAlg.runMeasure` →
  `LMLExplore.Identification.runMeasure`, `Learning.IdentAlg.isRun_runMeasure` →
  `LMLExplore.Identification.isRun_runMeasure`, `Learning.IdentAlg.map_snd_runMeasure` →
  `LMLExplore.Identification.snd_runMeasure`.
- `Learning.IdentAlg.stoppedHist_mem_stopSet_iff`, `Learning.IdentAlg.fst_stoppedHist`
  (ChangeOfMeasure) → LMLExplore's, same names.
- `Learning.IsAlgEnvSeq.klDiv_map_history_eq_sum_pullCount` (DivergenceDecomposition) →
  LMLExplore's, same name.
- `ProbabilityTheory.bernoulliMeasure_absolutelyContinuous`,
  `ProbabilityTheory.bernoulliMeasure_absolutelyContinuous_iff` → LMLExplore's, same names (the
  first now takes `(h0 : q = 0 → p = 0) (h1 : q = 1 → p = 1)`).

## MDP core (R1, R2, R3, R5, R8)

- File `ForLMLExplore/MarkovDecisionProcess/Basic.lean` deleted. `MDP` (and its fields),
  `Learning.MDP.env`, `policyAlg`, `policyMeasure`, `stateLaw`, `meanReward`: LMLExplore's, same
  names (`env`, `policyMeasure`, `stateLaw` take `[Nonempty 𝓢]`; `env` no longer needs
  `[IsProbabilityMeasure μ₀]`). `isProbabilityMeasure_policyMeasure`,
  `isProbabilityMeasure_stateLaw` → LMLExplore's instances. `envObs`, `envObs_zero`, `envObs_succ`,
  `isMarkovKernel_envObs` → LMLExplore `env_obs_zero`, `env_obs_add_one(_apply)`, `obsZero_env`,
  `env_feedback(_apply)`. `obsAction`, `measurable_obsAction`, `measurable_policyAlg_next` removed
  (LMLExplore inlines them). `lastObsAction`, `measurable_lastObsAction` moved to `Markov.lean`.
- `Episodic/Basic.lean`: `EpisodicMDP` (with fields and instances), `EpisodicMDP.ofDet`,
  `meanReward`, `RewardsIn`, `HasRewardFn`, `hasRewardFn_ofDet`, `meanReward_eq_of_hasRewardFn`,
  `augmented`: LMLExplore's, same names (bodies not exposed: use `rewardsIn_def`, `hasRewardFn_def`,
  `meanReward_def`, `ofDet_trans`, `ofDet_reward`). `augTransFun`, `measurable_augTransFun`,
  `augTrans`, `augTrans_apply`, `isProbabilityMeasure_augTrans`, `augRewardFun`,
  `measurable_augRewardFun`, `augReward`, `augReward_apply`, `isProbabilityMeasure_augReward`,
  `augmented_P`, `augmented_R` → LMLExplore `EpisodicMDP.augmented_P_apply`,
  `EpisodicMDP.augmented_R_apply`. New: `nonempty_augState` (the `Nonempty (S × ℕ)` instance of
  `stepLaw`, without a nested proof).
- `StepLaw.lean`: `augTrans_apply'`, `augReward_apply'` → `EpisodicMDP.augmented_P_apply`,
  `EpisodicMDP.augmented_R_apply`.
- `Values.lean`: `rewardsIn_of_hasRewardFn` → LMLExplore `EpisodicMDP.HasRewardFn.rewardsIn` (no
  measurability of the set needed).
- `Occupancy.lean`: `stateLawAt`, `hasLaw_fst_obs_stateLawAt`, `policyTransKernel`,
  `policyTransKernel_apply`, `isProbabilityMeasure_stateLawAt`,
  `hasCondDistrib_fst_obs_succ_stepLaw`, `occupancyMeasure_eq_map`, `stateLawAt_succ`,
  `stateLawAt_zero` → LMLExplore `stateMarginal M.trans (detPolicy hπ) (δ s₁)`,
  `EpisodicMDP.occupancy`, `occupancy_def`, `stateMarginal_trans_add_one`, `stateMarginal_zero`.
  New: `detPolicy`, `isAlgEnvSeq_markov_stepLaw`, `occupancyMeasure_eq_occupancy`. `occupancy_eq`
  restated with `stateMarginal`; `occupancy_succ` re-proved from LMLExplore's flow equation.
- `Markov.lean`: `ProbabilityTheory.Kernel.traj_congr` removed (`congr`); `measurable_finCons`,
  `measurable_finSnoc` re-proved from Mathlib's `MeasurableEquiv.piFinSuccAbove` and LML's
  `MeasurableEquiv.finSuccProd`; `feedbackZero_env`, `stepKernel_policyAlg_env_succ(_eq)`,
  `stepKernel_policyAlg_env_succ_eq_succStepKernel`, `iicOfFin_stepKernel_policyAlg_env` lost their
  `[IsProbabilityMeasure μ₀]` hypotheses.

## Information theory and identification (R15, R16, R18, R19)

- Files `InformationTheory/KLBer.lean`, `InformationTheory/Pinsker.lean` and
  `Probability/Process/HittingTime.lean` deleted; `InformationTheory/KullbackLeibler/Bernoulli.lean`
  (LMLExplore's path) holds what remains of the first two.
- `InformationTheory.klBerReal`, `klBer` → `LMLExplore.klBerReal`, `LMLExplore.klBer` (`klBer`
  clips its parameters to `[0, 1]`; the two agree on `[0, 1]²`, where every use lies).
  `klBerReal_apply` → `LMLExplore.klBerReal_def`; `klBerReal_one_left`, `klBerReal_self`,
  `klBerReal_eq_neg_binEntropy_sub`, `klBer_self`, `klBer_le_max`, `continuousOn_klBerReal`,
  `hasDerivAt_klBerReal` → LMLExplore's, same names in `LMLExplore`; `klBerReal_one_sub` →
  `LMLExplore.klBerReal_one_sub_one_sub`; `klBer_one_sub` → `LMLExplore.klBer_one_sub_one_sub`;
  `klBer_zero_right`, `klBer_one_right`, `klBer_eq_top_iff` → `LMLExplore.klBer_eq_top_iff`;
  `klBer_eq_ofReal` → `LMLExplore.klBer_eq_ofReal_klBerReal`, `LMLExplore.klBer_ne_top`;
  `klBer_zero_left`, `klBer_one_left`, `klBerReal_eq_of_ne`, `mul_log_div_eq_mul_sub` → dropped;
  `klBerReal_le_klBerReal_of_le_of_le` (and its primed form) → `LMLExplore.strictMonoOn_klBerReal`,
  `LMLExplore.strictAntiOn_klBerReal`; `klBerReal_le_div` → `LMLExplore.klBerReal_le_sq_sub_div`;
  `klBer_le_of_tendsto`, `klBer_le_of_tendsto_zero` → `LMLExplore.lowerSemicontinuous_klBer`.
  Moved to the namespace `LMLExplore`, re-proved: `klBerReal_zero_left` (`q` explicit),
  `sub_log_two_le_klBerReal`, `mul_log_sub_log_two_le_klBerReal`, `exp_neg_le_of_klBer_le`.
- `sq_sub_le_klBerReal_of_le`, `sq_sub_le_klBerReal` → `LMLExplore.two_mul_sq_le_klBerReal`;
  `sq_sub_le_klBer` → `LMLExplore.ofReal_two_mul_sq_le_klBer`; `ofReal_le_klDiv_bernoulliMeasure`,
  `sq_sub_le_klDiv` → Tau Ceti's `TauCeti.two_mul_sq_measureReal_sub_le_klDiv`;
  `map_mem_eq_bernoulliMeasure` → Mathlib's `hasLaw_indicator_one_bernoulliMeasure`;
  `klBer_measureReal_le_klDiv` → `LMLExplore.klBer_measureReal_le_klDiv`. Kept:
  `InformationTheory.klDiv_bernoulliMeasure` (now `= LMLExplore.klBer p q`, any two distinct points;
  R16), `klDiv_bernoulliMeasure_eq_klBerReal`, `abs_sub_le_sqrt_klDiv`.
- `ChangeOfMeasure.lean`: the truncation (`Learning.IdentAlg.truncSet`, `measurableSet_truncSet`,
  `prodMk_preimage_truncSet_eq_empty`, `preimage_truncSet`, `output_apply_hittingProcess_eq`,
  `map_hittingProcess_compProd_apply_truncSet`, `IsRun.klBer_le_klDiv_map_hittingProcess`,
  `IsRun.klBer_measureReal_inter_le_sum_pullCount`) → deleted;
  `IsRun.klBer_measureReal_le_sum_pullCount` (same statement) is re-proved from
  `LMLExplore.Identification.klBer_measureReal_histOutputMeasure_le` and
  `IsRun.hasLaw_stoppedHist_output`.
- `Learning.IsAlgEnvSeq.klDiv_map_hittingProcess_sigmaHistory` and its variants `_stepKernel`,
  `_compProd`, `_eq_sum_pullCount` → `…klDiv_map_stoppedProcess_sigmaHistory…`, and
  `…hittingValue…` → `…stoppedValue…`, stated with `stoppedProcess`/`stoppedValue
  (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0)`.
  `InformationTheory.klDiv_map_hittingProcess_sigmaPrefix{_compProd,}`,
  `klDiv_map_hittingValue_sigmaPrefix{_compProd,}` →
  `klDiv_map_stoppedProcess_sigmaPrefix_hittingAfter{_compProd,}`,
  `klDiv_map_stoppedValue_sigmaPrefix_hittingAfter{_compProd,}`.
  `measurable_hittingValue_sigmaPrefix`, `measurable_hittingProcess_sigmaPrefix` →
  `measurable_stoppedValue_sigmaPrefix`, `measurable_stoppedProcess_sigmaPrefix` at
  `measurable_hittingAfter_sigmaPrefix`.
- `MeasureTheory.hittingValue`, `hittingProcess` and their API → Mathlib's `stoppedValue`,
  `stoppedProcess` at `hittingAfter`, `hittingAfter_mem_set_of_ne_top`, `stoppedProcess_eq_of_le`,
  `stoppedProcess_eq_of_ge`, `stoppedProcess_const_top`.
- `Learning.sum_klDiv_eq_sum_pullCount` → LML's `Learning.sum_pullCount_mul`;
  `lintegral_sum_klDiv_eq_sum_pullCount` → `LMLExplore.sum_lintegral_pullCount_mul`;
  `natCast_pullCount_toNat_le` → `LMLExplore.natCast_pullCount_toNat_le`;
  `InformationTheory.tsum_ite_lt_eq_sum_range_toNat` →
  `LMLExplore.tsum_indicator_natCast_lt_eq_sum_range`.
- `ProbabilityTheory.ae_bernoulliMeasure` moved from `EV2026/HardMDP.lean` to
  `ForLMLExplore/Probability/Distributions/Bernoulli.lean`.

## Concentration and analysis (R12–R14, R20–R27)

- Files `MeasureTheory/Measure/Weighted.lean` and `WeightedProbability.lean` deleted:
  `MeasureTheory.weightedMeasure` and its API (`weightedMeasure_apply`,
  `measurable_weightedMeasure`, `weightedMeasure_singleton`,
  `measureReal_weightedMeasure_singleton`,
  `isFiniteMeasure_weightedMeasure`, `isProbabilityMeasure_weightedMeasure`,
  `weightedMeasure_absolutelyContinuous`) → LMLExplore's, same names in `LMLExplore`
  (`isProbabilityMeasure_weightedMeasure` takes `p ∈ simplex ι`).
- `MeasureTheory.Supermartingale.mul_measureReal_exists_le_le` →
  `MeasureTheory.Supermartingale.maximal_ineq`; `Supermartingale.measure_exists_ge_le` →
  `MeasureTheory.Supermartingale.measure_exists_le_le` (LMLExplore).
  `Probability/Martingale/Ville.lean`
  holds only R12 (with `condExp_exp_sub_le_one`, which LMLExplore does not have).
- `InformationTheory.ofReal_integral_sub_log_integral_exp_le_klDiv` →
  `TauCeti.ofReal_integral_sub_log_integral_exp_le_klDiv`.
- `ProbabilityTheory.integrable_of_ae_mem_Icc` → Mathlib's `MeasureTheory.Integrable.of_mem_Icc`;
  `integrable_of_ae_abs_le` → `MeasureTheory.Integrable.of_bound`.
- `ProbabilityTheory.condExp_exp_mul_sub_le_one` →
  `LMLExplore.condExp_exp_mul_sub_mul_condExp_sq_le_one` (on the increments `w i * Y i`);
  `setLIntegral_selfNorm_mixture_le` → `LMLExplore.supermartingale_integral_of_integrable`. New:
  `ProbabilityTheory.selfNormMixture_eq_integral`.
- `Real.exp_mul_le_of_abs_le`, `Real.expSubOneSub_mul_le` →
  `Real.exp_mul_le_one_add_mul_add_mul_sq`; `Real.expSubOneSub_eq_tsum` →
  `Real.hasSum_pow_add_two_div_factorial` (LMLExplore).
- `Real.sqrt_add_le` → Tau Ceti's `Real.sqrt_le_sqrt_add_sqrt_abs_sub`;
  `Real.le_sqrt_mul_sqrt_of_forall_two_mul_le` → dropped (Mathlib's `Real.sum_mul_le_sqrt_mul_sqrt`
  and `integral_mul_le_Lp_mul_Lq_of_nonneg`). `MeasureTheory.integral_sum_mul_sqrt_mul_le` lost
  three unused measurability hypotheses.
- `InformationTheory.rnDeriv_apply_eq_div` → Tau Ceti's
  `MeasureTheory.Measure.rnDeriv_eq_measure_singleton_div`; `InformationTheory.measure_typeCount_eq`
  and `ProbabilityTheory.iIndepFun.measure_prefix_mem_eq_pi` → Mathlib's `iIndepFun.hasLaw_pi`.
