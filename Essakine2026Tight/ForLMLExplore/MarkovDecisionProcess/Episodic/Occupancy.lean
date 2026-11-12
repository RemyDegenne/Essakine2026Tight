/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.ForLMLExplore.MarkovDecisionProcess.Episodic.StepLaw
public import LMLExplore.MarkovDecisionProcess.Episodic.Occupancy

/-!
# Occupancy measures of a finite-horizon MDP

For a finite-horizon MDP `M`, a policy `π : ℕ → S → A` (measurable at every step, `hπ`) and an
initial state `s₁`:

* `occupancyMeasure M π s₁ h` is the law of the state-action pair `(S_h, A_h)`
  (`ForLMLExplore/MarkovDecisionProcess/Episodic/Basic.lean`); the trajectory law is the law of a
  run of the Markov policy `detPolicy hπ` of the deterministic kernels of `π`
  (`isAlgEnvSeq_markov_stepLaw`), so the occupancy measure is LMLExplore's
  `EpisodicMDP.occupancy` of that policy from `δ_{s₁}` (`occupancyMeasure_eq_occupancy`), whose
  state marginals `stateMarginal M.trans (detPolicy hπ) (δ_{s₁})` satisfy the forward recursion
  `EpisodicMDP.stateMarginal_trans_add_one`; the action of each round is the policy's
  (`hasCondDistrib_action_obs_stepLaw`);
* the expectation of a function of `(S_h, A_h)` is its integral against the occupancy measure
  (`integral_comp_stateAction_stepLaw`);
* on finite state and action spaces, the occupancy `occupancy M π s₁ h s a = P^π(S_h = s, A_h = a)`
  is a probability vector concentrated on the graph of `π h` (`occupancy_nonneg`,
  `sum_occupancy`, `occupancy_eq`), the expectation of a sum of functions of the state-action
  pairs along the trajectory is a sum against the occupancies
  (`integral_sum_comp_obs_action_stepLaw`), and the forward recursion reads
  `p_{h+1}(s', a') = 1{a' = π_{h+1}(s')} ∑_{s, a} p_h(s, a) p_h(s' | s, a)` (`occupancy_succ`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP
open scoped ENNReal

namespace Learning.MDP.Episodic

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : EpisodicMDP S A)

section NoMeasurability

variable (π : ℕ → S → A) (s₁ : S)

lemma hasLaw_stateAction_occupancyMeasure (h : ℕ) :
    HasLaw (stateAction h) (occupancyMeasure M π s₁ h) (stepLaw M π (s₁, 0)) :=
  ⟨(measurable_stateAction h).aemeasurable, rfl⟩

/-- The expectation of an integrable function of the state-action pair of the step `h` is its
integral against the occupancy measure. -/
lemma integral_comp_stateAction_stepLaw (h : ℕ) {f : S × A → ℝ}
    (hf : AEStronglyMeasurable f (occupancyMeasure M π s₁ h)) :
    ∫ x, f (stateAction h x) ∂stepLaw M π (s₁, 0) = ∫ z, f z ∂occupancyMeasure M π s₁ h :=
  (integral_map (measurable_stateAction h).aemeasurable hf).symm

lemma lintegral_comp_stateAction_stepLaw (h : ℕ) {f : S × A → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f (stateAction h x) ∂stepLaw M π (s₁, 0) = ∫⁻ z, f z ∂occupancyMeasure M π s₁ h :=
  (lintegral_map hf (measurable_stateAction h)).symm

lemma occupancy_nonneg (h : ℕ) (s : S) (a : A) : 0 ≤ occupancy M π s₁ h s a :=
  measureReal_nonneg

variable [MeasurableSingletonClass S] [MeasurableSingletonClass A] [Fintype S] [Fintype A]

/-- The expectation of a function of the state-action pair of the step `h` is its sum against
the occupancies. -/
lemma integral_comp_obs_action_stepLaw (h : ℕ) (f : S → A → ℝ) :
    ∫ x, f (IT.obs h x).1 (IT.action h x) ∂stepLaw M π (s₁, 0)
      = ∑ s, ∑ a, occupancy M π s₁ h s a * f s a := by
  have h1 := integral_comp_stateAction_stepLaw M π s₁ h (f := fun z ↦ f z.1 z.2)
    (measurable_of_countable _).aestronglyMeasurable
  simp only [stateAction] at h1
  rw [h1, integral_fintype Integrable.of_finite, Fintype.sum_prod_type]
  rfl

/-- **Expectations of sums along the trajectory**: the expectation of `∑_{h < n} f_h(S_h, A_h)`
is `∑_{h < n} ∑_{s, a} p^π_h(s, a) f_h(s, a)`. -/
lemma integral_sum_comp_obs_action_stepLaw (n : ℕ) (f : ℕ → S → A → ℝ) :
    ∫ x, ∑ h ∈ range n, f h (IT.obs h x).1 (IT.action h x) ∂stepLaw M π (s₁, 0)
      = ∑ h ∈ range n, ∑ s, ∑ a, occupancy M π s₁ h s a * f h s a := by
  rw [integral_finsetSum _ fun h _ ↦ ?_]
  · exact sum_congr rfl fun h _ ↦ integral_comp_obs_action_stepLaw M π s₁ h (f h)
  · exact (Integrable.of_finite (f := fun z : S × A ↦ f h z.1 z.2)).comp_measurable
      (measurable_stateAction h)

end NoMeasurability

variable {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) (s₁ : S)

/-- The deterministic Markov policy `h ↦ δ_{π h}` of the policy `π`. -/
noncomputable def detPolicy (h : ℕ) : Kernel S A := Kernel.deterministic (π h) (hπ h)

instance (h : ℕ) : IsMarkovKernel (detPolicy hπ h) := by unfold detPolicy; infer_instance

include hπ

lemma isProbabilityMeasure_occupancyMeasure (h : ℕ) :
    IsProbabilityMeasure (occupancyMeasure M π s₁ h) := by
  have := isProbabilityMeasure_stepLaw M hπ (s₁, 0)
  unfold occupancyMeasure; infer_instance

lemma occupancy_le_one (h : ℕ) (s : S) (a : A) : occupancy M π s₁ h s a ≤ 1 := by
  have := isProbabilityMeasure_occupancyMeasure M hπ s₁ h
  exact measureReal_le_one

/-- The trajectory law of `π` from `p` is the law of a run of the Markov policy `detPolicy hπ` in
the time-augmented MDP. -/
lemma isAlgEnvSeq_markov_stepLaw (p : S × ℕ) :
    haveI := nonempty_augState p
    IsAlgEnvSeq IT.obs IT.action IT.feedback
      (Algorithm.markov fun _ ↦ augMarkovPolicy (detPolicy hπ))
      (M.augmented.env (Measure.dirac p)) (stepLaw M π p) := by
  have := nonempty_augState p
  have h := IT.isAlgEnvSeq_trajMeasure (policyAlg (augPolicy π) (measurable_augPolicy hπ))
    (M.augmented.env (Measure.dirac p))
  rw [← stepLaw_eq_trajMeasure M hπ, policyAlg_eq_markov] at h
  convert h using 3
  ext q : 1
  rw [augMarkovPolicy_apply, detPolicy, Kernel.deterministic_apply, Kernel.deterministic_apply,
    augPolicy_apply]

/-- The occupancy measure of `π` from `s₁` is LMLExplore's occupancy measure of the Markov policy
`detPolicy hπ` from the initial law `δ_{s₁}`. -/
lemma occupancyMeasure_eq_occupancy (h : ℕ) :
    occupancyMeasure M π s₁ h = M.occupancy (detPolicy hπ) (Measure.dirac s₁) h := by
  have : Nonempty S := ⟨s₁⟩
  have := isProbabilityMeasure_stepLaw M hπ (s₁, 0)
  have hl := EpisodicMDP.hasLaw_obs_fst_action_markov (μ := Measure.dirac (s₁, 0))
    ((ae_dirac_iff (measurableSet_eq_fun measurable_snd measurable_const)).2 rfl)
    (isAlgEnvSeq_markov_stepLaw M hπ (s₁, 0)) h
  rw [Measure.map_dirac' measurable_fst] at hl
  exact hl.map_eq

variable [MeasurableSingletonClass S] [MeasurableSingletonClass A]

/-- The action of the round `k` is the action of the policy at its state: conditional-law
form, valid without a measurable diagonal on the action space. -/
lemma hasCondDistrib_action_obs_stepLaw (s : S) (h k : ℕ) :
    HasCondDistrib (IT.action k) (fun x ↦ (IT.obs k x).1)
      (Kernel.deterministic (π (h + k)) (hπ (h + k))) (stepLaw M π (s, h)) := by
  have hc := (hasCondDistrib_shiftRounds_stepLaw M hπ s h k).comp_left (IT.measurable_action 0)
  have hK : (Kernel.prodMkLeft (Hist (S × ℕ) A ℝ k) (stepLawKernel M π (h + k))).map
      (IT.action 0) = Kernel.prodMkLeft (Hist (S × ℕ) A ℝ k)
        (Kernel.deterministic (π (h + k)) (hπ (h + k))) := by
    ext q : 1
    rw [Kernel.map_apply _ (IT.measurable_action 0), Kernel.prodMkLeft_apply,
      Kernel.prodMkLeft_apply, stepLawKernel_apply, Kernel.deterministic_apply]
    exact (hasLaw_action_zero_stepLaw M hπ q.2 (h + k)).map_eq
  rw [hK] at hc
  refine hc.comp_right.congr (Filter.Eventually.of_forall fun _ ↦ rfl)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  simp [shiftRounds, IT.action]

/-- The occupancy of `(s, a)` is the probability of visiting `s` if `a = π_h(s)`, and `0`
otherwise. -/
lemma occupancy_eq [DecidableEq A] (h : ℕ) (s : S) (a : A) :
    occupancy M π s₁ h s a = if a = π h s
      then (stateMarginal M.trans (detPolicy hπ) (Measure.dirac s₁) h).real {s} else 0 := by
  rw [occupancy, occupancyMeasure_eq_occupancy M hπ, EpisodicMDP.occupancy_def, detPolicy,
    Measure.compProd_deterministic (hπ h), map_measureReal_apply (f := fun s ↦ (s, π h s))
    (measurable_id.prodMk (hπ h)) (measurableSet_singleton _)]
  split_ifs with ha
  · congr 1
    ext s'
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.ext_iff]
    constructor
    · rintro ⟨rfl, -⟩; rfl
    · rintro rfl; exact ⟨rfl, ha.symm⟩
  · rw [← measureReal_empty (μ := stateMarginal M.trans (detPolicy hπ) (Measure.dirac s₁) h)]
    congr 1
    ext s'
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.ext_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl
    exact Ne.symm ha

variable [Fintype S] [Fintype A]

/-- Occupancies are probability vectors. -/
lemma sum_occupancy (h : ℕ) : ∑ s, ∑ a, occupancy M π s₁ h s a = 1 := by
  have := isProbabilityMeasure_stepLaw M hπ (s₁, 0)
  simpa using (integral_comp_obs_action_stepLaw M π s₁ h (fun _ _ ↦ 1)).symm

/-- **Forward recursion of the occupancies**, from LMLExplore's flow equation
`EpisodicMDP.stateMarginal_trans_add_one`. -/
lemma occupancy_succ [DecidableEq A] (h : ℕ) (s' : S) (a' : A) :
    occupancy M π s₁ (h + 1) s' a' = if a' = π (h + 1) s'
      then ∑ s, ∑ a, occupancy M π s₁ h s a * M.transVec h s a s' else 0 := by
  rw [occupancy_eq M hπ]
  split_ifs with ha
  · rw [EpisodicMDP.stateMarginal_trans_add_one, ← occupancyMeasure_eq_occupancy M hπ,
      measureReal_def, Measure.bind_apply (measurableSet_singleton _)
        (M.trans h).measurable.aemeasurable, lintegral_fintype, ENNReal.toReal_sum
        fun p _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _),
      Fintype.sum_prod_type]
    refine sum_congr rfl fun s _ ↦ sum_congr rfl fun a _ ↦ ?_
    rw [ENNReal.toReal_mul, mul_comm, occupancy, EpisodicMDP.transVec, MDP.transVec,
      measureReal_def, measureReal_def]
  · rfl

end Learning.MDP.Episodic
