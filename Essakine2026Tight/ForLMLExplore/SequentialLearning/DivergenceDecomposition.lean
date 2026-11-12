/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.SequentialLearning.DivergenceDecomposition
public import LeanMachineLearning.SequentialLearning.FiniteActions
public import Essakine2026Tight.ForLMLExplore.SequentialLearning.StoppedHistory
public import Essakine2026Tight.ForLMLExplore.InformationTheory.KLStoppedPrefix

/-!
# The divergence decomposition at a stopping time, with equality

LML's `LeanMachineLearning.SequentialLearning.DivergenceDecomposition` proves the chain rule and
the divergence decomposition for the history of a *fixed* number of rounds
(`IsAlgEnvSeq.klDiv_map_history_stepKernel`, `IsAlgEnvSeq.klDiv_map_history_compProd_bandit`,
`IsAlgEnvSeq.klDiv_map_history_bandit`) and for the whole trajectory
(`IsAlgEnvSeq.klDiv_map_trajectory_stepKernel`,
`IsAlgEnvSeq.klDiv_map_trajectory_compProd_bandit`, `IsAlgEnvSeq.klDiv_map_trajectory_bandit`),
and LMLExplore's `LMLExplore.SequentialLearning.DivergenceDecomposition` reindexes the fixed-time
decomposition by the actions (`IsAlgEnvSeq.klDiv_map_history_eq_sum_pullCount`) and proves the
chain rule at a stopping time as an *inequality*, for any two algorithm-environment pairs
(`Learning.klDiv_stoppedHistMeasure_le_tsum`, `Learning.klDiv_stoppedHistMeasure_le_lintegral`,
`Learning.klDiv_stoppedHistMeasure_le`). This file proves the *equalities* at a stopping time for
one algorithm against two environments, as special cases, for the process of rounds, of the chain
rule at a stopping time for a general process with conditional laws
(`Essakine2026Tight.ForLMLExplore.InformationTheory.KLStoppedPrefix`).

Let `alg` be an algorithm and `env, env'` two environments, and consider two algorithm-environment
sequences of `alg` against these environments, on arbitrary probability spaces. For a stopping
rule `S` with stopping time `τ = hittingAfter (sigmaHistory O X Y) S 0` (the number of rounds
played), the divergence between the laws of the histories stopped at time `M`
(`stoppedProcess (sigmaHistory O X Y) τ M`, the histories of the first `min τ M` rounds) is the
sum over the rounds `t < M` of the conditional divergences of the step at round `t`, on the event
`{t < τ}` (`IsAlgEnvSeq.klDiv_map_stoppedProcess_sigmaHistory_stepKernel`, a chain rule: the
observation and policy kernels are shared and only the feedback kernels differ), and when `τ` is
almost surely finite under both laws, the divergence between the laws of the stopped histories
(`stoppedValue (sigmaHistory O X Y) τ`, which is LML's `IdentAlg.stoppedHist` when `S` is the
stopping rule of an identification algorithm) is the series of these terms
(`IsAlgEnvSeq.klDiv_map_stoppedValue_sigmaHistory_stepKernel`).

For two stationary environments with reward kernels `κ, κ'` (environments without observations),
the conditional divergence of a step is the conditional divergence of the reward given the played
action. This is the *divergence decomposition* of bandit lower bounds, in composition-product form
(`klDiv_map_stoppedProcess_sigmaHistory_compProd`, `klDiv_map_stoppedValue_sigmaHistory_compProd`,
on arbitrary measurable spaces) and in integral form (`klDiv_map_stoppedProcess_sigmaHistory`,
`klDiv_map_stoppedValue_sigmaHistory`, when `𝓨` is countably generated), the latter reading
`klDiv (P.map (stoppedValue (sigmaHistory O X Y) τ))
    (P'.map (stoppedValue (sigmaHistory O' X' Y') τ'))
  = ∫⁻ ω, ∑ t < τ ω, klDiv (κ (X t ω)) (κ' (X t ω)) ∂P`
for almost surely finite stopping times `τ`, `τ'`. The integral forms follow from the
composition-product forms by LML's integrated chain rule `klDiv_compProd_right_eq_lintegral`;
the same passage turns LML's one-step composition-product identities
`klDiv_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd` and
`klDiv_compProd_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd` into their integral forms
`klDiv_compProd_compProd_prodMkLeft` and `klDiv_compProd_compProd_compProd_prodMkLeft`.

The reindexing of these sums by the actions, for a finite action set, turns them into the
familiar form `∑ a, E[N_a(τ)] KL(κ a ‖ κ' a)` where `N_a(n) = pullCount X a n` is the number of
rounds before `n` at which `a` was played
(`IsAlgEnvSeq.klDiv_map_stoppedProcess_sigmaHistory_eq_sum_pullCount`,
`IsAlgEnvSeq.klDiv_map_stoppedValue_sigmaHistory_eq_sum_pullCount`), through LMLExplore's Wald
identity `LMLExplore.sum_lintegral_pullCount_mul`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal ENat

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨}
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {O' : ℕ → Ω' → 𝓞} {X' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨}
  {alg : Algorithm 𝓞 𝓐 𝓨} {env env' : Environment 𝓞 𝓐 𝓨} {κ κ' : Kernel 𝓐 𝓨} [IsMarkovKernel κ]
  [IsMarkovKernel κ'] {S : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)}

section OneStep

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

/-- The divergence of one step of a policy/reward decomposition, in integral form: the policy
`π` is shared and the reward kernels `κ`, `η` (which ignore the history) differ, so the
divergence is the expected divergence of the reward kernels at the played action, whose law is
`π ∘ₘ μ`. -/
lemma klDiv_compProd_compProd_prodMkLeft [MeasurableSpace.CountableOrCountablyGenerated β γ]
    (μ : Measure α) [IsFiniteMeasure μ] (π : Kernel α β) [IsMarkovKernel π] (κ η : Kernel β γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    klDiv (μ ⊗ₘ (π ⊗ₖ Kernel.prodMkLeft α κ)) (μ ⊗ₘ (π ⊗ₖ Kernel.prodMkLeft α η)) =
      ∫⁻ b, klDiv (κ b) (η b) ∂(π ∘ₘ μ) := by
  rw [klDiv_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd,
    klDiv_compProd_right_eq_lintegral]

/-- The divergence of one step of an observation/policy/reward decomposition, in integral form:
the observation kernel `o` and the policy `π` are shared and the reward kernels `κ`, `η` (which
ignore the history and the observation) differ, so the divergence is the expected divergence of
the reward kernels at the played action, whose law is `π ∘ₘ (μ ⊗ₘ o)`. -/
lemma klDiv_compProd_compProd_compProd_prodMkLeft
    [MeasurableSpace.CountableOrCountablyGenerated γ δ] (μ : Measure α) [IsFiniteMeasure μ]
    (o : Kernel α β) [IsMarkovKernel o] (π : Kernel (α × β) γ) [IsMarkovKernel π] (κ η : Kernel γ δ)
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    klDiv (μ ⊗ₘ (o ⊗ₖ (π ⊗ₖ Kernel.prodMkLeft (α × β) κ)))
        (μ ⊗ₘ (o ⊗ₖ (π ⊗ₖ Kernel.prodMkLeft (α × β) η))) =
      ∫⁻ b, klDiv (κ b) (η b) ∂(π ∘ₘ (μ ⊗ₘ o)) := by
  rw [klDiv_compProd_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd,
    klDiv_compProd_right_eq_lintegral]

/-- The divergence of one step of a policy/reward decomposition for a finite action set: the
policy `π` is shared and the reward kernels `κ`, `η` differ, so the divergence is the sum over the
actions of the probability of the action times the divergence of the reward kernels there. -/
lemma klDiv_compProd_compProd_prodMkLeft_eq_sum [Fintype β] [MeasurableSingletonClass β]
    [MeasurableSpace.CountablyGenerated γ]
    (μ : Measure α) [IsFiniteMeasure μ] (π : Kernel α β) [IsMarkovKernel π] (κ η : Kernel β γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    klDiv (μ ⊗ₘ (π ⊗ₖ Kernel.prodMkLeft α κ)) (μ ⊗ₘ (π ⊗ₖ Kernel.prodMkLeft α η)) =
      ∑ b, (π ∘ₘ μ) {b} * klDiv (κ b) (η b) := by
  rw [klDiv_compProd_compProd_prodMkLeft, lintegral_fintype]
  exact sum_congr rfl fun b _ ↦ mul_comm _ _

end OneStep

/-! ### Chain rules for stopped histories -/

/-- **Chain rule for histories stopped at a bounded stopping time.** For an algorithm `alg` run
against two environments `env`, `env'`, and a stopping rule `S` with stopping time `τ`, the
divergence between the laws of the histories stopped at `min τ M` is the sum over the rounds
`t < M` of the conditional divergences, on the event `{t < τ}`, of the step at round `t` given
the first `t` rounds (composition-product form). This is
`klDiv_map_stoppedProcess_sigmaPrefix_hittingAfter_compProd` for the process of rounds. -/
lemma IsAlgEnvSeq.klDiv_map_stoppedProcess_sigmaHistory_stepKernel
    (h : IsAlgEnvSeq O X Y alg env P) (h' : IsAlgEnvSeq O' X' Y' alg env' P')
    (hS : MeasurableSet S) (M : ℕ) :
    klDiv (P.map (stoppedProcess (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0) M))
        (P'.map
          (stoppedProcess (sigmaHistory O' X' Y') (hittingAfter (sigmaHistory O' X' Y') S 0) M)) =
      ∑ t ∈ range M,
        klDiv ((P.restrict {ω | (t : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω}).map
            (history O X Y t) ⊗ₘ stepKernel alg env t)
          ((P.restrict {ω | (t : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω}).map
            (history O X Y t) ⊗ₘ stepKernel alg env' t) :=
  klDiv_map_stoppedProcess_sigmaPrefix_hittingAfter_compProd h.measurable_step h'.measurable_step
    h.hasCondDistrib_step h'.hasCondDistrib_step hS M

/-- **Chain rule for histories stopped at an almost surely finite stopping time.** For an
algorithm `alg` run against two environments `env`, `env'`, and a stopping rule `S` whose stopping
time is almost surely finite under both laws, the divergence between the laws of the stopped
histories is the series over the rounds `t` of the conditional divergences, on the event
`{t < τ}`, of the step at round `t` given the first `t` rounds (composition-product form). This
is `klDiv_map_stoppedValue_sigmaPrefix_hittingAfter_compProd` for the process of rounds. -/
lemma IsAlgEnvSeq.klDiv_map_stoppedValue_sigmaHistory_stepKernel
    (h : IsAlgEnvSeq O X Y alg env P) (h' : IsAlgEnvSeq O' X' Y' alg env' P')
    (hS : MeasurableSet S)
    (hτ : ∀ᵐ ω ∂P, hittingAfter (sigmaHistory O X Y) S 0 ω ≠ ⊤)
    (hτ' : ∀ᵐ ω ∂P', hittingAfter (sigmaHistory O' X' Y') S 0 ω ≠ ⊤) :
    klDiv (P.map (stoppedValue (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0)))
        (P'.map
          (stoppedValue (sigmaHistory O' X' Y') (hittingAfter (sigmaHistory O' X' Y') S 0))) =
      ∑' t : ℕ,
        klDiv ((P.restrict {ω | (t : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω}).map
            (history O X Y t) ⊗ₘ stepKernel alg env t)
          ((P.restrict {ω | (t : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω}).map
            (history O X Y t) ⊗ₘ stepKernel alg env' t) :=
  klDiv_map_stoppedValue_sigmaPrefix_hittingAfter_compProd h.measurable_step h'.measurable_step
    h.hasCondDistrib_step h'.hasCondDistrib_step hS hτ hτ'

section StationaryEnv

/-! ### The divergence decomposition for stationary environments

Stationary environments have no observations: the observation type is `Unit`. -/

variable {O : ℕ → Ω → Unit} {O' : ℕ → Ω' → Unit} {alg : Algorithm Unit 𝓐 𝓨}
  {S : Set (Σ n : ℕ, Hist Unit 𝓐 𝓨 n)}

/-- **Divergence decomposition for histories stopped at a bounded stopping time**,
composition-product form. For an algorithm `alg` run against two stationary environments with
reward kernels `κ` and `κ'`, and a stopping rule `S` with stopping time `τ`, the divergence
between the laws of the histories stopped at `min τ M` is the sum over the rounds `t < M` of the
conditional divergences of the reward kernels given the played action, on the event `{t < τ}`. -/
lemma IsAlgEnvSeq.klDiv_map_stoppedProcess_sigmaHistory_compProd
    (h : IsAlgEnvSeq O X Y alg (Environment.bandit κ) P)
    (h' : IsAlgEnvSeq O' X' Y' alg (Environment.bandit κ') P') (hS : MeasurableSet S) (M : ℕ) :
    klDiv (P.map (stoppedProcess (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0) M))
        (P'.map
          (stoppedProcess (sigmaHistory O' X' Y') (hittingAfter (sigmaHistory O' X' Y') S 0) M)) =
      ∑ t ∈ range M,
        klDiv ((P.restrict {ω | (t : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω}).map
            (X t) ⊗ₘ κ)
          ((P.restrict {ω | (t : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω}).map
            (X t) ⊗ₘ κ') := by
  rw [h.klDiv_map_stoppedProcess_sigmaHistory_stepKernel h' hS M]
  refine sum_congr rfl fun t _ ↦ ?_
  have h_obs := (h.hasCondDistrib_obs_restrict_lt_hittingAfter_sigmaHistory hS t).map_eq
  rw [obs_bandit] at h_obs
  rw [stepKernel_bandit, stepKernel_bandit,
    klDiv_compProd_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd, ← h_obs,
    ← (h.hasCondDistrib_action_restrict_lt_hittingAfter_sigmaHistory hS t).hasLaw_comp.map_eq]

/-- **Divergence decomposition for histories stopped at a bounded stopping time**, integral
form: the divergence between the laws of the histories stopped at `min τ M` is the expected sum,
along the first trajectory, of the divergences of the reward kernels at the actions played before
`min τ M`. -/
lemma IsAlgEnvSeq.klDiv_map_stoppedProcess_sigmaHistory [MeasurableSpace.CountablyGenerated 𝓨]
    (h : IsAlgEnvSeq O X Y alg (Environment.bandit κ) P)
    (h' : IsAlgEnvSeq O' X' Y' alg (Environment.bandit κ') P') (hS : MeasurableSet S) (M : ℕ) :
    klDiv (P.map (stoppedProcess (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0) M))
        (P'.map
          (stoppedProcess (sigmaHistory O' X' Y') (hittingAfter (sigmaHistory O' X' Y') S 0) M)) =
      ∫⁻ ω, ∑ t ∈ range (ENat.toNat (min (hittingAfter (sigmaHistory O X Y) S 0 ω) M)),
        klDiv (κ (X t ω)) (κ' (X t ω)) ∂P := by
  have hX := h.measurable_action
  have hmeas : ∀ t, Measurable fun ω ↦ klDiv (κ (X t ω)) (κ' (X t ω)) := fun t ↦
    (measurable_klDiv_kernel κ κ').comp (hX t)
  have hlt : ∀ t : ℕ,
      MeasurableSet {ω | (t : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω} :=
    measurableSet_lt_hittingAfter_sigmaPrefix (Z := step O X Y) h.measurable_step hS
  rw [h.klDiv_map_stoppedProcess_sigmaHistory_compProd h' hS M]
  simp_rw [klDiv_compProd_right_eq_lintegral, lintegral_map (measurable_klDiv_kernel κ κ') (hX _),
    ← lintegral_indicator (hlt _)]
  rw [← lintegral_finsetSum _ fun t _ ↦ (hmeas t).indicator (hlt t)]
  refine lintegral_congr fun ω ↦ ?_
  simp_rw [Set.indicator_apply, Set.mem_ofPred_eq]
  exact sum_ite_lt_eq_sum_range_toNat_min _ _ M

/-- **Divergence decomposition for histories stopped at an almost surely finite stopping time**,
composition-product form. For an algorithm `alg` run against two stationary environments with
reward kernels `κ` and `κ'`, and a stopping rule `S` whose stopping time is almost surely finite
under both laws, the divergence between the laws of the stopped histories is the series over the
rounds `t` of the conditional divergences of the reward kernels given the played action, on the
event `{t < τ}`. -/
lemma IsAlgEnvSeq.klDiv_map_stoppedValue_sigmaHistory_compProd
    (h : IsAlgEnvSeq O X Y alg (Environment.bandit κ) P)
    (h' : IsAlgEnvSeq O' X' Y' alg (Environment.bandit κ') P') (hS : MeasurableSet S)
    (hτ : ∀ᵐ ω ∂P, hittingAfter (sigmaHistory O X Y) S 0 ω ≠ ⊤)
    (hτ' : ∀ᵐ ω ∂P', hittingAfter (sigmaHistory O' X' Y') S 0 ω ≠ ⊤) :
    klDiv (P.map (stoppedValue (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0)))
        (P'.map
          (stoppedValue (sigmaHistory O' X' Y') (hittingAfter (sigmaHistory O' X' Y') S 0))) =
      ∑' t : ℕ,
        klDiv ((P.restrict {ω | (t : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω}).map
            (X t) ⊗ₘ κ)
          ((P.restrict {ω | (t : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω}).map
            (X t) ⊗ₘ κ') := by
  rw [h.klDiv_map_stoppedValue_sigmaHistory_stepKernel h' hS hτ hτ']
  refine tsum_congr fun t ↦ ?_
  have h_obs := (h.hasCondDistrib_obs_restrict_lt_hittingAfter_sigmaHistory hS t).map_eq
  rw [obs_bandit] at h_obs
  rw [stepKernel_bandit, stepKernel_bandit,
    klDiv_compProd_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd, ← h_obs,
    ← (h.hasCondDistrib_action_restrict_lt_hittingAfter_sigmaHistory hS t).hasLaw_comp.map_eq]

/-- **Divergence decomposition for histories stopped at an almost surely finite stopping time**,
integral form: the divergence between the laws of the stopped histories is the expected sum,
along the first trajectory, of the divergences of the reward kernels at the actions played before
stopping. -/
lemma IsAlgEnvSeq.klDiv_map_stoppedValue_sigmaHistory [MeasurableSpace.CountablyGenerated 𝓨]
    (h : IsAlgEnvSeq O X Y alg (Environment.bandit κ) P)
    (h' : IsAlgEnvSeq O' X' Y' alg (Environment.bandit κ') P') (hS : MeasurableSet S)
    (hτ : ∀ᵐ ω ∂P, hittingAfter (sigmaHistory O X Y) S 0 ω ≠ ⊤)
    (hτ' : ∀ᵐ ω ∂P', hittingAfter (sigmaHistory O' X' Y') S 0 ω ≠ ⊤) :
    klDiv (P.map (stoppedValue (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0)))
        (P'.map
          (stoppedValue (sigmaHistory O' X' Y') (hittingAfter (sigmaHistory O' X' Y') S 0))) =
      ∫⁻ ω, ∑ t ∈ range (ENat.toNat (hittingAfter (sigmaHistory O X Y) S 0 ω)),
        klDiv (κ (X t ω)) (κ' (X t ω)) ∂P := by
  have hX := h.measurable_action
  have hmeas : ∀ t, Measurable fun ω ↦ klDiv (κ (X t ω)) (κ' (X t ω)) := fun t ↦
    (measurable_klDiv_kernel κ κ').comp (hX t)
  have hlt : ∀ t : ℕ,
      MeasurableSet {ω | (t : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω} :=
    measurableSet_lt_hittingAfter_sigmaPrefix (Z := step O X Y) h.measurable_step hS
  rw [h.klDiv_map_stoppedValue_sigmaHistory_compProd h' hS hτ hτ']
  simp_rw [klDiv_compProd_right_eq_lintegral, lintegral_map (measurable_klDiv_kernel κ κ') (hX _),
    ← lintegral_indicator (hlt _)]
  rw [← lintegral_tsum fun t ↦ ((hmeas t).indicator (hlt t)).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [hτ] with ω hω
  exact (tsum_congr fun t ↦ rfl).trans (LMLExplore.tsum_indicator_natCast_lt_eq_sum_range hω
    fun t ↦ klDiv (κ (X t ω)) (κ' (X t ω)))

end StationaryEnv

/-! ### Reindexing by the actions

For a finite action set, the sums over the rounds are reindexed by the actions, by LMLExplore's
`LMLExplore.sum_lintegral_pullCount_mul`: the number of rounds before `n` at which the action `a`
was played is `pullCount X a n` (LML `Learning.pullCount`). -/

section FiniteActions

variable [Fintype 𝓐] [DecidableEq 𝓐] [MeasurableSingletonClass 𝓐]

omit [IsProbabilityMeasure P] [IsProbabilityMeasure P'] [MeasurableSingletonClass 𝓐]
  [IsMarkovKernel κ] [IsMarkovKernel κ'] in
/-- The right-hand side of the divergence decomposition at a stopping time is finite when the
stopping time has finite expectation and the divergences of the feedback kernels are finite. -/
lemma sum_lintegral_pullCount_mul_klDiv_ne_top {τ : Ω → ℕ∞}
    (hτ : ∫⁻ ω, (τ ω : ℝ≥0∞) ∂P ≠ ∞) (hκ : ∀ a, klDiv (κ a) (κ' a) ≠ ∞) :
    ∑ a, (∫⁻ ω, (pullCount X a (ENat.toNat (τ ω)) ω : ℝ≥0∞) ∂P) * klDiv (κ a) (κ' a) ≠ ∞ := by
  refine ENNReal.sum_ne_top.2 fun a _ ↦ ENNReal.mul_ne_top ?_ (hκ a)
  exact ne_top_of_le_ne_top hτ
    (lintegral_mono fun ω ↦ LMLExplore.natCast_pullCount_toNat_le a (τ ω) ω)

section AlgEnvSeq

variable {O : ℕ → Ω → Unit} {O' : ℕ → Ω' → Unit} {alg : Algorithm Unit 𝓐 𝓨}
  {S : Set (Σ n : ℕ, Hist Unit 𝓐 𝓨 n)} [MeasurableSpace.CountablyGenerated 𝓨]

/-- **Divergence decomposition at a bounded stopping time**, reindexed by the actions. -/
lemma IsAlgEnvSeq.klDiv_map_stoppedProcess_sigmaHistory_eq_sum_pullCount
    (h : IsAlgEnvSeq O X Y alg (Environment.bandit κ) P)
    (h' : IsAlgEnvSeq O' X' Y' alg (Environment.bandit κ') P') (hS : MeasurableSet S) (M : ℕ) :
    klDiv (P.map (stoppedProcess (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0) M))
        (P'.map
          (stoppedProcess (sigmaHistory O' X' Y') (hittingAfter (sigmaHistory O' X' Y') S 0) M)) =
      ∑ a, (∫⁻ ω, (pullCount X a
          (ENat.toNat (min (hittingAfter (sigmaHistory O X Y) S 0 ω) M)) ω : ℝ≥0∞) ∂P) *
        klDiv (κ a) (κ' a) := by
  have hτm := measurable_hittingAfter_sigmaHistory h.measurable_obs h.measurable_action
    h.measurable_feedback hS (S := S)
  have hfm : Measurable fun ω ↦
      ENat.toNat (min (hittingAfter (sigmaHistory O X Y) S 0 ω) (M : WithTop ℕ)) :=
    (measurable_of_countable fun n : WithTop ℕ ↦ ENat.toNat (min n (M : WithTop ℕ))).comp hτm
  rw [h.klDiv_map_stoppedProcess_sigmaHistory h' hS M]
  exact (LMLExplore.sum_lintegral_pullCount_mul h.measurable_action hfm
    fun a ↦ klDiv (κ a) (κ' a)).symm

/-- **Divergence decomposition at an almost surely finite stopping time**, reindexed by the
actions: the divergence between the laws of the stopped histories is
`∑ a, E[N_a(τ)] KL(κ a ‖ κ' a)`. -/
lemma IsAlgEnvSeq.klDiv_map_stoppedValue_sigmaHistory_eq_sum_pullCount
    (h : IsAlgEnvSeq O X Y alg (Environment.bandit κ) P)
    (h' : IsAlgEnvSeq O' X' Y' alg (Environment.bandit κ') P') (hS : MeasurableSet S)
    (hτ : ∀ᵐ ω ∂P, hittingAfter (sigmaHistory O X Y) S 0 ω ≠ ⊤)
    (hτ' : ∀ᵐ ω ∂P', hittingAfter (sigmaHistory O' X' Y') S 0 ω ≠ ⊤) :
    klDiv (P.map (stoppedValue (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0)))
        (P'.map
          (stoppedValue (sigmaHistory O' X' Y') (hittingAfter (sigmaHistory O' X' Y') S 0))) =
      ∑ a, (∫⁻ ω, (pullCount X a
          (ENat.toNat (hittingAfter (sigmaHistory O X Y) S 0 ω)) ω : ℝ≥0∞) ∂P) *
        klDiv (κ a) (κ' a) := by
  have hτm := measurable_hittingAfter_sigmaHistory h.measurable_obs h.measurable_action
    h.measurable_feedback hS (S := S)
  have hfm : Measurable fun ω ↦ ENat.toNat (hittingAfter (sigmaHistory O X Y) S 0 ω) :=
    (measurable_of_countable fun n : WithTop ℕ ↦ ENat.toNat n).comp hτm
  rw [h.klDiv_map_stoppedValue_sigmaHistory h' hS hτ hτ']
  exact (LMLExplore.sum_lintegral_pullCount_mul h.measurable_action hfm
    fun a ↦ klDiv (κ a) (κ' a)).symm

end AlgEnvSeq

end FiniteActions

end Learning
