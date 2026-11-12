/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.ForLMLExplore.SequentialLearning.DivergenceDecomposition
public import Essakine2026Tight.ForLMLExplore.InformationTheory.KullbackLeibler.Bernoulli
public import LMLExplore.Identification.ChangeOfMeasure

/-!
# Change of measure at a stopping time, for runs

Let `A : IdentAlg Unit 𝓐 𝓨 𝓓` be an identification algorithm (sampling rule, stopping rule
`A.stopSet`, output rule `A.output`) with a finite action set `𝓐`, and consider a run of `A` in
the stationary environment with feedback kernel `ν` on `(Ω, P)` and a run in the stationary
environment with feedback kernel `ν'` on `(Ω', P')`. Write `τ = A.stoppingTime O X Y` for the
number of rounds played and `N_a(τ) = pullCount X a τ` for the number of rounds before `τ` at
which the action `a` was played.

LMLExplore's transportation lemma `LMLExplore.Identification.klBer_measureReal_histOutputMeasure_le`
(Lemma 1 of Kaufmann, Cappé and Garivier, 2016), which rests on the divergence bound at a
stopping time `Learning.klDiv_stoppedHistMeasure_le`, is stated for the joint law
`histOutputMeasure` of the stopped history and the output, with the expectations of the numbers
of pulls taken under the law `trajMeasure` of the trajectory. Along runs on arbitrary probability
spaces, these laws are those of the (stopped history, output) pair
(`Learning.IdentAlg.IsRun.hasLaw_stoppedHist_output`) and of the trajectory
(`Learning.IsAlgEnvSeq.hasLaw_trajectory`). This file states the change of measure for runs.

## Main statements

* `IsRun.klDiv_map_stoppedHist_out`: the output is drawn from the same kernel in both runs, so the
  divergence between the laws of the pairs (stopped history, output) is the divergence between the
  laws of the stopped histories; `IsRun.klDiv_map_out_le_stoppedHist`: the divergence between the
  laws of the outputs is at most that between the laws of the stopped histories.
* `IsRun.klDiv_map_stoppedHist_out_eq_sum_pullCount`: when `τ` is almost surely finite under both
  runs, the divergence between the laws of the pairs is `∑ a, E[N_a(τ)] KL(ν a ‖ ν' a)`.
* `IsRun.klBer_measureReal_le_sum_pullCount`: **the change of measure** (Lemma 1 of Kaufmann,
  Cappé and Garivier, 2016, Lemma 17 of Essakine and Vernade, 2026), in the one-sided form where
  `τ` is only assumed almost surely finite under the *first* run: for every measurable set `C` of
  (stopped history, output) pairs, with `E`, `E'` the events that the pair belongs to `C`,
  `klBer (P E) (P' E') ≤ ∑ a, E[N_a(τ)] KL(ν a ‖ ν' a)`. The same bound in terms of Bernoulli
  measures is `IsRun.klDiv_bernoulliMeasure_le_sum_pullCount`, in real form
  `IsRun.klBerReal_measureReal_le_toReal_sum_pullCount`, and for an event of the output whose
  probability under `ν'` is given by the law `A.outputMeasure` of the output
  `IsRun.klBer_measureReal_outputMeasure_le_sum_pullCount`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory LMLExplore LMLExplore.Identification Finset
open scoped ENNReal

namespace Learning.IdentAlg

variable {𝓐 𝓨 𝓓 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {m𝓓 : MeasurableSpace 𝓓} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {A : IdentAlg Unit 𝓐 𝓨 𝓓} {O : ℕ → Ω → Unit} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {O' : ℕ → Ω' → Unit} {X' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨}
  {out : Ω → 𝓓} {out' : Ω' → 𝓓} {env env' : Environment Unit 𝓐 𝓨}
  {C : Set ((Σ n : ℕ, Hist Unit 𝓐 𝓨 n) × 𝓓)}

section Output

/-- **Appending the output does not change the divergence**: for two runs of the same
identification algorithm, the divergence between the laws of the pairs (history at the stopping
time, output) is the divergence between the laws of the histories at the stopping time. -/
lemma IsRun.klDiv_map_stoppedHist_out (h : A.IsRun env O X Y out P)
    (h' : A.IsRun env' O' X' Y' out' P') :
    klDiv (P.map fun ω ↦ (A.stoppedHist O X Y ω, out ω))
        (P'.map fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) =
      klDiv (P.map (A.stoppedHist O X Y)) (P'.map (A.stoppedHist O' X' Y')) := by
  rw [h.hasCondDistrib_output.map_eq, h'.hasCondDistrib_output.map_eq]
  exact klDiv_compProd_left _ _ _

/-- **Data processing for runs**: for two runs of the same identification algorithm, the
divergence between the laws of the outputs is at most the divergence between the laws of the
histories at the stopping time. -/
lemma IsRun.klDiv_map_out_le_stoppedHist (h : A.IsRun env O X Y out P)
    (h' : A.IsRun env' O' X' Y' out' P') :
    klDiv (P.map out) (P'.map out') ≤
      klDiv (P.map (A.stoppedHist O X Y)) (P'.map (A.stoppedHist O' X' Y')) := by
  rw [← h.klDiv_map_stoppedHist_out h']
  have hmap := klDiv_map_le (P.map fun ω ↦ (A.stoppedHist O X Y ω, out ω))
    (P'.map fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) measurable_snd
  rwa [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
    h.hasCondDistrib_output.aemeasurable, AEMeasurable.map_map_of_aemeasurable
    measurable_snd.aemeasurable h'.hasCondDistrib_output.aemeasurable] at hmap

end Output

section StationaryEnv

variable {ν ν' : Kernel 𝓐 𝓨} [IsMarkovKernel ν] [IsMarkovKernel ν'] [Fintype 𝓐] [DecidableEq 𝓐]
  [MeasurableSingletonClass 𝓐] [MeasurableSpace.CountablyGenerated 𝓨]

/-- **Divergence decomposition for a run**: for two runs of the same identification algorithm in
two stationary environments with feedback kernels `ν` and `ν'`, with almost surely finite
stopping times, the divergence between the laws of the pairs (stopped history, output) is
`∑ a, E[N_a(τ)] KL(ν a ‖ ν' a)`. -/
lemma IsRun.klDiv_map_stoppedHist_out_eq_sum_pullCount
    (h : A.IsRun (Environment.bandit ν) O X Y out P)
    (h' : A.IsRun (Environment.bandit ν') O' X' Y' out' P')
    (hτ : ∀ᵐ ω ∂P, A.stoppingTime O X Y ω ≠ ⊤)
    (hτ' : ∀ᵐ ω ∂P', A.stoppingTime O' X' Y' ω ≠ ⊤) :
    klDiv (P.map fun ω ↦ (A.stoppedHist O X Y ω, out ω))
        (P'.map fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) =
      ∑ a, (∫⁻ ω, (pullCount X a (ENat.toNat (A.stoppingTime O X Y ω)) ω : ℝ≥0∞) ∂P) *
        klDiv (ν a) (ν' a) := by
  rw [h.klDiv_map_stoppedHist_out h']
  exact h.isAlgEnvSeq.klDiv_map_stoppedValue_sigmaHistory_eq_sum_pullCount h'.isAlgEnvSeq
    A.measurableSet_stopSet hτ hτ'

/-- **Change of measure at a stopping time** (one-sided form of Lemma 1 of Kaufmann, Cappé and
Garivier, 2016). For two runs of the same identification algorithm in two stationary environments
with feedback kernels `ν` and `ν'`, with a stopping time which is almost surely finite under the
*first* environment, and for every measurable set `C` of (stopped history, output) pairs, the
binary divergence between the probabilities of `C` under the two runs is at most
`∑ a, E[N_a(τ)] KL(ν a ‖ ν' a)`, where `N_a(τ) = pullCount X a τ` is the number of rounds before
stopping at which the action `a` was played. This is LMLExplore's
`LMLExplore.Identification.klBer_measureReal_histOutputMeasure_le`, transported to the runs. -/
lemma IsRun.klBer_measureReal_le_sum_pullCount (h : A.IsRun (Environment.bandit ν) O X Y out P)
    (h' : A.IsRun (Environment.bandit ν') O' X' Y' out' P')
    (hτ : ∀ᵐ ω ∂P, A.stoppingTime O X Y ω ≠ ⊤) (hC : MeasurableSet C) :
    klBer (P.real ((fun ω ↦ (A.stoppedHist O X Y ω, out ω)) ⁻¹' C))
        (P'.real ((fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) ⁻¹' C)) ≤
      ∑ a, (∫⁻ ω, (pullCount X a (ENat.toNat (A.stoppingTime O X Y ω)) ω : ℝ≥0∞) ∂P) *
        klDiv (ν a) (ν' a) := by
  have hseq := h.isAlgEnvSeq
  have hE : P.real ((fun ω ↦ (A.stoppedHist O X Y ω, out ω)) ⁻¹' C) =
      (histOutputMeasure A (Environment.bandit ν)).real C :=
    h.hasLaw_stoppedHist_output.measureReal_eq hC
  have hE' : P'.real ((fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) ⁻¹' C) =
      (histOutputMeasure A (Environment.bandit ν')).real C :=
    h'.hasLaw_stoppedHist_output.measureReal_eq hC
  rw [hE, hE']
  refine (klBer_measureReal_histOutputMeasure_le A ν ν'
    ((stopsAS_iff_ae_stoppingTime_ne_top hseq).2 hτ) hC).trans_eq
    (sum_congr rfl fun a _ ↦ congrArg (· * klDiv (ν a) (ν' a)) ?_)
  -- The number of pulls before stopping is a function of the trajectory.
  have hf : Measurable fun t : ℕ → Round Unit 𝓐 𝓨 ↦ (pullCount IT.action a
      (ENat.toNat (A.stoppingTime IT.obs IT.action IT.feedback t)) t : ℝ≥0∞) :=
    (measurable_of_countable _).comp (measurable_uncurry_pullCount_comp IT.measurable_action
      measurable_const (Measurable.of_discrete.comp (A.measurable_stoppingTime IT.measurable_obs
        IT.measurable_action IT.measurable_feedback)))
  exact (hseq.hasLaw_trajectory.lintegral_comp hf.aemeasurable).symm

/-- **Change of measure at a stopping time**, with Bernoulli measures: the form of
`IsRun.klBer_measureReal_le_sum_pullCount` in which the binary divergence is the divergence
between the laws of the indicators of the two events. -/
lemma IsRun.klDiv_bernoulliMeasure_le_sum_pullCount
    (h : A.IsRun (Environment.bandit ν) O X Y out P)
    (h' : A.IsRun (Environment.bandit ν') O' X' Y' out' P')
    (hτ : ∀ᵐ ω ∂P, A.stoppingTime O X Y ω ≠ ⊤) (hC : MeasurableSet C) :
    klDiv (bernoulliMeasure true false
          ⟨P.real ((fun ω ↦ (A.stoppedHist O X Y ω, out ω)) ⁻¹' C), measureReal_nonneg,
            measureReal_le_one⟩)
        (bernoulliMeasure true false
          ⟨P'.real ((fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) ⁻¹' C), measureReal_nonneg,
            measureReal_le_one⟩) ≤
      ∑ a, (∫⁻ ω, (pullCount X a (ENat.toNat (A.stoppingTime O X Y ω)) ω : ℝ≥0∞) ∂P) *
        klDiv (ν a) (ν' a) := by
  rw [InformationTheory.klDiv_bernoulliMeasure (by decide)]
  exact h.klBer_measureReal_le_sum_pullCount h' hτ hC

/-- **Change of measure at a stopping time**, real form: when the probability of the event under
the second run is in `(0, 1)` and the right-hand side is finite, the real binary divergence
`klBerReal` is bounded by the real right-hand side. -/
lemma IsRun.klBerReal_measureReal_le_toReal_sum_pullCount
    (h : A.IsRun (Environment.bandit ν) O X Y out P)
    (h' : A.IsRun (Environment.bandit ν') O' X' Y' out' P')
    (hτ : ∀ᵐ ω ∂P, A.stoppingTime O X Y ω ≠ ⊤) (hC : MeasurableSet C)
    (h0 : 0 < P'.real ((fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) ⁻¹' C))
    (h1 : P'.real ((fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) ⁻¹' C) < 1)
    (hD : ∑ a, (∫⁻ ω, (pullCount X a (ENat.toNat (A.stoppingTime O X Y ω)) ω : ℝ≥0∞) ∂P) *
      klDiv (ν a) (ν' a) ≠ ∞) :
    klBerReal (P.real ((fun ω ↦ (A.stoppedHist O X Y ω, out ω)) ⁻¹' C))
        (P'.real ((fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) ⁻¹' C)) ≤
      (∑ a, (∫⁻ ω, (pullCount X a (ENat.toNat (A.stoppingTime O X Y ω)) ω : ℝ≥0∞) ∂P) *
        klDiv (ν a) (ν' a)).toReal := by
  have hle := h.klBer_measureReal_le_sum_pullCount h' hτ hC
  rwa [klBer_eq_ofReal_klBerReal ⟨measureReal_nonneg, measureReal_le_one⟩ ⟨h0.le, h1.le⟩
    (klBer_ne_top ⟨h0, h1⟩), ENNReal.ofReal_le_iff_le_toReal hD] at hle

/-- **Change of measure at a stopping time**, for an event of the output: for a run of `A` in the
stationary environment with feedback kernel `ν` whose stopping time is almost surely finite, and
any other feedback kernel `ν'`, the binary divergence between the probability that the output
belongs to `s` and the probability of `s` under the law `A.outputMeasure (Environment.bandit ν')` of
the output in the second environment is at most `∑ a, E[N_a(τ)] KL(ν a ‖ ν' a)`. -/
lemma IsRun.klBer_measureReal_outputMeasure_le_sum_pullCount
    (h : A.IsRun (Environment.bandit ν) O X Y out P) (hτ : ∀ᵐ ω ∂P, A.stoppingTime O X Y ω ≠ ⊤)
    {s : Set 𝓓} (hs : MeasurableSet s) :
    klBer (P.real (out ⁻¹' s)) ((A.outputMeasure (Environment.bandit ν')).real s) ≤
      ∑ a, (∫⁻ ω, (pullCount X a (ENat.toNat (A.stoppingTime O X Y ω)) ω : ℝ≥0∞) ∂P) *
        klDiv (ν a) (ν' a) := by
  have hrun := isRun_runMeasure A (Environment.bandit ν')
  have hle := h.klBer_measureReal_le_sum_pullCount hrun hτ (MeasurableSet.univ.prod hs)
  simp only [Set.mk_preimage_prod, Set.preimage_univ, Set.univ_inter] at hle
  rwa [← snd_runMeasure, Measure.snd, map_measureReal_apply measurable_snd hs]

end StationaryEnv

end Learning.IdentAlg
