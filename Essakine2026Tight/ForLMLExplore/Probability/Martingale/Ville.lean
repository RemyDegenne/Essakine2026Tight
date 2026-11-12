/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Martingale.Basic
public import LMLExplore.Probability.Martingale.Ville
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# The Bernoulli maximal inequality

The Bernoulli maximal inequality of Dann et al. (2017), Lemma F.4 (Lemma 20 of Essakine, Vernade
(2026)): if `X i ∈ {0, 1}` is adapted with `𝔼[X i | ℱ i] = P i`, then for every `δ > 0`,
`ℙ(∃ n, ∑_{i < n} X i < (1/2) ∑_{i < n} P i - log (1/δ)) ≤ δ`
(`MeasureTheory.measure_exists_sum_lt_half_mul_sum_sub_le`).

The one-step bound `𝔼[e^{P/2 - X} | 𝒢] ≤ 1` (`MeasureTheory.condExp_exp_sub_le_one`) makes
`exp (∑_{i < n} (P i / 2 - X i))` a supermartingale, by LMLExplore's
`LMLExplore.supermartingale_exp_sum_of_condExp_exp_le_one`, and Ville's inequality
(LMLExplore's `MeasureTheory.Supermartingale.measure_exists_le_le`) bounds the probability that it
ever reaches `1 / δ`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

section Bernoulli

variable {m : MeasurableSpace Ω} {X P : Ω → ℝ}

/-- One-step bound for a Bernoulli variable: if `X` has values in `{0, 1}` and `𝔼[X | 𝒢] = P`
with `P` a `𝒢`-measurable variable with values in `[0, 1]`, then `𝔼[e^{P/2 - X} | 𝒢] ≤ 1`. -/
lemma condExp_exp_sub_le_one (hm : m ≤ mΩ) (hX : ∀ ω, X ω = 0 ∨ X ω = 1)
    (hXm : StronglyMeasurable[mΩ] X) (hP : ∀ ω, P ω ∈ Set.Icc 0 1)
    (hPm : StronglyMeasurable[m] P) (hcond : μ[X | m] =ᵐ[μ] P) :
    μ[fun ω ↦ Real.exp (P ω / 2 - X ω) | m] ≤ᵐ[μ] 1 := by
  set k : ℝ := 1 - Real.exp (-1) with hk
  set G : Ω → ℝ := fun ω ↦ Real.exp (P ω / 2) with hG
  have hGm : StronglyMeasurable[m] G :=
    Real.continuous_exp.comp_stronglyMeasurable (hPm.div stronglyMeasurable_const)
  have hGm' : StronglyMeasurable[mΩ] G := hGm.mono hm
  have hGbdd : ∀ ω, G ω ∈ Set.Icc 0 (Real.exp (1 / 2)) := fun ω ↦
    ⟨(Real.exp_pos _).le, Real.exp_le_exp.2 (by linarith [(hP ω).2])⟩
  have hXbdd : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1 := fun ω ↦ by
    rcases hX ω with h | h <;> simp [h]
  have hk0 : 0 ≤ k := by
    simp only [hk, sub_nonneg]
    calc Real.exp (-1) ≤ Real.exp 0 := Real.exp_le_exp.2 (by norm_num)
      _ = 1 := Real.exp_zero
  have hk1 : k ≤ 1 := by
    simp only [hk, sub_le_self_iff]
    exact (Real.exp_pos _).le
  have hXint : Integrable X μ :=
    (memLp_of_bounded (μ := μ) (.of_forall hXbdd) hXm.aestronglyMeasurable 1).integrable le_rfl
  have hGint : Integrable G μ :=
    (memLp_of_bounded (μ := μ) (.of_forall hGbdd) hGm'.aestronglyMeasurable 1).integrable le_rfl
  have hKm : StronglyMeasurable[mΩ] ((fun ω ↦ k * G ω) * X) := (hGm'.const_mul k).mul hXm
  have hKbdd : ∀ ω, ((fun ω ↦ k * G ω) * X) ω ∈ Set.Icc 0 (Real.exp (1 / 2)) := by
    intro ω
    have h2 : 0 ≤ k * G ω := mul_nonneg hk0 (hGbdd ω).1
    have h1 : k * G ω ≤ Real.exp (1 / 2) := by nlinarith [(hGbdd ω).1, (hGbdd ω).2]
    refine ⟨mul_nonneg h2 (hXbdd ω).1, ?_⟩
    calc ((fun ω ↦ k * G ω) * X) ω = k * G ω * X ω := rfl
      _ ≤ k * G ω * 1 := by nlinarith [(hXbdd ω).2]
      _ ≤ Real.exp (1 / 2) := by linarith
  have hKint : Integrable ((fun ω ↦ k * G ω) * X) μ :=
    (memLp_of_bounded (μ := μ) (.of_forall hKbdd) hKm.aestronglyMeasurable 1).integrable le_rfl
  have hfun : (fun ω ↦ Real.exp (P ω / 2 - X ω)) = G - (fun ω ↦ k * G ω) * X := by
    funext ω
    rcases hX ω with h | h
    · simp [hG, hk, h, Real.exp_neg, Pi.sub_apply, Pi.mul_apply]
    · simp [hG, hk, h, Real.exp_sub, Real.exp_neg, Pi.sub_apply, Pi.mul_apply]
      ring
  have hcexp : μ[fun ω ↦ Real.exp (P ω / 2 - X ω) | m]
      =ᵐ[μ] fun ω ↦ G ω - k * G ω * P ω := by
    rw [hfun]
    refine (condExp_sub hGint hKint m).trans ?_
    have h1 : μ[G | m] = G := condExp_of_stronglyMeasurable hm hGm hGint
    have h2 : μ[(fun ω ↦ k * G ω) * X | m] =ᵐ[μ] (fun ω ↦ k * G ω) * μ[X | m] :=
      condExp_mul_of_stronglyMeasurable_left (hGm.const_mul k) hKint hXint
    filter_upwards [h2, hcond] with ω hω hω'
    simp only [Pi.sub_apply, h1, hω, Pi.mul_apply, hω']
  filter_upwards [hcexp] with ω hω
  rw [Pi.one_apply, hω]
  have hPk : 1 - k * P ω ≤ Real.exp (-(P ω / 2)) := by
    have he2 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith [Real.add_one_le_exp (1 : ℝ)]
    have h1 : 1 - k * P ω ≤ 1 - P ω / 2 := by
      simp only [hk]
      nlinarith [(hP ω).1, (hP ω).2]
    linarith [Real.add_one_le_exp (-(P ω / 2))]
  have hGpos : 0 < G ω := Real.exp_pos _
  calc G ω - k * G ω * P ω = G ω * (1 - k * P ω) := by ring
    _ ≤ G ω * Real.exp (-(P ω / 2)) := by nlinarith
    _ = 1 := by rw [hG]; rw [← Real.exp_add]; simp

/-- **The Bernoulli maximal inequality** (Lemma F.4 of Dann et al. (2017), Lemma 20 of
Essakine, Vernade (2026)): if `X i` has values in `{0, 1}` and is `ℱ (i + 1)`-measurable, and
`P i` is `ℱ i`-measurable with values in `[0, 1]` and `𝔼[X i | ℱ i] = P i`, then for every
`δ > 0`,
`ℙ(∃ n, ∑_{i < n} X i < (1/2) ∑_{i < n} P i - log (1/δ)) ≤ δ`. -/
theorem measure_exists_sum_lt_half_mul_sum_sub_le [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {X P : ℕ → Ω → ℝ} (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hXm : ∀ i, StronglyMeasurable[ℱ (i + 1)] (X i)) (hP : ∀ i ω, P i ω ∈ Set.Icc 0 1)
    (hPm : ∀ i, StronglyMeasurable[ℱ i] (P i)) (hcond : ∀ i, μ[X i | ℱ i] =ᵐ[μ] P i)
    {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | ∃ n, ∑ i ∈ Finset.range n, X i ω
        < 1 / 2 * ∑ i ∈ Finset.range n, P i ω - Real.log (1 / δ)} ≤ ENNReal.ofReal δ := by
  -- `exp (∑_{i < n} Z i)` with `Z i = P i / 2 - X i` is a supermartingale
  have hZm : ∀ i, StronglyMeasurable[ℱ (i + 1)] (fun ω ↦ P i ω / 2 - X i ω) := fun i ↦
    (((hPm i).mono (ℱ.mono i.le_succ)).div stronglyMeasurable_const).sub (hXm i)
  have hZint : ∀ i, Integrable (fun ω ↦ Real.exp (P i ω / 2 - X i ω)) μ := fun i ↦
    Integrable.of_bound ((hZm i).mono (ℱ.le (i + 1))).measurable.exp.aestronglyMeasurable
      (Real.exp (1 / 2)) (.of_forall fun ω ↦ by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
        rcases hX i ω with h | h <;> simp only [h] <;> linarith [(hP i ω).1, (hP i ω).2])
  have hsuper := LMLExplore.supermartingale_exp_sum_of_condExp_exp_le_one (μ := μ)
    (fun i ↦ (hZm i).measurable) hZint fun i ↦ condExp_exp_sub_le_one (ℱ.le i) (hX i)
      ((hXm i).mono (ℱ.le (i + 1))) (hP i) (hPm i) (hcond i)
  have hville := hsuper.measure_exists_le_le (fun n ↦ ae_of_all _ fun ω ↦ (Real.exp_pos _).le)
    (c := 1 / δ) (by positivity)
  simp only [Finset.range_zero, Finset.sum_empty, Real.exp_zero, integral_const, probReal_univ,
    smul_eq_mul, one_mul, one_div_one_div] at hville
  refine (measure_mono fun ω hω ↦ ?_).trans hville
  obtain ⟨n, hn⟩ := hω
  refine ⟨n, ?_⟩
  have hsum : ∑ i ∈ Finset.range n, (P i ω / 2 - X i ω)
      = 1 / 2 * ∑ i ∈ Finset.range n, P i ω - ∑ i ∈ Finset.range n, X i ω := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    exact congrArg₂ _ (Finset.sum_congr rfl fun i _ ↦ by ring) rfl
  calc (1 : ℝ) / δ = Real.exp (Real.log (1 / δ)) := (Real.exp_log (by positivity)).symm
    _ ≤ Real.exp (∑ i ∈ Finset.range n, (P i ω / 2 - X i ω)) :=
        Real.exp_le_exp.2 (by rw [hsum]; linarith)

end Bernoulli

end MeasureTheory
