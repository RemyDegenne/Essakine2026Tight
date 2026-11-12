/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Moments.Bernstein
public import TauCeti.InformationTheory.KullbackLeibler.Variational
public import Essakine2026Tight.ForLMLExplore.Analysis.Real.Sqrt
public import Essakine2026Tight.ForLMLExplore.Analysis.SpecialFunctions.PoissonCramer
public import Essakine2026Tight.ForLMLExplore.Probability.Moments.VarianceTransport

/-!
# The KL–Bernstein inequality

A Kullback–Leibler constraint `KL(μ ‖ ν) ≤ a` bounds the difference of the means of a bounded
function by a Bernstein-type quantity. The two ingredients are upstream: the
Gibbs/Donsker–Varadhan variational inequality `∫ f ∂μ - log (∫ e^f ∂ν) ≤ KL(μ ‖ ν)` is Tau Ceti's
`TauCeti.ofReal_integral_sub_log_integral_exp_le_klDiv`, and Bennett's bound on the moment
generating function is LMLExplore's `MeasureTheory.MemLp.mgf_le_exp_mul_exp_sub_one_sub_of_ae_le`.

* `ProbabilityTheory.log_integral_exp_mul_sub_le`: the Bernstein bound on the log-moment
  generating function of a centered function with values in `[0, b]`;
* `InformationTheory.integral_sub_log_integral_exp_le_of_klDiv_le`: the variational inequality
  under a KL constraint `KL(μ ‖ ν) ≤ a`;
* `InformationTheory.abs_integral_sub_integral_le_of_klDiv_le`: the KL–Bernstein inequality
  (Lemma 22 of Essakine, Vernade (2026), Lemma 3 of Talebi, Maillard (2018)),
  `|∫ f ∂μ - ∫ f ∂ν| ≤ √(2 Var_ν(f) a) + (2/3) b a`;
* `InformationTheory.variance_le_two_mul_variance_add_of_klDiv_le` and its primed version: the
  variance transport under a KL constraint (Lemma 25 of Essakine, Vernade (2026), Lemma 11 of
  Ménard et al. (2021)), `Var_ν(f) ≤ 2 Var_μ(f) + 4 b² a` and `Var_μ(f) ≤ 2 Var_ν(f) + 4 b² a`.
-/

@[expose] public section

open MeasureTheory Real

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {ν : Measure α} {f : α → ℝ} {b lam : ℝ}

/-- Bernstein bound on the log-moment generating function of a centered bounded function:
`log (∫ e^{lam (f - ν[f])} ∂ν) ≤ Var_ν(f) φ_b(lam) / b²` for `lam ≥ 0` and `f ∈ [0, b]`. -/
lemma log_integral_exp_mul_sub_le [IsProbabilityMeasure ν] (hb : 0 < b) (hlam : 0 ≤ lam)
    (hf : ∀ᵐ x ∂ν, f x ∈ Set.Icc 0 b) (hfm : AEStronglyMeasurable f ν) :
    log (∫ x, exp (lam * (f x - ν[f])) ∂ν) ≤ variance f ν * expSubOneSub (lam * b) / b ^ 2 := by
  have hmean : ν[f] ∈ Set.Icc 0 b := integral_mem_Icc_of_ae_mem_Icc hf hfm
  have hY : ∀ᵐ x ∂ν, f x - ν[f] ∈ Set.Icc (-b) b := hf.mono fun x hx ↦
    ⟨by linarith [hx.1, hmean.2], by linarith [hx.2, hmean.1]⟩
  have hYm : AEStronglyMeasurable (fun x ↦ f x - ν[f]) ν := hfm.sub aestronglyMeasurable_const
  have hYb : ∀ᵐ x ∂ν, f x - ν[f] ≤ b := hY.mono fun x hx ↦ hx.2
  -- Bennett's bound on the moment generating function of the centered function
  have hmgf := (memLp_of_bounded hY hYm 2).mgf_le_exp_mul_exp_sub_one_sub_of_ae_le
    (by rw [integral_sub (Integrable.of_mem_Icc 0 b hfm.aemeasurable hf) (integrable_const _)]
        simp) hb hYb hlam
  rw [← variance_eq_integral hfm.aemeasurable] at hmgf
  refine (log_le_log (mgf_pos (integrable_exp_mul_of_le lam b hlam hYm.aemeasurable hYb))
    hmgf).trans_eq ?_
  rw [log_exp, expSubOneSub]
  ring

end ProbabilityTheory

namespace InformationTheory

open ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {f : α → ℝ} {a b : ℝ}

/-- The Gibbs variational inequality under a KL constraint: if `KL(μ ‖ ν) ≤ a`, then
`∫ f ∂μ - log (∫ e^f ∂ν) ≤ a`. -/
lemma integral_sub_log_integral_exp_le_of_klDiv_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (ha : 0 ≤ a) (hfμ : Integrable f μ)
    (hfν : Integrable (fun x ↦ exp (f x)) ν) (h : klDiv μ ν ≤ ENNReal.ofReal a) :
    ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν) ≤ a := by
  have h' := (TauCeti.ofReal_integral_sub_log_integral_exp_le_klDiv hfμ hfν).trans h
  rwa [ENNReal.ofReal_le_ofReal_iff ha] at h'

section KLBernstein

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The one-sided KL–Bernstein inequality: if `KL(μ ‖ ν) ≤ a` and `f` has values in `[0, b]`,
then `∫ f ∂μ - ∫ f ∂ν ≤ √(2 Var_ν(f) a) + (2/3) b a`. -/
lemma integral_sub_integral_le_of_klDiv_le (hb : 0 < b) (ha : 0 ≤ a)
    (hf : ∀ᵐ x ∂ν, f x ∈ Set.Icc 0 b) (hfm : AEStronglyMeasurable f ν)
    (h : klDiv μ ν ≤ ENNReal.ofReal a) :
    ∫ x, f x ∂μ - ∫ x, f x ∂ν ≤ √(2 * variance f ν * a) + 2 / 3 * b * a := by
  have htop : klDiv μ ν ≠ ∞ := fun htop ↦ by simp [htop] at h
  obtain ⟨hμν, -⟩ := klDiv_ne_top_iff.1 htop
  have hfmμ : AEStronglyMeasurable f μ := AEStronglyMeasurable.mono_ac hμν hfm
  have hfμ : ∀ᵐ x ∂μ, f x ∈ Set.Icc 0 b := hμν.ae_le hf
  have hintμ : Integrable f μ := .of_mem_Icc 0 b hfmμ.aemeasurable hfμ
  have hintν : Integrable f ν := .of_mem_Icc 0 b hfm.aemeasurable hf
  have hvar : 0 ≤ variance f ν := variance_nonneg _ _
  set d := ∫ x, f x ∂μ - ∫ x, f x ∂ν with hd
  -- the Gibbs inequality at every nonnegative `lam`
  have key : ∀ lam : ℝ, 0 ≤ lam →
      lam * d - variance f ν * expSubOneSub (lam * b) / b ^ 2 ≤ a := by
    intro lam hlam
    have hg : Integrable (fun x ↦ lam * (f x - ν[f])) μ :=
      (hintμ.sub (integrable_const _)).const_mul lam
    have habs : ∀ᵐ x ∂ν, |f x - ν[f]| ≤ b := by
      have hmean : ν[f] ∈ Set.Icc 0 b := integral_mem_Icc_of_ae_mem_Icc hf hfm
      filter_upwards [hf] with x hx
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hmean.1, hmean.2]
    have hexpb : ∀ᵐ x ∂ν, exp (lam * (f x - ν[f])) ∈ Set.Icc 0 (exp (lam * b)) := by
      filter_upwards [habs] with x hx
      exact ⟨(exp_pos _).le, exp_le_exp.2 (by nlinarith [abs_le.1 hx])⟩
    have hiexp : Integrable (fun x ↦ exp (lam * (f x - ν[f]))) ν :=
      .of_mem_Icc _ _ (by fun_prop) hexpb
    have hgibbs := integral_sub_log_integral_exp_le_of_klDiv_le ha hg hiexp h
    have hmgf := log_integral_exp_mul_sub_le (ν := ν) (f := f) hb hlam hf hfm
    have hint_eq : ∫ x, lam * (f x - ν[f]) ∂μ = lam * d := by
      rw [integral_const_mul, integral_sub hintμ (integrable_const _)]
      simp [hd]
    rw [hint_eq] at hgibbs
    linarith
  rcases le_or_gt d 0 with hd0 | hd0
  · have : 0 ≤ √(2 * variance f ν * a) + 2 / 3 * b * a := by positivity
    linarith
  rcases eq_or_lt_of_le hvar with hv0 | hv0
  · exfalso
    have := key ((a + 1) / d) (by positivity)
    rw [← hv0] at this
    rw [div_mul_cancel₀ _ hd0.ne'] at this
    simp at this
    linarith
  · set c := variance f ν / b ^ 2 with hc
    set s := d / b with hs
    have hcpos : 0 < c := by positivity
    have hs0 : 0 ≤ s := by positivity
    have hlam : 0 ≤ log (1 + s / c) / b := by
      apply div_nonneg _ hb.le
      exact log_nonneg (by nlinarith [div_nonneg hs0 hcpos.le])
    have hkey := key (log (1 + s / c) / b) hlam
    have he1 : log (1 + s / c) / b * b = log (1 + s / c) := by field_simp
    have he2 : log (1 + s / c) / b * d = log (1 + s / c) * s := by rw [hs]; ring
    rw [he1, he2] at hkey
    have he3 : variance f ν * expSubOneSub (log (1 + s / c)) / b ^ 2
        = c * expSubOneSub (log (1 + s / c)) := by rw [hc]; ring
    rw [he3, mul_poissonCramer_eq hcpos hs0] at hkey
    have hsle := le_sqrt_add_of_mul_poissonCramer_le hcpos hs0 ha hkey
    have hbs : d = b * s := by rw [hs]; field_simp
    have hsqrt : b * √(2 * c * a) = √(2 * variance f ν * a) := by
      have hbc : (2 : ℝ) * variance f ν * a = b ^ 2 * (2 * c * a) := by
        rw [hc]; field_simp
      rw [hbc, Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb.le]
    calc d = b * s := hbs
      _ ≤ b * (√(2 * c * a) + 2 / 3 * a) := by
          exact mul_le_mul_of_nonneg_left hsle hb.le
      _ = √(2 * variance f ν * a) + 2 / 3 * b * a := by rw [mul_add, hsqrt]; ring

/-- **The KL–Bernstein inequality** (Lemma 22 of Essakine, Vernade (2026)): if `KL(μ ‖ ν) ≤ a`
and `f` has values in `[0, b]`, then
`|∫ f ∂μ - ∫ f ∂ν| ≤ √(2 Var_ν(f) a) + (2/3) b a`. -/
lemma abs_integral_sub_integral_le_of_klDiv_le (hb : 0 < b) (ha : 0 ≤ a)
    (hf : ∀ᵐ x ∂ν, f x ∈ Set.Icc 0 b) (hfm : AEStronglyMeasurable f ν)
    (h : klDiv μ ν ≤ ENNReal.ofReal a) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ √(2 * variance f ν * a) + 2 / 3 * b * a := by
  have htop : klDiv μ ν ≠ ∞ := fun htop ↦ by simp [htop] at h
  obtain ⟨hμν, -⟩ := klDiv_ne_top_iff.1 htop
  have hfmμ : AEStronglyMeasurable f μ := AEStronglyMeasurable.mono_ac hμν hfm
  have hfμ : ∀ᵐ x ∂μ, f x ∈ Set.Icc 0 b := hμν.ae_le hf
  have hintμ : Integrable f μ := .of_mem_Icc 0 b hfmμ.aemeasurable hfμ
  have hintν : Integrable f ν := .of_mem_Icc 0 b hfm.aemeasurable hf
  have h1 := integral_sub_integral_le_of_klDiv_le (μ := μ) (ν := ν) hb ha hf hfm h
  have hf' : ∀ᵐ x ∂ν, b - f x ∈ Set.Icc 0 b := by
    filter_upwards [hf] with x hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h2 := integral_sub_integral_le_of_klDiv_le (μ := μ) (ν := ν) (f := fun x ↦ b - f x)
    hb ha hf' (by fun_prop) h
  rw [variance_const_sub hfm b] at h2
  rw [integral_sub (integrable_const b) hintμ, integral_sub (integrable_const b) hintν] at h2
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h2
  rw [abs_sub_le_iff]
  constructor
  · exact h1
  · linarith

/-- Variance transport under a KL constraint (Lemma 25 of Essakine, Vernade (2026)):
`Var_ν(f) ≤ 2 Var_μ(f) + 4 b² a` when `KL(μ ‖ ν) ≤ a` and `f` has values in `[0, b]`. -/
lemma variance_le_two_mul_variance_add_of_klDiv_le (hb : 0 < b) (ha : 0 ≤ a)
    (hf : ∀ᵐ x ∂ν, f x ∈ Set.Icc 0 b) (hfm : AEStronglyMeasurable f ν)
    (h : klDiv μ ν ≤ ENNReal.ofReal a) :
    variance f ν ≤ 2 * variance f μ + 4 * b ^ 2 * a := by
  have htop : klDiv μ ν ≠ ∞ := fun htop ↦ by simp [htop] at h
  obtain ⟨hμν, -⟩ := klDiv_ne_top_iff.1 htop
  have hfmμ : AEStronglyMeasurable f μ := AEStronglyMeasurable.mono_ac hμν hfm
  have hfμ : ∀ᵐ x ∂μ, f x ∈ Set.Icc 0 b := hμν.ae_le hf
  have hmean : μ[f] ∈ Set.Icc 0 b := integral_mem_Icc_of_ae_mem_Icc hfμ hfmμ
  set g : α → ℝ := fun x ↦ (f x - μ[f]) ^ 2 with hg
  have hgν : ∀ᵐ x ∂ν, g x ∈ Set.Icc 0 (b ^ 2) := by
    filter_upwards [hf] with x hx
    refine ⟨sq_nonneg _, ?_⟩
    have h1 : -b ≤ f x - μ[f] := by linarith [hx.1, hmean.2]
    have h2 : f x - μ[f] ≤ b := by linarith [hx.2, hmean.1]
    nlinarith
  have hgm : AEStronglyMeasurable g ν := by fun_prop
  have hbern' := abs_integral_sub_integral_le_of_klDiv_le (μ := μ) (ν := ν) (f := g)
    (b := b ^ 2) (by positivity) ha hgν hgm h
  have hbern : ∫ x, g x ∂ν - ∫ x, g x ∂μ ≤ √(2 * variance g ν * a) + 2 / 3 * b ^ 2 * a := by
    have := (abs_le.1 hbern').1
    linarith
  have hvg : variance g ν ≤ b ^ 2 * ∫ x, g x ∂ν := variance_le_mul_integral hgν hgm
  have hgint_μ : ∫ x, g x ∂μ = variance f μ :=
    (variance_eq_integral hfmμ.aemeasurable).symm
  have hvν : variance f ν ≤ ∫ x, g x ∂ν :=
    variance_le_integral_sub_sq hfm _
  have hg0 : 0 ≤ ∫ x, g x ∂ν := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hgν] with x hx using hx.1
  have hsq : √(2 * variance g ν * a) ≤ (∫ x, g x ∂ν) / 2 + b ^ 2 * a := by
    have h1 : 2 * variance g ν * a ≤ (∫ x, g x ∂ν) * (2 * a * b ^ 2) := by nlinarith [ha, hvg]
    calc √(2 * variance g ν * a) ≤ √((∫ x, g x ∂ν) * (2 * a * b ^ 2)) := Real.sqrt_le_sqrt h1
      _ ≤ 1 * (∫ x, g x ∂ν) / 2 + (2 * a * b ^ 2) / (2 * 1) :=
          Real.sqrt_mul_le_half_add_half hg0 (by positivity) one_pos
      _ = (∫ x, g x ∂ν) / 2 + b ^ 2 * a := by ring
  rw [hgint_μ] at hbern
  have hba : 0 ≤ b ^ 2 * a := by positivity
  linarith

/-- Variance transport under a KL constraint, the other direction (Lemma 25 of Essakine,
Vernade (2026)): `Var_μ(f) ≤ 2 Var_ν(f) + 4 b² a` when `KL(μ ‖ ν) ≤ a` and `f ∈ [0, b]`. -/
lemma variance_le_two_mul_variance_add_of_klDiv_le' (hb : 0 < b) (ha : 0 ≤ a)
    (hf : ∀ᵐ x ∂ν, f x ∈ Set.Icc 0 b) (hfm : AEStronglyMeasurable f ν)
    (h : klDiv μ ν ≤ ENNReal.ofReal a) :
    variance f μ ≤ 2 * variance f ν + 4 * b ^ 2 * a := by
  have htop : klDiv μ ν ≠ ∞ := fun htop ↦ by simp [htop] at h
  obtain ⟨hμν, -⟩ := klDiv_ne_top_iff.1 htop
  have hfmμ : AEStronglyMeasurable f μ := AEStronglyMeasurable.mono_ac hμν hfm
  have hmean : ν[f] ∈ Set.Icc 0 b := integral_mem_Icc_of_ae_mem_Icc hf hfm
  set g : α → ℝ := fun x ↦ (f x - ν[f]) ^ 2 with hg
  have hgν : ∀ᵐ x ∂ν, g x ∈ Set.Icc 0 (b ^ 2) := by
    filter_upwards [hf] with x hx
    refine ⟨sq_nonneg _, ?_⟩
    have h1 : -b ≤ f x - ν[f] := by linarith [hx.1, hmean.2]
    have h2 : f x - ν[f] ≤ b := by linarith [hx.2, hmean.1]
    nlinarith
  have hgm : AEStronglyMeasurable g ν := by fun_prop
  have hbern := integral_sub_integral_le_of_klDiv_le (μ := μ) (ν := ν) (f := g)
    (b := b ^ 2) (by positivity) ha hgν hgm h
  have hgint_ν : ∫ x, g x ∂ν = variance f ν := (variance_eq_integral hfm.aemeasurable).symm
  have hvg : variance g ν ≤ b ^ 2 * ∫ x, g x ∂ν := variance_le_mul_integral hgν hgm
  have hvμ : variance f μ ≤ ∫ x, g x ∂μ := variance_le_integral_sub_sq hfmμ _
  have hvar : 0 ≤ variance f ν := variance_nonneg _ _
  have hsq : √(2 * variance g ν * a) ≤ variance f ν / 2 + b ^ 2 * a := by
    have h1 : 2 * variance g ν * a ≤ variance f ν * (2 * a * b ^ 2) := by
      rw [hgint_ν] at hvg; nlinarith [ha, hvg]
    calc √(2 * variance g ν * a) ≤ √(variance f ν * (2 * a * b ^ 2)) := Real.sqrt_le_sqrt h1
      _ ≤ 1 * variance f ν / 2 + (2 * a * b ^ 2) / (2 * 1) :=
          Real.sqrt_mul_le_half_add_half hvar (by positivity) one_pos
      _ = variance f ν / 2 + b ^ 2 * a := by ring
  rw [hgint_ν] at hbern
  have hba : 0 ≤ b ^ 2 * a := by positivity
  linarith

end KLBernstein

end InformationTheory
