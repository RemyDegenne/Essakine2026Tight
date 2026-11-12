/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A Cauchy–Schwarz inequality for sums of integrals

For real functions `W i`, `V i ≥ 0`, `U i ≥ 0` (`i ∈ s`, a finite set) with `W i ^ 2 * V i` and
`U i` integrable,
`∫ ∑ i ∈ s, W i √(V i U i) ≤ √(∫ ∑ i ∈ s, W i ^ 2 V i) √(∫ ∑ i ∈ s, U i)`
(`MeasureTheory.integral_sum_mul_sqrt_mul_le`). The proof bounds the integrand pointwise by
`√(∑ i ∈ s, W i ^ 2 V i) √(∑ i ∈ s, U i)` (Mathlib's finite Cauchy–Schwarz inequality
`Real.sum_mul_le_sqrt_mul_sqrt`) and integrates with Hölder's inequality for the exponents `2, 2`
(Mathlib's `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`).
-/

@[expose] public section

open MeasureTheory Finset

namespace MeasureTheory

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Cauchy–Schwarz inequality for a finite sum of integrals**:
`∫ ∑ i ∈ s, W i √(V i U i) ≤ √(∫ ∑ i ∈ s, W i ^ 2 V i) √(∫ ∑ i ∈ s, U i)` for `V i, U i ≥ 0`. -/
lemma integral_sum_mul_sqrt_mul_le (s : Finset ι) {W V U : ι → Ω → ℝ}
    (hV0 : ∀ i ∈ s, 0 ≤ᵐ[μ] V i) (hU0 : ∀ i ∈ s, 0 ≤ᵐ[μ] U i)
    (hWV : ∀ i ∈ s, Integrable (fun ω ↦ W i ω ^ 2 * V i ω) μ) (hUi : ∀ i ∈ s, Integrable (U i) μ) :
    ∫ ω, ∑ i ∈ s, W i ω * √(V i ω * U i ω) ∂μ
      ≤ √(∫ ω, ∑ i ∈ s, W i ω ^ 2 * V i ω ∂μ) * √(∫ ω, ∑ i ∈ s, U i ω ∂μ) := by
  set F : Ω → ℝ := fun ω ↦ ∑ i ∈ s, W i ω ^ 2 * V i ω with hF
  set G : Ω → ℝ := fun ω ↦ ∑ i ∈ s, U i ω with hG
  have hVU : ∀ᵐ ω ∂μ, ∀ i ∈ s, 0 ≤ V i ω ∧ 0 ≤ U i ω := by
    rw [Filter.eventually_all_finset]
    exact fun i hi ↦ (hV0 i hi).and (hU0 i hi)
  have hF0 : 0 ≤ᵐ[μ] F :=
    hVU.mono fun ω h ↦ sum_nonneg fun i hi ↦ mul_nonneg (sq_nonneg _) (h i hi).1
  have hG0 : 0 ≤ᵐ[μ] G := hVU.mono fun ω h ↦ sum_nonneg fun i hi ↦ (h i hi).2
  -- `√F` and `√G` are square integrable
  have hL2 : ∀ H : Ω → ℝ, 0 ≤ᵐ[μ] H → Integrable H μ →
      MemLp (fun ω ↦ √(H ω)) 2 μ := fun H hH0 hHi ↦ by
    rw [memLp_two_iff_integrable_sq
      hHi.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable]
    exact hHi.congr (hH0.mono fun ω h ↦ (Real.sq_sqrt h).symm)
  have hsF := hL2 F hF0 (integrable_finsetSum _ hWV)
  have hsG := hL2 G hG0 (integrable_finsetSum _ hUi)
  -- the pointwise Cauchy–Schwarz inequality `∑ W √(V U) ≤ √F √G`
  have hpt : ∀ᵐ ω ∂μ, ∑ i ∈ s, W i ω * √(V i ω * U i ω) ≤ √(F ω) * √(G ω) := by
    filter_upwards [hVU] with ω h
    calc ∑ i ∈ s, W i ω * √(V i ω * U i ω) = ∑ i ∈ s, W i ω * √(V i ω) * √(U i ω) :=
          sum_congr rfl fun i hi ↦ by rw [Real.sqrt_mul (h i hi).1, mul_assoc]
      _ ≤ √(∑ i ∈ s, (W i ω * √(V i ω)) ^ 2) * √(∑ i ∈ s, √(U i ω) ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = √(F ω) * √(G ω) := by
          congr 2 <;> refine sum_congr rfl fun i hi ↦ ?_
          · rw [mul_pow, Real.sq_sqrt (h i hi).1]
          · rw [Real.sq_sqrt (h i hi).2]
  -- Hölder's inequality for `√F` and `√G`
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ fun ω ↦ Real.sqrt_nonneg (F ω)) (ae_of_all _ fun ω ↦ Real.sqrt_nonneg (G ω))
    (by rwa [ENNReal.ofReal_ofNat]) (by rwa [ENNReal.ofReal_ofNat])
  have hsq : ∀ H : Ω → ℝ, 0 ≤ᵐ[μ] H →
      (∫ ω, √(H ω) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) = √(∫ ω, H ω ∂μ) := fun H hH0 ↦ by
    rw [← Real.sqrt_eq_rpow]
    congr 1
    refine integral_congr_ae (hH0.mono fun ω h ↦ ?_)
    simp only [Real.rpow_two, Real.sq_sqrt h]
  rw [hsq F hF0, hsq G hG0] at hH
  by_cases hint : Integrable (fun ω ↦ ∑ i ∈ s, W i ω * √(V i ω * U i ω)) μ
  · exact (integral_mono_ae hint (hsF.integrable_mul hsG) hpt).trans hH
  · rw [integral_undef hint]
    positivity

end MeasureTheory
