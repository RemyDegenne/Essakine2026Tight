/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli

/-!
# Complements on the binary relative entropy and Pinsker's inequality

Complements to LMLExplore's binary relative entropy `LMLExplore.klBer` (the divergence of the
Bernoulli laws on `{1, 0} ⊆ ℝ`, its parameters clipped to `[0, 1]`) and its closed form
`LMLExplore.klBerReal` (`LMLExplore.InformationTheory.KullbackLeibler.Bernoulli`), and to Tau
Ceti's Pinsker inequality for an event, `TauCeti.two_mul_sq_measureReal_sub_le_klDiv`.

## Main statements

* `LMLExplore.klBerReal_zero_left`: `klBerReal 0 q = -log (1 - q)`.
* `LMLExplore.sub_log_two_le_klBerReal`, `LMLExplore.mul_log_sub_log_two_le_klBerReal`: for
  `q ∈ (0, 1)`, `(1 - p) log (1 / (1 - q)) - log 2 ≤ klBerReal p q` and
  `p log (1 / q) - log 2 ≤ klBerReal p q`.
* `LMLExplore.exp_neg_le_of_klBer_le`: a finite bound `klBer p q ≤ D` with `p > 0` bounds `q` away
  from `0`: `exp (-(D + log 2) / p) ≤ q`.
* `InformationTheory.klDiv_bernoulliMeasure`: for two distinct points `x ≠ y` of a measurable space
  with measurable singletons, `KL(Ber(x, y, p) ‖ Ber(x, y, q)) = klBer p q`; LMLExplore's
  `LMLExplore.klDiv_bernoulliMeasure` is the case `x = 1`, `y = 0` in `ℝ`, from which it follows
  by data processing in both directions. `InformationTheory.klDiv_bernoulliMeasure_eq_klBerReal`
  is its closed form for `q ∉ {0, 1}`.
* `InformationTheory.abs_sub_le_sqrt_klDiv`: Pinsker's inequality for an event, in real form,
  `|μ A - ν A| ≤ √(KL(μ ‖ ν) / 2)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real unitInterval
open scoped ENNReal

namespace LMLExplore

variable {p q : ℝ}

/-- `d(0, q) = -log (1 - q)`. -/
@[simp]
lemma klBerReal_zero_left (q : ℝ) : klBerReal 0 q = -log (1 - q) := by simp [klBerReal_def]

/-- **Lower bound on the binary relative entropy**: for `p ≥ 0` and `q ∈ (0, 1)`,
`(1 - p) log (1 / (1 - q)) - log 2 ≤ klBerReal p q`. -/
lemma sub_log_two_le_klBerReal (hp0 : 0 ≤ p) (hq0 : 0 < q) (hq1 : q < 1) :
    (1 - p) * log (1 / (1 - q)) - log 2 ≤ klBerReal p q := by
  rw [klBerReal_eq_neg_binEntropy_sub hq0.ne' hq1.ne, one_div, log_inv]
  have h1 : binEntropy p ≤ log 2 := binEntropy_le_log_two
  have h2 : p * log q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp0 (log_nonpos hq0.le hq1.le)
  linarith

/-- **Lower bound on the binary relative entropy**, the form used for a second argument close to
`0`: for `p ≤ 1` and `q ∈ (0, 1)`, `p log (1 / q) - log 2 ≤ klBerReal p q`. -/
lemma mul_log_sub_log_two_le_klBerReal (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    p * log (1 / q) - log 2 ≤ klBerReal p q := by
  have h := sub_log_two_le_klBerReal (p := 1 - p) (q := 1 - q) (by linarith) (by linarith)
    (by linarith)
  rwa [klBerReal_one_sub_one_sub, sub_sub_cancel, sub_sub_cancel] at h

/-- A finite bound `klBer p q ≤ D` with `p ∈ (0, 1]` bounds `q ∈ [0, 1]` away from `0`:
`exp (-(D + log 2) / p) ≤ q`. -/
lemma exp_neg_le_of_klBer_le {D : ℝ≥0∞} (hD : D ≠ ∞) (hp0 : 0 < p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (h : klBer p q ≤ D) :
    exp (-((D.toReal + log 2) / p)) ≤ q := by
  have hK : 0 ≤ D.toReal + log 2 := by
    have : (0 : ℝ) < log 2 := log_pos (by norm_num)
    positivity
  rcases eq_or_lt_of_le hq0 with rfl | hq0'
  · rw [(klBer_eq_top_iff ⟨hp0.le, hp1⟩ ⟨le_rfl, zero_le_one⟩).2 (Or.inl ⟨rfl, hp0.ne'⟩)] at h
    exact absurd (top_le_iff.1 h) hD
  rcases eq_or_lt_of_le hq1 with rfl | hq1'
  · refine exp_le_one_iff.2 ?_
    simp only [neg_nonpos]
    positivity
  have hq : q ∈ Set.Ioo 0 1 := ⟨hq0', hq1'⟩
  rw [klBer_eq_ofReal_klBerReal ⟨hp0.le, hp1⟩ (Set.Ioo_subset_Icc_self hq) (klBer_ne_top hq),
    ENNReal.ofReal_le_iff_le_toReal hD] at h
  have hlow := mul_log_sub_log_two_le_klBerReal hp1 hq0' hq1'
  have hlog : log (1 / q) ≤ (D.toReal + log 2) / p := by
    rw [le_div_iff₀ hp0]
    linarith
  rw [one_div, log_inv, neg_le] at hlog
  exact (le_log_iff_exp_le hq0').1 (by linarith)

end LMLExplore

namespace InformationTheory

section bernoulli

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {x y : X}

/-- The Kullback-Leibler divergence between two Bernoulli measures `Ber(x, y, p)` and
`Ber(x, y, q)` on two distinct points is the binary relative entropy `klBer p q`. -/
lemma klDiv_bernoulliMeasure (hxy : x ≠ y) (p q : I) :
    klDiv Ber(x, y, p) Ber(x, y, q) = LMLExplore.klBer p q := by
  classical
  -- `Ber(x, y, ·)` and `Ber(1, 0, ·)` are images of each other by measurable maps.
  have hf : Measurable fun z : X ↦ if z = x then (1 : ℝ) else 0 :=
    Measurable.ite (measurableSet_singleton x) measurable_const measurable_const
  have hg : Measurable fun r : ℝ ↦ if r = 1 then x else y :=
    Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const
  have hfB (r : I) : Ber(x, y, r).map (fun z ↦ if z = x then (1 : ℝ) else 0) =
      Ber((1 : ℝ), 0, r) := by
    rw [map_bernoulliMeasure' x y hf]
    simp [hxy.symm]
  have hgB (r : I) : Ber((1 : ℝ), 0, r).map (fun r ↦ if r = 1 then x else y) = Ber(x, y, r) := by
    rw [map_bernoulliMeasure' _ _ hg]
    simp
  refine le_antisymm ?_ ?_
  · calc klDiv Ber(x, y, p) Ber(x, y, q)
        = klDiv (Ber((1 : ℝ), 0, p).map fun r ↦ if r = 1 then x else y)
            (Ber((1 : ℝ), 0, q).map fun r ↦ if r = 1 then x else y) := by rw [hgB, hgB]
      _ ≤ klDiv Ber((1 : ℝ), 0, p) Ber((1 : ℝ), 0, q) := klDiv_map_le _ _ hg
      _ = LMLExplore.klBer p q := LMLExplore.klDiv_bernoulliMeasure p q
  · calc LMLExplore.klBer p q = klDiv Ber((1 : ℝ), 0, p) Ber((1 : ℝ), 0, q) :=
          (LMLExplore.klDiv_bernoulliMeasure p q).symm
      _ = klDiv (Ber(x, y, p).map fun z ↦ if z = x then (1 : ℝ) else 0)
            (Ber(x, y, q).map fun z ↦ if z = x then (1 : ℝ) else 0) := by rw [hfB, hfB]
      _ ≤ klDiv Ber(x, y, p) Ber(x, y, q) := klDiv_map_le _ _ hf

/-- The Kullback-Leibler divergence between two Bernoulli measures `Ber(x, y, p)` and
`Ber(x, y, q)` on two distinct points, for `q ∉ {0, 1}`, is the closed form `klBerReal p q`. -/
lemma klDiv_bernoulliMeasure_eq_klBerReal (hxy : x ≠ y) (p : I) {q : I} (hq : q ≠ 0)
    (hq1 : q ≠ 1) :
    klDiv Ber(x, y, p) Ber(x, y, q) = ENNReal.ofReal (LMLExplore.klBerReal p q) := by
  have hq' : (q : ℝ) ∈ Set.Ioo 0 1 :=
    ⟨coe_pos.2 (unitInterval.pos_iff_ne_zero.2 hq),
      coe_lt_one.2 (unitInterval.lt_one_iff_ne_one.2 hq1)⟩
  rw [klDiv_bernoulliMeasure hxy,
    LMLExplore.klBer_eq_ofReal_klBerReal p.2 q.2 (LMLExplore.klBer_ne_top hq')]

end bernoulli

/-- **Pinsker's inequality** for a single event, real form: `|μ A - ν A| ≤ √(KL(μ ‖ ν) / 2)`.
This is Tau Ceti's `TauCeti.two_mul_sq_measureReal_sub_le_klDiv` when the divergence is
finite. -/
lemma abs_sub_le_sqrt_klDiv {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {A : Set Ω} (hA : MeasurableSet A)
    (h : klDiv μ ν ≠ ∞) :
    |μ.real A - ν.real A| ≤ √((klDiv μ ν).toReal / 2) := by
  have := TauCeti.two_mul_sq_measureReal_sub_le_klDiv (μ := μ) (ν := ν) hA
  rw [ENNReal.ofReal_le_iff_le_toReal h] at this
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

end InformationTheory
