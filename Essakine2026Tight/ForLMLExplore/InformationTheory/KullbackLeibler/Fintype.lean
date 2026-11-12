/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import TauCeti.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# The Kullback–Leibler divergence on a finite type

For probability measures `μ ≪ ν` on a finite type with measurable singletons,
`(klDiv μ ν).toReal = ∑ x, μ{x} log (μ{x} / ν{x})` (`InformationTheory.toReal_klDiv_eq_sum`), and
`klDiv μ ν ≠ ∞` (`InformationTheory.klDiv_ne_top_of_finite`). The first is Tau Ceti's
`TauCeti.klDiv_eq_ofReal_sum_log_singleton` with `μ ≪ ν` in place of the full support of `ν`; the
proof evaluates the Radon–Nikodym derivative at the atoms with Tau Ceti's
`MeasureTheory.Measure.rnDeriv_eq_measure_singleton_div`.
-/

@[expose] public section

open MeasureTheory Real
open scoped ENNReal

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} [MeasurableSingletonClass α] {μ ν : Measure α}

/-- The Kullback–Leibler divergence between probability measures on a finite type is the finite
sum `∑ x, μ{x} log (μ{x} / ν{x})`. -/
lemma toReal_klDiv_eq_sum [Fintype α] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) :
    (klDiv μ ν).toReal = ∑ x, μ.real {x} * log (μ.real {x} / ν.real {x}) := by
  rw [toReal_klDiv_of_measure_eq hμν (by simp), integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [smul_eq_mul]
  by_cases hμx : μ {x} = 0
  · simp [measureReal_def, hμx]
  have hνx : ν {x} ≠ 0 := fun h ↦ hμx (hμν h)
  rw [llr, Measure.rnDeriv_eq_measure_singleton_div hνx (measure_ne_top ν _),
    ENNReal.toReal_div]
  rfl

/-- On a finite type, the Kullback–Leibler divergence between finite measures `μ ≪ ν` is finite. -/
lemma klDiv_ne_top_of_finite [Finite α] [IsFiniteMeasure μ] (hμν : μ ≪ ν) :
    klDiv μ ν ≠ ∞ :=
  klDiv_ne_top hμν Integrable.of_finite

end InformationTheory
