/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Sigma

/-!
# Measurable singletons in sigma types

A sigma type `Σ i, α i` whose fibers have measurable singletons has measurable singletons: the
singleton `{⟨i, a⟩}` is the image of `{a}` under the measurable embedding `Sigma.mk i` (LML's
`measurableEmbedding_sigmaMk`).
-/

@[expose] public section

open MeasureTheory

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  [∀ i, MeasurableSingletonClass (α i)]

/-- In a sigma type whose fibers have measurable singletons, singletons are measurable. -/
lemma measurableSet_singleton_sigma (x : Σ i, α i) : MeasurableSet {x} := by
  obtain ⟨i, a⟩ := x
  simpa using (measurableEmbedding_sigmaMk i).measurableSet_image.2 (measurableSet_singleton a)

/-- A sigma type whose fibers have measurable singletons has measurable singletons. -/
instance Sigma.instMeasurableSingletonClass : MeasurableSingletonClass (Σ i, α i) :=
  ⟨measurableSet_singleton_sigma⟩
