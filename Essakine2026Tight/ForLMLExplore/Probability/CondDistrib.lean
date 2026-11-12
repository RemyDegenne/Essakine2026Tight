/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.HasCondDistrib
public import TauCeti.Probability.Kernel.Composition.MeasureCompProd

/-!
# Restrictions and transport of conditional distributions

Facts about `HasCondDistrib`, complementing Mathlib's `Mathlib.Probability.HasCondDistrib`, LML's
`LeanMachineLearning.ForMathlib.Probability.HasCondDistrib` and LMLExplore's
`LMLExplore.Probability.HasCondDistrib`, used by the chain rule at a stopping time
(`Essakine2026Tight.ForLMLExplore.InformationTheory.KLStoppedPrefix`):

* `HasCondDistrib.restrict_preimage`: a conditional law given `X` is preserved by restricting the
  measure to an event determined by `X` (through Tau Ceti's `Measure.compProd_restrict_left`);
* `HasCondDistrib.of_comp_hasLaw`: a conditional law of `Z ∘ g` given `X ∘ g` under `P` is a
  conditional law of `Z` given `X` under the law of `g`, the converse of LML's
  `HasCondDistrib.comp_hasLaw`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

section restrict

variable {Ω α β : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {P : Measure Ω} [SFinite P] {X : Ω → α} {Y : Ω → β} {κ : Kernel α β}
  [IsSFiniteKernel κ]

/-- A conditional law given `X` is a conditional law given `X` under the restriction of `P` to an
event determined by `X`. -/
lemma HasCondDistrib.restrict_preimage (hX : Measurable X) (hY : Measurable Y)
    (h : HasCondDistrib Y X κ P) {s : Set α} (hs : MeasurableSet s) :
    HasCondDistrib Y X κ (P.restrict (X ⁻¹' s)) := by
  refine ⟨(hX.prodMk hY).aemeasurable, ?_⟩
  have h1 : (fun ω ↦ (X ω, Y ω)) ⁻¹' (s ×ˢ Set.univ) = X ⁻¹' s := by ext ω; simp
  calc (P.restrict (X ⁻¹' s)).map (fun ω ↦ (X ω, Y ω))
      = (P.map (fun ω ↦ (X ω, Y ω))).restrict (s ×ˢ Set.univ) := by
        rw [Measure.restrict_map (hX.prodMk hY) (hs.prod MeasurableSet.univ), h1]
    _ = (P.map X ⊗ₘ κ).restrict (s ×ˢ Set.univ) := by rw [h.map_eq]
    _ = (P.map X).restrict s ⊗ₘ κ := (Measure.compProd_restrict_left _ _ hs).symm
    _ = (P.restrict (X ⁻¹' s)).map X ⊗ₘ κ := by rw [Measure.restrict_map hX hs]

end restrict

section transport

variable {Ω Ω' 𝓧 𝓩 : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓩 : MeasurableSpace 𝓩} {P : Measure Ω} {P' : Measure Ω'}
  {g : Ω → Ω'}

/-- A conditional distribution of `Z ∘ g` given `X ∘ g` under `P` is a conditional distribution
of `Z` given `X` under the law `P'` of `g`. -/
lemma HasCondDistrib.of_comp_hasLaw {X : Ω' → 𝓧} {Z : Ω' → 𝓩} {κ : Kernel 𝓧 𝓩}
    (hX : Measurable X) (hZ : Measurable Z) (hg : HasLaw g P' P)
    (h : HasCondDistrib (Z ∘ g) (X ∘ g) κ P) :
    HasCondDistrib Z X κ P' := by
  refine ⟨(hX.prodMk hZ).aemeasurable, ?_⟩
  have h1 : P'.map (fun ω ↦ (X ω, Z ω)) = P.map ((fun ω ↦ (X ω, Z ω)) ∘ g) := by
    rw [← hg.map_eq,
      AEMeasurable.map_map_of_aemeasurable (hX.prodMk hZ).aemeasurable hg.aemeasurable]
  have h2 : P'.map X = P.map (X ∘ g) := by
    rw [← hg.map_eq, AEMeasurable.map_map_of_aemeasurable hX.aemeasurable hg.aemeasurable]
  rw [h1, h2]
  exact h.map_eq

end transport

end ProbabilityTheory
