/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ReflectionMassMeasurability
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Reflection moment transport with measurable input laws

The joint-law transport lemma only needs almost-everywhere measurability of the induced mass
moment. Reflection data provide this through their path measurability and the lateral measure's
almost-sure local finiteness, so the measurability premise can be discharged at the data boundary.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Joint input-law equality transports the reflection moment for reflection data without a
separate measurability premise on the mass functional. -/
theorem reflectionBarR_eq_of_joint_input_law_of_reflectionData
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (γ α : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (B' : Ω' → BrownianPath × BrownianPath) (Z' : Ω' → Measure ℝ)
    (hData : IsReflectionData P γ α B Z)
    (hData' : IsReflectionData P' γ α B' Z')
    (hLaw : P.map (fun ω => (B ω, Z ω)) = P'.map (fun ω => (B' ω, Z' ω))) :
    reflectionBarR P γ α B Z = reflectionBarR P' γ α B' Z' := by
  rcases hData with ⟨hB, hZ, _hInd⟩
  rcases hData' with ⟨hB', hZ', _hInd'⟩
  rcases hB with ⟨hB₁, hB₂, _hPathInd⟩
  rcases hB' with ⟨hB₁', hB₂', _hPathInd'⟩
  rcases hB₁ with ⟨hB₁m, _⟩
  rcases hB₂ with ⟨hB₂m, _⟩
  rcases hB₁' with ⟨hB₁'m, _⟩
  rcases hB₂' with ⟨hB₂'m, _⟩
  rcases hZ with ⟨_, _, _, hZm, hZlocal, _, _, _, _⟩
  rcases hZ' with ⟨_, _, _, hZ'm, _, _, _, _, _⟩
  let pair : Ω → (BrownianPath × BrownianPath) × Measure ℝ := fun ω => (B ω, Z ω)
  let pair' : Ω' → (BrownianPath × BrownianPath) × Measure ℝ := fun ω => (B' ω, Z' ω)
  have hpair : AEMeasurable pair P := by
    change AEMeasurable (fun ω => (B ω, Z ω)) P
    exact (show AEMeasurable B P by exact (hB₁m.prodMk hB₂m).congr (Eventually.of_forall fun ω => rfl)).prodMk hZm
  exact reflectionBarR_eq_of_joint_input_law P P' γ α B Z B' Z'
    hpair (by change AEMeasurable (fun ω => (B' ω, Z' ω)) P'; exact (show AEMeasurable B' P' by exact (hB₁'m.prodMk hB₂'m).congr (Eventually.of_forall fun ω => rfl)).prodMk hZ'm) (by simpa [pair, pair'] using hLaw) (by exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (aemeasurable_reflectionMassInput_map_of_locallyFinite P γ pair hpair (by simpa [pair] using (by filter_upwards [hZlocal] with ω hω; intro n; simpa [LocallyFiniteOnTranslationWindows, translationWindow] using hω (-(n : ℝ)) (n : ℝ)))))

end DOZZ.Proofs

end
