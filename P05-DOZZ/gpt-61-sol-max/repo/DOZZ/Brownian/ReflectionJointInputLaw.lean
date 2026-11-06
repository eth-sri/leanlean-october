/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.Brownian.ReflectionMassLawTransport
public import DOZZ.Brownian.ConditionedFDDUniqueness

/-!
# Reflection input-law reduction to the lateral marginal

The two-sided conditioned path law is fixed by the one-sided entrance FDDs and path independence.
Together with independence of the lateral measure, this reduces reflection-moment transport to
uniqueness of the lateral-measure marginal law.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Two independent conditioned path pairs with the same drift parameter have the same pair law.
The one-path marginals agree by FDD uniqueness; independence then determines the pair law. -/
theorem twoSidedConditionedPathPair_law_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (B : Ω → BrownianPath × BrownianPath)
    (B' : Ω' → BrownianPath × BrownianPath) (ν : ℝ)
    (hB : IsTwoSidedConditionedBrownianProcess P B ν)
    (hB' : IsTwoSidedConditionedBrownianProcess P' B' ν) :
    P.map B = P'.map B' := by
  rcases hB with ⟨hB₁, hB₂, hBInd⟩
  rcases hB' with ⟨hB₁', hB₂', hB'Ind⟩
  rcases hB₁ with ⟨hB₁m, hB₁law⟩
  rcases hB₂ with ⟨hB₂m, hB₂law⟩
  rcases hB₁' with ⟨hB₁'m, hB₁'law⟩
  rcases hB₂' with ⟨hB₂'m, hB₂'law⟩
  let  :=
    (Measure.isProbabilityMeasure_map_iff hB₁m).1 hB₁law.2.1
  let  :=
    (Measure.isProbabilityMeasure_map_iff hB₁'m).1 hB₁'law.2.1
  have hMarg₁  :=
    isNegativeConditionedBrownianLaw_eq ν hB₁law hB₁'law
  have hMarg₂  :=
    isNegativeConditionedBrownianLaw_eq ν hB₂law hB₂'law
  have hPair : P.map B =
      (P.map (fun ω => (B ω).1)).prod (P.map (fun ω => (B ω).2)) := by
    have h := (indepFun_iff_map_prod_eq_prod_map_map hB₁m hB₂m).1 hBInd
    exact h
  have hPair' : P'.map B' =
      (P'.map (fun ω => (B' ω).1)).prod (P'.map (fun ω => (B' ω).2)) := by
    have h := (indepFun_iff_map_prod_eq_prod_map_map hB₁'m hB₂'m).1 hB'Ind
    exact h
  simp_all

variable {Ω Ω' : Type*} [_inst1 : MeasurableSpace Ω] [_inst2 : MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω') (γ α : ℝ) (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (B' : Ω' → BrownianPath × BrownianPath) (Z' : Ω' → Measure ℝ) (hData : IsReflectionData P γ α B Z) (hData' : IsReflectionData P' γ α B' Z') (hZlaw : P.map Z = P'.map Z')

include Ω Ω' _inst1 _inst2 P P' γ α B Z B' Z' hData hData' hZlaw in
/-- For reflection data, equality of the lateral-measure marginals implies equality of the full
joint input laws. The conditioned path-pair marginal is fixed by the explicit entrance FDDs. -/
theorem reflection_jointInputLaw_eq_of_lateralLaw_eq
     :
    P.map (fun ω => (B ω, Z ω)) = P'.map (fun ω => (B' ω, Z' ω)) := by
  rcases hData with ⟨hB, hZ, hBInd⟩
  rcases hData' with ⟨hB', hZ', hB'Ind⟩
  let  := hZ.2.2.1
  let  := hZ'.2.2.1
  have hBlaw := twoSidedConditionedPathPair_law_eq P P' B B'
    (Q γ - α) hB hB'
  rcases hB with ⟨hB₁, hB₂, _⟩
  rcases hB' with ⟨hB₁', hB₂', _⟩
  rcases hB₁ with ⟨hB₁m, _⟩
  rcases hB₂ with ⟨hB₂m, _⟩
  rcases hB₁' with ⟨hB₁'m, _⟩
  rcases hB₂' with ⟨hB₂'m, _⟩
  have hBm : AEMeasurable B P := by
    have hm := hB₁m.prodMk hB₂m
    exact hm
  have hB'm : AEMeasurable B' P' := by
    have hm := hB₁'m.prodMk hB₂'m
    exact hm
  have hZm  := hZ.2.2.2.1
  have hZ'm  := hZ'.2.2.2.1
  have hJoint  :=
    (indepFun_iff_map_prod_eq_prod_map_map hBm hZm).1 hBInd
  have hJoint'  :=
    (indepFun_iff_map_prod_eq_prod_map_map hB'm hZ'm).1 hB'Ind
  simp_all

include Ω Ω' _inst1 _inst2 P P' γ α B Z B' Z' hData hData' hZlaw in
/-- Reflection moments agree as soon as the lateral marginal law is unique across the two
reflection-data realizations. -/
theorem reflectionBarR_eq_of_lateralLaw_eq
     :
    reflectionBarR P γ α B Z = reflectionBarR P' γ α B' Z' := reflectionBarR_eq_of_joint_input_law_of_reflectionData P P' γ α B Z B' Z'
    hData hData' (reflection_jointInputLaw_eq_of_lateralLaw_eq
      P P' γ α B Z B' Z' hData hData' hZlaw)

end DOZZ.Proofs

end
