/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.OriginPolarMass
public import DOZZ.Correlations.Tails.TranslatedLateralLaw
public import DOZZ.Correlations.Tails.WilliamsPolarMassLaw

/-! The canonical translated singular mass has the exponential-maximum last-cut law. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The genuine translated equator chaos has the exact `exp(γ M) J_M` law. The reference
functional is measurable on all inputs and equals the literal last-cut mass
`DOZZ.twoSidedReflectionCutMass` on locally finite lateral measures. The exponential level,
conditioned copies and lateral law are independent. -/
theorem translated_canonical_williams_mass_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    Xc (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    z (γ α : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Q γ)
    (N : Ω → Measure ℂ) (hN : IsGMCOf P (translatedField X Xc z) γ N)
    (Qν : Measure BrownianPath) (hQν : IsNegativeConditionedBrownianLaw (Q γ - α) Qν) :
    let Uc := fun ω x r => Xc ω (z+x) r - Xc ω z 0
    P.map (localSingularMass N (fun _ => 1) 0 γ α) =
      (((((brownianMaximumReferenceLaw (Q γ - α)).prod Qν).map
        (fun v => (v.1, negativeConditionedLastExitSegment v.1 v.2))).prod Qν).prod
          (P.map (fun ω => lateralProjectedGMC γ (originRadialPath Uc ω) (N ω)))).map (williamsMassFunctional γ) := by
  let Uc := fun ω x r => Xc ω (z+x) r - Xc ω z 0
  let A := originRadialPath Uc
  let D := fun ω => radialPositiveHalf (A ω)
  let Z := fun ω => lateralProjectedGMC γ (A ω) (N ω)
  have hU := translated_field_isEquatorGFF P X Xc hX hc z
  have hcU := translated_field_circleAverage P X Xc hX hc z
  have hcontU := translated_circle_continuous P Xc hcont z
  have hA := originRadialPath_aemeasurable P _ Uc hcU hcontU
  have hmass : (localSingularMass N (fun _ => 1) 0 γ α) =ᵐ[P]
      (fun ω => ∫⁻ t, (if 0 < t then ENNReal.ofReal
        (Real.exp (γ * (D ω (Real.toNNReal t) - (Q γ - α) * t))) else 0) ∂Z ω) := by
    filter_upwards [translated_canonical_singular_mass_polar P X Xc hX hc
      z γ α hγ hγ2 N hN A] with ω hω
    rw [hω]
    apply lintegral_congr
    intro t
    by_cases ht : 0 < t
    · rw [ite_eq_left ht, ite_eq_left ht]
      rw [(show D ω (Real.toNNReal t) = A ω t by change A ω ((Real.toNNReal t : ℝ≥0) : ℝ) = A ω t; rw [Real.coe_toNNReal t ht.le])]
    · rw [ite_eq_right ht, ite_eq_right ht]
  rw [Measure.map_congr hmass]
  exact williams_polar_mass_law P D (continuous_radialPositiveHalf.measurable.comp_aemeasurable hA) (radialPositiveHalf_map_isBrownian P A hA ((originRadialPath_isBrownian P _ Uc hU hcU hcontU).1)) γ Z (translated_lateral_isLateralGMCOf P X Xc hX hc hm hcont z γ hγ hγ2 N hN) ((lateralProjectedGMC_indep P _ Uc hU hcU (translated_circle_jointMeasurable Xc hm z) hcontU γ hγ hγ2 N hN).comp continuous_radialPositiveHalf.measurable measurable_id) (Q γ - α)
    (sub_pos.mpr hα) Qν hQν


end DOZZ.Proofs
