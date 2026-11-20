module

public import NearlyMinimax.CardinalSeparatedBand


@[expose] public section

/-! Genuine joint Borel spatial factors of the Gaussian cardinal rows. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

variable {d n : ℕ} {i : Fin n} (lam t : ℝ) (e : GaussianPrimitiveMark d) (l : Fin n)

theorem centered_cardinal_factor_continuous
    (z : CenteredCardinalMark d i) (l : Fin n) : Continuous (centeredCardinalFactor lam z l) := by
  unfold centeredCardinalFactor
  split_ifs
  · exact by unfold gaussianPrimitiveRight gaussianTrig gaussianAffineFactor; split_ifs <;> unfold gaussianPhase <;> fun_prop
  · exact continuous_finset_prod _ (fun _ _ => by unfold gaussianPrimitiveLeft gaussianTrig; split_ifs <;> unfold gaussianPhase <;> fun_prop)

theorem cardinal_separated_factor_continuous
    (z : CardinalSeparatedMark d n) (l : Fin n) : Continuous (cardinalSeparatedFactor lam z l) :=
  centered_cardinal_factor_continuous ..

theorem cardinal_separated_factor_joint_measurable :
    Measurable (fun zx : CardinalSeparatedMark d n × Covariate d =>
      cardinalSeparatedFactor lam zx.1 l zx.2) := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun x (z : CardinalSeparatedMark d n) => cardinalSeparatedFactor lam z l x)
    (fun z => cardinal_separated_factor_continuous lam z l)
    (fun x => cardinal_separated_factor_measurable lam l x)
  exact h.comp measurable_swap

theorem cardinal_band_factor_joint_measurable :
    Measurable (fun zx : CardinalBandMark d n × Covariate d =>
      cardinalBandFactor lam zx.1 l zx.2) := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun x (z : CardinalBandMark d n) => cardinalBandFactor lam z l x)
    (fun z => cardinal_separated_factor_continuous ..)
    (fun x => ((cardinal_separated_factor_measurable lam l x).comp measurable_snd : Measurable fun z => cardinalBandFactor lam z l x))
  exact h.comp measurable_swap

end NearlyMinimax
