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

section
variable {d : ℕ} (lam t : ℝ) (e : GaussianPrimitiveMark d)

theorem gaussianPrimitiveLeft_continuous :
    Continuous (gaussianPrimitiveLeft lam t e) := by
  unfold gaussianPrimitiveLeft gaussianTrig
  split_ifs <;> unfold gaussianPhase <;> fun_prop

theorem gaussianPrimitiveRight_continuous :
    Continuous (gaussianPrimitiveRight lam t e) := by
  unfold gaussianPrimitiveRight gaussianTrig gaussianAffineFactor
  split_ifs <;> unfold gaussianPhase <;> fun_prop

end

section
variable {d n : ℕ}

theorem centered_cardinal_factor_continuous (i : Fin n) (lam : ℝ)
    (z : CenteredCardinalMark d n i) (l : Fin n) : Continuous (centeredCardinalFactor i lam z l) := by
  unfold centeredCardinalFactor
  split_ifs
  · exact gaussianPrimitiveRight_continuous _ _ _
  · exact continuous_finset_prod _ (fun _ _ => gaussianPrimitiveLeft_continuous _ _ _)

section
variable (lam : ℝ)

theorem cardinal_separated_factor_continuous
    (z : CardinalSeparatedMark d n) (l : Fin n) : Continuous (cardinalSeparatedFactor lam z l) :=
  centered_cardinal_factor_continuous z.1 lam z.2 l

theorem cardinal_separated_factor_joint_measurable (l : Fin n) :
    Measurable (fun zx : CardinalSeparatedMark d n × Covariate d =>
      cardinalSeparatedFactor lam zx.1 l zx.2) := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : Covariate d) (z : CardinalSeparatedMark d n) => cardinalSeparatedFactor lam z l x)
    (fun z => cardinal_separated_factor_continuous lam z l)
    (fun x => cardinal_separated_factor_measurable lam l x)
  exact h.comp measurable_swap

theorem cardinal_band_factor_joint_measurable (l : Fin n) :
    Measurable (fun zx : CardinalBandMark d n × Covariate d =>
      cardinalBandFactor lam zx.1 l zx.2) :=
  (cardinal_separated_factor_joint_measurable lam l).comp (measurable_fst.snd.prodMk measurable_snd)

end

end

end NearlyMinimax
