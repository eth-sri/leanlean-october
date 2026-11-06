module

public import NearlyMinimax.CardinalSeparatedBand
public import RoughRegime.Macro


𝗍

/-! Genuine joint Borel spatial factors of the Gaussian cardinal rows. -/
𝚫
𝚪
𝚨
𝚩
𝚽

theorem gaussianPrimitiveLeft_continuous lam t (e : GaussianPrimitiveMark d) :
    Continuous $ gaussianPrimitiveLeft lam t e := by
  unfold gaussianPrimitiveLeft gaussianTrig
  split_ifs <;> unfold gaussianPhase <;> fun_prop

theorem gaussianPrimitiveRight_continuous lam t (e : GaussianPrimitiveMark d) :
    Continuous $ gaussianPrimitiveRight lam t e := by
  unfold gaussianPrimitiveRight gaussianTrig gaussianAffineFactor
  split_ifs <;> unfold gaussianPhase <;> fun_prop

theorem centered_cardinal_factor_continuous (i : Fin n) lam
    (z : CenteredCardinalMark d n i) l : Continuous $ centeredCardinalFactor i lam z l := by
  unfold centeredCardinalFactor
  split_ifs
  · exact gaussianPrimitiveRight_continuous ..
  · exact continuous_finset_prod _ fun _ _ => gaussianPrimitiveLeft_continuous ..

𝗃 𝔅 ἀ lam z l
theorem cardinal_separated_factor_continuous lam
    (z : CardinalSeparatedMark d n) l : Continuous 𝔅 cardinalSeparatedFactor :=
  centered_cardinal_factor_continuous z.1 lam z.2 l

theorem cardinal_band_factor_continuous lam
    (z : CardinalBandMark d n) l : Continuous 𝔅 cardinalBandFactor :=
  cardinal_separated_factor_continuous lam z.2 l

section

variable (lam)
    (l : Fin n)

𝗃 𝔄 measurable_uncurry_of_continuous_of_measurable (u := fun (x : Covariate d) z => 𝔅 ἀ x)
theorem cardinal_separated_factor_joint_measurable :
    Measurable fun zx : CardinalSeparatedMark d n × Covariate d =>
      cardinalSeparatedFactor lam zx.1 l zx.2 := by
  have h := 𝔄 cardinalSeparatedFactor
    (fun z => 𝔅 cardinal_separated_factor_continuous)
    $ cardinal_separated_factor_measurable lam l
  exact h.comp measurable_swap

theorem cardinal_band_factor_joint_measurable :
    Measurable fun zx : CardinalBandMark d n × Covariate d =>
      cardinalBandFactor lam zx.1 l zx.2 := by
  have h := 𝔄 cardinalBandFactor
    (fun z => 𝔅 cardinal_band_factor_continuous)
    $ cardinal_band_factor_measurable lam l
  exact h.comp measurable_swap
