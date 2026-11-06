module

public import NearlyMinimax.CardinalBandSpatial
public import NearlyMinimax.SpatialCardinalContinuity
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Continuity of the actual integrated cardinal matrices and weights,
including every collision configuration. -/
𝚫
𝚪
𝚨
𝚩
𝚰

𝗇 𝔄 𝙇
𝗇 𝔉 𝔄 × SpatialScaleVector i
𝗃 𝔅 fun z : 𝔉 => ἀ lam (spatialScaleExtend i z.2) z.1 i
theorem spatial_centered_cardinal_scale_joint_continuous i lam :
    Continuous 𝔅 spatialCardinalScale := by
  simp_rw [spatial_cardinal_scale_product]
  unfold spatialSquaredDistance
  fun_prop

𝗇 𝔈 𝙮
theorem spatial_centered_cardinal_matrix_joint_continuous (i : Fin n) lam
    (β β' : 𝔈) :
    Continuous fun z : 𝔉 =>
      spatialCenteredCardinalMatrix i lam z.1 z.2 β β' := by
  have hc (γ : 𝔈) : Continuous fun z : 𝔉 =>
      highFrameCoefficients (spatialCardinalPolynomial z.1 i) γ :=
    (spatial_cardinal_polynomial_coefficients_continuous i $ polynomialBoxExponent γ.val ).comp continuous_fst
  exact ((spatial_centered_cardinal_scale_joint_continuous i lam).mul $ hc β ).mul $ hc β'

𝗇 𝔇 spatial_scale_domain_isCompact i T hT
𝗃 𝔊 integratedCardinalMatrix lam ἀ U β β'
theorem integrated_cardinal_matrix_continuous lam (hT : 𝖹)
    (β β' : 𝔈) :
    Continuous fun U : 𝔄 => 𝔊 T := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_parametric_integral_of_continuous
    (spatial_centered_cardinal_matrix_joint_continuous i lam β β')
    𝔇

theorem spatial_cardinal_weight_joint_continuous i lam :
    Continuous 𝔅 spatialCardinalWeight := by
  simp_rw [spatial_cardinal_weight_scale_product]
  unfold spatialUnaryWeight spatialSquaredDistance
  fun_prop

theorem integrated_cardinal_weight_continuous (i : Fin n) lam (hT : 𝖹) :
    Continuous fun U : 𝔄 => 𝙵₁ := continuous_parametric_integral_of_continuous
    (spatial_cardinal_weight_joint_continuous i lam) 𝔇

theorem integrated_cardinal_band_continuous lam (hL : 𝚛₂) (hT : 𝖹)
    (β β' : 𝔈) :
    Continuous fun U : 𝔄 =>
      𝔊 T - 𝔊 L :=
  (integrated_cardinal_matrix_continuous lam hT β β').sub
    $ integrated_cardinal_matrix_continuous lam hL β β'
