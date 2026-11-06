module

public import NearlyMinimax.PopulationPairBounds
public import RoughRegime.Macro
public import RoughRegime.Notation


public section

/-! Uniform extension-domain constants for the actual population upper proof.
Numerical witnesses are chosen before the open domain; no extension theorem
or fixed-domain admissibility transfer is assumed. -/
𝛍
𝚨

𝗇 𝔴 𝘷
𝗇 𝔄 𝔴 ⁻¹
𝗇 𝔉 𝗣
𝗇 𝔊 Admissible (C.withDomain Udom) θ
𝗇 𝔍 euclideanNorm 𝙪₁
𝗇 𝔐 𝘮
𝗃 𝕳 ἀ (C.withDomain Udom) θ hθ
𝗃 𝖌 𝕳 ἀ j x
𝗇 𝔒 𝖌 dyadicNormalizedDensity_bounds
𝗇 𝔓 𝖌 dyadicNormalizedDensity_measurable
𝗇 𝔔 C.smoothness - 1
𝗇 𝔚 𝘠
𝗇 𝔡 𝚎₂
𝗇 𝔢 0 < E
𝗃 𝕴 ἀ (ℓ := C.order)
𝗃 𝖊 ἀ j x
𝗇 𝔣 𝖊 dyadicAnchoredFeature y ⬝ᵥ 𝕴 dyadicPopulationIncrement θ x j
𝗇 𝔤 𝘘
𝗇 𝔨 𝖊 dyadicNormalizedAnchor
𝗇 𝔳 E * 𝔍
𝗇 𝔜 dyadicPopulationPolynomial C θ j x
𝗇 𝔷 𝕳 admissible_regression_value_bound
𝗇 𝕬 𝕳 dyadicNormalizedDensity_measurable
𝗇 𝕭 𝕳 dyadicNormalizedDensity_bounds
𝗇 𝕯 𝕴 dyadicFinPilotMoments θ
𝗇 𝕲 𝖊 dyadicPilotRow y
𝗃 𝕵 ἀ (d := d) (ℓ := C.order)
𝗃 𝖑 ἀ Udom θ hθ
𝗃 𝕶 𝖑 ἀ j x hx
𝗃 𝕸 ἀ θ j x
𝗇 𝖆 𝔄 ^ 𝔔
𝗃 𝖋 (ἀ ..).trans
𝗃 𝖐 ἀ 𝔐 x
𝗃 𝖒 ἀ θ 𝔐 x
section

variable (C : ModelConstants d)
    [Nonempty 𝔤]

𝗃 𝖎 ( 2 ^ ἀ)⁻¹
𝗇 𝔑 𝖎 j
𝗇 𝖈 𝙷₂
𝗃 𝖔 D * ἀ
𝗇 𝔗 𝖔 𝖈
𝗇 𝔥 𝘏
𝗇 𝔦 𝕳 dyadicPopulationFit_eq_normalized
𝗇 𝔧 𝖌 dyadicRegressionDifference_continuousOn
𝗇 𝔭 mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le
𝗇 𝔠 𝔄 ^ C.smoothness
𝗇 𝔅 (EuclideanSpace.equiv 𝘘 ℝ).symm
𝗇 𝔶 𝕵 anchoredPopulationFit_coefficient_error C.densityLower C.densityUpper C.densityLower_pos
𝗇 𝕹 dyadicTaylorCoefficients c j
𝗇 𝕺 mul_le_mul_of_nonneg_right $ le_max_right ..
𝗃 𝖍 ἀ * 𝔠
theorem uniform_domain_admissible_dyadicPopulationFit_taylor_coefficients :
    ∃ D , 𝙱₁ ∧ ∀ Udom , ∀ θ , 𝔊 →
      ∀ x ∈ unitCube d, ∃ c , ∀ j ,
      ‖𝔅
        (𝕸 dyadicPopulationFit - 𝕹)‖ ≤
          D * 𝔑 ^ C.smoothness := by
  obtain ⟨D, hD, hfit⟩ := 𝔶 $ by linarith [C.one_lt_densityUpper]
  let E := max 1 𝔗
  refine ⟨E, 𝔥, ?_⟩
  intro Udom θ hθ x hx
  obtain ⟨c, hc⟩ := 𝕳 admissible_dyadic_taylor_family x hx
  refine ⟨c, ?_⟩
  intro j
  let R := 𝖍 𝖈
  have hR : 𝖡₂ := mul_nonneg 𝔭
    $ Real.rpow_nonneg  𝖠₃  _
  rw [𝔦]
  have h := hfit _ (gridNormalizedAnchor_mem_cube _  𝖠₃  x hx)
    _ _ 𝔓 𝔒
    𝔧 𝕹
    R hR fun w hw => (hc j w hw).1
  apply h.trans
  calc
    𝖔 R = 𝖍 𝔗 := 𝖢₃
    _ ≤ 𝖍 E :=
      𝕺 $ Real.rpow_nonneg  𝖠₃  _


𝗇 𝔏 euclideanNorm $ w - 𝖊 dyadicNormalizedAnchor
𝗇 𝔟 max 1 $ Real.sqrt d ^ C.smoothness
𝗇 𝔩 2 * C.holderBound
𝗇 𝔮 𝕴 dyadicPopulationFit θ j x
𝗇 𝕻 T * 𝔟 + 𝔗
theorem uniform_domain_admissible_dyadicPopulationFit_spatial_error :
    ∃ E , 𝔢 ∧ ∀ Udom , ∀ θ , 𝔊 →
      ∀ j , ∀ x ∈ unitCube d, ∀ w ∈ unitCube d,
      |𝕸 dyadicRegressionDifference w - anchoredFitPolynomial 𝔨
        𝔮 w| ≤
          E * 𝔑 ^ C.smoothness * 𝔏 := by
  obtain ⟨D, hD, hpoint⟩ := 𝕵 anchoredPopulationFit_pointwise_error
    C.densityLower C.densityUpper C.densityLower_pos $ by linarith [C.one_lt_densityUpper]
  let T := d ^ C.order * 𝔩 / C.order.factorial
  have hT : 𝚞 := div_nonneg (mul_nonneg 𝘑₂
    $ mul_nonneg  𝖠₄  C.holderBound_pos.le ) $ Nat.cast_nonneg _
  let E := max 1 𝕻
  refine ⟨E, 𝔥, ?_⟩
  intro Udom θ hθ j x hx w hw
  obtain ⟨c, hc⟩ := 𝕳 admissible_dyadic_taylor_family x hx
  let R := 𝖍 𝖈
  have hR : 𝖡₂ := mul_nonneg 𝔭
    $ Real.rpow_nonneg  𝖠₃  _
  have hu : 𝔨 ∈ unitCube d := gridNormalizedAnchor_mem_cube _  𝖠₃  x hx
  have hp := hpoint _ hu _ _ 𝔓
    𝔒 𝔧
    𝕹 R hR (fun v hv => (hc j v hv).1) w hw
  rw [𝔦]
  apply hp.trans
  have hrad : 𝔏 ≤ Real.sqrt d := by
    have h := euclideanNorm_le_coordinate_radius (w - 𝔨) 1  𝖠₄ 
       fun i => by
        change |w i - 𝖊 dyadicNormalizedAnchor i| ≤ 1
        exact abs_le.mpr ⟨by linarith [(hw i).1, (hu i).2], by linarith [(hw i).2, (hu i).1]⟩
    linarith
  have hs : 1 ≤ C.smoothness := by
    obtain ⟨γ⟩ := (inferInstance : Nonempty 𝔤)
    have hor : 𝙠 ≤ C.order := by exact_mod_cast γ.property.1.trans_le γ.property.2
    exact hor.trans C.order_lt.le
  have hr0 : 0 ≤ 𝔏 := by unfold euclideanNorm; positivity
  have hpow := bounded_rpow_le_linear _ _ _ hr0 hrad hs
  calc
    _ ≤ 𝖍 T *
        𝔏 ^ C.smoothness +
        𝖔 R * 𝔏 := add_le_add (hc j w hw).2 le_rfl
    _ ≤ 𝖍 T *
        (𝔟 * 𝔏) +
        𝖔 R * 𝔏 := 𝖩₃
    _ = 𝖍 𝕻 * 𝔏 := 𝖢₃
    _ ≤ 𝖍 E * 𝔏 := mul_le_mul_of_nonneg_right (𝕺
        $ Real.rpow_nonneg  𝖠₃  _ ) hr0

𝗇 𝔙 𝘑₁
𝗇 𝔲 anchoredTransport d C.order *ᵥ e j
𝗇 𝖁 𝔅 $ e 𝔙
theorem uniform_domain_admissible_dyadicPopulationIncrement_successor_bound :
    ∃ E , 𝔢 ∧ ∀ Udom , ∀ θ , 𝔊 →
      ∀ x ∈ unitCube d, ∀ j ,
      ‖𝔅 (dyadicPopulationIncrement θ x 𝔙)‖ ≤
        E * 𝖎 𝔙 ^ C.smoothness := by
  obtain ⟨D, hD, hcoeff⟩ := uniform_domain_admissible_dyadicPopulationFit_taylor_coefficients C
  let E := D * (1 + 𝙖 * 2 ^ C.smoothness)
  refine ⟨E, mul_pos hD 𝖠₃ , ?_⟩
  intro Udom θ hθ x hx j
  obtain ⟨c, hc⟩ := 𝖑 hcoeff x hx
  let e := fun i => dyadicPopulationFit θ i x - dyadicTaylorCoefficients c i
  rw [dyadicPopulationIncrement_error_identity θ x c j]
  have hsub : ‖𝔅
      (e 𝔙 - 𝔲)‖ ≤
      ‖𝖁‖ +
      ‖𝔅 𝔲‖ := by
    simpa [EuclideanSpace.equiv] using norm_sub_le
      𝖁
      $ 𝔅 𝔲
  apply hsub.trans
  have ht := anchoredTransport_euclidean_norm $ e j
  apply (add_le_add (hc 𝔙) $ ht.trans $ mul_le_mul_of_nonneg_left (hc j) 𝖠₄ ).trans_eq
  rw [dyadic_inverse_scale_succ j, Real.mul_rpow  𝖠₄  𝖠₃ ]
  ring

𝗃 𝖏 ἀ 0 x
theorem uniform_domain_admissible_dyadicPopulationIncrement_root_bound :
    ∃ E : ℝ, 𝔢 ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, 𝔊 →
      ∀ x ∈ unitCube d,
      ‖𝔅 (dyadicPopulationIncrement θ x 0)‖ ≤ E := by
  obtain ⟨D, hD, hfit⟩ := 𝔶 $ by linarith [C.one_lt_densityUpper]
  let E := max 1 𝖔 𝔩
  refine ⟨E, 𝔥, ?_⟩
  intro Udom θ hθ x hx
  have hres : ∀ w ∈ unitCube d, |dyadicRegressionDifference θ 0 x w -
      anchoredFitPolynomial 𝖏 dyadicNormalizedAnchor (0 : 𝔤 → ℝ) w| ≤
        𝔩 := by
    intro w hw
    simp only [anchoredFitPolynomial, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
    exact 𝖋 abs_sub $ by
      have ha := 𝔷 _ $ 𝖏 dyadicCellAffine_mem_cube w hw
      have hb := 𝔷 x hx
      dsimp [ModelConstants.withDomain] at ha hb
      linarith
  have h := hfit _ (gridNormalizedAnchor_mem_cube _  𝖠₃  x hx) _ _
    𝖏 𝕬 𝖏 𝕭
    (𝕳 dyadicRegressionDifference_continuousOn 0 x) 0 𝔩
    (mul_nonneg  𝖠₄  C.holderBound_pos.le) hres
  change ‖𝔅 (dyadicPopulationFit θ 0 x)‖ ≤ E
  rw [𝔦]
  aesop


𝗇 𝕮 dyadicPopulationIncrement θ x j
theorem uniform_domain_admissible_dyadicPopulationIncrement_bound :
    ∃ E , 𝔢 ∧ ∀ Udom , ∀ θ , 𝔊 →
      ∀ x ∈ unitCube d, ∀ j ,
      ‖𝔅 𝕮‖ ≤
        E * 𝔑 ^ C.smoothness := by
  obtain ⟨E0, hE0, hroot⟩ := uniform_domain_admissible_dyadicPopulationIncrement_root_bound C
  obtain ⟨E1, hE1, hsucc⟩ := uniform_domain_admissible_dyadicPopulationIncrement_successor_bound C
  refine ⟨max E0 E1, hE0.trans_le $ le_max_left .. , ?_⟩
  intro Udom θ hθ x hx j
  cases j with
  | zero => simpa using (𝖑 hroot x hx).trans $ le_max_left E0 E1
  | succ j =>
    exact (𝖑 hsucc x hx j).trans
      $ 𝕺 $ Real.rpow_nonneg  𝖠₃  _

theorem uniform_domain_admissible_dyadicPopulationFit_physical_error :
    ∃ E , 𝔢 ∧ ∀ Udom , ∀ θ , 𝔊 →
      ∀ j , ∀ x ∈ unitCube d, ∀ y ∈ unitCube d, y ∈ 𝖊 dyadicPilotCell →
      |θ.regression y - θ.regression x - 𝖊 dyadicAnchoredFeature y ⬝ᵥ 𝔮| ≤
        𝔳 * 𝔑 ^ 𝔔 := by
  obtain ⟨E, hE, hfit⟩ := uniform_domain_admissible_dyadicPopulationFit_spatial_error C
  refine ⟨E, hE, ?_⟩
  intro Udom θ hθ j x hx y hy hcell
  have hw : dyadicNormalizedAnchor j y ∈ unitCube d := gridNormalizedAnchor_mem_cube _  𝖠₃  y hy
  have he := 𝖊 dyadicCellAffine_same_cell y hcell
  have h := 𝕶 hfit _ hw
  rw [𝖊 dyadicPopulationFit_physical_evaluation y hcell] at h
  unfold dyadicRegressionDifference at h
  rw [he] at h
  apply h.trans_eq
  have hd := 𝖊 dyadicCellAffine_euclidean_distance $ dyadicNormalizedAnchor j y
  rw [he] at hd
  rw [mul_assoc, positive_rpow_times_distance _ _ _ 𝖠₃ , ← hd]
  ring


𝗇 𝔇 (𝙉 ^ j)⁻¹ ^ C.smoothness
𝗇 𝔈 Real.exp $ -𝘏₂ * exteriorTau ((C.densityLower + C.densityUpper) / (C.densityUpper - C.densityLower))
𝗇 𝔎 (𝘻 : ℕ)
𝗇 𝖉 anchoredFinNormalizedGram v q
𝗇 𝔘 𝖼₁ *ᵥ 𝖉⁻¹ *ᵥ (V false - θ.regression x • V true)
𝗇 𝔫 U false - θ.regression x • U true
𝗇 𝔰 𝕴 anchoredFinNormalizedGram u p
𝗇 𝔪 (𝔎 : ℝ) ^ 𝔉
𝗇 𝕰 𝕳 dyadicFinPilotGram_eq_normalized
𝗇 𝕼 (EuclideanSpace.equiv (Fin 𝔉) ℝ).symm
𝗇 𝕽 𝖔 𝔇
𝗇 𝖂 𝖼₁
𝗇 𝖃 E * 𝔇 * 𝔪 * 𝔈
𝗇 𝖄 E₀ * D
𝗇 𝖅 anchoredFinNormalizedGram u p
𝗃 𝖓 ἀ ⁻¹ *ᵥ 𝔫 - 𝔘
theorem uniform_domain_admissible_dyadic_increment_polynomial_error :
    ∃ E : ℝ, 𝔢 ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, 𝔊 →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ m : ℕ,
      ‖𝕼
        (incrementFinVector 𝔉 C.densityLower C.densityUpper
          𝖂 (θ.regression x) m 𝕸 dyadicIncrementRawMean -
            anchoredFinVector 𝕮)‖ ≤
        𝖃 := by
  obtain ⟨χ, hχ, hcond⟩ := 𝕵 anchoredFinSimilarityUnit_uniform_condition
  obtain ⟨D, hD, hinc⟩ := uniform_domain_admissible_dyadicPopulationIncrement_bound C
  let E₀ := χ ^ 2 * C.densityUpper ^ (𝔉 + 1) *
    parentInverseErrorConstant C.densityLower C.densityUpper 𝔉
  let E := max 1 𝖄
  refine ⟨E, zero_lt_one.trans_le 𝚂₁, ?_⟩
  intro Udom θ hθ j x hx m
  let u := 𝔨
  let v := 𝖐 dyadicNormalizedAnchor
  let p := 𝕸 dyadicNormalizedDensity
  let q := if 𝔚 then fun _ : Covariate d => 𝙠 else 𝖒 dyadicNormalizedDensity
  let U := 𝖊 𝕯
  let V := if 𝔚 then 0 else 𝖐 𝕯
  have hqmeas : Measurable q := by
    by_cases hj : 𝔚
    · aesop
    · simpa [q, hj, ModelConstants.withDomain] using 𝖐 𝕬
  have hqb : 𝔡 := by
    by_cases hj : 𝔚
    · exact Filter.Eventually.of_forall fun _ => by
        simpa [q, hj, ModelConstants.withDomain] using And.intro C.densityLower_lt_one.le C.one_lt_densityUpper.le
    · simpa [q, hj, ModelConstants.withDomain] using 𝖐 𝕭
  have hparent : 𝕴 anchoredFinNormalizedGram v q =
      if 𝔚 then 1 else 𝖒 dyadicFinPilotGram := by
    by_cases hj : 𝔚
    · simp [q, hj, anchoredFinNormalizedGram_one]
    · simp only [q, hj, ite_false]
      exact (𝖐 𝕰).symm
  have hactual : 𝖓 𝔰 =
        anchoredFinVector 𝕮 := by
    rw [hparent, ← 𝖊 𝕰]
    exact 𝖌 dyadicFinite_increment_eq_actual hx
  have hsmall : ‖𝕼
      𝖓 𝖅‖ ≤
      𝕽 := by
    rw [hactual, anchoredFinVector_norm]
    bound
  have he := anchoredNormalized_increment_error u v p q
    𝔓 hqmeas
    C.densityLower C.densityUpper χ 𝕽
    C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper)
    𝔒 hqb
    (hcond u $ gridNormalizedAnchor_mem_cube _  𝖠₃  x hx )
    U V (θ.regression x) 𝖂 hsmall m
  rw [hactual] at he
  have hval : 𝕴 dyadicIncrementRawMean θ j x = fun a =>
      incrementValuation 𝖅 𝖉 U V
        $ (Fintype.equivFin $ incrementVariables 𝔉 ).symm a := by
    rw [𝖌 dyadicIncrementRawMean_eq_population hx]
    have hcurrent : 𝔰 = 𝕸 dyadicFinPilotGram :=
      (𝖊 𝕰).symm
    simp only [dyadicIncrementPopulation, hparent, hcurrent]
    rfl
  rw [hval, incrementFinVector_eval_population]
  calc
    _ ≤ E₀ * 𝕽 * 𝔪 *
        𝔈 := he
    _ = 𝖄 * 𝔇 * 𝔪 *
        𝔈 := 𝖢₃
    _ ≤ 𝖃 := by
      bound

𝗇 𝔖 Real.exp $ -m * paperTau C
𝗇 𝔵 B * 𝔉
𝗇 𝕾 𝔎 ^ 𝔉
theorem uniform_domain_admissible_dyadic_polynomial_row_error :
    ∃ E , 𝔢 ∧ ∀ Udom , ∀ θ , 𝔊 →
      ∀ j , ∀ x ∈ unitCube d, ∀ y ∈ unitCube d, y ∈ 𝖊 dyadicPilotCell → ∀ m ,
      |𝕲 ⬝ᵥ 𝔜 (θ.regression x) m -
        𝔣| ≤
      𝔳 * 𝔑 ^ 𝔔 *
        𝕾 * 𝔖 := by
  obtain ⟨B, hB, herror⟩ := uniform_domain_admissible_dyadic_increment_polynomial_error C
  let E := max 1 𝔵
  refine ⟨E, 𝔥, ?_⟩
  intro Udom θ hθ j x hx y hy hcell m
  have hnorm := 𝕶 herror m
  rw [exteriorTau_sqrt_ratio C.densityLower C.densityUpper C.densityLower_pos
    $ C.densityLower_lt_one.trans C.one_lt_densityUpper ] at hnorm
  rw [← dyadicPilotRow_dot_coefficients, ← dotProduct_sub]
  apply 𝖋 finite_row_abs_dot_le_euclidean_norm
  have hd : 0 ≤ 𝔍 := by unfold euclideanNorm; positivity
  calc
    _ ≤ 𝔉 * 𝔴 * 𝔍 *
        (𝖍 B * 𝕾 *
          𝔖) := mul_le_mul (𝕴 dyadicPilotRow_sum_abs_le_distance j x y hx hy hcell) hnorm (norm_nonneg _) 𝖠₃
    _ = 𝔵 * 𝔍 *
        𝖍 𝔴 *
          𝕾 * 𝔖 := 𝖢₃
    _ = 𝔵 * 𝔍 *
        𝖆 *
          𝕾 * 𝔖 := by
      rw [dyadic_scale_rpow_cancel]
    _ ≤ 𝔳 * 𝖆 *
        𝕾 * 𝔖 := by
      bound

end

𝗇 𝔛 Finset.range 𝗯
𝗇 𝔬 - m j * paperTau C
𝗇 𝔯 (2 ^ J)⁻¹
𝗃 𝕷 ἀ C θ J m
𝗇 𝕿 y ∈ dyadicPilotCell J x
𝗇 𝖇 𝘎
theorem uniform_domain_admissible_dyadicPopulationResidual_bound C
    (hs : 𝖇) :
    ∃ E , 𝔢 ∧ ∀ Udom , ∀ θ , 𝔊 →
      ∀ J , ∀ m , ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      𝕿 →
        |𝕷 dyadicPopulationResidual x y| ≤
          𝔳 * dyadicPopulationBiasBudget C J m := by
  let := anchoredIndex_nonempty_of_one_lt_smoothness C hs
  obtain ⟨A, hA, hfit⟩ := uniform_domain_admissible_dyadicPopulationFit_physical_error C
  obtain ⟨B, hB, hpoly⟩ := uniform_domain_admissible_dyadic_polynomial_row_error C
  let E := max A B
  refine ⟨E, hA.trans_le $ le_max_left .. , ?_⟩
  intro Udom θ hθ J m x hx y hy hcell
  have hd : 0 ≤ 𝔍 := by unfold euclideanNorm; positivity
  have heq : 𝕷 dyadicPopulationResidual x y =
       θ.regression y - θ.regression x - dyadicAnchoredFeature J x y ⬝ᵥ 𝕴 dyadicPopulationFit θ J x +
      ∑ j ∈ 𝔛, (𝔣 -
        𝕲 ⬝ᵥ 𝔜 (θ.regression x) (m j)) := by
    rw [dyadicPopulationIncrement_telescope, Finset.sum_sub_distrib]
    unfold dyadicPopulationResidual
    ring
  rw [heq]
  apply 𝖋 abs_add_le
  apply (add_le_add (𝖑 hfit J x hx y hy hcell) $ Finset.abs_sum_le_sum_abs .. ).trans
  calc
    _ ≤ A * 𝔍 * 𝔯 ^ 𝔔 +
        ∑ j ∈ 𝔛, B * 𝔍 *
          𝖆 * (m j + 1 : ℕ) ^ 𝔉 *
            Real.exp 𝔬 := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_sub_comm]
      exact 𝕶 hpoly y hy
        (dyadicPilotCell_subset_coarser j J (Nat.le_of_lt_succ $ Finset.mem_range.mp hj ) x hcell) $ m j
    _ ≤ 𝔳 * 𝔯 ^ 𝔔 +
        ∑ j ∈ 𝔛, 𝔳 *
          𝖆 * ( m j + 1 ) ^ 𝔉 *
            Real.exp 𝔬 := by
      bound
    _ = 𝔳 * dyadicPopulationBiasBudget C J m := by
      unfold dyadicPopulationBiasBudget
      rw [mul_add, Finset.mul_sum]
      grind


section

𝛇

theorem uniform_domain_admissible_dyadicFinPilotMoments_uniform_bound :
    ∃ W , 0 < W ∧ ∀ Udom , ∀ θ , 𝔊 →
      ∀ j , ∀ x ∈ unitCube d, ∀ t ,
        ‖𝖊 𝕯 t‖ ≤ W := by
  obtain ⟨W, hW, hb⟩ := anchoredFinMomentFamilies_uniform_bound
    C.densityUpper C.holderBound (zero_le_one.trans C.one_lt_densityUpper.le) C.holderBound_pos.le
  refine ⟨W, hW, ?_⟩
  intro Udom θ hθ j x hx t
  rw [𝖌 dyadicFinPilotMoments_eq_anchored hx]
  exact hb _ (gridNormalizedAnchor_mem_cube _  𝖠₃  x hx) _ _
    ((𝔒).mono
      𝗴₁)
    (fun w hw => 𝔷 _ $ 𝖊 dyadicCellAffine_mem_cube w hw ) t

theorem uniform_domain_admissible_dyadicPopulationPolynomial_uniform_bound
    [Nonempty 𝔤] Y (hY : 0 ≤ Y) :
    ∃ B , 𝘶₁ ∧ ∀ Udom , ∀ θ , 𝔊 →
      ∀ j , ∀ x ∈ unitCube d, ∀ y , |y| ≤ Y → ∀ m ,
        ‖𝔜 y m‖ ≤ B := by
  obtain ⟨W, hW, hmom⟩ := uniform_domain_admissible_dyadicFinPilotMoments_uniform_bound C
  obtain ⟨B, A, hB, hA, hder⟩ := 𝕵 anchored_population_inverse_derivatives C.densityLower C.densityUpper W Y C.densityLower_pos
    (C.densityLower_lt_one.trans C.one_lt_densityUpper) hW.le hY
  refine ⟨B, hB, ?_⟩
  intro Udom θ hθ j x hx y hy m
  let q := if 𝔚 then 𝙃 else 𝖒 dyadicNormalizedDensity
  have hqm : Measurable q := by
    by_cases hj : 𝔚
    · simpa [q, hj, ModelConstants.withDomain] using measurable_const
    · simpa [q, hj, ModelConstants.withDomain] using 𝖐 𝕬
  have hqb : 𝔡 := by
    by_cases hj : 𝔚
    · exact Filter.Eventually.of_forall fun _ => by
        simpa [q, hj, ModelConstants.withDomain] using And.intro C.densityLower_lt_one.le C.one_lt_densityUpper.le
    · simpa [q, hj, ModelConstants.withDomain] using 𝖐 𝕭
  have hV t : ‖(if 𝔚 then (0 : Bool → Fin 𝔉 → ℝ)
      else 𝖒 dyadicFinPilotMoments) t‖ ≤ W := by
    by_cases hj : 𝔚
    · simpa [hj] using hW.le
    grind
  have hd := hder 𝔨 𝖐 dyadicNormalizedAnchor
    (gridNormalizedAnchor_mem_cube 𝔴  𝖠₃  x hx)
    (gridNormalizedAnchor_mem_cube (2 ^ 𝔐)  𝖠₃  x hx)
    𝕸 dyadicNormalizedDensity q
    𝔓 hqm
    𝔒 hqb
    𝕸 dyadicFinPilotMoments (if 𝔚 then 0 else 𝖒 dyadicFinPilotMoments)
    𝕶 hmom hV y hy m 0 Fin.elim0
  rw [← 𝖌 dyadicIncrementRawMean_eq_with_virtual_parent hx] at hd
  simpa only [dyadicPopulationPolynomial, iteratedFDeriv_zero_apply, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one,
    Fin.prod_univ_zero] using hd

end

𝗇 𝕱 𝕶 hb
𝗇 𝖀 dyadicPopulationRawPolynomial C θ j x
theorem uniform_domain_admissible_dyadicPopulationRawPolynomial_uniform_bound C
    (hs : 𝖇) :
    ∃ B , 𝘶₁ ∧ ∀ Udom , ∀ θ , 𝔊 →
      ∀ j , ∀ x ∈ unitCube d, ∀ t , ∀ m ,
        ‖𝖀 t m‖ ≤ B := by
  let := anchoredIndex_nonempty_of_one_lt_smoothness C hs
  obtain ⟨B, hB, hb⟩ := uniform_domain_admissible_dyadicPopulationPolynomial_uniform_bound C 1 zero_le_one
  refine ⟨2 * B, mul_pos  𝖠₄  hB, ?_⟩
  intro Udom θ hθ j x hx t m
  have h0 := 𝕱 0  𝖠₄  m
  have h1 := 𝕱 1  𝖠₄  m
  have he0 : 𝖀 false m = 𝔜 0 m := by
    rw [dyadicPopulationPolynomial_affine, zero_smul, sub_zero]
  cases t
  · grind
  · have he : 𝖀 true m =
        𝔜 0 m - 𝔜 1 m := by
      rw [dyadicPopulationPolynomial_affine, dyadicPopulationPolynomial_affine]
      simp
    rw [he]
    exact 𝖋 norm_sub_le 𝖡₄

𝗇 𝔱 𝖮
theorem uniform_domain_admissible_dyadicPopulationPilotSum_uniform_bound C
    (hs : 𝖇) :
    ∃ R , 𝖡₂ ∧ ∀ Udom , ∀ θ , 𝔊 →
      ∀ J , ∀ m , ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      𝕿 → ∀ t , |𝕷 dyadicPopulationPilotSum t 𝔱| ≤ R := by
  obtain ⟨B, hB, hb⟩ := uniform_domain_admissible_dyadicPopulationRawPolynomial_uniform_bound C hs
  let R := 2 * 𝔉 * Real.sqrt d * B
  refine ⟨R, 𝖠₃, ?_⟩
  intro Udom θ hθ J m x hx y hy hcell t
  apply 𝖋 Finset.abs_sum_le_sum_abs
  calc
    _ ≤ ∑ j ∈ 𝔛, (∑ i, |𝕲 i|) * B := by
      apply Finset.sum_le_sum
      intro j hj
      exact 𝖋 finite_row_abs_dot_le_pi_norm
        $ mul_le_mul_of_nonneg_left (𝕱 t $ m j ) $ Finset.sum_nonneg 𝖢
    _ = (∑ j ∈ 𝔛, ∑ i, |𝕲 i|) * B := by
      rw [Finset.sum_mul]
    _ ≤ R := mul_le_mul_of_nonneg_right (dyadicPilotRow_total_abs_le J x y hx hy hcell) hB.le

𝗇 𝔞 1 + R
theorem uniform_domain_admissible_dyadicPopulationCoefficients_uniform_bound C
    (hs : 𝖇) :
    ∃ Cp , 0 < Cp ∧ ∀ Udom , ∀ θ , 𝔊 →
      ∀ J , ∀ m , ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      𝕿 → ‖𝕷 dyadicPopulationCoefficients 𝔱‖ ≤ Cp := by
  obtain ⟨R, hR, hb⟩ := uniform_domain_admissible_dyadicPopulationPilotSum_uniform_bound C hs
  refine ⟨Real.sqrt 3 * 𝔞, mul_pos  𝖠₃  𝖠₃ , ?_⟩
  intro Udom θ hθ J m x hx y hy hc
  have hcoord i : |𝕷 dyadicPopulationCoefficients 𝔱 i| ≤ 𝔞 := by
    fin_cases i
    · simpa [dyadicPopulationCoefficients] using hR
    · change |-1 + 𝕷 dyadicPopulationPilotSum true 𝔱| ≤ 𝔞
      grind
    · change |-𝕷 dyadicPopulationPilotSum false 𝔱| ≤ 𝔞
      grind
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨𝖠₃, ?_⟩
  calc
     ∑ i : Fin 3, ‖𝕷 dyadicPopulationCoefficients 𝔱 i‖ ^ 2 ≤ ∑ _i : Fin 3, 𝔞 ^ 2 := by
      bound
    _ = 3 * 𝔞 ^ 2 := 𝖢₄
    _ = (Real.sqrt 3 * 𝔞) ^ 2 := 𝖤₃
