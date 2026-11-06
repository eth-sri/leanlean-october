module

public import NearlyMinimax.SpatialCardinalCovariance
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The actual logarithmically truncated scale integral in Appendix A.
Compactness proves genuine integrability before any matrix/response
interchange is used. -/
𝛄
𝚪
𝚨
𝚩
set_option maxHeartbeats 2000000

abbrev SpatialScaleIndex (i : Fin n) := {j : Fin n // 𝖰₁}
abbrev SpatialScaleVector (i : Fin n) := SpatialScaleIndex i → ℝ

def spatialScaleExtend (i : Fin n) (t : SpatialScaleVector i) (j : Fin n) : ℝ :=
  if h : 𝖰₁ then t 𝗷₂ else 0

𝗇 𝔉 1 + max 0 (t j)
def spatialScaleLogSum (i : Fin n) (t : SpatialScaleVector i) : ℝ :=
  ∑ j, Real.log 𝔉

/-- Equal to S≤2logT in the nonnegative scale orthant. The max only
makes the defining function globally continuous. -/
def spatialScaleDomain (i : Fin n) (T : ℝ) : Set $ SpatialScaleVector i :=
  Ici 0 ∩ {t | 𝚞₂ ≤ 2 * Real.log T}

theorem spatial_scale_log_sum_continuous (i : Fin n) :
    Continuous $ spatialScaleLogSum i := by
  apply continuous_finsetSum
  intro j _
  exact (continuous_const.add $ continuous_const.max $ continuous_apply j ).log 𝖤₃

𝗇 𝔈 𝗕₁
theorem spatial_scale_domain_isClosed (i : Fin n) T :
    IsClosed 𝔈 :=
  isClosed_Ici.inter $ isClosed_le (spatial_scale_log_sum_continuous i) continuous_const

𝗇 𝔊 𝖹
theorem spatial_scale_domain_subset_box (i : Fin n) T (hT : 𝔊) :
    𝔈 ⊆ Icc 0 fun _ => 𝖫₁ - 1 := by
  intro t ht
  refine ⟨ht.1, fun j => ?_⟩
  have hT0 : 𝗹₁ := 𝖡₄
  have hlog0 j : 0 ≤ Real.log 𝔉 :=
    Real.log_nonneg 𝖢₄
  have hlogj := (Finset.single_le_sum (fun j _ => hlog0 j) $ Finset.mem_univ j ).trans ht.2
  have htj : 𝖥₂ := ht.1 j
  rw [max_eq_right htj] at hlogj
  have he := Real.exp_le_exp.mpr hlogj
  rw [Real.exp_log 𝖡₄ ] at he
  have hpow : Real.exp (2 * Real.log T) = 𝖫₁ := by
    simpa only [Nat.cast_ofNat, Real.exp_log hT0] using Real.exp_nat_mul (Real.log T) 2
  linarith

𝗃 𝔓 ἀ i T hT
theorem spatial_scale_domain_isCompact (i : Fin n) T (hT : 𝔊) :
    IsCompact 𝔈 :=
  isCompact_Icc.of_isClosed_subset (spatial_scale_domain_isClosed i T)
    𝔓 spatial_scale_domain_subset_box

def spatialScaleMeasure (i : Fin n) (T : ℝ) : Measure $ SpatialScaleVector i :=
  volume.restrict 𝔈

𝗇 𝔍 spatialScaleMeasure i T
theorem spatial_scale_measure_finite (i : Fin n) T (hT : 𝔊) :
    IsFiniteMeasure 𝔍 := by
  apply isFiniteMeasure_restrict.mpr
  exact (𝔓 spatial_scale_domain_isCompact).measure_ne_top

theorem spatial_scale_extend_continuous (i : Fin n) :
    Continuous $ spatialScaleExtend i := by
  apply continuous_pi
  intro j
  by_cases hji : 𝖰₁
  · simpa only [spatialScaleExtend, dite_eq_left hji] using continuous_apply (⟨j, hji⟩ : SpatialScaleIndex i)
  · simp only [spatialScaleExtend, dite_eq_right hji]; exact continuous_const

𝗇 𝔄 𝙇
𝗇 𝔎 𝘒₁
𝗇 𝔐 𝙮
𝗇 𝔑 spatialCardinalPolynomial U i
def spatialCenteredCardinalMatrix (i : Fin n) (lam : ℝ)
    (U : 𝔄) (t : SpatialScaleVector i) (β β' : 𝔐) : ℝ :=
  spatialCardinalScale lam 𝔎 U i *
    highFrameCoefficients 𝔑 β *
    highFrameCoefficients 𝔑 β'

theorem spatial_centered_cardinal_scale_continuous
    i lam (U : 𝔄) :
    Continuous fun t => spatialCardinalScale lam 𝔎 U i := by
  apply continuous_finsetProd
  intro j _
  have hj := (continuous_apply j).comp $ spatial_scale_extend_continuous i
  fun_prop

𝗇 𝔒 spatialCenteredCardinalMatrix i lam U t β β'
theorem spatial_centered_cardinal_matrix_integrable
    (i : Fin n) lam T (hT : 𝔊) U
    (β β' : 𝔐) :
    Integrable (fun t => 𝔒) 𝔍 := by
  apply ContinuousOn.integrableOn_compact 𝔓 spatial_scale_domain_isCompact
  exact (((spatial_centered_cardinal_scale_continuous i lam U).mul continuous_const).mul
    continuous_const).continuousOn

/-- The exact E_(k,T) from the paper, as a genuine coefficientwise
Lebesgue integral of its explicit cardinal products. -/
def integratedCardinalMatrix (lam T : ℝ) (U : 𝔄)
    (β β' : 𝔐) : ℝ :=
  ∑ i, ∫ t, 𝔒 ∂𝔍

def integratedCardinalWeight (lam T : ℝ) (U : 𝔄) (i : Fin n) : ℝ :=
  ∫ t, spatialCardinalWeight lam 𝔎 U i ∂𝔍

𝗇 𝔅 fun β' _ => (hA β β').const_mul $ φ i β * φ l β'
theorem spatial_frame_covariance_integral [Fintype κ] [DecidableEq κ]
    [MeasurableSpace α] (μ : Measure α) (A : α → κ → 𝖱₁)
    (hA : ∀ β β', Integrable (fun t => A t β β') μ)
    φ (i l : Fin n) :
    spatialFrameCovariance (fun β β' => ∫ t, A t β β' ∂μ) φ i l =
      ∫ t, spatialFrameCovariance (A t) φ i l ∂μ := by
  unfold spatialFrameCovariance
  rw [integral_finsetSum _ fun β _ => integrable_finsetSum _
    𝔅 ]
  apply Finset.sum_congr rfl
  intro β _
  rw [integral_finsetSum _ 𝔅]
  apply Finset.sum_congr rfl
  intro β' _
  rw [integral_const_mul]

theorem spatial_centered_cardinal_matrix_diagonal (hn : 𝖠₁)
    j lam (U : 𝔄) t i l :
    spatialFrameCovariance (spatialCenteredCardinalMatrix (D := D) j lam U t)
      (fun r => highFrameFeature $ U r ) i l =
      if j = i ∧ 𝚛₁ then spatialCardinalWeight lam (spatialScaleExtend j t) U j else 0 := by
  unfold spatialCenteredCardinalMatrix
  rw [spatial_frame_covariance_rank_one]
  have hdegree := (spatial_cardinal_polynomial_degree U j).trans $ Nat.sub_le_sub_right hn 1
  rw [← high_frame_polynomial_evaluation _ hdegree, ← high_frame_polynomial_evaluation _ hdegree]
  by_cases hji : j = i
  · subst j
    by_cases hil : 𝚛₁
    · subst l
      rw [ite_eq_left ⟨rfl, rfl⟩, ← spatial_cardinal_weight_product]
      ring
    · rw [ite_eq_right $ by tauto , spatial_cardinal_polynomial_eval_neighbor U i l $ Ne.symm hil , mul_zero]
  · rw [ite_eq_right $ by tauto , spatial_cardinal_polynomial_eval_neighbor U j i $ Ne.symm hji ,
      mul_zero, zero_mul]

𝗇 𝔏 𝖯₁
/-- The integrated covariance matrix is genuinely symmetric. -/
theorem integrated_cardinal_matrix_symmetric
    lam T (U : 𝔄) (β β' : 𝔐) :
    𝔏 β β' = 𝔏 β' β := by
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [] with t
  unfold spatialCenteredCardinalMatrix
  ring

/-- Exact evaluated diagonal of the actual scale integral E_(k,T). -/
theorem integrated_cardinal_matrix_diagonal (hn : 𝖠₁)
    lam T (hT : 𝔊) (U : 𝔄) i l :
    spatialFrameCovariance (integratedCardinalMatrix (D := D) lam T U)
      (fun j => highFrameFeature $ U j ) i l =
      if 𝚛₁ then 𝙵₁ else 0 := by
  unfold integratedCardinalMatrix
  rw [spatial_frame_covariance_sum]
  simp_rw [spatial_frame_covariance_integral _ _
     fun β β' => spatial_centered_cardinal_matrix_integrable _ lam T hT U β β' ]
  simp_rw [spatial_centered_cardinal_matrix_diagonal hn]
  rw [Finset.sum_eq_single i]
  all_goals aesop

𝗇 𝔇 𝙬
theorem integrated_cardinal_response_heat (hn : 𝖠₁) q
    C a V η lam T (hC : 𝚆) (hT : 𝔊) U
    (g w : 𝙔) (c : 𝔐 → ℝ) y :
    𝗔 𝔏 c
      (fun c => 𝖨 𝔇 c y) =
      𝙎 * ∑ i, 𝖩 * 𝙵₁ *
        𝖷 𝔇 c y i +
      highResponseDefect q C a V η 𝔏 g w
        𝔇 c y := by
  apply high_response_matrix_heat_with_defect q C a V η _ hC
  · exact integrated_cardinal_matrix_symmetric lam T U
  · exact integrated_cardinal_matrix_diagonal hn lam T hT U
