module

public import NearlyMinimax.CardinalScaleTail
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual spatial interpolation bias: genuine patch integrals of the
integrated cardinal-weight defect, using Gaussian decay and scale tails. -/
𝚫
𝚨
𝚩
𝚰

𝗇 𝔎 𝗖₁
def anchoredPatchConfiguration (i : Fin n) (x : Covariate d)
    (Y : 𝔎) : 𝙇 :=
  fun j => if h : 𝖰₁ then Y 𝗷₂ else x

def spatialPatchDesignMeasure (i : Fin n) (d : ℕ) :
    Measure 𝔎 :=
  Measure.pi fun _ : SpatialScaleIndex i => 𝖪

instance spatialPatchCube_finite (d : ℕ) :
    IsFiniteMeasure $ (volume : 𝘹₁).restrict $ spatialPatchBox d := by
  apply isFiniteMeasure_restrict.mpr
  exact isCompact_Icc.measure_ne_top

𝗇 𝔄 𝘓₁
instance spatialPatchDesignMeasure_finite (i : Fin n) (d : ℕ) :
    IsFiniteMeasure 𝔄 := by
  unfold spatialPatchDesignMeasure
  infer_instance

𝗇 𝔈 anchoredPatchConfiguration i x Y
def anchoredCardinalScaleWeight (i : Fin n) (lam : ℝ) (x : Covariate d)
    (t : SpatialScaleVector i) (Y : 𝔎) : ℝ :=
  spatialCardinalWeight lam 𝘒₁ 𝔈 i

𝗇 𝔐 Ici 0 \ 𝗕₁
𝗃 𝔤 ἀ i lam
𝗇 𝔡 𝔤 anchoredCardinalScaleWeight x
𝗇 𝔉 𝔡 t Y
𝗇 𝔓 anchoredPatchConfiguration i x Y
𝗇 𝔙 𝖺
𝗃 𝔣 ∫ Y, ἀ ∂ 𝔄
section

𝛔

theorem anchored_configuration_same (x : Covariate d)
    Y : 𝔓 i = x := by
  simp [anchoredPatchConfiguration]

theorem anchored_configuration_other (x : Covariate d)
    Y j :
    𝔓 j.val = Y j := by
  simp [anchoredPatchConfiguration, j.property]

𝗇 𝔔 spatialUnaryWeight lam (t j) x
theorem anchored_cardinal_scale_product lam (x : Covariate d)
    t Y :
    𝔉 =
      ∏ j, 𝔔 (Y j) := by
  unfold anchoredCardinalScaleWeight
  rw [spatial_cardinal_weight_scale_product]
  simp_rw [anchored_configuration_same, anchored_configuration_other]

theorem anchored_cardinal_scale_joint_continuous lam x :
    Continuous fun z : SpatialScaleVector i × 𝔎 =>
      𝔡 z.1 z.2 := by
  simp_rw [anchored_cardinal_scale_product]
  unfold spatialUnaryWeight spatialSquaredDistance
  fun_prop

𝗇 𝔛 fun t => 𝔉
theorem anchored_cardinal_scale_integrable (hlam : 𝔙)
    (x : Covariate d) Y :
    IntegrableOn 𝔛 $ Ici 0 :=
  𝔤 spatial_cardinal_weight_orthant_integrable hlam 𝔈

theorem anchored_cardinal_scale_norm_integral_le (hlam : 𝔙) (x : Covariate d) Y :
     ∫ t : SpatialScaleVector i in Ici 0, ‖𝔉‖ ≤ 1 := by
  have he : (fun t => ‖𝔉‖) =ᵐ[𝙶₁]
      𝔛 := by
    filter_upwards [𝔤 spatial_cardinal_weight_orthant_nonnegative 𝔈] with t ht
    simpa
  rw [integral_congr_ae he]
  exact 𝔤 spatial_cardinal_weight_orthant_integral_le_one hlam 𝔈

𝗇 𝔑 fun z => 𝔡 z.1 z.2
/-- Actual joint integrability, derived from the exact Gamma-normalized scale
weights and the finite patch measure. -/
theorem anchored_cardinal_scale_joint_integrable (hlam : 𝔙) x :
    Integrable 𝔑
      $ (𝙶₁).prod 𝔄 := by
  have hc := 𝔤 anchored_cardinal_scale_joint_continuous x
  apply (integrable_prod_iff' hc.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall $ anchored_cardinal_scale_integrable i hlam x , ?_⟩
  exact (integrable_const 1).mono'
    hc.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    $ Filter.Eventually.of_forall fun Y => by
      rw [Real.norm_eq_abs, 𝗪]
      exact anchored_cardinal_scale_norm_integral_le i hlam x Y

/-- The tail restriction preserves genuine joint integrability. -/
theorem anchored_cardinal_tail_joint_integrable (hlam : 𝔙) T x :
    Integrable 𝔑
      $ (volume.restrict 𝔐).prod 𝔄 := (anchored_cardinal_scale_joint_integrable i hlam x).mono_measure
    $ Measure.prod_mono (Measure.restrict_mono_set _ Set.diff_subset) le_rfl

theorem anchored_cardinal_spatial_integral_product lam
    x t :
    𝔣 𝔉 =
      ∏ j : SpatialScaleIndex i, ∫ y in spatialPatchBox d, 𝔔 y := by
  simp_rw [anchored_cardinal_scale_product]
  exact integral_fintype_prod_eq_prod
     fun j y => 𝔔 y

end

𝗇 𝔗 -𝙊
𝗇 𝔇 𝖦₂ ^ 𝗈 * T ^ 𝔗 * 𝗶 ^ 𝗥
𝗇 𝔠 anchoredCardinalScaleWeight i (spatialInterpolationLambda d) x t Y
𝗇 𝔍 ∫ t : SpatialScaleVector i in Ici 0 \ 𝗕₁, 𝔠
𝗇 𝔜 𝔣 𝔍
𝗇 𝔞 𝘸₂
section

variable (hd : 𝗆)

include hd

𝗇 𝔅 𝗴₂ ^ (𝔗 / 2 - 1)
𝗇 𝔊 spatialUnaryIntegralConstant d ^ 𝖪₁
𝗇 𝔒 𝔣 𝔠
theorem anchored_cardinal_spatial_integral_decay (i : Fin n)
    x (hx : 𝔞) t (ht : 𝘩₁) :
    𝔒 ≤
      𝔊 *
        ∏ j, 𝔅 := by
  rw [anchored_cardinal_spatial_integral_product]
  have h : ∏ j : SpatialScaleIndex i, ∫ y in spatialPatchBox d,
      spatialUnaryWeight (spatialInterpolationLambda d) (t j) x y ≤
      ∏ j : SpatialScaleIndex i, spatialUnaryIntegralConstant d * 𝔅 := by
    apply Finset.prod_le_prod₀
    · intro j _
      apply integral_nonneg
      intro y
      have htj : 𝖥₂ := ht j
      unfold spatialUnaryWeight
      positivity
    · intro j _
      exact spatial_unary_patch_integral_decay hd (t j) (ht j) x hx
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using h

𝗇 𝔟 d / 2
/-- The actual spatial-and-scale complement integral, with all Fubini
exchanges justified by previously derived joint integrability. -/
theorem anchored_cardinal_tail_spatial_integral_bound (hn : 𝗏)
    (i : Fin n) x (hx : 𝔞) (hT : 𝖹) :
    𝔜 ≤
      𝔇 := by
  have hdR : 𝙠 ≤ d := by exact_mod_cast hd
  have hlam : 𝘹₂ := by unfold spatialInterpolationLambda; positivity
  have hjoint := anchored_cardinal_tail_joint_integrable i hlam T x
  rw [ (integral_prod_symm _ hjoint).symm.trans $ integral_prod _ hjoint ]
  have hpowint := (spatial_scale_complement_power_integrable hn i
    (by positivity : 𝙋 < 𝔟) T).const_mul
      𝔊
  have hdom : (fun t =>
      𝔒) ≤ᵐ[
        volume.restrict 𝔐]
       fun t => 𝔊 *
        ∏ j, 𝔅 := by
    filter_upwards [ae_restrict_mem $ measurableSet_Ici.diff 𝘻₂ ] with t ht
    exact anchored_cardinal_spatial_integral_decay hd i x hx t ht.1
  have hneg : -d / 2 = -(𝙊 / 2) := 𝖢₃
  rw [hneg] at hdom
  have h := integral_mono_ae hjoint.integral_prod_left hpowint hdom
  rw [integral_const_mul, spatial_scale_index_card] at h
  have htail := spatial_scale_complement_power_integral_le hn i
    (by linarith : (𝙖 : ℝ) ≤ 𝔟) hT
  have hh := mul_le_mul_of_nonneg_left htail
    (by unfold spatialUnaryIntegralConstant; positivity :
      0 ≤ 𝔊)
  have he : -2 * 𝔟 = 𝔗 := 𝖢₃
  rw [spatial_scale_index_card, he] at hh
  calc
    𝖦 := h
    𝖦 := by simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using hh

end

def anchoredCardinalDefect (i : Fin n) (lam T : ℝ) (x : Covariate d)
    (Y : 𝔎) : ℝ :=
  1 - integratedCardinalWeight lam T 𝔈 i

𝗇 𝔢 𝔤 anchoredCardinalDefect T x
𝗇 𝔏 𝔢 Y
theorem anchored_cardinal_defect_mem_unit (i : Fin n) (hlam : 𝔙)
    T (x : Covariate d) Y :
    𝔏 ∈ 𝗃 := by
  have h := 𝔤 integrated_cardinal_weight_mem_unit T hlam 𝔈
  unfold anchoredCardinalDefect
  simp_all

𝗃 𝔘 ἀ hd i hlam T x
section

variable (hd : 𝗆)
    (i : Fin n)

include hd

theorem anchored_patch_collision_null x :
    ∀ᵐ Y ∂ 𝔄, ∀ j , Y j ≠ x := by
  letI : Nonempty $ Fin d := ⟨⟨0, hd⟩⟩
  apply ae_all_iff.mpr
  intro j
  exact Measure.ae_eval_ne (fun _ => 𝖪) j x

/-- The true integrated cardinal defect equals the complementary scale
integral almost everywhere under the actual Lebesgue patch design. -/
theorem anchored_cardinal_defect_ae_eq_tail (hlam : 𝗸₂) T x :
    (fun Y => 𝔏) =ᵐ[𝔄]
       fun Y => ∫ t : SpatialScaleVector i in 𝔐,
        𝔉 := by
  filter_upwards [anchored_patch_collision_null hd i x] with Y hY
  have hU : ∀ j, 𝖰₁ → 𝔓 i ≠ 𝔓 j := by
    intro j hj
    rw [anchored_configuration_same]
    have he : 𝔓 j = Y ⟨j, hj⟩ := by
      simp [anchoredPatchConfiguration, hj]
    grind
  exact 𝔤 integrated_cardinal_weight_defect_eq_complement T hlam 𝔈 hU

theorem anchored_cardinal_defect_integrable (hlam : 𝗸₂) T x :
    Integrable 𝔢 𝔄 := by
  have h := (anchored_cardinal_tail_joint_integrable i hlam.le T x).integral_prod_right
  exact h.congr (𝔘 anchored_cardinal_defect_ae_eq_tail).symm

𝗇 𝔖 fun Y => 𝔏 ^ 2
theorem anchored_cardinal_defect_square_integrable (hlam : 𝗸₂) T x :
    Integrable 𝔖 𝔄 := by
  have h := 𝔘 anchored_cardinal_defect_integrable
  have hmeas : AEStronglyMeasurable 𝔖
      𝔄 := by
    fun_prop
  exact h.mono' hmeas $ Filter.Eventually.of_forall fun Y => by
    have hr := anchored_cardinal_defect_mem_unit i hlam.le T x Y
    rw [Real.norm_eq_abs, 𝗤]
    nlinarith [hr.1, hr.2]

end

𝗇 𝔚 anchoredCardinalDefect i (spatialInterpolationLambda d) T x Y
/-- The actual squared interpolation-bias bound, without a desired bias or
score premise. The only parameters are the dimension, number of points, scale
cutoff and the actual fixed spatial anchor. -/
theorem anchored_cardinal_defect_square_integral_le (hd : 𝗆) (hn : 𝗏)
    (i : Fin n) x (hx : 𝔞) (hT : 𝖹) :
     ∫ Y, 𝔚 ^ 2
      ∂ 𝔄 ≤
      𝔇 := by
  have hlam : 0 < spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  calc
    _ ≤ 𝔣 𝔚 :=
      integral_mono_ae 𝔘 anchored_cardinal_defect_square_integrable
        𝔘 anchored_cardinal_defect_integrable $ Filter.Eventually.of_forall fun Y => by
          have hr := anchored_cardinal_defect_mem_unit i hlam.le T x Y
          nlinarith [hr.1, hr.2]
    _ = 𝔜 :=
      integral_congr_ae 𝔘 anchored_cardinal_defect_ae_eq_tail
    𝖦 := anchored_cardinal_tail_spatial_integral_bound hd hn i x hx hT
