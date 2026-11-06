module

public import NearlyMinimax.ExponentialSpatialKernels
public import Mathlib.Probability.Independence.Integration
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual independent spatial-coordinate projections and pair integrations. -/
𝚴
𝚳
𝚨
𝚩
𝚰

𝗇 𝔒 fun _ => π
𝗇 𝔄 Measure.pi 𝔒
𝗇 𝔇 Measure.pi fun _ : J => π
𝗇 𝔊 J → E
𝗇 𝔍 fun j U => U j
𝗇 𝔐 fun _ => aemeasurable_id
𝗃 𝔙 fun i => ἀ $ e i
/-- Actual projection onto any distinct finite spatial coordinates preserves the true independent law. -/
theorem spatialPi_projection_preserving [Fintype I] [Fintype J]
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] (e : I ↪ J) :
    MeasurePreserving (fun U : 𝔊 => 𝔙 U)
      𝔄 𝔄 := by
  have hc : iIndepFun 𝔍 𝔇 :=
    iIndepFun_pi 𝔐
  have hs := iIndepFun.precomp e.injective hc
  refine ⟨ measurable_pi_iff.mpr 𝔙 measurable_pi_apply , ?_⟩
  simpa only [(measurePreserving_eval 𝔒 _).map_eq] using (iIndepFun_iff_map_fun_eq_pi_map fun i => (measurable_pi_apply $ e i ).aemeasurable ).mp hs

/-- Scaling each genuine finite coordinate measure scales its product by the cardinal power. -/
theorem spatialPi_const_smul [Fintype J] [MeasurableSpace E]
    (π : Measure E) [SigmaFinite π] (c : 𝙉₁) [SigmaFinite $ c • π ] :
    Measure.pi (fun _ => c • π) = c^ Fintype.card J • 𝔇 := by
  classical
  apply Measure.pi_eq
  intro S hS
  rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

𝗇 𝔏 𝘹₁
/-- The actual uniform probability law on the source local cube. -/
def spatialPatchProbability (d : ℕ) : 𝔏 :=
  ((2 : 𝙉₁)^d)⁻¹ • 𝖪

instance spatialPatchProbability_isProbability (d : ℕ) : IsProbabilityMeasure $ spatialPatchProbability d := by
  constructor
  rw [spatialPatchProbability, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ, spatialPatchBox_volume]
  exact ENNReal.inv_mul_cancel  𝖠₃  $ by finiteness

theorem spatialPatchProbability_le_volume d : spatialPatchProbability d ≤ volume := by
  intro S
  exact (mul_le_of_le_one_left zero_le $ ENNReal.inv_le_one.mpr $ one_le_pow₀ 𝖠₄ ).trans $ Measure.restrict_le_self S

𝗇 𝔑 (U i, U j)
𝗃 𝔘 fun U : 𝔊 => ἀ
/-- Actual distinct-coordinate pair evaluation preserves the true independent product law. -/
theorem spatialPi_pair_preserving [Fintype J] [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] i j (hij : 𝘚₁) :
    MeasurePreserving 𝔘 𝔑
      𝔄 $ π.prod π := by
  classical
  let e : Fin 2 ↪ J := ⟨![i,j], by
    simpa⟩
  convert (measurePreserving_finTwoArrow π).comp $ spatialPi_projection_preserving π e using 1
  funext U
  simp [e]

/-- Genuine integration through an actual pair projection. -/
theorem spatialPi_pair_integral [Fintype J] [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] i j (hij : 𝘚₁)
    (F : 𝖸₂ → ℝ) (hF : Measurable F) :
     ∫ U : 𝔊, F 𝔑 ∂𝔄 = ∫ z, F z ∂π.prod π := by
  have hp := spatialPi_pair_preserving π i j hij
  exact (integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable).symm.trans
    $ congrArg (fun μ => ∫ z, F z ∂μ) hp.map_eq

𝗇 𝔅 𝚈₁
𝗇 𝔎 ∫ xy : 𝙩, 𝔅 ∂π.prod π
/-- A true probability spatial law dominated by volume has the dimension-scaled pair exponential integral. -/
theorem spatial_probability_pair_exponential_integral_le (hd : 𝗆)
    (π : 𝔏) [IsProbabilityMeasure π] (hπ : π ≤ volume)
    (hT : 𝗹₁) :
    𝔎 ≤
      spatialExponentialConstant d / T^d := by
  have hm :=
    (exactEuclideanDistance_continuous (d := d) |>.const_mul T |>.neg |>.rexp).measurable
  have hi : Integrable (fun xy =>
      𝔅) $ π.prod π :=
    Integrable.of_bound hm.aestronglyMeasurable 1 $ Filter.Eventually.of_forall fun xy => by
      rw [Real.norm_eq_abs, 𝚖]
      exact Real.exp_le_one_iff.mpr $ neg_nonpos.mpr $ mul_nonneg hT.le $ exactEuclideanDistance_nonneg ..
  rw [integral_prod _ hi]
  have hb x :=
    (integral_mono_measure hπ (Filter.Eventually.of_forall fun _ => 𝙫)
      $ exactEuclideanDistance_exponential_integrable hd hT x ).trans_eq
        $ exactEuclideanDistance_exponential_integral hd hT x
  simpa only [integral_const, probReal_univ, one_smul] using
    integral_mono hi.integral_prod_left (integrable_const _) hb

𝗇 𝔓 U $ q 0
𝗇 𝔔 U $ q 1
𝗇 𝔈 F (𝔓, 𝔔)
𝗇 𝔖 U $ q 2
𝗇 𝔗 U $ q 3
𝗇 𝔉 F (𝔖, 𝔗)
/-- Genuine factorization of functions of two disjoint iid coordinate pairs. -/
theorem spatialPi_two_pair_functions_factor [Fintype J] [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (q : Fin 4 ↪ J)
    (F : 𝖸₂ → ℝ) (hF : Measurable F) :
     ∫ U : 𝔊, 𝔈 * 𝔉
      ∂𝔄 = (∫ xy, F xy ∂π.prod π)^2 := by
  have hc : iIndepFun 𝔍 𝔇 :=
    iIndepFun_pi 𝔐
  have hne i j (h : 𝘚₁) := fun he => h $ q.injective he
  have hind0 := hc.indepFun_prodMk_prodMk measurable_pi_apply
    (q 0) (q 1) (q 2) (q 3)
    (hne 0 2 𝖨₃ ) (hne 0 3 𝖨₃ )
    (hne 1 2 𝖨₃ ) $ hne 1 3 𝖨₃
  have hind := hind0.comp hF hF
  have hfm : Measurable 𝔘 𝔈 :=
    hF.comp $ (measurable_pi_apply $ q 0 ).prodMk $ measurable_pi_apply $ q 1
  have hgm : Measurable 𝔘 𝔉 :=
    hF.comp $ (measurable_pi_apply $ q 2 ).prodMk $ measurable_pi_apply $ q 3
  have he := hind.integral_mul_eq_mul_integral hfm.aestronglyMeasurable hgm.aestronglyMeasurable
  simp at he
  rw [spatialPi_pair_integral π (q 0) (q 1) (hne 0 1 𝖨₃ ) F hF,
    spatialPi_pair_integral π (q 2) (q 3) (hne 2 3 𝖨₃ ) F hF] at he
  linarith

𝗃 𝔚 -(T*ἀ)
/-- Exact independence of the two actual disjoint spatial exponential pair kernels. -/
theorem spatialPi_two_pairs_integral_factor [Fintype J]
    (π : 𝔏) [IsProbabilityMeasure π]
    (q : Fin 4 ↪ J) T :
     ∫ U : J → Covariate d,
      Real.exp (-(T * (exactEuclideanDistance 𝔓 𝔔 +
        exactEuclideanDistance 𝔖 𝔗))) ∂𝔄 =
      𝔎^2 := by
  have hpair : Measurable fun xy : 𝙩 => 𝔅 :=
    (exactEuclideanDistance_continuous |>.const_mul T |>.neg |>.rexp).measurable
  have he := spatialPi_two_pair_functions_factor π q _ hpair
  simp_rw [← Real.exp_add] at he
  simp_rw [show ∀ a b , 𝔚 a + 𝔚 b = 𝔚 𝗓₁ by intros; ring] at he
  exact he
