module

public import NearlyMinimax.SpatialLaplaceTail
public import NearlyMinimax.CardinalProductDesign
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Genuine bounded-domain pair integration of the actual fine-alias
Laplace kernel, including the real Fin2 product coordinate law. -/
𝚫
𝚪
𝚨
𝚩
𝚰

𝗇 𝔈 𝖮
/-- A nonnegative whole-space kernel with a uniform true section bound has
an actual finite-domain product integral bound. -/
theorem finite_pair_kernel_integrable_and_integral_le
    [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ ≤ ν) f (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) K
    (hi : ∀ x, Integrable (fun y => f 𝔈) ν)
    (hb : ∀ x, ∫ y, f 𝔈 ∂ν ≤ K) :
    Integrable f (μ.prod μ) ∧ ∫ z, f z ∂μ.prod μ ≤ μ.real univ * K := by
  have hsection x := (hi x).mono_measure hμ
  have hsectionBound x :=
    (integral_mono_measure hμ (Filter.Eventually.of_forall fun y => hn 𝔈) $ hi x ).trans $ hb x
  have hinner : Integrable (fun x => ∫ y, ‖f 𝔈‖ ∂μ) μ := by
    apply (integrable_const K).mono' hm.norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg $ integral_nonneg fun _ => norm_nonneg _ ]
    simp_rw [Real.norm_eq_abs, abs_of_nonneg $ hn _ ]
    exact hsectionBound x
  have hf :=
    (integrable_prod_iff hm.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hsection, hinner⟩
  refine ⟨hf, ?_⟩
  rw [integral_prod _ hf]
  simpa only [integral_const, smul_eq_mul] using
    integral_mono hf.integral_prod_left (integrable_const K) hsectionBound

𝗇 𝔄 𝖪
𝗇 𝔍 T0^𝗗₁
𝗇 𝔅 6 * 𝖥 * spatialInverseFourConstant d / 𝔍
𝗇 𝔉 fineAliasLaplaceKernel T0 N (exactEuclideanDistance xy.1 xy.2) ^2
𝗇 𝔊 (𝔄).prod 𝔄
/-- Actual Wfi² integration over the two source cube points. -/
theorem fineAlias_spatial_pair_squared_integrable_and_integral_le (hd : 4 < d)
    (hT0 : 0 < T0) (hN : 𝖽₂) :
    Integrable (fun xy =>
      𝔉)
      𝔊 ∧
     ∫ xy : 𝙩,
      𝔉
      ∂𝔊 ≤
      𝔅 := by
  have hm := ((fineAliasLaplaceKernel_measurable T0 N hN).comp
    (exactEuclideanDistance_continuous (d := d)).measurable).pow_const 2
  have h := finite_pair_kernel_integrable_and_integral_le volume 𝔄
    Measure.restrict_le_self _ hm 𝖸 (6*spatialInverseFourConstant d/𝔍)
    (fun x => (fineAlias_spatial_squared_integrable_and_integral_le hd hT0 hN x).1)
     fun x => (fineAlias_spatial_squared_integrable_and_integral_le hd hT0 hN x).2
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [measureReal_def, Measure.restrict_apply_univ]
  change 𝗮₁ * _ = _
  rw [spatialPatchBox_real_volume]
  ring

𝗇 𝔇 fineAliasLaplaceKernel T0 N 𝙹 ^2
/-- The same genuine fine-alias estimate in the paper's Fin2 tuple coordinates. -/
theorem fineAlias_fullSpatialPatchDesign_squared_integrable_and_integral_le (hd : 4 < d)
    (hT0 : 0 < T0) (hN : 𝖽₂) :
    Integrable (fun U =>
      𝔇)
      𝗿₂ ∧
     ∫ U : 𝖿₁,
      𝔇
      ∂𝗿₂ ≤
      𝔅 := by
  have h := fineAlias_spatial_pair_squared_integrable_and_integral_le hd hT0 hN
  have hp := measurePreserving_finTwoArrow 𝔄
  refine ⟨?_, ?_⟩
  · exact hp.integrable_comp_of_integrable h.1
  · exact (hp.integral_comp MeasurableEquiv.finTwoArrow.measurableEmbedding _).trans_le h.2
