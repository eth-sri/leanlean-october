module

public import NearlyMinimax.CardinalScaleVolume
public import NearlyMinimax.GaussianTensorCost
public import NearlyMinimax.FiniteTensorPolynomialMoments
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual tensor Gaussian and compact-scale separated representation of the
integrated spatial cardinal covariance. -/
𝛄
𝚨
𝚩
𝚱

𝗇 𝔑 𝙇
𝗇 𝔢 Finset.prod_subtype (p := fun j => 𝖰₁) $ Finset.univ.erase i
𝗃 𝔵 ἀ $ U i
theorem spatial_cardinal_polynomial_scale_product i (U : 𝔑) :
    spatialCardinalPolynomial U i = ∏ j : SpatialScaleIndex i, 𝔵 spatialCardinalAffine (U j.val) := by
  unfold spatialCardinalPolynomial
  rw [𝔢
     fun j => by simp fun j => 𝔵 spatialCardinalAffine $ U j ]

𝗇 𝔭 𝘒₁
𝗃 𝕮 ἀ j * lam ^ 2
theorem spatial_cardinal_scale_product i lam
    (U : 𝔑) t :
    spatialCardinalScale lam 𝔭 U i =
      ∏ j : SpatialScaleIndex i, 𝕮 t *
        Real.exp (-(𝘺₂ * 𝔵 spatialSquaredDistance (U j.val))) := by
  unfold spatialCardinalScale
  rw [𝔢
     fun j => by simp fun j => 𝕮 𝔭 *
      Real.exp (-(𝔭 j * lam * 𝔵 spatialSquaredDistance (U j))) ]
  apply Finset.prod_congr rfl
  intro j _
  simp only [spatialScaleExtend, dite_eq_left j.property]

𝗃 𝕱 ἀ (x j) $ y j
𝗇 𝔈 𝕮 t * Real.exp (-(𝘺₂ * 𝕱 spatialSquaredDistance))
𝗇 𝔊 gaussianTensorObservable lam t x y e * gaussianTensorAmplitude lam e β β'
𝗃 𝔶 ἀ lam $ t j
𝗇 𝔍 𝔶 gaussianPrimitiveLeft e (x j) * 𝔶 gaussianPrimitiveRight e (y j)
𝗇 𝔒 𝕱 spatialCardinalAffine
𝗇 𝔨 polynomialPairMoment (w j) (P j) (P' j) b b'
𝗇 𝔓 𝔨
𝗇 𝔫 𝖺
𝗇 𝔮 (∏ j, 𝔒).coeff
𝗃 𝔷 fun e => ἀ
/-- Tensorization of the actual primitive Gaussian coefficient moments. -/
theorem gaussian_tensor_cardinal_moments [Fintype κ]
    (lam : ℝ) (hlam : 𝔫) (t : 𝖱₁) (ht : ∀ j, 𝖥₂)
    (x y : κ → Covariate d) β β' :
    Integrable 𝔷 𝔊 (gaussianTensorMeasure κ d) ∧
       ∫ e, 𝔊
        ∂gaussianTensorMeasure κ d =
        (∏ j, 𝔈) *
          𝔮 β *
          𝔮 β' := by
  let w := fun j e =>
    𝔍 *
      gaussianPrimitiveScalar d lam e
  let P := fun (_j : κ) (e : GaussianPrimitiveMark d) => gaussianAffinePolynomial e.2.1.1 e.2.2.1.1
  let P' := fun (_j : κ) (e : GaussianPrimitiveMark d) => gaussianAffinePolynomial e.2.1.2 e.2.2.1.2
  let p := fun j => 𝔒
  let a := fun j => 𝔈
  have hpair j b b' :
      𝔓 =
        fun e => 𝔍 *
          gaussianPrimitiveAmplitude lam e b b' := by
    funext e
    dsimp [w, polynomialPairMoment, gaussianPrimitiveAmplitude, gaussianPrimitiveScalar]
    ring
  have hi j b b' :
      Integrable 𝔓 $ gaussianPrimitiveMeasure d := by
    rw [hpair]
    exact 𝔶 gaussianPrimitive_observable_integrable (x j) (y j) b b'
  have he j b b' :
       ∫ e, 𝔨 e ∂gaussianPrimitiveMeasure d =
        a j * (p j).coeff b * (p j).coeff b' := by
    rw [hpair]
    exact (𝔶 gaussianPrimitive_separated_exact hlam (ht j) (x j) (y j) b b').symm
  have h := tensorPolynomialPairMoment_fintype_integral (gaussianPrimitiveMeasure d)
    w P P' p p a hi he β β'
  have hfun : tensorPolynomialPairMoment_fintype w P P' β β' =
      𝔷 𝔊 := by
    funext e
    unfold tensorPolynomialPairMoment_fintype gaussianTensorObservable gaussianTensorAmplitude
      gaussianTensorScalar gaussianTensorLeftPolynomial gaussianTensorRightPolynomial gaussianPolynomialProduct
    rw [Finset.prod_mul_distrib]
    ring
  aesop

𝗃 𝕯 ἀ (SpatialScaleIndex i) d
𝗇 𝔜 𝕯 GaussianTensorMark
/-- Genuine scale-and-Gaussian mark space for a fixed cardinal center. -/
abbrev CenteredCardinalMark (d n : ℕ) (i : Fin n) :=
  SpatialScaleVector i × 𝔜

𝗇 𝔇 𝕯 gaussianTensorMeasure
𝗇 𝔎 CenteredCardinalMark d n i
𝗇 𝔞 spatialScaleMeasure i T
def centeredCardinalMeasure (i : Fin n) (d : ℕ) (T : ℝ) :
    Measure 𝔎 :=
  (𝔞).prod 𝔇

𝗇 𝔔 𝙮
def centeredCardinalAmplitude (i : Fin n) (lam : ℝ)
    (z : 𝔎) : 𝔔 → 𝔔 → ℝ :=
  gaussianTensorSymmetricAmplitude lam z.2

𝗇 𝔏 ⟨l, h⟩
𝗃 𝕰 ἀ lam (z.1 j) $ z.2 j
𝗇 𝔥 𝕰 gaussianPrimitiveLeft
/-- Each observation receives one bounded spatial factor. The distinguished
observation receives the product of the left factors. -/
def centeredCardinalFactor (i : Fin n) (lam : ℝ)
    (z : 𝔎) (l : Fin n) (x : Covariate d) : ℝ :=
  if h : l ≠ i then gaussianPrimitiveRight lam (z.1 𝔏) (z.2 𝔏) x
    else ∏ j : SpatialScaleIndex i, 𝔥 x

𝗇 𝔡 𝖢
𝗃 𝔪 ἀ i lam
𝗇 𝔦 𝔪 centeredCardinalFactor z
theorem centered_cardinal_factor_abs_le_one i lam
    z (l : Fin n) (x : Covariate d) (hx : ∀ r, |x r| ≤ 2) :
    |𝔦 l x| ≤ 1 := by
  unfold centeredCardinalFactor
  split_ifs
  · exact gaussianPrimitiveRight_bound lam _ _ x hx
  · rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _j : SpatialScaleIndex i, 1 :=
        Finset.prod_le_prod₀ 𝔡 fun j _ => gaussianPrimitiveLeft_bound lam _ _ x
      𝘿 := 𝖢₄

𝗇 𝔧 (measurable_pi_apply (𝔏 : SpatialScaleIndex i)).comp
theorem centered_cardinal_factor_measurable i lam
    (l : Fin n) x :
    Measurable fun z : 𝔎 => 𝔦 l x := by
  unfold centeredCardinalFactor
  split_ifs with h
  · have hm : Measurable fun z : 𝔎 => (z.1 𝔏, z.2 𝔏) :=
       (𝔧 measurable_fst).prodMk
        $ 𝔧 measurable_snd
    have hh := (gaussianPrimitiveRight_scale_measurable lam x).comp hm
    assumption
  · apply Finset.measurable_fun_prod
    intro j _
    have hm : Measurable fun z : 𝔎 => (z.1 j, z.2 j) :=
       (𝗹₂ measurable_fst).prodMk
        $ 𝗹₂ measurable_snd
    have hh := (gaussianPrimitiveLeft_scale_measurable lam x).comp hm
    assumption

𝗇 𝔉 centeredCardinalMeasure i d T
𝗇 𝔐 centeredCardinalAmplitude (D := D) i lam
𝗇 𝔖 𝔪 centeredCardinalAmplitude z β β'
𝗇 𝔗 𝕯 gaussianTensorMeasure_finite
𝗇 𝔟 𝖹
𝗇 𝔤 ∫ z, separatedMatrixCost 𝔐 z ∂ 𝔉
𝗃 𝔩 ἀ (κ := SpatialScaleIndex i) (d := d) (D := D) lam
𝗇 𝔯 spatial_scale_measure_finite i T hT
section

𝛔

include i

𝗇 𝔬 fun z => 𝔖
theorem centered_cardinal_amplitude_measurable lam
    (β β' : 𝔔) :
    Measurable 𝔬 :=
  (gaussianTensorSymmetricAmplitude_measurable lam β β').comp measurable_snd

theorem centered_cardinal_measure_finite d (hT : 𝔟) :
    IsFiniteMeasure 𝔉 := by
  letI := 𝔯
  letI := 𝔗
  unfold centeredCardinalMeasure
  infer_instance

theorem centered_cardinal_cost_integrable lam
    (hT : 𝔟) :
    Integrable (separatedMatrixCost 𝔐)
      𝔉 := by
  letI := 𝔯
  letI := 𝔗
  have h := (integrable_const 1 (μ := 𝔞)).mul_prod
    𝔩 gaussianTensorSymmetricAmplitude_cost_integrable
  aesop

theorem centered_cardinal_entry_integrable lam
    (hT : 𝔟) (β β' : 𝔔) :
    Integrable 𝔬 𝔉 :=
  separatedMatrix_entry_integrable _ _ 𝔪 centered_cardinal_amplitude_measurable
    (𝔪 centered_cardinal_cost_integrable hT) β β'

𝗇 𝔠 gaussianTensorSymmetricAmplitude (D := D) lam
theorem centered_cardinal_cost_integral_eq lam T :
    𝔤 =
      volume.real 𝗕₁ *
         ∫ e, separatedMatrixCost 𝔠 e ∂ 𝔇 := by
  letI := 𝔗
  letI : SFinite 𝔞 := by unfold spatialScaleMeasure; infer_instance
  have h := integral_prod_mul (μ := 𝔞)
    (ν := 𝔇) 𝙃
    $ separatedMatrixCost 𝔠
  simp at h
  simpa only [centeredCardinalMeasure, centeredCardinalAmplitude, separatedMatrixCost,
    spatialScaleMeasure, Measure.real, Measure.restrict_apply_univ] using h

end

/-- Actual representation cost, obtained from the actual Gaussian tensor
moment cost and actual logarithmic scale-domain volume. -/
theorem centered_cardinal_cost_integral_le (hn : 𝗏) (i : Fin n) lam
    (hT : 𝔟) :
    𝔤 ≤
      (1024 * |lam| * 𝙷₁) ^ 𝗈 * 𝖫₁ * 𝗶 ^ 𝗥 := by
  rw [centered_cardinal_cost_integral_eq]
  have hcost := 𝔩 gaussianTensorSymmetricAmplitude_integrated_cost
  rw [spatial_scale_index_card] at hcost
  have hvol := spatial_scale_domain_volume_le_uniform hn i hT
  have hlog := Real.log_nonneg hT
  have h := mul_le_mul hvol hcost (integral_nonneg fun e => Finset.sum_nonneg 𝗺₂ ) $ by positivity
  convert h using 1
  rw [show 1024 * |lam| * 𝙷₁ = 2 * (512 * |lam| * 𝙷₁) by ring, mul_pow]
  ring

𝗇 𝔱 𝔪 centeredCardinalFactor z l $ U l
𝗇 𝔅 ∏ l, 𝔱
𝗇 𝔘 fun l => 𝔱
𝗇 𝔳 fun _ => U i
𝗇 𝔙 𝔳
𝗇 𝔴 fun j => U j.val
𝗇 𝔚 𝔴
theorem centered_cardinal_factor_product i lam
    z (U : 𝔑) :
    𝔅 =
      gaussianTensorObservable lam z.1 𝔙 𝔚 z.2 := by
  rw [← Finset.mul_prod_erase Finset.univ
    𝔘 $ Finset.mem_univ i ]
  have he : 𝔦 i (U i) =
      ∏ j : SpatialScaleIndex i, 𝔵 𝔥 := by
    simp [centeredCardinalFactor]
  rw [he]
  rw [Finset.prod_subtype (p := fun l => l ≠ i) (Finset.univ.erase i)
     fun l => by simp 𝔘]
  have hr : ∏ j : SpatialScaleIndex i, 𝔦 j.val (U j.val) =
      ∏ j : SpatialScaleIndex i, 𝕰 gaussianPrimitiveRight (U j.val) := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [centeredCardinalFactor, dite_eq_left j.property]
  rw [hr, ← Finset.prod_mul_distrib]
  rfl

𝗇 𝔄 gaussianTensorObservable lam t 𝔳 𝔴 e
𝗇 𝔣 𝔄 * gaussianTensorFrameAmplitude lam e β β'
𝗇 𝔰 𝘩₁
theorem centered_cardinal_raw_tensor_integrable i lam (hlam : 𝔫)
    (t : SpatialScaleVector i) (ht : 𝔰) (U : 𝔑) (β β' : 𝔔) :
    Integrable 𝔷 𝔣 𝔇 :=
  (gaussian_tensor_cardinal_moments lam hlam t ht
    𝔙 𝔚 ..).1

section

𝛔

𝗇 𝔛 𝔪 spatialCenteredCardinalMatrix U t β β'
𝗃 𝕭 ∫ e : 𝔜, ἀ ∂ 𝔇 = 𝔛
theorem centered_cardinal_raw_tensor_exact (lam : ℝ) (hlam : 𝔫)
    (t : SpatialScaleVector i) (ht : 𝔰) U (β β' : 𝔔) :
    𝕭 𝔣 := by
  have h := (gaussian_tensor_cardinal_moments lam hlam t ht
    𝔙 𝔚 (polynomialBoxExponent β.val) $ polynomialBoxExponent β'.val ).2
  simpa only [gaussianTensorFrameAmplitude, gaussianTensorAmplitude, spatialCenteredCardinalMatrix, highFrameCoefficients,
    spatial_cardinal_scale_product, spatial_cardinal_polynomial_scale_product] using h

𝗇 𝔲 𝔄 * gaussianTensorSymmetricAmplitude lam e β β'
𝗃 𝕬 𝔪 ἀ hlam t ht U
theorem centered_cardinal_symmetric_tensor_exact lam (hlam : 𝔫)
    (t : SpatialScaleVector i) (ht : 𝔰) U (β β' : 𝔔) :
    𝕭 𝔲 := by
  have he : 𝔷 𝔲 =
      fun e => (𝔣 +
        𝔄 *
        gaussianTensorFrameAmplitude lam e β' β) / 2 := by
    funext e
    unfold gaussianTensorSymmetricAmplitude realMatrixSymmetrize
    ring
  rw [he, integral_div, integral_add
    (𝕬 centered_cardinal_raw_tensor_integrable β β')
    $ 𝕬 centered_cardinal_raw_tensor_integrable β' β ,
    𝕬 centered_cardinal_raw_tensor_exact β β',
    𝕬 centered_cardinal_raw_tensor_exact β' β]
  unfold spatialCenteredCardinalMatrix
  ring

theorem centered_cardinal_product_entry_integrable (lam : ℝ)
    (hT : 𝔟) (U : 𝔑) (hU : ∀ l r, |𝚚₂| ≤ 2)
    (β β' : 𝔔) :
    Integrable (fun z => 𝔅 *
      𝔖) 𝔉 := by
  have hm : Measurable fun z => 𝔅 :=
    Finset.measurable_fun_prod _ fun l _ => 𝔪 centered_cardinal_factor_measurable l $ U l
  have hb : ∀ z : 𝔎, |𝔅| ≤ 1 := by
    intro z
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _l : Fin n, 1 := Finset.prod_le_prod₀ 𝔡
         fun l _ => 𝔪 centered_cardinal_factor_abs_le_one z l (U l) $ hU l
      𝘿 := 𝖢₄
  have h := (𝔪 centered_cardinal_entry_integrable hT β β').mul_bdd hm.aestronglyMeasurable
    $ Filter.Eventually.of_forall fun z => 𝖥₄
  grind

/-- Exact positive separated representation of each centered, scale-integrated
term of the genuine cardinal covariance. -/
theorem centered_cardinal_integrated_separated_exact lam (hlam : 𝔫) (hT : 𝔟) U
    (hU : ∀ l r, |𝚚₂| ≤ 2) (β β' : 𝔔) :
     ∫ t, 𝔛 ∂ 𝔞 =
      ∫ z, 𝔅 * 𝔖
        ∂ 𝔉 := by
  letI := 𝔯
  letI := 𝔗
  symm
  rw [centeredCardinalMeasure, integral_prod _ $ 𝔪 centered_cardinal_product_entry_integrable hT U hU β β' ]
  apply integral_congr_ae
  filter_upwards [ ae_restrict_mem 𝘻₂ ] with t ht
  simp_rw [centered_cardinal_factor_product]
  exact 𝔪 centered_cardinal_symmetric_tensor_exact hlam t ht.1 U β β'
