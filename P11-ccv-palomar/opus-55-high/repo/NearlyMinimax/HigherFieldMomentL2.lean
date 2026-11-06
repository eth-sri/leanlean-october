module

public import NearlyMinimax.BoundedHyperplaneField
public import NearlyMinimax.SpatialLaplaceTail
public import NearlyMinimax.SpatialPairProductIntegration
public import Mathlib.Algebra.Order.Chebyshev
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual spatial L² moments of the constructed bounded hyperplane field.
The estimate derives from its fair-sign occupancy law and genuine independent
spatial-coordinate integration. -/
𝚴
𝚮
𝚨
𝚩
𝚰

𝗇 𝔅 𝗲₂
𝗇 𝔘 ∏ l, boundedHyperplaneFieldValue z (U l)
𝗃 𝔦 ἀ d T
def boundedHyperplaneSpatialMoment (d : ℕ) (T : ℝ) (j : ℕ)
    (U : 𝔅) : ℝ :=
  ∫ z, 𝔘 ∂𝔦 boundedHyperplaneFieldLaw

𝗇 𝔄 𝔦 boundedHyperplaneSpatialMoment j U
section

variable (d : ℕ)
    [NeZero d]
    (T)
    (j)

theorem boundedHyperplaneSpatialMoment_measurable :
    Measurable $ 𝔦 boundedHyperplaneSpatialMoment j := by
  have hm : Measurable fun Uz : 𝔅 × partitionFieldMark 𝚛 =>
      ∏ l, boundedHyperplaneFieldValue Uz.2 (Uz.1 l) :=
    Finset.measurable_prod _ fun l _ =>
      (boundedHyperplaneFieldValue_measurable d).comp
        $ measurable_snd.prodMk $ (measurable_pi_apply l).comp measurable_fst
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem boundedHyperplaneSpatialMoment_abs_le_one U :
    |𝔄| ≤ 1 := by
  calc
    _ ≤ ∫ z, |𝔘| ∂𝔦 boundedHyperplaneFieldLaw :=
      abs_integral_le_integral_abs
    𝚘₂ := by simp only [Finset.abs_prod, boundedHyperplaneFieldValue_abs,
      Finset.prod_const_one, integral_const, probReal_univ, smul_eq_mul, one_mul]

end

𝗇 𝔡 U $ q.val 0
𝗇 𝔢 U $ q.val 1
𝗇 𝔒 exactEuclideanDistance 𝔡 𝔢
𝗇 𝔣 U $ q.val 2
𝗇 𝔤 U $ q.val 3
𝗇 𝔓 exactEuclideanDistance 𝔣 𝔤
def spatialQuadDistance (q : CellMomentQuadruple j)
    (U : 𝔅) : ℝ :=
  𝔒 +
    𝔓

𝗃 𝔧 ἀ q U
theorem spatialQuadDistance_nonneg q
    (U : 𝔅) : 0 ≤ 𝔧 spatialQuadDistance :=
  add_nonneg (exactEuclideanDistance_nonneg ..) $ exactEuclideanDistance_nonneg ..

𝗃 𝔨 fun U : 𝔅 => ἀ
theorem spatialQuadDistance_continuous (q : CellMomentQuadruple j) :
    Continuous $ spatialQuadDistance (d := d) q := by
  have hm01 : Continuous fun U : 𝔅 => (𝔡, 𝔢) :=
    (continuous_apply $ q.val 0 ).prodMk $ continuous_apply $ q.val 1
  have hm23 : Continuous fun U : 𝔅 => (𝔣, 𝔤) :=
    (continuous_apply $ q.val 2 ).prodMk $ continuous_apply $ q.val 3
  have h01 : Continuous 𝔨 𝔒 := by
    simpa only [Function.comp_def] using (exactEuclideanDistance_continuous ).comp hm01
  have h23 : Continuous 𝔨 𝔓 := by
    simpa only [Function.comp_def] using (exactEuclideanDistance_continuous ).comp hm23
  exact h01.add h23

theorem spatialPatchBox_eq_hyperplaneCube d :
    spatialPatchBox d = hyperplaneCube d := by
  ext x
  simp only [spatialPatchBox, mem_Icc, Pi.le_def, hyperplaneCube]
  grind

theorem spatialPatchProbability_ae_cube d :
    ∀ᵐ x ∂spatialPatchProbability d, x ∈ hyperplaneCube d := by
  rw [spatialPatchProbability, ← spatialPatchBox_eq_hyperplaneCube]
  exact (ae_restrict_mem measurableSet_Icc).filter_mono $ Measure.ae_smul_measure_le _

𝗇 𝔊 Measure.pi fun _ : Fin j => spatialPatchProbability d
/-- The true independent local-cube law has every coordinate in the source cube almost surely. -/
theorem spatialPatchProbability_pi_ae_cube d j :
    ∀ᵐ U ∂ 𝔊,
      ∀ l, U l ∈ hyperplaneCube d := by
  apply ae_all_iff.mpr
  intro l
  exact (measurePreserving_eval (fun _ => spatialPatchProbability d) l).quasiMeasurePreserving.tendsto_ae.eventually
    $ spatialPatchProbability_ae_cube d

𝗇 𝔠 T^d
𝗇 𝔇 (spatialExponentialConstant d / 𝔠)^2
𝗇 𝔈 Real.exp $ -T / 2 * 𝔧 spatialQuadDistance
𝗇 𝔉 ∫ xy : 𝙩, 𝚈₁ ∂π.prod π
𝗇 𝔏 ∫ U, 𝔧 E ∂μ
𝗇 𝔖 fun q _ => hei q
𝗇 𝔙 ∑ q : CellMomentQuadruple j, 𝔈
𝗇 𝔛 a * ∑ q, 𝔧 E
𝗃 𝔥 ἀ^2
𝗇 𝔜 𝔥 𝔄
𝗇 𝔞 j^8
/-- Genuine squared higher-moment bound under normalized independent spatial coordinates. -/
theorem boundedHyperplaneSpatialMoment_squared_probability_integral_le
    (d : ℕ) [NeZero d] (T : ℝ) (hT : 𝗹₁) (j : ℕ) (hj : 𝙳₁) :
     ∫ U : 𝔅, 𝔜
      ∂ 𝔊 ≤
      𝖭₁^8 * 𝔇 := by
  classical
  let π := spatialPatchProbability d
  let μ := Measure.pi fun _ : Fin j => π
  let a : ℝ := Fintype.card $ CellMomentQuadruple j
  let E : CellMomentQuadruple j → 𝔅 → ℝ :=
    fun q U => Real.exp $ -(T * 𝔧 spatialQuadDistance)
  have hem q : Measurable $ E q :=
    (spatialQuadDistance_continuous q |>.const_mul T |>.neg |>.rexp).measurable
  have hei q : Integrable (E q) μ :=
    Integrable.of_bound (hem q).aestronglyMeasurable 1
      $ Filter.Eventually.of_forall fun U => by
        rw [Real.norm_eq_abs, 𝚖]
        exact Real.exp_le_one_iff.mpr $ neg_nonpos.mpr $ mul_nonneg hT.le 𝔧 spatialQuadDistance_nonneg
  have hmi : Integrable (fun U => 𝔜) μ :=
    Integrable.of_bound ((𝔦 boundedHyperplaneSpatialMoment_measurable j).pow_const 2).aestronglyMeasurable 1
      $ Filter.Eventually.of_forall fun U => by
        rw [Real.norm_eq_abs, 𝗤]
        nlinarith [𝔦 boundedHyperplaneSpatialMoment_abs_le_one j U, abs_nonneg 𝔄,
          sq_abs 𝔄]
  have hpoint : ∀ᵐ U ∂μ, 𝔜 ≤ 𝔛 := by
    filter_upwards [spatialPatchProbability_pi_ae_cube d j] with U hU
    have hb := 𝔦 boundedHyperplaneField_higher_moment_envelope hT.le j hj U hU
    simp_rw [← exactEuclideanDistance_eq_euclideanNorm] at hb
    change |𝔄| ≤
      𝔙 at hb
    have hs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun q => 𝔈)
    have hsq : 𝔜 ≤
        𝔥 𝔙 := by
      nlinarith [sq_abs 𝔄, abs_nonneg 𝔄]
    have heq q :
        𝔥 𝔈 = 𝔧 E := by
      rw [← Real.exp_nat_mul]
      grind
    grind
  have hpair q : 𝔏 ≤ 𝔇 := by
    rw [show 𝔏 =
        𝔥 𝔉 from
      spatialPi_two_pairs_integral_factor π ⟨q.val,q.property⟩ T]
    have hb := spatial_probability_pair_exponential_integral_le (NeZero.pos d) π (spatialPatchProbability_le_volume d) hT
    have h0 : 0 ≤ 𝔉 :=
      integral_nonneg fun _ => 𝙫
    nlinarith
  have ha : 𝖢₂ := Nat.cast_nonneg _
  have hac : a ≤ j^4 := by
    dsimp [a]
    exact_mod_cast cellMomentQuadruple_card_le j
  calc
    _ ≤ ∫ U, 𝔛 ∂μ :=
      integral_mono_ae hmi ((integrable_finsetSum _ 𝔖).const_mul a) hpoint
    _ = a * ∑ q, 𝔏 := by
      rw [integral_const_mul, integral_finsetSum _ 𝔖]
    _ ≤ a * ∑ _q : CellMomentQuadruple j, 𝔇 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => hpair q ) ha
    _ = 𝔥 a * 𝔇 := by simp ; ring
    𝖦 := by
      have hb : 𝔥 a ≤ 𝔞 := by
        nlinarith
      bound

𝗇 𝔍 (2 : 𝙉₁)^d
/-- The actual source cube volume is its volume times the genuine uniform law. -/
theorem spatialPatchVolume_eq_smulProbability d :
    𝖪 = 𝔍 • spatialPatchProbability d := by
  rw [spatialPatchProbability, smul_smul, ENNReal.mul_inv_cancel  𝖠₃  $ by finiteness , one_smul]

𝗇 𝔎 Measure.pi fun _ => 𝖪
𝗇 𝔐 d*j
𝗇 𝔗 ∫ U : 𝔅, 𝔥 𝔄 ∂ 𝔎
𝗇 𝔚 𝙉
/-- The genuine unnormalized source-cube product integral with the exact volume factor. -/
theorem boundedHyperplaneSpatialMoment_squared_cube_integral_le
    (d : ℕ) [NeZero d] T (hT : 𝗹₁) j (hj : 𝙳₁) :
    𝔗 ≤
       2 ^𝔐 * 𝔞 * 𝔇 := by
  let : IsFiniteMeasure $ 𝔍 • spatialPatchProbability d := by
    rw [← spatialPatchVolume_eq_smulProbability]
    infer_instance
  have he : 𝔎 =
      𝔍^j • 𝔊 := by
    simp only [spatialPatchVolume_eq_smulProbability]
    simpa only [Fintype.card_fin] using spatialPi_const_smul (J := Fin j) (spatialPatchProbability d) 𝗝
  rw [he, integral_smul_measure]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofNat, ← pow_mul]
  convert mul_le_mul_of_nonneg_left (𝔦 boundedHyperplaneSpatialMoment_squared_probability_integral_le hT j hj) (by positivity : 0 ≤ 𝔚^𝔐) using 1; ring

/-- A fixed dimension constant for the actual higher-moment spatial L² estimate. -/
def hyperplaneSpatialMomentConstant (d : ℕ) : ℝ :=
  𝔚^d * (1 + spatialExponentialConstant d)

theorem hyperplaneSpatialMomentConstant_positive d :
    0 < hyperplaneSpatialMomentConstant d := by
  unfold hyperplaneSpatialMomentConstant
  have := spatialExponentialConstant_nonneg d
  positivity

𝗇 𝔑 hyperplaneSpatialMomentConstant d ^j * j^4 / 𝔠
𝗇 𝔔 2*j
𝗇 𝔟 1+C
/-- The paper's higher-moment L² estimate for the genuinely constructed field,
with no spatial-moment or integral bound as a premise. -/
theorem boundedHyperplaneSpatialMoment_L2_le
    (d : ℕ) [NeZero d] T (hT : 𝗹₁) j (hj : 𝙳₁) :
    Real.sqrt 𝔗 ≤
      𝔑 := by
  let C := spatialExponentialConstant d
  have hC := spatialExponentialConstant_nonneg d
  have hV : 2^𝔐 ≤ (𝔚^d)^𝔔 := by
    rw [pow_mul]
    bound
  have hCp : 𝔥 C ≤ 𝔟^𝔔 := by
    calc 𝔥 C ≤ 𝔥 𝔟 := pow_le_pow_left₀ hC  𝖡₄  2
         𝖦 := pow_le_pow_right₀  𝖡₄  𝖡₃
  have hconstant : 2^𝔐 * 𝔥 C ≤ hyperplaneSpatialMomentConstant d ^𝔔 := by
    unfold hyperplaneSpatialMomentConstant
    rw [mul_pow]
    bound
  have hb := 𝔦 boundedHyperplaneSpatialMoment_squared_cube_integral_le hT j hj
  have hupper : 2^𝔐 * 𝔞 * (C/𝔠)^2 ≤
      𝔥 𝔑 := by
    convert mul_le_mul_of_nonneg_right hconstant $ show 0 ≤ 𝔞 / 𝔥 𝔠 by positivity using 1 <;> simp only [div_pow] <;> ring
  exact Real.sqrt_le_iff.mpr ⟨by positivity [hyperplaneSpatialMomentConstant_positive d], hb.trans hupper⟩
