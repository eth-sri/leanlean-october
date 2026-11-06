module

public import NearlyMinimax.GaussianHyperplaneGeometry
public import NearlyMinimax.GaussianProjectionMean
public import NearlyMinimax.PoissonCellMomentBounds
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The actual bounded Gaussian-hyperplane cell field: a Borel probability
law with exact exponential Euclidean covariance and vanishing odd moments. -/
𝚴
open scoped ENNReal NNReal BigOperators
𝚨
𝚩
𝚽

𝗇 𝔏 𝖩₁
theorem hyperplaneNormalizingConstant_actual d :
    hyperplaneNormalizingConstant d = 𝔏 * gaussianAbsoluteMean :=
  hyperplaneNormalizingConstant_eq d

theorem hyperplaneNormalizingConstant_pos (d : ℕ) [NeZero d] :
    0 < hyperplaneNormalizingConstant d := by
  rw [hyperplaneNormalizingConstant_actual]
  exact mul_pos (mul_pos  𝖠₄  $ Nat.cast_pos.mpr $ NeZero.pos d ) gaussianAbsoluteMean_pos

𝗇 𝔇 𝚛
def gaussianHyperplaneLaw (d : ℕ) : Measure 𝔇 :=
  (ENNReal.ofReal $ hyperplaneNormalizingConstant d )⁻¹ • gaussianHyperplaneIntensity d

𝗃 𝔐 ἀ $ gaussianHyperplaneLaw d
instance gaussianHyperplaneLaw_probability (d : ℕ) [NeZero d] :
    𝔐 IsProbabilityMeasure := by
  constructor
  rw [gaussianHyperplaneLaw, Measure.smul_apply, smul_eq_mul,
    gaussianHyperplaneIntensity_univ_ofReal]
  exact ENNReal.inv_mul_cancel (by simp [hyperplaneNormalizingConstant_pos d])
    ENNReal.ofReal_ne_top

𝗇 𝔄 𝖤₂
theorem gaussianPhase_sub (u v Z : Covariate d) :
    gaussianPhase u Z - gaussianPhase v Z = gaussianPhase 𝔄 Z := by
  simp only [gaussianPhase, sub_mul, Finset.sum_sub_distrib]

𝗇 𝔈 (gaussianHyperplaneLaw d).real
section

variable (d : ℕ)
    [NeZero d]
    (u)
    (v)

𝗇 𝔍 hyperplaneSeparationSet u v
theorem gaussianHyperplaneLaw_separation_real (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
    𝔈 𝔍 =
      euclideanNorm 𝔄 / 𝔏 := by
  rw [gaussianHyperplaneLaw, measureReal_ennreal_smul_apply, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (hyperplaneNormalizingConstant_pos d).le]
  rw [measureReal_def, gaussianHyperplaneIntensity_separation_ofReal u v hu hv]
  rw [ENNReal.toReal_ofReal $ integral_nonneg 𝗔₁ ]
  simp_rw [gaussianPhase_sub]
  rw [gaussianPhase_abs_integral, hyperplaneNormalizingConstant_actual]
  have hg := gaussianAbsoluteMean_pos.ne'
  field_simp

𝗇 𝔊 𝔐 partitionSameProbability hyperplaneHalfspace u v
theorem gaussianHyperplaneLaw_same_complement :
    1 - 𝔊 =
      𝔈 𝔍 := by
  let s := {h | hyperplaneHalfspace h u = hyperplaneHalfspace h v}
  have hs : MeasurableSet s := (hyperplaneSeparationSet_measurable u v).of_compl
  have he : 𝔊 =
      𝔈 s := by
    simpa only [partitionSameProbability, s, Set.indicator, Pi.one_apply, Set.mem_setOf_eq] using
       integral_indicator_one hs
  rw [he]
  change 1 - 𝔈 s = 𝔈 sᶜ
  rw [measureReal_compl hs]
  simp

end

𝗇 𝔅 𝔏 * T
def boundedHyperplaneFieldLaw (d : ℕ) (T : ℝ) : Measure $ partitionFieldMark 𝔇 :=
  𝔐 poissonCellFieldLaw $ Real.toNNReal 𝔅

def boundedHyperplaneFieldValue (z : partitionFieldMark 𝔇)
    (u : Covariate d) : ℝ := poissonCellFieldValue hyperplaneHalfspace z u

𝗇 𝔎 boundedHyperplaneFieldLaw d T
instance boundedHyperplaneFieldLaw_probability (d : ℕ) [NeZero d] (T : ℝ) :
    IsProbabilityMeasure 𝔎 := by
  unfold boundedHyperplaneFieldLaw
  infer_instance

theorem boundedHyperplaneFieldLaw_measurable d :
    Measurable $ boundedHyperplaneFieldLaw d := (𝔐 poissonCellFieldLaw_measurable).comp
    $ measurable_real_toNNReal.comp $ measurable_const.mul measurable_id

theorem boundedHyperplaneFieldValue_measurable d :
    Measurable fun z : partitionFieldMark 𝔇 × Covariate d =>
      boundedHyperplaneFieldValue z.1 z.2 :=
  poissonCellFieldValue_measurable hyperplaneHalfspace hyperplaneHalfspace_measurable

theorem boundedHyperplaneFieldValue_abs
    z (u : Covariate d) :
    |boundedHyperplaneFieldValue z u| = 1 := poissonCellFieldValue_abs ..

theorem boundedHyperplaneField_covariance (d : ℕ) [NeZero d] T (hT : 𝚞)
    u v (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
     ∫ z, boundedHyperplaneFieldValue z u * boundedHyperplaneFieldValue z v
      ∂𝔎 =
      Real.exp (-T * euclideanNorm 𝔄) := by
  simp only [boundedHyperplaneFieldLaw, boundedHyperplaneFieldValue]
  rw [poissonCellField_covariance _ _ _ hyperplaneHalfspace_measurable,
    gaussianHyperplaneLaw_same_complement, gaussianHyperplaneLaw_separation_real d u v hu hv]
  rw [Real.coe_toNNReal 𝔅 𝖠₃ ]
  have hd : 𝚙₂ := Nat.cast_ne_zero.mpr $ NeZero.ne d
  field_simp

𝗇 𝔉 gaussianHyperplaneLaw_separation_real d _ _ (hU _) $ hU _
theorem boundedHyperplaneField_higher_moment_envelope (d : ℕ) [NeZero d]
    T (hT : 𝚞) j (hj : 𝙳₁) (U : 𝗲₂)
    (hU : ∀ l, U l ∈ hyperplaneCube d) :
    |∫ z, ∏ l, boundedHyperplaneFieldValue z (U l) ∂𝔎| ≤
      ∑ q : CellMomentQuadruple j, Real.exp (-T / 2 *
        (euclideanNorm (fun r => U (q.val 0) r - U (q.val 1) r) +
          euclideanNorm fun r => U (q.val 2) r - U (q.val 3) r )) := by
  have hb := 𝔐 poissonCellField_product_moment_abs_le_two_pairs
    (Real.toNNReal 𝔅) hyperplaneHalfspace hyperplaneHalfspace_measurable j hj U
  apply hb.trans_eq
  apply Finset.sum_congr rfl
  intro q _
  rw [gaussianHyperplaneLaw_same_complement, gaussianHyperplaneLaw_same_complement,
    𝔉,
    𝔉,
    Real.coe_toNNReal 𝔅 𝖠₃ ]
  have hd : 𝚙₂ := Nat.cast_ne_zero.mpr $ NeZero.ne d
  field_simp
