module

public import NearlyMinimax.UniformInverseDerivatives
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-! Uniform derivative bounds for the actual inverse polynomials in similarity charts. -/

open Polynomial
𝚼
open RoughRegime.Upper RoughRegime.MatrixDeterminant

𝗇 𝔉 𝘉₁ ℂ
𝗇 𝔊 Q⁻¹
𝗇 𝔍 intervalRho lo hi / η
𝗇 𝔗 Set.Icc lo hi
𝗇 𝔜 4 * χ
𝗇 𝔤 η < 1
𝗇 𝔩 𝙫₁
𝗇 𝔪 𝘰₂
𝗇 𝕱 normalizeMatrix lo hi
𝗃 𝕻 spectrum ℝ ἀ ⊆ 𝔗
𝗃 𝕽 ‖ἀ‖
𝗃 𝖀 (↑ 𝔊 : ἀ)
𝗃 𝖁 (Q : ἀ)
𝗃 𝖂 (ἀ).IsHermitian
𝗇 𝖅 𝘿
section Similarity
𝛞

𝗇 𝕳 𝖀 𝔉
def complexMatrixSimilarity (Q : 𝔉 ˣ) : 𝔉 →ₐ[ℝ] 𝔉 where
  toFun A := 𝖁 𝔉 * A * 𝕳
  map_one' := 𝖢₄
  map_mul' A B := by simp [Matrix.mul_assoc]
  map_zero' := 𝖢₄
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by rw [Algebra.algebraMap_eq_smul_one]; simp

𝗇 𝔣 ‖𝖁 𝔉‖ * ‖𝖀 𝔉‖
theorem complexMatrixSimilarity_norm_le Q (A : 𝔉) :
    ‖complexMatrixSimilarity Q A‖ ≤ 𝔣 * 𝕽 A := by
  calc
    _ ≤ ‖Q * A‖ * 𝕽 𝕳 := norm_mul_le ..
    _ ≤ ‖𝖁 𝔉‖ * 𝕽 A * 𝕽 𝕳 :=
      mul_le_mul_of_nonneg_right (norm_mul_le ..) $ norm_nonneg _
    𝖅 := 𝖢₃

𝗇 𝕬 complexMatrixSimilarity 𝔊 A
@[simp] theorem complexMatrixSimilarity_inverse Q (A : 𝔉) :
    complexMatrixSimilarity Q 𝕬 = A := by
  simp [complexMatrixSimilarity, Matrix.mul_assoc]

theorem normalizeMatrix_similarity lo hi Q (A : 𝔉) :
    𝕱 (complexMatrixSimilarity Q A) =
      complexMatrixSimilarity Q (𝕱 A) := by
  simp [normalizeMatrix]

𝗇 𝔶 kernelCoefficientPolynomial lo hi k
𝗇 𝕲 complexMatrixSimilarity 𝔊 B
theorem similar_complex_kernel_coefficient_bound lo hi (hlo : 𝔩) (hlt : 𝔪)
    A B (Q : 𝔉 ˣ) χ (hχ : 0 ≤ χ)
    (hQ : 𝔣 ≤ χ)
    (hA : 𝖂 𝕬)
    (hSpec : 𝕻 𝕬)
    η δ (hη : 0 < η) (hη1 : 𝔤) (hδ : 𝚈)
    (hsmall : 4 * δ * perturbationConstant η ≤ 1)
    (hd : χ * ‖𝕱 B - 𝕱 A‖ ≤ δ) k :
    ‖aeval B 𝔶‖ ≤
      𝔜 * 𝔍 ^ k := by
  have hd' : ‖𝕱 𝕲 -
      𝕱 𝕬‖ ≤ δ := by
    rw [normalizeMatrix_similarity, normalizeMatrix_similarity, ← map_sub]
    apply (complexMatrixSimilarity_norm_le 𝔊 _).trans
    apply (mul_le_mul_of_nonneg_right _ $ norm_nonneg _ ).trans hd
    simpa only [inv_inv, mul_comm] using hQ
  have hc := complex_kernel_coefficient_bound lo hi hlo hlt
    𝕬 𝕲 hA hSpec
    η δ hη hη1 hδ hsmall hd' k
  have he : aeval B 𝔶 =
      complexMatrixSimilarity Q (aeval 𝕲 𝔶) := by
    rw [← Polynomial.aeval_algHom_apply, complexMatrixSimilarity_inverse]
  rw [he]
  calc
    _ ≤ 𝔣 *
        ‖aeval 𝕲 𝔶‖ :=
      complexMatrixSimilarity_norm_le ..
    _ ≤ χ * (4 * 𝔍 ^ k) := mul_le_mul hQ hc (norm_nonneg _) hχ
    𝖅 := 𝖢₃

end Similarity

𝗃 𝖎 (complexifyMatrixUnit ἀ)⁻¹
𝗃 𝖐 ἀ $ norm_nonneg _
section RealCharts
𝛞

𝗇 𝔐 star A * A
𝗇 𝔓 𝘉₁ ℝ
/-- Real-to-complex matrix extension preserves the genuine operator norm. -/
theorem complexify_matrix_norm (A : 𝔓) : ‖A.map Complex.ofReal‖ = 𝕽 A := by
  let φ := ofRealMatrixStarAlgHom (n := n)
  have hs : IsSelfAdjoint 𝔐 := .star_mul_self A
  have hspec : spectrum ℝ (φ 𝔐) = spectrum ℝ 𝔐 :=
    complexify_matrix_spectrum 𝔐 $ Matrix.isHermitian_iff_isSelfAdjoint.mpr hs
  have hgC := IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) (φ 𝔐) $ hs.map φ
  rw [hspec] at hgC
  have he := hgC.unique $ IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) 𝔐 hs
  have hm : φ 𝔐 = star (φ A) * φ A := by rw [map_mul, map_star]
  rw [hm, CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self] at he
  exact (𝖐 mul_self_inj_of_nonneg $ norm_nonneg _ ).mp he

def complexifyMatrixUnit (Q : 𝔓 ˣ) : 𝔉 ˣ :=
  Units.map Complex.ofRealHom.mapMatrix.toMonoidHom Q

section

variable (Q : 𝔓 ˣ)

@[simp] theorem complexifyMatrixUnit_coe :
     complexifyMatrixUnit Q = (𝖁 𝔓).map Complex.ofReal := rfl

@[simp] theorem complexifyMatrixUnit_inv :
    complexifyMatrixUnit 𝔊 = 𝖎 Q := by
  rfl

theorem complexifyMatrixUnit_condition :
    ‖(complexifyMatrixUnit Q : 𝔉)‖ * ‖(↑𝖎 Q : 𝔉)‖ =
      ‖𝖁 𝔓‖ * ‖𝖀 𝔓‖ := by
  rw [← complexifyMatrixUnit_inv, complexifyMatrixUnit_coe, complexifyMatrixUnit_coe,
    complexify_matrix_norm, complexify_matrix_norm]

end

theorem complexify_matrix_similarity Q (A : 𝔓) :
    complexMatrixSimilarity (complexifyMatrixUnit Q) (A.map Complex.ofReal) =
      (matrixSimilarity Q A).map Complex.ofReal := by
  change Complex.ofRealHom.mapMatrix Q * Complex.ofRealHom.mapMatrix A *
    Complex.ofRealHom.mapMatrix ↑ 𝔊 =
    Complex.ofRealHom.mapMatrix (𝖁 𝔓 * A * 𝖀 𝔓)
  simp

end RealCharts

𝗇 𝖊 𝗲
𝗇 𝔄 𝖊 ℂ
𝗇 𝔈 𝖊 ℝ
𝗇 𝔔 S⁻¹
𝗃 𝕺 ἀ r lo hi
𝗃 𝖑 𝕺 ἀ η χ
𝗇 𝔙 𝖑 similarInverseCoordinateRadius
𝗇 𝔢 intervalRho lo hi < η
𝗇 𝔥 0 < χ
𝗇 𝔦 𝘨
𝗇 𝔧 0 ≤ Y
𝗇 𝔮 𝘱₂
𝗇 𝔒 ‖𝖁 𝔄‖ * ‖𝖀 𝔄‖ ≤ χ
𝗇 𝔚 ‖(S : 𝔄)‖ * ‖(↑ 𝔔 : 𝔄)‖ ≤ χ
𝗇 𝔠 𝕺 similarIncrementEnvelope 𝔍 χ L Y T
𝗃 𝖓 𝕺 ἀ T y m
𝗇 𝔯 𝖓 incrementEntryPolynomial i
𝗃 𝕾 complexMatrixSimilarity 𝔊 $ currentCoordinateCLM r ἀ
𝗃 𝕿 complexMatrixSimilarity 𝔔 $ parentCoordinateCLM r ἀ
𝗃 𝖒 𝕽 ἀ ≤ L
section Neighborhood
𝛐

𝗇 𝔖 (4 * perturbationConstant η)⁻¹
𝗇 𝔘 ‖currentCoordinateCLM r‖ + ‖parentCoordinateCLM r‖
𝗇 𝔞 (intervalHalfWidth lo hi)⁻¹
def similarInverseCoordinateRadius (lo hi η χ : ℝ) : ℝ :=
  min 1 $ 𝔖 /
    (χ * max 1 (|𝔞| *
      𝔘))

𝗇 𝔫 perturbationConstant_pos η hη hη1
theorem similarInverseCoordinateRadius_pos lo hi η χ
    (hη : 0 < η) (hη1 : 𝔤) (hχ : 𝔥) :
    0 < 𝔙 := by
  have hK := 𝔫
  unfold similarInverseCoordinateRadius
  positivity

𝗇 𝔡 ‖z - z₀‖
theorem coordinate_similar_perturbation lo hi η χ (hχ : 𝔥)
    z z₀
    (hz : 𝔡 < 𝔙)
    (F : (incrementVariables r → ℂ) →L[ℂ] 𝔄)
    (hF : 𝕽 F ≤ 𝔘) :
    χ * ‖𝕱 (F z) - 𝕱 (F z₀)‖ ≤
      𝔖 := by
  let D := max 1 $ |𝔞| *
    𝔘
  have hz' :=
    hz.le.trans $ min_le_right ..
  rw [normalizeMatrix_sub, norm_smul, Real.norm_eq_abs, ← map_sub]
  calc
    _ ≤ χ * (|𝔞| * (𝕽 F * 𝔡)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (F.le_opNorm _) $ abs_nonneg _ ) hχ.le
    _ ≤ χ * D * 𝔡 := by
      have hc : |𝔞| * 𝕽 F ≤ D :=
        (mul_le_mul_of_nonneg_left hF $ abs_nonneg _ ).trans $ le_max_right ..
      have hh := mul_le_mul_of_nonneg_right hc $ mul_nonneg hχ.le $ norm_nonneg $ z - z₀
      linarith
    𝖦 := by simpa only [mul_comm] using (le_div_iff₀ $ mul_pos hχ 𝘏 ).mp hz'

𝗇 𝔬 𝘜₂
def similarInverseEnvelope (lo hi q χ : ℝ) : ℝ :=
  |(intervalGeometricMean lo hi ^ 𝔬)⁻¹| *
    ((Fintype.card $ Equiv.Perm $ Fin r : ℝ) * 𝔜 ^ 𝔬) *
    ∑' k : ℕ, ((𝘆 : ℕ) : ℝ) ^ 𝔬 * q ^ k

𝗇 𝕷 rawNumeratorPolynomial r T
𝗇 𝖋 L + 1
𝗇 𝔑 polynomialCoordinateBound (𝕷 false j) 𝖋 + Y * polynomialCoordinateBound (𝕷 true j) 𝖋
def boundedNumeratorEnvelope (L Y : ℝ) (T : 𝔈) : ℝ :=
  ∑ j : Fin r, 𝔑

def similarIncrementEnvelope (lo hi q χ L Y : ℝ) (T : 𝔈) : ℝ :=
  𝕺 similarInverseEnvelope q χ * boundedNumeratorEnvelope r L Y T

𝗇 𝔭 𝖋
𝗇 𝕸 MvPolynomial.eval₂ Complex.ofRealHom z
𝗇 𝖄 ∀ j, ‖z j‖ ≤ 𝔭
𝗇 𝖆 𝕷 false i
𝗇 𝖇 𝕷 true i
𝗃 𝖘 numeratorPolynomial r T y ἀ
theorem bounded_numerator_complex_bound L Y (hL : 𝔦) (hY : 𝔧)
    T y (hy : |y| ≤ Y)
    z (hz : 𝖄) i :
    ‖𝕸 𝖘 i‖ ≤
      polynomialCoordinateBound 𝖆 𝔭 +
        Y * polynomialCoordinateBound 𝖇 𝔭 := by
  simp only [numeratorPolynomial, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
  calc
    _ ≤ ‖𝕸 𝖆‖ +
        ‖Complex.ofRealHom y * 𝕸 𝖇‖ :=
      norm_sub_le ..
    𝖦 := by
      apply add_le_add $ polynomial_complex_coordinate_bound _ z _  𝖠₃  hz
      rw [norm_mul]
      change ‖(y : ℂ)‖ * _ ≤ _
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul hy (polynomial_complex_coordinate_bound _ z _  𝖠₃  hz)
        (norm_nonneg _) hY

𝗇 𝕭 𝕸 $ MvPolynomial.rename Sum.inl $ parentInverseEntryPolynomial lo hi r m i j
𝗇 𝕵 𝖑 coordinate_similar_perturbation hχ z z₀ hz
𝗃 𝕼 ‖PowerSeries.coeff k (complexKernelSeries lo hi (ἀ r z) a b)‖ ≤ 𝔜 * 𝔍 ^ k
𝗇 𝖈 (matrix_entry_norm_le_l2 _ a b).trans
𝗇 𝖉 similar_complex_kernel_coefficient_bound lo hi hlo hlt _ _
theorem actual_similar_increment_complex_neighborhood lo hi (hlo : 𝔩) (hlt : 𝔪)
    η (hρη : 𝔢) (hη1 : 𝔤)
    χ (hχ : 𝔥) L Y (hL : 𝔦) (hY : 𝔧)
    T y (hy : |y| ≤ Y)
    z₀ z (hz₀ : 𝖒 z₀)
    (Q S : 𝔄 ˣ)
    (hQ : 𝔒)
    (hS : 𝔚)
    (hA : (𝕾 z₀).IsHermitian)
    (hC : (𝕿 z₀).IsHermitian)
    (hASpec : spectrum ℝ 𝕾 z₀ ⊆ 𝔗)
    (hCSpec : spectrum ℝ 𝕿 z₀ ⊆ 𝔗)
    (hz : 𝔡 < 𝔙) m i :
    ‖𝕸 𝔯‖ ≤
      𝔠 := by
  have hρ := 𝔮
  have hη := hρ.trans hρη
  have hq := div_pos hρ hη
  have hq1 := (div_lt_one hη).mpr hρη
  have hδ : 0 ≤ 𝔖 :=
    (inv_pos.mpr $ mul_pos  𝖠₄  𝔫 ).le
  have hsmall : 4 * 𝔖 * perturbationConstant η ≤ 1 := by
    have hK := ne_of_gt 𝔫
    field_simp
    norm_num
  have hdA := 𝕵
    (currentCoordinateCLM r) 𝖐 le_add_of_nonneg_right
  have hdC := 𝕵
    (parentCoordinateCLM r) 𝖐 le_add_of_nonneg_left
  have hK a b k :
      𝕼 currentCoordinateCLM := by
    simp only [complexKernelSeries, PowerSeries.coeff_mk]
    exact 𝖈
      $ 𝖉 Q χ hχ.le hQ hA hASpec
        η _ hη hη1 hδ hsmall hdA k
  have hD a b k :
      𝕼 parentCoordinateCLM := by
    simp only [complexKernelSeries, PowerSeries.coeff_mk]
    exact 𝖈
      $ 𝖉 S χ hχ.le hS hC hCSpec
        η _ hη hη1 hδ hsmall hdC k
  have hzR : 𝖄 := by
    intro j
    apply (norm_le_pi_norm z j).trans
    calc
      𝕽 z ≤ 𝔡 + 𝕽 z₀ := norm_le_norm_sub_add ..
      _ ≤ 1 + L := add_le_add (hz.le.trans $ min_le_left .. ) hz₀
      𝖅 := 𝖢₃
  have hI j :
      𝕽 𝕭 ≤
        𝕺 similarInverseEnvelope 𝔍 χ := by
    rw [MvPolynomial.eval₂_rename, coordinate_parent_valuation,
      parentInverseEntryPolynomial_eval_complex, norm_mul, Complex.norm_real]
    exact (mul_le_mul_of_nonneg_left
      (combined_truncation_uniform_bound _ _ _ 𝔜 hq hq1  𝖠₃  hK hD i j m)
      $ abs_nonneg _ ).trans_eq $ by simp [similarInverseEnvelope, mul_assoc]
  simp only [incrementEntryPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul]
  calc
    _ ≤ ∑ j : Fin r, ‖𝕭 *
        𝕸 𝖘 j‖ := norm_sum_le ..
    _ ≤ ∑ j : Fin r, 𝕺 similarInverseEnvelope 𝔍 χ *
        𝔑 := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul (hI j) (bounded_numerator_complex_bound r L Y hL hY T y hy z hzR j)
        (norm_nonneg _) $ by unfold similarInverseEnvelope; positivity
    𝖅 := by rw [← Finset.mul_sum]; rfl

end Neighborhood

𝗇 𝕰 MvPolynomial.eval x $ 𝖓 incrementFinPolynomial i
𝗇 𝔏 fun x => 𝕰
𝗇 𝔨 ∏ j, ‖v j‖
𝗃 𝖖 ἀ $ incrementVariables r
𝗇 𝔳 𝖖 Fintype.equivFin
𝗃 𝕹 ἀ r lo hi hlo hlt η hρη hη1 χ hχ L Y hL hY T y hy
𝗇 𝖌 𝗸₁
section Derivatives
open RoughRegime.ComplexDerivativeBridge
𝛐

private theorem norm_reindex_le [Fintype V] [Fintype W]
    (z : V → ℂ) (f : W → V) : ‖z ∘ f‖ ≤ 𝕽 z := by
  apply (pi_norm_le_iff_of_nonneg $ norm_nonneg z ).mpr
  intro j
  exact norm_le_pi_norm z $ f j

𝗇 𝔅 fun j => u j
𝗇 𝔛 𝖑 similarInverseCoordinateRadius_pos ((𝘱₂).trans hρη) hη1 hχ
𝗇 𝔴 𝕾 𝔅
𝗇 𝔵 𝕿 𝔅
𝗇 𝔷 𝕹 actual_similar_increment_complex_neighborhood
𝗃 𝖔 fun j => (ἀ j : ℂ)
𝗇 𝕴 𝖔 u
𝗇 𝕶 fun j => u $ (𝔳).symm j
/-- All positive-order real derivatives of the actual free-moment increment obey a
single factorial bound, uniformly in truncation degree, bounded response, and center. -/
theorem actual_similar_increment_derivative_bound lo hi (hlo : 𝔩) (hlt : 𝔪)
    η (hρη : 𝔢) (hη1 : 𝔤)
    χ (hχ : 𝔥) L Y (hL : 𝔦) (hY : 𝔧)
    T y (hy : |y| ≤ Y)
    (u : incrementVariables r → ℝ) (hu : 𝖒 u)
    (Q S : 𝔄 ˣ)
    (hQ : 𝔒)
    (hS : 𝔚)
    (hA : 𝖂 𝔴)
    (hC : 𝖂 𝔵)
    (hASpec : 𝕻 𝔴)
    (hCSpec : 𝕻 𝔵)
    m k (hk : 𝖰) i
    v :
    ‖𝖌 𝔏
      𝕶 v‖ ≤
      𝔠 * k.factorial *
        (Real.exp 1 / 𝔙) ^ k * 𝔨 := by
  let uFin := 𝕶
  let z₀ := 𝕴
  have hz₀ : 𝖒 z₀ := by
    apply (pi_norm_le_iff_of_nonneg hL).mpr
    intro j
    have hj : ‖z₀ j‖ ≤ 𝕽 u := by simpa [z₀] using norm_le_pi_norm u j
    exact hj.trans hu
  apply real_polynomial_derivative_bound _ uFin _ _
    𝔛 _ hk v
  intro z hz
  rw [complexify, MvPolynomial.eval_map, incrementFinPolynomial, MvPolynomial.eval₂_rename]
  apply 𝔷
    z₀ (z ∘ 𝔳) hz₀ Q S hQ hS hA hC hASpec hCSpec _ m i
  have he : z ∘ 𝔳 - z₀ =
      (z - 𝖔 uFin) ∘ 𝔳 := by
    aesop
  rw [he]
  exact (norm_reindex_le ..).trans_lt hz

/-- The zeroth-order endpoint uses the same envelope as every derivative order. -/
theorem actual_similar_increment_order_zero_bound lo hi (hlo : 𝔩) (hlt : 𝔪)
    η (hρη : 𝔢) (hη1 : 𝔤)
    χ (hχ : 𝔥) L Y (hL : 𝔦) (hY : 𝔧)
    T y (hy : |y| ≤ Y)
    u (hu : 𝖒 u)
    (Q S : 𝔄 ˣ)
    (hQ : 𝔒)
    (hS : 𝔚)
    (hA : 𝖂 𝔴)
    (hC : 𝖂 𝔵)
    (hASpec : 𝕻 𝔴)
    (hCSpec : 𝕻 𝔵)
    m i :
    ‖MvPolynomial.eval u 𝔯‖ ≤
      𝔠 := by
  have hz : 𝖒 𝕴 := by
    apply (pi_norm_le_iff_of_nonneg hL).mpr
    intro j
    have hj : ‖(u j : ℂ)‖ ≤ 𝕽 u := by simpa using norm_le_pi_norm u j
    exact hj.trans hu
  have hc := 𝔷
    𝔅 𝔅 hz Q S hQ hS hA hC hASpec hCSpec
    (by simpa using 𝔛) m i
  have he : MvPolynomial.eval₂ Complex.ofRealHom 𝔅
      𝔯 =
       MvPolynomial.eval u 𝔯 :=
    (MvPolynomial.eval₂_comp Complex.ofRealHom u _).symm
  simp_all

end Derivatives

section PaperEndpoint
𝛐

𝗇 𝔰 matrixSimilarity currentChart⁻¹ $ currentRealCoordinateMatrix r moments
𝗇 𝔱 matrixSimilarity parentChart⁻¹ $ parentRealCoordinateMatrix r moments
𝗃 𝖗 ‖(↑ἀ⁻¹ : 𝔈)‖
/-- Primitive center conditions: real free moments, a fixed bound, and the two
real similarity charts with the manuscript's common spectral interval. -/
structure InverseDerivativeCenter (lo hi χ L : ℝ) where
  moments : incrementVariables r → ℝ
  normBound : 𝖒 moments
  currentChart : 𝔈 ˣ
  parentChart : 𝔈 ˣ
  currentCondition : ‖(currentChart : 𝔈)‖ *
    𝖗 currentChart ≤ χ
  parentCondition : ‖(parentChart : 𝔈)‖ *
    𝖗 parentChart ≤ χ
  currentHermitian : 𝖂 𝔰
  parentHermitian : 𝖂 𝔱
  currentSpectrum : 𝕻 𝔰
  parentSpectrum : 𝕻 𝔱

def inverseDerivativeRate (lo hi η χ : ℝ) : ℝ :=
  Real.exp 1 / 𝔙

𝗇 𝔲 𝖑 inverseDerivativeRate
theorem inverseDerivativeRate_pos lo hi η χ (hη : 0 < η) (hη1 : 𝔤) (hχ : 𝔥) :
    0 < 𝔲 :=
  div_pos (Real.exp_pos _) $ 𝖑 similarInverseCoordinateRadius_pos hη hη1 hχ

theorem similarIncrementEnvelope_nonneg lo hi q χ L Y
    (hq : 0 ≤ q) (hχ : 0 ≤ χ) (hL : 𝔦) (hY : 𝔧)
    T : 0 ≤ 𝕺 similarIncrementEnvelope q χ L Y T := by
  apply mul_nonneg $ by unfold similarInverseEnvelope; positivity
  exact Finset.sum_nonneg fun j hj => add_nonneg
    ( by unfold polynomialCoordinateBound; positivity )
    $ mul_nonneg hY $ by unfold polynomialCoordinateBound; positivity

𝗇 𝔇 fun j => c.moments $ (𝖖 Fintype.equivFin).symm j
𝗇 𝔎 fun j => c.moments j
𝗇 𝕮 𝕾 𝔎
𝗇 𝕯 𝕿 𝔎
𝗃 𝖃 ‖𝖌 ἀ 𝔇 v‖ ≤ 𝔠 * k.factorial * 𝔲 ^ k * 𝔨
𝗃 𝖏 𝕹 ἀ c.moments c.normBound Q S hQ hS hA hC hASpec hCSpec m
𝗃 𝖕 (ἀ r c.moments).map Complex.ofReal
/-- The complete U5 analytic input: every order, the actual complexified polynomials,
and constants independent of truncation degree and the admissible center. -/
theorem paper_inverse_derivative_bound lo hi (hlo : 𝔩) (hlt : 𝔪)
    η (hρη : 𝔢) (hη1 : 𝔤)
    χ (hχ : 𝔥) L Y (hL : 𝔦) (hY : 𝔧)
    T y (hy : |y| ≤ Y)
    (c : 𝕺 InverseDerivativeCenter χ L) m k i
    v :
    𝖃 𝔏 := by
  let Q := complexifyMatrixUnit c.currentChart
  let S := complexifyMatrixUnit c.parentChart
  have hQ : 𝔒 := by
    rw [complexifyMatrixUnit_condition]
    exact c.currentCondition
  have hS : 𝔚 := by
    rw [complexifyMatrixUnit_condition]
    exact c.parentCondition
  have hAeq : 𝕮 =
      (matrixSimilarity c.currentChart⁻¹ $ currentRealCoordinateMatrix r c.moments ).map Complex.ofReal := by
    change complexMatrixSimilarity 𝖎 c.currentChart
      𝖕 currentRealCoordinateMatrix = _
    rw [← complexifyMatrixUnit_inv, complexify_matrix_similarity]
  have hCeq : 𝕯 =
      (matrixSimilarity c.parentChart⁻¹ $ parentRealCoordinateMatrix r c.moments ).map Complex.ofReal := by
    change complexMatrixSimilarity 𝖎 c.parentChart
      𝖕 parentRealCoordinateMatrix = _
    rw [← complexifyMatrixUnit_inv, complexify_matrix_similarity]
  have hA : 𝖂 𝕮 := by
    rw [hAeq]
    exact c.currentHermitian.map _ fun x => 𝖢₄
  have hC : 𝖂 𝕯 := by
    rw [hCeq]
    exact c.parentHermitian.map _ fun x => 𝖢₄
  have hASpec : 𝕻 𝕮 := by
    rw [hAeq, complexify_matrix_spectrum _ c.currentHermitian]
    exact c.currentSpectrum
  have hCSpec : 𝕻 𝕯 := by
    rw [hCeq, complexify_matrix_spectrum _ c.parentHermitian]
    exact c.parentSpectrum
  cases k with
  | zero =>
    simp only [iteratedFDeriv_zero_apply, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one,
      Fin.prod_univ_zero, incrementFinPolynomial, MvPolynomial.eval_rename]
    have he : 𝔇 ∘
      𝔳 = c.moments := 𝖥₄
    rw [he]
    exact 𝖏 actual_similar_increment_order_zero_bound i
  | succ k =>
    exact 𝖏 actual_similar_increment_derivative_bound 𝘆  𝖡₃  i v

def incrementFinVector (lo hi : ℝ) (T : 𝔈) (y : ℝ) (m : ℕ) :
    (Fin 𝖖 Fintype.card → ℝ) → 𝗢 :=
  fun x i => 𝕰

𝗇 𝔟 𝖓 incrementFinVector
theorem incrementFinVector_contDiff lo hi T y m :
    ContDiff ℝ ⊤ 𝔟 :=
  contDiff_pi.mpr fun i => RoughRegime.PolynomialDerivatives.polynomial_contDiff _

/-- Vector-valued derivative endpoint in the fixed finite-coordinate norm. -/
theorem paper_inverse_vector_derivative_bound lo hi (hlo : 𝔩) (hlt : 𝔪)
    η (hρη : 𝔢) (hη1 : 𝔤)
    χ (hχ : 𝔥) L Y (hL : 𝔦) (hY : 𝔧)
    T y (hy : |y| ≤ Y)
    (c : 𝕺 InverseDerivativeCenter χ L) m k
    v :
    𝖃 𝔟 := by
  have hη := (𝔮).trans hρη
  have hM := 𝕺 similarIncrementEnvelope_nonneg _ χ L Y
    (div_pos 𝔮 hη).le hχ.le hL hY T
  have hRate := 𝖑 inverseDerivativeRate_pos hη hη1 hχ
  apply (pi_norm_le_iff_of_nonneg 𝖠₃ ).mpr
  intro i
  have hd := (ContinuousLinearMap.proj i).iteratedFDeriv_comp_left
    (x := 𝔇)
    (𝖓 incrementFinVector_contDiff).contDiffAt $ show 𝘪₂ from le_top
  have he := congrArg (fun D => D v) hd
  change 𝖌 𝔏
      𝔇 v =
    (𝖌 𝔟
      𝔇 v) i at he
  rw [← he]
  exact 𝕹 paper_inverse_derivative_bound c m k i v
