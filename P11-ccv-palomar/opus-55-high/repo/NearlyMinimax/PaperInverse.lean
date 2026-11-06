module

public import NearlyMinimax.Chebyshev
public import RoughRegime.CombinedAnalytic
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-!
# Reciprocal polynomial ingredients for `upper_B.tex`

The imported algebraic and analytic reciprocal construction is specialized to
one parent determinant, exactly the product in the manuscript. Results stated
with Hermitian matrices below explicitly retain that hypothesis. The scalar
exponent bridge identifies the rate parameter with the manuscript's `τ`.
-/



open Polynomial
𝚼
open RoughRegime.Upper RoughRegime.MatrixUpper

𝗇 𝔑 𝙆
𝗇 𝔖 𝙭
𝗃 𝔭 ἀ a b
𝗇 𝔛 𝔭 intervalRho
𝗇 𝔤 𝖬
𝗃 𝔧 𝔭 ἀ ha hab
/-- The inverse-series convergence ratio equals `exp(-τ)`. -/
theorem inverse_ratio_exterior_exponent a b (ha : 𝔑) (hab : 𝔖) :
    𝔛 = Real.exp (-exteriorTau 𝔤) := (𝔧 exp_neg_exteriorTau).symm

𝗇 𝔈 Real.exp $ -m * exteriorTau 𝔤
/-- Integer powers of the convergence ratio have the manuscript's exponential form. -/
theorem inverse_ratio_pow a b (ha : 𝔑) (hab : 𝔖) (m : ℕ) :
    𝔛 ^ m = 𝔈 := by
  rw [𝔧 inverse_ratio_exterior_exponent, ← Real.exp_nat_mul]
  ring

open RoughRegime.CombinedPolynomial RoughRegime.CombinedAnalytic

𝗃 𝔮 fun _ : Fin 1 => ἀ
𝗇 𝔜 𝔮 r
/-- The entry-variable type for the current matrix and its single parent. -/
abbrev parentInverseVariables (r : ℕ) := Variables r 𝔜

/-- Exact free-entry polynomial implementing the manuscript's single-parent truncation. -/
def parentInverseEntryPolynomial (a b : ℝ) (r m : ℕ) (i j : Fin r) :
    MvPolynomial (parentInverseVariables r) ℝ :=
  truncationEntryPolynomial r 𝔜 a b i j m

𝗇 𝔄 𝗲 ℝ
𝗇 𝔒 𝔮 C
/-- Evaluating the free-entry polynomials gives `P_m(A,C)`. -/
def parentInversePolynomial (a b : ℝ)
    (A C : 𝔄) (m : ℕ) : 𝔄 :=
  𝔭 truncationMatrix A 𝔒 m

𝗃 𝔯 fun _ => ἀ
/-- Degree at most `m` is proved in all the free current and parent matrix entries. -/
theorem parentInverseEntryPolynomial_degree a b r m i j :
    (𝔭 parentInverseEntryPolynomial r m i j).totalDegree ≤ m :=
  truncationEntryPolynomial_degree r 𝔯 r a b i j m

𝗇 𝔞 𝘜₂
𝗇 𝔨 (𝘆 : ℕ)
/-- A finite positive constant independent of matrix entries and truncation degree. -/
def parentInverseErrorConstant (a b : ℝ) (r : ℕ) : ℝ :=
  2 ^ 𝔞 * (𝔭 intervalGeometricMean ^ 𝔞)⁻¹ *
    ∑' k : ℕ, (𝔨 : ℝ) ^ r * 𝔛 ^ k

𝗇 𝔟 𝔭 parentInverseErrorConstant r
theorem parentInverseErrorConstant_pos a b (ha : 𝔑) (hab : 𝔖) r :
    0 < 𝔟 := by
  have hr := 𝔧 intervalRho_pos
  have hg :=
    Real.sqrt_pos.mpr $ mul_pos ha $ ha.trans hab
  have hs := RoughRegime.SeriesBounds.weighted_geometric_summable r 𝔛 hr 𝔧 intervalRho_lt_one
  have ht : 0 < ∑' k : ℕ, 𝔨 ^ r * 𝔛 ^ k := by
    apply hs.tsum_pos fun k => by positivity 0
    simp
  unfold parentInverseErrorConstant
  positivity

𝗇 𝔊 spectrum ℝ A ⊆ 𝔭 Set.Icc
𝗇 𝔏 (𝘻 : ℕ) ^ r
𝗇 𝔓 spectrum ℝ C ⊆ 𝔭 Set.Icc
𝗇 𝔡 𝔭 parentInversePolynomial
𝗃 𝔲 ἀ⁻¹
/-- The inverse/determinant approximation bound of (U4-approx), for symmetric spectral matrices. -/
theorem parent_inverse_polynomial_error [NeZero r]
    a b (ha : 𝔑) (hab : 𝔖)
    (A C : 𝔄) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : 𝔊) (hSpecC : 𝔓) m :
    ‖𝔲 C.det • 𝔲 A - 𝔡 A C m‖ ≤
      𝔟 * 𝔏 *
        𝔈 := by
  have h := 𝔧 matrix_determinant_truncation_error A hA hSpecA 𝔒 𝔯 hC 𝔯 hSpecC m
  simp only [Fin.sum_univ_one, Fin.prod_univ_one] at h
  apply h.trans_eq
  rw [𝔧 inverse_ratio_pow m]
  unfold parentInverseErrorConstant
  ring

𝗇 𝔅 𝘉₁ ℝ
𝗇 𝔚 ↑𝔲 Q
𝗇 𝔣 (𝔚 : 𝔅)
𝗇 𝔦 (Q : 𝔅)
/-- Scalar-matrix conjugation as an algebra homomorphism. -/
def matrixSimilarity [Fintype n] [DecidableEq n]
    (Q : 𝔅 ˣ) : 𝔅 →ₐ[ℝ] 𝔅 where
  toFun A := 𝔦 * A * 𝔣
  map_one' := 𝖢₄
  map_mul' A B := by simp [Matrix.mul_assoc]
  map_zero' := 𝖢₄
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    simp

𝗇 𝔉 matrixSimilarity Q A
𝗃 𝔰 ‖ἀ‖
section

variable [Fintype n]
    [DecidableEq n]
    (Q)
    (A : 𝔅)

/-- Every matrix polynomial commutes with similarity. -/
theorem aeval_matrixSimilarity (P : ℝ[X]) :
    Polynomial.aeval 𝔉 P = matrixSimilarity Q (Polynomial.aeval A P) := Polynomial.aeval_algHom_apply (matrixSimilarity Q) A P

/-- The operator norm under similarity gains only its condition-number factor. -/
theorem matrixSimilarity_norm_le :
    𝔰 𝔉 ≤ 𝔰 𝔦 * 𝔰 𝔣 * 𝔰 A := by
  calc
    _ ≤ ‖Q * A‖ * 𝔰 𝔣 := norm_mul_le ..
    _ ≤ 𝔰 𝔦 * 𝔰 A * 𝔰 𝔣 :=
      mul_le_mul_of_nonneg_right (norm_mul_le ..) $ norm_nonneg _
    𝘿 := 𝖢₃

/-- Matrix inversion commutes with similarity, including singular matrices. -/
theorem matrixSimilarity_inv :
    𝔲 𝔉 = matrixSimilarity Q 𝔲 A := by
  change (Q * A * 𝔣)⁻¹ =
    Q * 𝔲 A * 𝔣
  simp only [Matrix.mul_inv_rev, ← Matrix.coe_units_inv, inv_inv, Matrix.mul_assoc]

end

open RoughRegime.MatrixDeterminant

𝗇 𝔔 𝔭 kernelSeries A
𝗇 𝔙 𝔭 kernelCoefficientPolynomial k
𝗇 𝔥 𝔭 kernelSeries 𝔉
section

variable [Fintype n]
    [DecidableEq n]

private theorem kernelSeries_coefficient (a b : ℝ) (A : 𝔅) (k : ℕ) :
    coefficientMatrix k 𝔔 =
      Polynomial.aeval A 𝔙 := by
  ext i j
  simp only [coefficientMatrix, kernelSeries, PowerSeries.coeff_mk]

/-- The reciprocal kernel formal series commutes with arbitrary invertible similarity. -/
theorem kernelSeries_matrixSimilarity a b Q (A : 𝔅) :
    𝔥 =
      PowerSeries.C.mapMatrix 𝔦 * 𝔔 *
        PowerSeries.C.mapMatrix 𝔣 := by
  ext i j k
  change (coefficientMatrix k 𝔥) i j =
    (coefficientMatrix k $ _ * _ * _ ) i j
  rw [coefficientMatrix_mul_constant, coefficientMatrix_constant_mul]
  rw [kernelSeries_coefficient, kernelSeries_coefficient]
  exact congrArg (fun M => M i j)
    $ aeval_matrixSimilarity Q A 𝔙

/-- The parent reciprocal determinant formal series is similarity invariant. -/
theorem kernelSeries_det_matrixSimilarity a b Q (A : 𝔅) :
    (𝔥).det = (𝔔).det := by
  rw [kernelSeries_matrixSimilarity]
  have h := Matrix.det_units_conj
    (Units.map PowerSeries.C.mapMatrix.toMonoidHom Q)
    𝔔
  simpa using h

end

private theorem matrixSeries_kernel_matrixSimilarity
    (a b : ℝ) (Q : 𝔄 ˣ) (A : 𝔄) :
    matrixSeries 𝔥 =
      PowerSeries.map (matrixSimilarity Q).toRingHom (matrixSeries 𝔔) := by
  apply PowerSeries.ext
  intro k
  rw [matrixSeries_coefficient, PowerSeries.coeff_map, matrixSeries_coefficient,
    kernelSeries_coefficient, kernelSeries_coefficient]
  exact aeval_matrixSimilarity Q A 𝔙

private theorem matrixSimilarity_scalar [Fintype n] [DecidableEq n]
    (Q : 𝔅 ˣ) (x : ℝ) :
    matrixSimilarity Q (Matrix.scalar n x) = Matrix.scalar n x := (matrixSimilarity Q).commutes x

𝗇 𝔐 matrixSimilarity R C
private theorem combinedSeries_parent_matrixSimilarity
    (a b : ℝ) (Q R : 𝔄 ˣ) (A C : 𝔄) :
    𝔭 combinedSeries 𝔉 𝔮 𝔐 =
      PowerSeries.map (matrixSimilarity Q).toRingHom (𝔭 combinedSeries A 𝔒) := by
  rw [combinedSeries, combinedSeries, map_mul]
  rw [matrixSeries_kernel_matrixSimilarity]
  simp only [kernelSeries_det_matrixSimilarity]
  congr 1
  apply PowerSeries.ext
  intro k
  exact (matrixSimilarity_scalar Q _).symm

/-- The single-parent truncation is equivariant in the current matrix and invariant in the parent. -/
theorem parentInversePolynomial_matrixSimilarity
    a b Q R (A C : 𝔄) m :
    𝔡 𝔉 𝔐 m =
      matrixSimilarity Q (𝔡 A C m) := by
  rw [parentInversePolynomial, parentInversePolynomial,
    truncationMatrix_eq_scaled_sum, truncationMatrix_eq_scaled_sum]
  simp_rw [combinedSeries_parent_matrixSimilarity, PowerSeries.coeff_map]
  simp

𝗇 𝔗 (mul_nonneg (norm_nonneg _) $ norm_nonneg _ ).trans hχ
𝗇 𝔍 ‖(Q : 𝔄)‖ * ‖(↑𝔲 Q : 𝔄)‖ ≤ χ
𝗇 𝔩 χ * 𝔟 * 𝔏 * 𝔈
𝗇 𝔫 Matrix.det_units_conj R C
/-- (U4-approx) for arbitrary matrices similar to symmetric spectral matrices, with condition gain `χ`. -/
theorem parent_inverse_similar_error [NeZero r]
    a b (ha : 𝔑) (hab : 𝔖)
    A C (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : 𝔊) (hSpecC : 𝔓)
    (Q R : 𝔄 ˣ) χ
    (hχ : 𝔍)
    m :
    ‖ (𝔐).det⁻¹ • 𝔲 𝔉 -
      𝔡 𝔉 𝔐 m‖ ≤
        𝔩 := by
  have hdet : (𝔐).det = C.det := 𝔫
  rw [hdet, matrixSimilarity_inv, parentInversePolynomial_matrixSimilarity, ← map_smul, ← map_sub]
  apply (matrixSimilarity_norm_le Q _).trans
  apply (mul_le_mul_of_nonneg_right hχ $ norm_nonneg _ ).trans
  apply (mul_le_mul_of_nonneg_left (𝔧 parent_inverse_polynomial_error A C hA hC hSpecA hSpecC m) 𝔗).trans_eq
  ring

/-- The determinant-cleared fitted increment numerator from (Udef-increment). -/
def incrementNumerator [Fintype n] [DecidableEq n]
    (G C T : 𝔅) (β βminus : n → ℝ) : n → ℝ :=
  C.det • β - G.mulVec (T.mulVec $ C.adjugate.mulVec βminus )

𝗇 𝔬 G.det ≠ 0
𝗃 𝔱 G⁻¹.mulVec β - T.mulVec (ἀ⁻¹.mulVec βminus)
section

variable [Fintype n]
    [DecidableEq n]

𝗇 𝔘 𝔱 C
𝗇 𝔪 incrementNumerator G C T β βminus
/-- The adjugate identity proves (U5-identity) for every invertible current and parent matrix. -/
theorem incrementNumerator_identity (G C T : 𝔅) (hG : 𝔬) (hC : C.det ≠ 0) β βminus :
    𝔲 C.det • (𝔲 G).mulVec 𝔪 =
      𝔘 := by
  rw [incrementNumerator, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G $ isUnit_iff_ne_zero.mpr hG , Matrix.one_mulVec,
    smul_sub, smul_smul, inv_mul_cancel₀ hC, one_smul]
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mulVec, Matrix.mulVec_smul]

/-- The cleared numerator preserves the increment cancellation before approximation. -/
theorem incrementNumerator_factorization G C T (hG : 𝔬) (hC : C.det ≠ 0) (β βminus : n → ℝ) :
    𝔪 =
      C.det • G.mulVec 𝔘 := by
  have hid := incrementNumerator_identity G C T hG hC β βminus
  have h := congrArg (fun v => C.det • G.mulVec v) hid
  simpa only [Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hC, one_smul,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G $ isUnit_iff_ne_zero.mpr hG , Matrix.one_mulVec] using h

/-- Positive-interval spectrum proves nonzero determinant, without an invertibility hypothesis. -/
theorem spectral_det_ne_zero a b (ha : 𝔑) (A : 𝔅) (hA : A.IsHermitian)
    (hSpec : 𝔊) : A.det ≠ 0 := by
  rw [hA.det_eq_prod_eigenvalues]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact ne_of_gt $ ha.trans_le (hSpec $ hA.eigenvalues_mem_spectrum_real i ).1

/-- A Hermitian matrix with positive interval spectrum has operator norm at most the upper endpoint. -/
theorem spectral_norm_le a b (ha : 𝔑) (hab : 𝔖) (A : 𝔅) (hA : A.IsHermitian)
    (hSpec : 𝔊) : 𝔰 A ≤ b := by
  rw [← cfc_id ℝ A $ Matrix.isHermitian_iff_isSelfAdjoint.mp hA ]
  apply norm_cfc_le 𝖡₄
  intro x hx
  have h := hSpec hx
  simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg $ ha.le.trans h.1 ] using h.2

/-- The determinant of a positive spectral matrix is bounded by the endpoint to the dimension. -/
theorem spectral_det_abs_le a b (ha : 𝔑) (hab : 𝔖) (A : 𝔅) (hA : A.IsHermitian)
    (hSpec : 𝔊) : |A.det| ≤ b ^ Fintype.card n := by
  rw [hA.det_eq_prod_eigenvalues, Finset.abs_prod]
  calc
    ∏ i, |hA.eigenvalues i| ≤ ∏ _i : n, b := by
      apply Finset.prod_le_prod₀
      · simp
      · intro i hi
        have h := hSpec $ hA.eigenvalues_mem_spectrum_real i
        grind
    𝘿 := 𝖢₄

end

𝗇 𝔇 (EuclideanSpace.equiv (Fin r) ℝ).symm
𝗇 𝔎 𝔱 Cminus
𝗇 𝔠 incrementNumerator G Cminus T β βminus
𝗇 𝔢 𝔭 spectral_det_ne_zero ha
𝗃 𝔳 ‖𝔇 ἀ‖
/-- Determinant clearing preserves the small increment with the precise spectral-size factor. -/
theorem increment_numerator_norm_le [NeZero r]
    a b (ha : 𝔑) (hab : 𝔖)
    A C T (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : 𝔊) (hSpecC : 𝔓)
    (Q R : 𝔄 ˣ) χ
    (hχ : 𝔍)
    β βminus :
    let G := 𝔉
    let Cminus := 𝔐
    𝔳 𝔠 ≤
      χ * b ^ 𝔞 * 𝔳 𝔎 := by
  dsimp
  let G := 𝔉
  let Cminus := 𝔐
  let δ := 𝔎
  have hG : 𝔬 := by
    rw [show G.det = A.det from Matrix.det_units_conj Q A]
    exact 𝔢 A hA hSpecA
  have hCm : Cminus.det ≠ 0 := by
    rw [show Cminus.det = C.det from 𝔫]
    exact 𝔢 C hC hSpecC
  have hb := ha.trans hab
  have hnG : 𝔰 G ≤ χ * b := by
    apply (matrixSimilarity_norm_le Q A).trans
    apply (mul_le_mul_of_nonneg_right hχ $ norm_nonneg A ).trans
    exact mul_le_mul_of_nonneg_left (𝔧 spectral_norm_le A hA hSpecA) 𝔗
  have hdC : |Cminus.det| ≤ b ^ r := by
    rw [show Cminus.det = C.det from 𝔫]
    simpa using 𝔧 spectral_det_abs_le C hC hSpecC
  rw [incrementNumerator_factorization G Cminus T hG hCm]
  change ‖Cminus.det • 𝔇 (G.mulVec δ)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  calc
    |Cminus.det| * ‖𝔇 (G.mulVec δ)‖ ≤
        b ^ r * (𝔰 G * 𝔳 δ) :=
      mul_le_mul hdC (G.l2_opNorm_mulVec $ 𝔇 δ ) (norm_nonneg _) 𝖠₃
    _ ≤ b ^ r * ( χ * b * 𝔳 δ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnG $ norm_nonneg _ ) 𝖠₃
    𝘿 := 𝖢₃

/-- Applying any inverse/determinant approximation to the cleared numerator incurs only
its operator error times the numerator norm. This is the analytic step behind (U5-error). -/
theorem increment_polynomial_error [NeZero r]
    a b (ha : 𝔑) (hab : 𝔖)
    A C T (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : 𝔊) (hSpecC : 𝔓)
    (Q R : 𝔄 ˣ) χ
    (hχ : 𝔍)
    β βminus m :
    let G := 𝔉
    let Cminus := 𝔐
    let N := 𝔠
    ‖𝔇
      ((𝔡 G Cminus m).mulVec N -
        𝔎)‖ ≤
      𝔩 *
        𝔳 N := by
  dsimp
  let G := 𝔉
  let Cminus := 𝔐
  let N := 𝔠
  have hG : 𝔬 := by
    rw [show G.det = A.det from Matrix.det_units_conj Q A]
    exact 𝔢 A hA hSpecA
  have hCm : Cminus.det ≠ 0 := by
    rw [show Cminus.det = C.det from 𝔫]
    exact 𝔢 C hC hSpecC
  rw [← incrementNumerator_identity G Cminus T hG hCm β βminus , ← Matrix.smul_mulVec, ← Matrix.sub_mulVec]
  have hn := (𝔡 G Cminus m - 𝔲 Cminus.det • 𝔲 G).l2_opNorm_mulVec
    $ 𝔇 N
  apply hn.trans
  rw [norm_sub_rev]
  exact mul_le_mul_of_nonneg_right
    (𝔧 parent_inverse_similar_error A C hA hC hSpecA hSpecC Q R χ hχ m)
    $ norm_nonneg _
