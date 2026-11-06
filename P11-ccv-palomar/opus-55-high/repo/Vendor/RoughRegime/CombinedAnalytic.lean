module

public import RoughRegime.MatrixKernel
public import RoughRegime.CombinedPolynomial
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Operator norm and convergence bridge for the full matrix/determinant
combined-index reciprocal truncation of Lemma 5(a). -/
𝚼

namespace RoughRegime.CombinedAnalytic
open RoughRegime.MatrixDeterminant RoughRegime.MatrixKernel RoughRegime.SeriesBounds
open RoughRegime.Upper RoughRegime.CombinedPolynomial

𝗇 𝔦 𝘉₁ $ PowerSeries ℝ
/-- Convert entrywise scalar formal series to a matrix-valued formal series. -/
def matrixSeries [Fintype n] [DecidableEq n] (K : 𝔦) : PowerSeries $ 𝘉₁ ℝ :=
  PowerSeries.mk fun k => coefficientMatrix k K

𝗇 𝔡 PowerSeries.map $ Matrix.scalar n
section

variable [Fintype n]
    [DecidableEq n]

theorem matrixSeries_coefficient (K : 𝔦) k :
    PowerSeries.coeff k (matrixSeries K) = coefficientMatrix k K := PowerSeries.coeff_mk ..

/-- Entrywise multiplication by a scalar series is matrix multiplication by its scalar matrix. -/
theorem matrixSeries_scalar_mul K g :
    matrixSeries (fun i j => K i j * g) =
      matrixSeries K * 𝔡 g := by
  ext k i j
  simp only [matrixSeries, PowerSeries.coeff_mk, coefficientMatrix, PowerSeries.coeff_mul,
    PowerSeries.coeff_map, Matrix.sum_apply, Matrix.scalar_apply, Matrix.mul_diagonal]

end

𝗇 𝔚 fun g j => PowerSeries.coeff j g
𝗃 𝔰 fun j => PowerSeries.coeff j ἀ
/-- Formal coefficients of a product are the actual recursively defined combined indices. -/
theorem addFactors_eq_powerSeries_coeff [Semiring R]
    f (gs : List $ PowerSeries R ) k :
    addFactors 𝔰 f
      (gs.map 𝔚) k =
      PowerSeries.coeff k (f * gs.reverse.prod) := by
  induction gs generalizing k with
  | nil => simp [addFactors]
  | cons g gs ih =>
    simp only [List.map_cons, addFactors, List.reverse_cons, List.prod_append,
      List.prod_singleton]
    rw [← mul_assoc, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro ij _
    rw [ih]

section

variable [Fintype n]
    [DecidableEq n]

/-- A scalar coefficient embedded as a scalar matrix has the same operator norm. -/
theorem scalarMatrix_coefficient_norm [Nonempty n]
    (g : PowerSeries ℝ) k :
    ‖PowerSeries.coeff k (𝔡 g)‖ = ‖PowerSeries.coeff k g‖ := by
  simp

theorem mapped_scalar_prod_reverse (gs : List $ PowerSeries ℝ ) :
    (gs.map 𝔡).reverse.prod =
      𝔡 gs.prod := by
  rw [← List.map_reverse, ← map_list_prod, List.prod_reverse]

end

𝗇 𝔟 Fin $ dims i
𝗇 𝔄 (i : Fin N) → Matrix 𝔟 𝔟 ℝ
𝗃 𝔣 ἀ $ Fin n0
𝗇 𝔇 𝔣 Matrix (Fin n0) ℝ
𝗃 𝔮 ἀ lo hi
𝗇 𝔊 ∏ i, (𝔮 kernelSeries $ M i ).det
𝗇 𝔎 𝔣 Matrix.scalar
𝗇 𝔐 Fin N → ℕ
𝗇 𝔒 matrixSeries $ 𝔮 kernelSeries M0
/-- The genuine matrix/determinant combined generating series. -/
def combinedSeries {N n0 : ℕ} {dims : 𝔐}
    (lo hi : ℝ) (M0 : 𝔇)
    (M : 𝔄) :
    PowerSeries 𝔇 :=
  𝔒 *
    PowerSeries.map 𝔎 𝔊

𝗃 𝔱 𝔮 ἀ M0 M
𝗇 𝔈 PowerSeries.coeff k 𝔱 combinedSeries
𝗇 𝔧 entryValuation M0 M
/-- The matrix-valued coefficients evaluate exactly the entry polynomials. -/
theorem combinedSeries_coefficient_entry
    lo hi (M0 : 𝔇)
    (M : 𝔄)
    a b k :
    𝔈 a b =
      MvPolynomial.eval 𝔧
        (combinedCoefficientPolynomial n0 dims lo hi a b k) := by
  rw [combinedCoefficientPolynomial_eval]
  rw [combinedSeries, ← matrixSeries_scalar_mul]
  simp only [matrixSeries, PowerSeries.coeff_mk, coefficientMatrix]

𝗇 𝔏 ∀ i, (M i).IsHermitian
𝗇 𝔗 𝔮 scalarKernelSeries $ (hM ij.1).eigenvalues ij.2
/-- Flatten all reciprocal eigenvalue factors, including zero-dimensional determinant blocks. -/
def eigenvalueSeriesList {N : ℕ} {dims : 𝔐}
    (lo hi : ℝ) (M : 𝔄)
    (hM : 𝔏) : List $ PowerSeries ℝ :=
  (Finset.univ : Finset $ (i : Fin N) × 𝔟 ).toList.map
     fun ij => 𝔗

𝗇 𝔉 ∑ i, dims i
𝗇 𝔘 𝔮 eigenvalueSeriesList M hM
section

variable {N }
    {dims : 𝔐}
    (lo)
    (hi)
    (M : 𝔄)
    (hM)

theorem eigenvalueSeriesList_length :
    (𝔘).length = 𝔉 := by
  simp only [eigenvalueSeriesList, List.length_map, Finset.length_toList, Finset.card_univ,
    Fintype.card_sigma, Fintype.card_fin]

theorem eigenvalueSeriesList_prod :
    (𝔘).prod = 𝔊 := by
  rw [eigenvalueSeriesList, Finset.prod_map_toList, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  exact (𝔮 kernelSeries_det_spectral (M i) $ hM i ).symm

end

𝗇 𝔅 (𝔮 eigenvalueSeriesList M hM).map fun g j => 𝔣 Matrix.scalar $ PowerSeries.coeff j g
𝗇 𝔔 𝔮 matrixKernelCoefficient M0
𝗇 𝔠 (𝔘).map $ PowerSeries.map 𝔎
/-- The actual combined series coefficients are the Cauchy products of all eigenvalue kernels. -/
theorem combinedSeries_coefficient_eq_addFactors {N n0 } {dims : 𝔐}
    lo hi M0
    (M : 𝔄)
    hM k :
    𝔈 =
      addFactors 𝔔
        𝔅 k := by
  have he := addFactors_eq_powerSeries_coeff 𝔒
    𝔠 k
  rw [mapped_scalar_prod_reverse, eigenvalueSeriesList_prod] at he
  have hf : 𝔰 𝔒 =
      𝔔 := by
    funext j
    ext a b
    simp only [matrixSeries, PowerSeries.coeff_mk, coefficientMatrix, kernelSeries,
      matrixKernelCoefficient]
  have hg : (𝔠).map 𝔚 =
      𝔅 := by
    simp
  aesop

𝗇 𝔍 ∀ i, spectrum ℝ (M i) ⊆ 𝔮 Set.Icc
𝗇 𝔖 𝔮 intervalRho
𝗇 𝔙 spectrum ℝ M0 ⊆ 𝔮 Set.Icc
𝗇 𝔛 (𝘆 : ℕ)
𝗇 𝔞 𝔉 + 1
𝗃 𝔢 𝔮 ἀ hlo hlt
𝗇 𝔨 𝙫₁
𝗇 𝔩 𝘰₂
𝗃 𝔯 𝔢 ἀ M0 hM0 hSpec0
/-- Full factor-count coefficient bound of Lemma 5(a), in the actual operator norm. -/
theorem combinedSeries_coefficient_norm_le {N n0 : ℕ} [𝔣 Nonempty] {dims : 𝔐}
    lo hi (hlo : 𝔨) (hlt : 𝔩)
    (M0 : 𝔇) (hM0 : M0.IsHermitian)
    (hSpec0 : 𝔙)
    (M : 𝔄)
    (hM : 𝔏) (hSpec : 𝔍)
    k :
    ‖𝔈‖ ≤
      2 ^ 𝔞 * 𝔛 ^ 𝔉 * 𝔖 ^ k := by
  rw [𝔱 combinedSeries_coefficient_eq_addFactors hM]
  have hg : ∀ g ∈ 𝔅,
      ∀ j, ‖g j‖ ≤ 2 * 𝔖 ^ j := by
    intro g hg j
    rcases List.mem_map.mp hg with ⟨q, hq, rfl⟩
    rcases List.mem_map.mp hq with ⟨ij, _, rfl⟩
    change ‖PowerSeries.coeff j (PowerSeries.map 𝔎
      𝔗)‖ ≤ _
    rw [scalarMatrix_coefficient_norm]
    exact 𝔮 scalarKernelSeries_coefficient_norm_le _ hlo hlt
      (hSpec ij.1 $ (hM ij.1).eigenvalues_mem_spectrum_real ij.2 ) j
  have hh := addFactors_coefficient_bound 𝔔
    𝔅
    𝔖 2 2 𝔢 intervalRho_pos  𝖠₄   𝖠₄ 
    𝔯 matrixKernelCoefficient_norm_le hg k
  simpa only [List.length_map, eigenvalueSeriesList_length, pow_succ, mul_assoc,
    mul_left_comm, mul_comm] using hh

/-- Scalar matrices commute with coefficient summation. -/
theorem scalarMatrix_tsum [Fintype n] [DecidableEq n]
    (f : 𝙜) (hf : Summable f) :
     ∑' k, (Matrix.scalar n) (f k) = (Matrix.scalar n) (∑' k, f k) := by
  have hc : Continuous (Matrix.scalar n : ℝ → 𝘉₁ ℝ) := by
    change Continuous fun x => Matrix.diagonal fun _ => x
    fun_prop
  exact (hf.hasSum.map (Matrix.scalar n) hc).tsum_eq

𝗇 𝔑 ∏ i, (M i).det
𝗇 𝔓 𝔢 kernelSeries_det_summable_norm (M i) (hM i) $ hSpec i
𝗇 𝔜 𝔮 intervalGeometricMean
/-- The sum of all determinant factors is the common normalization divided by the determinant product. -/
theorem determinantProduct_tsum {N } {dims : 𝔐}
    lo hi (hlo : 𝔨) (hlt : 𝔩)
    (M : 𝔄)
    (hM : 𝔏) (hSpec : 𝔍) :
     ∑' k, PowerSeries.coeff k 𝔊 =
      𝔜 ^ 𝔉 / 𝔑 := by
  rw [powerSeries_prod_tsum]
  · simp_rw [𝔢 kernelSeries_det_tsum _ (hM _) $ hSpec _ , Fintype.card_fin]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  · intro i _
    exact 𝔓

𝗇 𝔤 𝔜 ^ 𝔞
𝗇 𝔥 fun k => 𝔈
𝗇 𝔪 ∑' k, 𝔈
𝗇 𝔫 PowerSeries.coeff k $ PowerSeries.map 𝔎 D
/-- The actual combined generating series sums to ḡ^(ν'+1) times the inverse/determinant target. -/
theorem combinedSeries_tsum {N n0 : ℕ} [𝔣 Nonempty] {dims : 𝔐}
    lo hi (hlo : 𝔨) (hlt : 𝔩)
    (M0 : 𝔇) (hM0 : M0.IsHermitian)
    (hSpec0 : 𝔙)
    (M : 𝔄)
    (hM : 𝔏) (hSpec : 𝔍) :
    𝔪 =
      (𝔤 / 𝔑) • M0⁻¹ := by
  let D := 𝔊
  have hDn := powerSeries_prod_summable_norm Finset.univ _ fun i _ =>
      𝔓
  have hDmn : Summable fun k => ‖𝔫‖ := by
    simpa
  have hcoef : 𝔥 =
      convolution 𝔔
         fun k => 𝔫 := by
    funext k
    rw [combinedSeries, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro ij _
    congr 1
    ext a b
    simp only [matrixSeries, PowerSeries.coeff_mk, coefficientMatrix, kernelSeries,
      matrixKernelCoefficient]
  rw [hcoef, convolution_tsum _ _
    𝔯 matrixKernelCoefficient_summable_norm hDmn,
    𝔯 matrixKernelCoefficient_tsum]
  simp only [PowerSeries.coeff_map]
  rw [scalarMatrix_tsum _ hDn.of_norm, 𝔢 determinantProduct_tsum M hM hSpec,
    Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal, smul_smul]
  ring

/-- Finite matrix polynomial with the exact combined-index truncation and normalization. -/
def truncationMatrix {N n0 : ℕ} {dims : 𝔐}
    (lo hi : ℝ) (M0 : 𝔇)
    (M : 𝔄) (m : ℕ) :
    𝔇 :=
  fun a b => MvPolynomial.eval 𝔧 $ truncationEntryPolynomial n0 dims lo hi a b m

/-- Exact identification of the concrete entry polynomials with the formal combined-index truncation. -/
theorem truncationMatrix_eq_scaled_sum {N n0 } {dims : 𝔐}
    lo hi (M0 : 𝔇)
    (M : 𝔄) m :
    𝔱 truncationMatrix m =
      𝔤⁻¹ •
        ∑ k ∈ Finset.range 𝘻, 𝔈 := by
  ext a b
  simp only [truncationMatrix, truncationEntryPolynomial_eval, Matrix.smul_apply,
    smul_eq_mul, Matrix.sum_apply, combinedSeries_coefficient_entry,
    combinedCoefficientPolynomial_eval]

𝗇 𝔬 𝔑 ⁻¹ • M0⁻¹
𝗇 𝔭 ν + 1
/-- Full Lemma 5(a): the arbitrary determinant-product approximation error in operator norm.
Together with `truncationEntryPolynomial_degree`, this proves the matrix polynomial assertion. -/
theorem matrix_determinant_truncation_error {N n0 : ℕ} [𝔣 Nonempty] {dims : 𝔐}
    lo hi (hlo : 𝔨) (hlt : 𝔩)
    (M0 : 𝔇) (hM0 : M0.IsHermitian)
    (hSpec0 : 𝔙)
    (M : 𝔄)
    (hM : 𝔏) (hSpec : 𝔍) m :
    ‖ 𝔬 - 𝔱 truncationMatrix m‖ ≤
      2 ^ 𝔞 * 𝔤⁻¹ *
         (𝘻 : ℕ) ^ 𝔉 * 𝔖 ^ m *
        ∑' k : ℕ, 𝔛 ^ 𝔉 * 𝔖 ^ k := by
  let ν := 𝔉
  let α := (𝔜 ^ 𝔭)⁻¹
  have hg : 𝔜 ≠ 0 :=
    ne_of_gt $ Real.sqrt_pos.mpr $ mul_pos hlo $ hlo.trans hlt
  have hα : 0 ≤ α := by dsimp [α, intervalGeometricMean]; positivity
  have htarget : 𝔬 =
      α • 𝔪 := by
    rw [𝔯 combinedSeries_tsum M hM hSpec, smul_smul]
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ $ pow_ne_zero _ hg , one_mul]
  rw [htarget, truncationMatrix_eq_scaled_sum]
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]
  have he := series_truncation_bound
    𝔥 ν m 𝔖
    (2 ^ 𝔭) 𝔢 intervalRho_pos 𝔢 intervalRho_lt_one
     𝖠₃  $ 𝔯 combinedSeries_coefficient_norm_le M hM hSpec
  nlinarith
