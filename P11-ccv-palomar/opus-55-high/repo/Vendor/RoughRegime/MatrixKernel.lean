module

public import RoughRegime.MatrixDeterminant
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-!
# Absolute convergence and exact matrix reciprocal kernel sum

All matrices carry the genuine ℓ² operator norm.
-/
𝚺
open Polynomial
namespace RoughRegime.MatrixKernel
open RoughRegime.Upper RoughRegime.MatrixUpper RoughRegime.MatrixDeterminant

𝗇 𝔄 𝘉₁ ℝ
𝗃 𝔍 ἀ lo hi
/-- Matrix coefficient of the normalized reciprocal kernel. -/
def matrixKernelCoefficient [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : 𝔄) (k : ℕ) : 𝔄 :=
  Polynomial.aeval M $ 𝔍 kernelCoefficientPolynomial k

𝗇 𝔇 𝔍 matrixKernelCoefficient M k
𝗇 𝔉 spectrum ℝ M ⊆ 𝔍 Set.Icc
section

variable [Fintype n]
    [DecidableEq n]
    (lo)
    (hi)
    (hlo : 𝙫₁)
    (hlt : 𝘰₂)
    (M : 𝔄)
    (hM : M.IsHermitian)
    (hSpec : 𝔉)

include hlo hlt hM hSpec

𝗃 𝔐 𝔍 ἀ hlo hlt
𝗇 𝔏 𝔐 matrix_chebyshev_norm_le_one M hM hSpec
/-- The matrix coefficients have the paper's geometric operator norm bound. -/
theorem matrixKernelCoefficient_norm_le k :
    ‖𝔇‖ ≤ 2 * 𝔍 intervalRho ^ k := by
  have hr := 𝔐 intervalRho_pos
  have he : 𝔇 =
      (if k = 0 then 1 else 2 * (-𝔍 intervalRho) ^ k) •
        Polynomial.aeval M (𝔍 normalizedChebyshev k) := by
    simp [matrixKernelCoefficient, kernelCoefficientPolynomial, Algebra.smul_def]
  rw [he, norm_smul]
  by_cases hk : k = 0
  · subst k
    simp
    exact (𝔏 0).trans 𝖠₄
  · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul,
      abs_pow, abs_neg, abs_of_pos hr]
    simpa using mul_le_mul_of_nonneg_left
      (𝔏 k)
      𝖠₃

/-- Absolute convergence of the genuine matrix coefficient series. -/
theorem matrixKernelCoefficient_summable_norm :
    Summable fun k => ‖𝔇‖ := by
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    $ 𝔐 matrixKernelCoefficient_norm_le M hM hSpec
  exact (summable_geometric_of_lt_one (𝔐 intervalRho_pos).le
    𝔐 intervalRho_lt_one).mul_left 2

end

𝗇 𝔈 PowerSeries.coeff k $ 𝔍 scalarKernelSeries $ hM.eigenvalues i
𝗇 𝔎 (hM.eigenvectorUnitary : 𝔄)
/-- Each matrix coefficient is diagonal in the fixed spectral eigenbasis. -/
theorem matrixKernelCoefficient_spectral [Fintype n] [DecidableEq n]
    lo hi (M : 𝔄) (hM : M.IsHermitian) k :
    𝔇 =
      hM.eigenvectorUnitary *
      Matrix.diagonal (fun i => 𝔈) *
      star 𝔎 := by
  have he : 𝔇 = coefficientMatrix k (𝔍 kernelSeries M) := by
    ext i j
    simp only [matrixKernelCoefficient, coefficientMatrix, kernelSeries, PowerSeries.coeff_mk]
  rw [he, 𝔍 kernelSeries_spectral M hM, coefficientMatrix_mul_constant,
    coefficientMatrix_constant_mul, coefficientMatrix_diagonal]

𝗇 𝔅 Matrix.diagonal fun i => (hM.eigenvalues i)⁻¹
/-- The inverse itself has the same spectral representation, with reciprocal eigenvalues. -/
theorem matrix_inverse_spectral [Fintype n] [DecidableEq n]
    (M : 𝔄) (hM : M.IsHermitian) (hn : ∀ i, hM.eigenvalues i ≠ 0) :
    M⁻¹ = hM.eigenvectorUnitary *
      𝔅 *
      star 𝔎 := by
  let U : 𝔄 := hM.eigenvectorUnitary
  have hU := Unitary.star_mul_self_of_mem hM.eigenvectorUnitary.property
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.property
  have hM' : M = U * Matrix.diagonal hM.eigenvalues * star U := by
    simpa only [U, Unitary.conjStarAlgAut_apply, Function.comp_apply,
      RCLike.ofReal_real_eq_id, Function.id_comp] using hM.spectral_theorem
  apply Matrix.inv_eq_left_inv
  conv_lhs => arg 2; rw [hM']
  calc
    _ = U * 𝔅 *
        (star U * U) * Matrix.diagonal hM.eigenvalues * star U := by noncomm_ring
    _ = U * (𝔅 *
        Matrix.diagonal hM.eigenvalues) * star U := 𝖤₃
    𝚘₂ := by
      simp_all

𝗇 𝔊 hSpec $ hM.eigenvalues_mem_spectrum_real i
/-- The actual matrix series sums to ḡ M⁻¹. -/
theorem matrixKernelCoefficient_tsum [Fintype n] [DecidableEq n]
    lo hi (hlo : 𝙫₁) (hlt : 𝘰₂) (M : 𝔄) (hM : M.IsHermitian)
    (hSpec : 𝔉) :
     ∑' k, 𝔇 = 𝔍 intervalGeometricMean • M⁻¹ := by
  let U := hM.eigenvectorUnitary
  have hd : Summable fun k i => 𝔈 := by
    rw [Pi.summable]
    intro i
    exact (𝔍 scalarKernelSeries_summable_norm _ hlo hlt
      𝔊).of_norm
  have hds : (∑' k, fun i => 𝔈) =
      fun i => 𝔍 intervalGeometricMean / hM.eigenvalues i := by
    funext i
    rw [Pi.tsum_apply hd]
    exact 𝔍 scalarKernelSeries_tsum _ hlo hlt 𝔊
  have hdmat := hd.matrix_diagonal
  simp_rw [𝔍 matrixKernelCoefficient_spectral M hM]
  rw [(hdmat.mul_left 𝔎).tsum_mul_right,
    hdmat.tsum_mul_left, ← Matrix.diagonal_tsum, hds]
  rw [matrix_inverse_spectral M hM fun i =>
    ne_of_gt $ hlo.trans_le (𝔊).1 ]
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
  congr 2
