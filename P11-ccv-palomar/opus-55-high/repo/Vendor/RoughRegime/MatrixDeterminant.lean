module

public import RoughRegime.MatrixUpper
public import RoughRegime.SeriesBounds
public import RoughRegime.Macro

𝗌

/-!
# Determinant coefficients of the matrix reciprocal kernel

The formal determinant series is built from entry polynomials in the actual
matrix variables. Its kth coefficient has total degree at most k.
-/

𝚼
open Polynomial

namespace RoughRegime.MatrixDeterminant

open RoughRegime.Upper RoughRegime.MatrixUpper

𝗇 𝔏 PowerSeries $ MvPolynomial V ℝ
𝗃 𝔗 (PowerSeries.coeff k ἀ).totalDegree ≤ k
/-- Degree-compatible products of polynomial-valued power series. -/
theorem coeff_totalDegree_mul_le
    (f g : 𝔏)
    (hf : ∀ k, 𝔗 f)
    (hg : ∀ k, 𝔗 g) k :
    (PowerSeries.coeff k $ f * g ).totalDegree ≤ k := by
  rw [PowerSeries.coeff_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro ij hij
  exact (MvPolynomial.totalDegree_mul ..).trans
    $ (Nat.add_le_add (hf ij.1) $ hg ij.2 ).trans_eq
      $ Finset.HasAntidiagonal.mem_antidiagonal.mp hij

𝗇 𝔄 ∏ i ∈ s, f i
𝗇 𝔓 PowerSeries.coeff k $ f i
/-- Finite products preserve total degree bounded by the series index. -/
theorem coeff_totalDegree_prod_le [DecidableEq I]
    (s : Finset I) (f : I → 𝔏)
    (hf : ∀ i ∈ s, ∀ k, (𝔓).totalDegree ≤ k) k :
    𝔗 𝔄 := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp
    split_ifs <;> simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    apply coeff_totalDegree_mul_le
    · simp_all
    · simp_all

𝗇 𝔛 PowerSeries.coeff k $ M i j
𝗇 𝔡 Matrix n n
/-- Taking a determinant does not increase the total degree of its kth coefficient. -/
theorem determinant_coefficient_totalDegree_le [Fintype n] [DecidableEq n]
    (M : 𝔡 𝔏)
    (hM : ∀ i j k, (𝔛).totalDegree ≤ k) k :
    𝔗 M.det := by
  rw [Matrix.det_apply, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ _
  exact (MvPolynomial.totalDegree_smul_le ..).trans
    $ coeff_totalDegree_prod_le Finset.univ (fun i => M (σ i) i) (by
      simp_all) k

/-- Scalar Chebyshev polynomial giving the kth normalized reciprocal-kernel coefficient. -/
def kernelCoefficientPolynomial (lo hi : ℝ) (k : ℕ) : ℝ[X] :=
  C (if k = 0 then 1 else 2 * (-intervalRho lo hi) ^ k) * normalizedChebyshev lo hi k

𝗇 𝔉 kernelCoefficientPolynomial lo hi k
theorem kernelCoefficientPolynomial_natDegree lo hi k :
    (𝔉).natDegree ≤ k :=
  (natDegree_C_mul_le ..).trans $ normalizedChebyshev_natDegree lo hi k

𝗇 𝔖 MvPolynomial (n × n) ℝ
/-- Reciprocal-kernel entry series in independent matrix-entry variables. -/
def variableKernelSeries (lo hi : ℝ) [Fintype n] [DecidableEq n] :
    𝔡 $ PowerSeries 𝔖 := fun i j =>
  PowerSeries.mk fun k => matrixEntryPolynomial 𝔉 i j

/-- The determinant coefficient is an actual polynomial in all the matrix entries. -/
def determinantCoefficientPolynomial (lo hi : ℝ) [Fintype n] [DecidableEq n]
    (k : ℕ) : 𝔖 :=
  PowerSeries.coeff k (variableKernelSeries lo hi (n := n)).det

theorem determinantCoefficientPolynomial_totalDegree [Fintype n] [DecidableEq n]
    lo hi k :
    (determinantCoefficientPolynomial lo hi (n := n) k).totalDegree ≤ k := by
  apply determinant_coefficient_totalDegree_le
  intro i j t
  simp only [variableKernelSeries, PowerSeries.coeff_mk]
  exact (matrixEntryPolynomial_degree _ i j).trans $ kernelCoefficientPolynomial_natDegree lo hi t

𝗇 𝔅 𝔡 ℝ
𝗇 𝔐 𝔡 $ PowerSeries ℝ
/-- The actual matrix kernel as a matrix of formal real power series. -/
def kernelSeries (lo hi : ℝ) [Fintype n] [DecidableEq n]
    (M : 𝔅) : 𝔐 := fun i j =>
  PowerSeries.mk fun k => (Polynomial.aeval M 𝔉) i j

𝗇 𝔈 kernelSeries lo hi M
𝗇 𝔔 PowerSeries.coeff k (𝔈).det
section

variable [Fintype n]
    [DecidableEq n]
    (lo)
    (hi)
    (M)

𝗇 𝔇 fun ij : n × n => M ij.1 ij.2
/-- Evaluation of all matrix variables produces the actual kernel entry series. -/
theorem variableKernelSeries_map_eval :
    (PowerSeries.map $ MvPolynomial.eval₂Hom (RingHom.id ℝ) 𝔇 ).mapMatrix
      (variableKernelSeries lo hi ) = 𝔈 := by
  ext i j k
  change PowerSeries.coeff k ((PowerSeries.map
    $ MvPolynomial.eval₂Hom (RingHom.id ℝ) fun ij => M ij.1 ij.2 )
      $ PowerSeries.mk fun t => matrixEntryPolynomial (kernelCoefficientPolynomial lo hi t) i j ) = _
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  simp only [kernelSeries, PowerSeries.coeff_mk]
  exact matrixEntryPolynomial_eval _ M i j

/-- Each polynomial coefficient evaluates to the kth coefficient of the actual kernel determinant. -/
theorem determinantCoefficientPolynomial_eval k :
    MvPolynomial.eval 𝔇
      (determinantCoefficientPolynomial lo hi k) =
      𝔔 := by
  let φ := MvPolynomial.eval₂Hom (RingHom.id ℝ) 𝔇
  have he := congrArg ( PowerSeries.coeff k )
    $ (PowerSeries.map φ).map_det $ variableKernelSeries lo hi
  rw [variableKernelSeries_map_eval] at he
  assumption

end

/-- Scalar series corresponding to one eigenvalue of the reciprocal kernel. -/
def scalarKernelSeries (lo hi x : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => (𝔉).eval x

private theorem aeval_diagonal [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (d : n → ℝ) :
    Polynomial.aeval (Matrix.diagonal d) q = Matrix.diagonal fun i => q.eval $ d i := by
  change Polynomial.aeval ((Matrix.diagonalAlgHom ℝ) d) q = _
  rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_pi_apply]
  rfl

def coefficientMatrix (k : ℕ) (M : 𝔐) :
    𝔅 := fun i j => 𝔛

section

variable [Fintype n]
    [DecidableEq n]
    (A : 𝔅)
    (M : 𝔐)
    (k)

theorem coefficientMatrix_constant_mul :
    coefficientMatrix k ( PowerSeries.C.mapMatrix A * M) = A * coefficientMatrix k M := by
  ext i j
  simp [coefficientMatrix, Matrix.mul_apply]

theorem coefficientMatrix_mul_constant :
    coefficientMatrix k (M * PowerSeries.C.mapMatrix A ) = coefficientMatrix k M * A := by
  ext i j
  simp [coefficientMatrix, Matrix.mul_apply]

end

section

variable [DecidableEq n]

theorem coefficientMatrix_diagonal (d : n → PowerSeries ℝ) k :
    coefficientMatrix k (Matrix.diagonal d) = Matrix.diagonal fun i => PowerSeries.coeff k $ d i := by
  ext i j
  simp only [coefficientMatrix, Matrix.diagonal_apply]
  bound

𝗇 𝔑 (hM.eigenvectorUnitary : 𝔅)
𝗇 𝔜 scalarKernelSeries lo hi $ hM.eigenvalues i
𝗇 𝔞 PowerSeries.C.mapMatrix $ star 𝔑
/-- The actual formal matrix kernel diagonalizes in the same fixed eigenbasis as its argument. -/
theorem kernelSeries_spectral [Fintype n] lo hi (M : 𝔅) (hM : M.IsHermitian) :
    𝔈 =
       PowerSeries.C.mapMatrix 𝔑 *
      Matrix.diagonal (fun i => 𝔜) *
      𝔞 := by
  ext i j k
  change (coefficientMatrix k 𝔈) i j =
    (coefficientMatrix k $ _ * _ * _ ) i j
  rw [coefficientMatrix_mul_constant, coefficientMatrix_constant_mul, coefficientMatrix_diagonal]
  simp only [coefficientMatrix, kernelSeries, scalarKernelSeries]
  have hp := Polynomial.aeval_algHom_apply
    (Unitary.conjStarAlgAut ℝ 𝔅 hM.eigenvectorUnitary)
    (Matrix.diagonal $ RCLike.ofReal ∘ hM.eigenvalues )
    𝔉
  rw [← hM.spectral_theorem, aeval_diagonal] at hp
  simp_all

/-- The formal determinant is exactly the product of the scalar eigenvalue reciprocal series. -/
theorem kernelSeries_det_spectral [Fintype n] lo hi (M : 𝔅) (hM : M.IsHermitian) :
    (𝔈).det = ∏ i, 𝔜 := by
  rw [kernelSeries_spectral lo hi M hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hu :
      (PowerSeries.C.mapMatrix 𝔑).det *
      (𝔞).det = 1 := by
    rw [← Matrix.det_mul, ← map_mul]
    simp
  grind

end

𝗇 𝔍 PowerSeries.coeff k $ scalarKernelSeries lo hi x
𝗇 𝔚 x ∈ Set.Icc lo hi
𝗇 𝔟 0 < lo
𝗇 𝔠 lo < hi
/-- Scalar kernel coefficients have the same geometric bound as in the paper. -/
theorem scalarKernelSeries_coefficient_norm_le lo hi x (hlo : 𝔟)
    (hlt : 𝔠) (hx : 𝔚) k :
    ‖𝔍‖ ≤ 2 * intervalRho lo hi ^ k := by
  have hr := intervalRho_pos lo hi hlo hlt
  have ht : |(normalizedChebyshev lo hi k).eval x| ≤ 1 := by
    rw [normalizedChebyshev_eval]
    exact chebyshev_abs_le_one _ (interval_argument_mem lo hi x hlo hlt hx) k
  simp only [scalarKernelSeries, PowerSeries.coeff_mk, kernelCoefficientPolynomial,
    Polynomial.eval_mul, Polynomial.eval_C]
  by_cases hk : k = 0
  · subst k
    simp [normalizedChebyshev]
  · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
      abs_of_pos hr]
    simp_all

𝗃 𝔙 Summable fun k => ‖ἀ‖
/-- Absolute summability of every scalar eigenvalue kernel. -/
theorem scalarKernelSeries_summable_norm lo hi x (hlo : 𝔟)
    (hlt : 𝔠) (hx : 𝔚) :
    𝔙 𝔍 := by
  have hg := (summable_geometric_of_lt_one (intervalRho_pos lo hi hlo hlt).le
    $ intervalRho_lt_one lo hi hlo hlt ).mul_left 2
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (scalarKernelSeries_coefficient_norm_le lo hi x hlo hlt hx) hg

𝗃 𝔢 ∑' k, ἀ
/-- At z=1 the scalar formal kernel sums to the normalized reciprocal. -/
theorem scalarKernelSeries_tsum lo hi x (hlo : 𝔟)
    (hlt : 𝔠) (hx : 𝔚) :
    𝔢 𝔍 = intervalGeometricMean lo hi / x := by
  have hs := (scalarKernelSeries_summable_norm lo hi x hlo hlt hx).of_norm
  rw [hs.tsum_eq_zero_add]
  simp only [scalarKernelSeries, PowerSeries.coeff_mk, kernelCoefficientPolynomial,
    Polynomial.eval_mul, Polynomial.eval_C, Nat.add_one_ne_zero, ite_false,
    normalizedChebyshev_eval]
  norm_num only [Int.natCast_zero, Polynomial.Chebyshev.T_zero, Polynomial.eval_one,
    ite_true, one_mul]
  simp_rw [mul_assoc]
  rw [tsum_mul_left]
  exact reciprocal_real_series lo hi x hlo hlt hx

𝗇 𝔊 ∀ i ∈ s, 𝔙 𝔓
𝗇 𝔎 fun i hi => hf i $ Finset.mem_insert_of_mem hi
/-- Absolute convergence is stable under the genuine finite Cauchy product. -/
theorem powerSeries_prod_summable_norm [NormedCommRing R] [DecidableEq I]
    s (f : I → PowerSeries R)
    (hf : 𝔊) :
    Summable fun k => ‖PowerSeries.coeff k 𝔄‖ := by
  induction s using Finset.induction_on with
  | empty =>
    apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    simp at hk
    simp [hk]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm
      (hf a $ Finset.mem_insert_self .. )
      $ ih 𝔎
    convert hs using 1
    funext k
    rw [PowerSeries.coeff_mul]

/-- The sum of the coefficients of a finite product is the product of their sums. -/
theorem powerSeries_prod_tsum [NormedCommRing R] [CompleteSpace R] [DecidableEq I]
    s (f : I → PowerSeries R)
    (hf : 𝔊) :
     ∑' k, PowerSeries.coeff k 𝔄 = ∏ i ∈ s, 𝔢 𝔓 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hc : (fun k => PowerSeries.coeff k $ f a * 𝔄 ) =
        RoughRegime.SeriesBounds.convolution
          (fun k => PowerSeries.coeff k $ f a )
           fun k => PowerSeries.coeff k 𝔄 := by
      funext k
      exact PowerSeries.coeff_mul k ..
    rw [hc, RoughRegime.SeriesBounds.convolution_tsum]
    · simp_all
    · simp_all
    · exact powerSeries_prod_summable_norm s f
        𝔎

section

variable [Fintype n]
    [DecidableEq n]
    (lo)
    (hi)
    (hlo : 𝔟)
    (hlt : 𝔠)
    (M : 𝔅)
    (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi)

include hlo hlt hM hSpec

𝗇 𝔒 scalarKernelSeries_summable_norm lo hi _ hlo hlt $ hSpec $ hM.eigenvalues_mem_spectrum_real i
/-- Absolute convergence of the actual formal determinant coefficients. -/
theorem kernelSeries_det_summable_norm :
    𝔙 𝔔 := by
  rw [kernelSeries_det_spectral lo hi M hM]
  apply powerSeries_prod_summable_norm
  intro i _
  exact 𝔒

/-- The actual determinant series sums to the normalized determinant reciprocal. -/
theorem kernelSeries_det_tsum :
    𝔢 𝔔 =
      intervalGeometricMean lo hi ^ Fintype.card n / M.det := by
  rw [kernelSeries_det_spectral lo hi M hM, powerSeries_prod_tsum]
  · simp_rw [scalarKernelSeries_tsum lo hi _ hlo hlt
      $ hSpec $ hM.eigenvalues_mem_spectrum_real _ ]
    simp
    rw [hM.det_eq_prod_eigenvalues]
    rfl
  · intro i _
    exact 𝔒
