module
public import Mathlib
public import RoughRegime.Upper
public import NearlyMinimax.Chebyshev
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
@[expose] public section
noncomputable section
section
namespace RoughRegime.SeriesBounds
open scoped BigOperators
lemma weighted_geometric_summable (ν : ℕ) (ρ : ℝ) (hp : 0 < ρ) (h1 : ρ < 1) :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k) := by
  have hn : ‖ρ‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hp] using h1
  have hraw := summable_pow_mul_geometric_of_norm_lt_one ν hn
  have hshift  :=
    (summable_nat_add_iff 1).mpr hraw
  convert hshift.mul_right ρ⁻¹ using 1
  ext k
  rw [pow_succ]
  field_simp
theorem series_truncation_bound {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℕ → E) (ν m : ℕ) (ρ A : ℝ) (hp : 0 < ρ) (h1 : ρ < 1) (hA : 0 ≤ A)
    (hcoeff : ∀ k : ℕ, ‖f k‖ ≤ A * ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k) :
    ‖(∑' k : ℕ, f k) - ∑ k ∈ Finset.range (m + 1), f k‖ ≤
      A * ((m + 1 : ℕ) : ℝ) ^ ν * ρ ^ m *
        ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k := by
  let w : ℕ → ℝ := fun k => ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k
  have hw  := weighted_geometric_summable ν ρ hp h1
  have hmajor  := hw.mul_left A
  have hcoeff' (k : ℕ) : ‖f k‖ ≤ A * w k := by
    simpa only [w, mul_assoc] using hcoeff k
  have hnorm  :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcoeff' hmajor
  have hf  := hmajor.of_norm_bounded hcoeff'
  have htail : (∑' k : ℕ, f k) - ∑ k ∈ Finset.range (m + 1), f k =
      ∑' k : ℕ, f (k + m + 1) := by
    have h := hf.sum_add_tsum_nat_add (m + 1)
    rw [← h]
    abel
  have hn0  :=
    (summable_nat_add_iff (f := fun k => ‖f k‖) m).mpr hnorm
  have htmono : (∑' k : ℕ, ‖f (k + m + 1)‖) ≤ ∑' k : ℕ, ‖f (k + m)‖ := by
    have h := hn0.tsum_eq_zero_add
    simp only [zero_add] at h
    have he : (fun k : ℕ => ‖f (k + 1 + m)‖) = (fun k : ℕ => ‖f (k + m + 1)‖) := by
      ext k
      congr 2
      omega
    rw [he] at h
    rw [h]
    exact le_add_of_nonneg_left (norm_nonneg _)
  let C := A * ((m + 1 : ℕ) : ℝ) ^ ν * ρ ^ m
  have : 0 ≤ C := by dsimp [C]; positivity
  have htbound (k : ℕ) : ‖f (k + m)‖ ≤ C * w k := by
    apply (hcoeff (k + m)).trans
    have hindex : (k + m + 1 : ℝ) ≤ (m + 1) * (k + 1) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
        (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (k + m + 1 : ℝ)) hindex ν
    have hpow' : (((k + m + 1 : ℕ) : ℝ)) ^ ν ≤
        ((m + 1 : ℕ) : ℝ) ^ ν * ((k + 1 : ℕ) : ℝ) ^ ν := by
      simpa [mul_pow] using hpow
    have hmul := mul_le_mul_of_nonneg_left hpow' hA
    have hmul' := mul_le_mul_of_nonneg_right hmul (pow_nonneg hp.le (k + m))
    convert hmul' using 1 <;> rw [pow_add] <;> ring
  rw [htail]
  calc
    _ ≤ ∑' k : ℕ, ‖f (k + m + 1)‖ := norm_tsum_le_tsum_norm ((summable_nat_add_iff (f := fun k => ‖f k‖) (m + 1)).mpr hnorm)
    _ ≤ ∑' k : ℕ, ‖f (k + m)‖ := htmono
    _ ≤ ∑' k : ℕ, C * w k := Summable.tsum_le_tsum htbound hn0 (hw.mul_left C)
    _ = _ := by rw [tsum_mul_left]
def convolution {R : Type*} [NonUnitalNonAssocSemiring R] (f g : ℕ → R) (k : ℕ) : R :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, f ij.1 * g ij.2
theorem convolution_coefficient_bound {R : Type*} [NormedRing R]
    (f g : ℕ → R) (ν k : ℕ) (ρ A B : ℝ) (hp : 0 < ρ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ i : ℕ, ‖f i‖ ≤ A * ((i + 1 : ℕ) : ℝ) ^ ν * ρ ^ i)
    (hg : ∀ j : ℕ, ‖g j‖ ≤ B * ρ ^ j) :
    ‖convolution f g k‖ ≤ A * B * ((k + 1 : ℕ) : ℝ) ^ (ν + 1) * ρ ^ k := by
  have hterm (ij : ℕ × ℕ) (hij : ij ∈ Finset.HasAntidiagonal.antidiagonal k) :
      ‖f ij.1 * g ij.2‖ ≤ A * B * ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k := by
    have he  := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hle : ij.1 + 1 ≤ k + 1 := by omega
    have hpow : (((ij.1 + 1 : ℕ) : ℝ)) ^ ν ≤ ((k + 1 : ℕ) : ℝ) ^ ν :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hle) ν
    have hnorm := (norm_mul_le (f ij.1) (g ij.2)).trans
      (mul_le_mul (hf ij.1) (hg ij.2) (norm_nonneg _) (by positivity))
    calc
      _ ≤ A * ((ij.1 + 1 : ℕ) : ℝ) ^ ν * ρ ^ ij.1 * (B * ρ ^ ij.2) := hnorm
      _ = A * B * ((ij.1 + 1 : ℕ) : ℝ) ^ ν * ρ ^ k := by rw [← he, pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (mul_nonneg hA hB)) (pow_nonneg hp.le k)
  unfold convolution
  calc
    _ ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, ‖f ij.1 * g ij.2‖ := norm_sum_le _ _
    _ ≤ ∑ _ij ∈ Finset.HasAntidiagonal.antidiagonal k,
      A * B * ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k := Finset.sum_le_sum hterm
    _ = _ := by simp only [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]; rw [pow_succ]; ring
theorem convolution_tsum {R : Type*} [NormedRing R] [CompleteSpace R]
    (f g : ℕ → R) (hf : Summable (fun i => ‖f i‖)) (hg : Summable (fun i => ‖g i‖)) :
    ∑' k : ℕ, convolution f g k = (∑' i : ℕ, f i) * ∑' j : ℕ, g j := (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg).symm
def addFactors {R : Type*} [NonUnitalNonAssocSemiring R] (f : ℕ → R) :
    List (ℕ → R) → ℕ → R
  | [] => f
  | g :: gs => convolution (addFactors f gs) g
theorem addFactors_coefficient_bound {R : Type*} [NormedRing R]
    (f : ℕ → R) (gs : List (ℕ → R)) (ρ A B : ℝ) (hp : 0 < ρ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ k : ℕ, ‖f k‖ ≤ A * ρ ^ k)
    (hg : ∀ g ∈ gs, ∀ k : ℕ, ‖g k‖ ≤ B * ρ ^ k) (k : ℕ) :
    ‖addFactors f gs k‖ ≤ A * B ^ gs.length * ((k + 1 : ℕ) : ℝ) ^ gs.length * ρ ^ k := by
  induction gs generalizing k with
  | nil => simpa [addFactors] using hf k
  | cons g gs ih =>
    have hh := convolution_coefficient_bound (addFactors f gs) g gs.length k ρ
      (A * B ^ gs.length) B hp (by positivity) hB (by intro k; exact ih (fun q hq => hg q (List.mem_cons_of_mem g hq)) k) (hg g (List.mem_cons_self ..))
    change ‖convolution (addFactors f gs) g k‖ ≤ _
    convert hh using 1
    simp only [List.length_cons, pow_succ]
    ring
end RoughRegime.SeriesBounds
namespace RoughRegime.MatrixUpper
open Polynomial RoughRegime.Upper
open scoped BigOperators Matrix.Norms.L2Operator
def normalizedChebyshev (lo hi : ℝ) (k : ℕ) : ℝ[X] :=
  (Polynomial.Chebyshev.T ℝ k).comp
    (C (intervalHalfWidth lo hi)⁻¹ * (X - C (intervalCenter lo hi)))
lemma normalizedChebyshev_eval (lo hi x k) :
    (normalizedChebyshev lo hi k).eval x =
      (Polynomial.Chebyshev.T ℝ k).eval
        ((x - intervalCenter lo hi) / intervalHalfWidth lo hi) := by
  simp [normalizedChebyshev, div_eq_mul_inv, mul_comm]
def variableMatrix (n ) : Matrix n n (MvPolynomial (n × n) ℝ) :=
  fun i j => MvPolynomial.X (i, j)
def matrixEntryPolynomial  [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (i j : n) : MvPolynomial (n × n) ℝ :=
  ∑ k ∈ Finset.range (q.natDegree + 1),
    MvPolynomial.C (q.coeff k) * (variableMatrix n ^ k) i j
lemma matrixEntryPolynomial_degree  [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (i j : n) :
    (matrixEntryPolynomial q i j).totalDegree ≤ q.natDegree := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  have h_variableMatrix_power_degree (k) : ((variableMatrix n ^ k) i j).totalDegree ≤ k := by
    induction k generalizing i j with
    | zero =>
      simp only [pow_zero, Matrix.one_apply]
      split_ifs <;> simp
    | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply MvPolynomial.totalDegree_finsetSum_le
      intro a _
      exact (MvPolynomial.totalDegree_mul _ _).trans
        (Nat.add_le_add (ih i a) (by simp [variableMatrix]))
  calc
    _ ≤ (MvPolynomial.C (q.coeff k) : MvPolynomial (n × n) ℝ).totalDegree +
      ((variableMatrix n ^ k) i j).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + k := Nat.add_le_add (by simp) (h_variableMatrix_power_degree k)
    _ ≤ q.natDegree := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)
end RoughRegime.MatrixUpper
namespace RoughRegime.MatrixDeterminant
open Polynomial RoughRegime.Upper RoughRegime.MatrixUpper
open scoped BigOperators Matrix.Norms.L2Operator
theorem coeff_totalDegree_mul_le 
    (f g : PowerSeries (MvPolynomial V ℝ))
    (hf : ∀ k, (PowerSeries.coeff k f).totalDegree ≤ k)
    (hg : ∀ k, (PowerSeries.coeff k g).totalDegree ≤ k) (k : ℕ) :
    (PowerSeries.coeff k (f * g)).totalDegree ≤ k := by
  rw [PowerSeries.coeff_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro ij hij
  exact (MvPolynomial.totalDegree_mul _ _).trans
    ((Nat.add_le_add (hf ij.1) (hg ij.2)).trans_eq
      (Finset.HasAntidiagonal.mem_antidiagonal.mp hij))
theorem coeff_totalDegree_prod_le {V I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → PowerSeries (MvPolynomial V ℝ))
    (hf : ∀ i ∈ s, ∀ k, (PowerSeries.coeff k (f i)).totalDegree ≤ k) (k : ℕ) :
    (PowerSeries.coeff k (∏ i ∈ s, f i)).totalDegree ≤ k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, PowerSeries.coeff_one]
    split_ifs <;> simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    apply coeff_totalDegree_mul_le
    · exact hf a (Finset.mem_insert_self ..)
    · intro j
      exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) j
theorem determinant_coefficient_totalDegree_le {V n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (PowerSeries (MvPolynomial V ℝ)))
    (hM : ∀ i j k, (PowerSeries.coeff k (M i j)).totalDegree ≤ k) (k : ℕ) :
    (PowerSeries.coeff k M.det).totalDegree ≤ k := by
  rw [Matrix.det_apply, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ _
  simp only [Units.smul_def]
  exact (MvPolynomial.totalDegree_smul_le _ _).trans
    (coeff_totalDegree_prod_le Finset.univ (fun i => M (σ i) i) (by
      intro i _
      exact hM (σ i) i) k)
def kernelCoefficientPolynomial (lo hi : ℝ) (k : ℕ) : ℝ[X] :=
  C (if k = 0 then 1 else 2 * (-intervalRho lo hi) ^ k) * normalizedChebyshev lo hi k
lemma kernelCoefficientPolynomial_natDegree (lo hi k) :
    (kernelCoefficientPolynomial lo hi k).natDegree ≤ k :=
  have h_normalizedChebyshev_natDegree : (normalizedChebyshev lo hi k).natDegree ≤ k := by
    calc
      _ ≤ (Polynomial.Chebyshev.T ℝ k).natDegree *
        (C (intervalHalfWidth lo hi)⁻¹ * (X - C (intervalCenter lo hi))).natDegree :=
        natDegree_comp_le
      _ ≤ k * 1 := by
        apply Nat.mul_le_mul
        · simp [Polynomial.Chebyshev.natDegree_T]
        · exact (natDegree_C_mul_le _ _).trans (by simp)
      _ = k := by simp
  (natDegree_C_mul_le _ _).trans h_normalizedChebyshev_natDegree
def variableKernelSeries (lo hi : ℝ)  [Fintype n] [DecidableEq n] :
    Matrix n n (PowerSeries (MvPolynomial (n × n) ℝ)) := fun i j =>
  PowerSeries.mk (fun k => matrixEntryPolynomial (kernelCoefficientPolynomial lo hi k) i j)
def determinantCoefficientPolynomial (lo hi : ℝ)  [Fintype n] [DecidableEq n]
    (k : ℕ) : MvPolynomial (n × n) ℝ :=
  PowerSeries.coeff k (variableKernelSeries lo hi (n := n)).det
def kernelSeries (lo hi : ℝ)  [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) : Matrix n n (PowerSeries ℝ) := fun i j =>
  PowerSeries.mk (fun k => (Polynomial.aeval M (kernelCoefficientPolynomial lo hi k)) i j)
theorem variableKernelSeries_map_eval  [Fintype n] [DecidableEq n]
    (lo hi M) :
    (PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun ij => M ij.1 ij.2))).mapMatrix
      (variableKernelSeries lo hi (n := n)) = kernelSeries lo hi M := by
  ext i j k
  change PowerSeries.coeff k ((PowerSeries.map
    (MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun ij => M ij.1 ij.2)))
      (PowerSeries.mk (fun t => matrixEntryPolynomial (kernelCoefficientPolynomial lo hi t) i j))) = _
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  change MvPolynomial.eval (fun ij => M ij.1 ij.2)
    (matrixEntryPolynomial (kernelCoefficientPolynomial lo hi k) i j) = _
  simp only [kernelSeries, PowerSeries.coeff_mk]
  have h_matrixEntryPolynomial_eval (q : ℝ[X]) : MvPolynomial.eval (fun ij : n × n => M ij.1 ij.2) (matrixEntryPolynomial q i j) =
      (Polynomial.aeval M q) i j := by
    rw [Polynomial.aeval_eq_sum_range]
    unfold matrixEntryPolynomial
    have h_variableMatrix_power_eval k (i : n) (j : n) : MvPolynomial.eval (fun ij => M ij.1 ij.2) ((variableMatrix n ^ k) i j) =
        (M ^ k) i j := by
      induction k generalizing i j with
      | zero =>
        simp only [pow_zero, Matrix.one_apply]
        split_ifs <;> simp
      | succ k ih =>
        simp only [pow_succ, Matrix.mul_apply, map_sum, map_mul, ih]
        simp [variableMatrix]
    simp only [map_sum, map_mul, MvPolynomial.eval_C, h_variableMatrix_power_eval,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact h_matrixEntryPolynomial_eval _
def scalarKernelSeries (lo hi x : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (fun k => (kernelCoefficientPolynomial lo hi k).eval x)
theorem aeval_diagonal  [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (d : n → ℝ) :
    Polynomial.aeval (Matrix.diagonal d) q = Matrix.diagonal (fun i => q.eval (d i)) := by
  change Polynomial.aeval ((Matrix.diagonalAlgHom ℝ) d) q = _
  rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_pi_apply]
  rfl
def coefficientMatrix  (k : ℕ) (M : Matrix n n (PowerSeries ℝ)) :
    Matrix n n ℝ := fun i j => PowerSeries.coeff k (M i j)
theorem coefficientMatrix_constant_mul  [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (M : Matrix n n (PowerSeries ℝ)) (k : ℕ) :
    coefficientMatrix k ((PowerSeries.C.mapMatrix A) * M) = A * coefficientMatrix k M := by
  ext i j
  simp [coefficientMatrix, Matrix.mul_apply, map_sum, PowerSeries.coeff_C_mul]
theorem coefficientMatrix_mul_constant  [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (M : Matrix n n (PowerSeries ℝ)) (k : ℕ) :
    coefficientMatrix k (M * PowerSeries.C.mapMatrix A) = coefficientMatrix k M * A := by
  ext i j
  simp [coefficientMatrix, Matrix.mul_apply, map_sum, PowerSeries.coeff_mul_C]
theorem coefficientMatrix_diagonal  [DecidableEq n]
    (d : n → PowerSeries ℝ) (k : ℕ) :
    coefficientMatrix k (Matrix.diagonal d) = Matrix.diagonal (fun i => PowerSeries.coeff k (d i)) := by
  ext i j
  simp only [coefficientMatrix, Matrix.diagonal_apply]
  split_ifs <;> simp
theorem kernelSeries_spectral  [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℝ) (hM : M.IsHermitian) :
    kernelSeries lo hi M =
      PowerSeries.C.mapMatrix (hM.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal (fun i => scalarKernelSeries lo hi (hM.eigenvalues i)) *
      (PowerSeries.C.mapMatrix (star (hM.eigenvectorUnitary : Matrix n n ℝ))) := by
  ext i j k
  change (coefficientMatrix k (kernelSeries lo hi M)) i j =
    (coefficientMatrix k (_ * _ * _)) i j
  rw [coefficientMatrix_mul_constant, coefficientMatrix_constant_mul, coefficientMatrix_diagonal]
  simp only [coefficientMatrix, kernelSeries, scalarKernelSeries, PowerSeries.coeff_mk]
  have hp := Polynomial.aeval_algHom_apply
    (Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hM.eigenvectorUnitary)
    (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues))
    (kernelCoefficientPolynomial lo hi k)
  rw [← hM.spectral_theorem, aeval_diagonal] at hp
  have hp' : Polynomial.aeval M (kernelCoefficientPolynomial lo hi k) =
      (hM.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal (fun i => (kernelCoefficientPolynomial lo hi k).eval (hM.eigenvalues i)) *
      star (hM.eigenvectorUnitary : Matrix n n ℝ) := by
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_apply, RCLike.ofReal_real_eq_id,
      id_eq] using hp
  exact congrArg (fun A : Matrix n n ℝ => A i j) hp'
theorem kernelSeries_det_spectral  [Fintype n] [DecidableEq n]
    (lo hi ) (M : Matrix n n ℝ) (hM : M.IsHermitian) :
    (kernelSeries lo hi M).det = ∏ i, scalarKernelSeries lo hi (hM.eigenvalues i) := by
  rw [kernelSeries_spectral lo hi M hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hu :
      (PowerSeries.C.mapMatrix (hM.eigenvectorUnitary : Matrix n n ℝ)).det *
      (PowerSeries.C.mapMatrix (star (hM.eigenvectorUnitary : Matrix n n ℝ))).det = 1 := by
    rw [← Matrix.det_mul, ← map_mul]
    have hunit  :=
      Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.property
    rw [hunit, map_one, Matrix.det_one]
  calc
    _ = (∏ i, scalarKernelSeries lo hi (hM.eigenvalues i)) *
      ((PowerSeries.C.mapMatrix (hM.eigenvectorUnitary : Matrix n n ℝ)).det *
      (PowerSeries.C.mapMatrix (star (hM.eigenvectorUnitary : Matrix n n ℝ))).det) := by ring
    _ = _ := by rw [hu, mul_one]
theorem scalarKernelSeries_coefficient_norm_le (lo hi x ) (hlo : 0 < lo)
    (hlt : lo < hi) (hx : x ∈ Set.Icc lo hi) (k ) :
    ‖PowerSeries.coeff k (scalarKernelSeries lo hi x)‖ ≤ 2 * intervalRho lo hi ^ k := by
  have hr := intervalRho_pos lo hi hlo hlt
  have ht : |(normalizedChebyshev lo hi k).eval x| ≤ 1 := by
    rw [normalizedChebyshev_eval]
    exact chebyshev_abs_le_one _ (interval_argument_mem lo hi x hlo hlt hx) k
  simp only [scalarKernelSeries, PowerSeries.coeff_mk, kernelCoefficientPolynomial,
    Polynomial.eval_mul, Polynomial.eval_C]
  by_cases hk : k = 0
  · subst k
    simp [normalizedChebyshev]
  · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_pow, abs_neg,
      abs_of_pos hr]
    simpa using mul_le_mul_of_nonneg_left ht (by positivity)
theorem scalarKernelSeries_summable_norm (lo hi x ) (hlo : 0 < lo)
    (hlt : lo < hi) (hx : x ∈ Set.Icc lo hi) :
    Summable (fun k => ‖PowerSeries.coeff k (scalarKernelSeries lo hi x)‖) := by
  have hg := (summable_geometric_of_lt_one (intervalRho_pos lo hi hlo hlt).le
    (intervalRho_lt_one lo hi hlo hlt)).mul_left 2
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (scalarKernelSeries_coefficient_norm_le lo hi x hlo hlt hx) hg
theorem scalarKernelSeries_tsum (lo hi x ) (hlo : 0 < lo)
    (hlt : lo < hi) (hx : x ∈ Set.Icc lo hi) :
    (∑' k, PowerSeries.coeff k (scalarKernelSeries lo hi x)) = intervalGeometricMean lo hi / x := by
  rw [((scalarKernelSeries_summable_norm lo hi x hlo hlt hx).of_norm).tsum_eq_zero_add]
  simp only [scalarKernelSeries, PowerSeries.coeff_mk, kernelCoefficientPolynomial,
    Polynomial.eval_mul, Polynomial.eval_C, Nat.add_one_ne_zero, ite_false,
    normalizedChebyshev_eval]
  norm_num only [Int.natCast_zero, Polynomial.Chebyshev.T_zero, Polynomial.eval_one,
    ite_true, one_mul]
  simp_rw [mul_assoc]
  rw [tsum_mul_left]
  have h_reciprocal_expansion_at_one : reciprocalSeries lo hi 1 x = (intervalGeometricMean lo hi : ℂ) / (x : ℂ) := by
    let y := (x - intervalCenter lo hi) / intervalHalfWidth lo hi
    let t := Real.arccos y
    have hy := interval_argument_mem lo hi x hlo hlt hx
    have hcos  := Real.cos_arccos hy.1 hy.2
    have hp := intervalRho_pos lo hi hlo hlt
    have hlt1 := intervalRho_lt_one lo hi hlo hlt
    have hq : ‖(-(intervalRho lo hi : ℂ) * (1 : ℂ))‖ < 1 := by
      simpa [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp] using hlt1
    have h_reciprocalSeries_eq_cosineKernel (z : ℂ) (hrep : (x - intervalCenter lo hi) / intervalHalfWidth lo hi = Real.cos t) (hq : ‖(-(intervalRho lo hi : ℂ) * z)‖ < 1) : reciprocalSeries lo hi z x = cosineKernel (-(intervalRho lo hi : ℂ) * z) t := by
      have hs := (cosine_geometric_hasSum (-(intervalRho lo hi : ℂ) * z) t hq).summable
      have heval (k : ℕ) :
          (Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval (Real.cos t) =
            Real.cos (((k + 1 : ℕ) : ℝ) * t) := by
        simp
      unfold reciprocalSeries cosineKernel
      rw [hrep]
      simp_rw [heval]
      rw [hs.tsum_eq_zero_add]
      simp only [pow_zero, Nat.cast_zero, zero_mul, Real.cos_zero, Complex.ofReal_one, mul_one]
      ring
    rw [h_reciprocalSeries_eq_cosineKernel 1 hcos.symm hq]
    simp only [mul_one]
    have h_interval_reciprocal_angular : cosineKernel (-(intervalRho lo hi : ℂ)) t =
        (intervalGeometricMean lo hi : ℂ) /
          (intervalCenter lo hi + intervalHalfWidth lo hi * Real.cos t : ℝ) := by
      let ρ := intervalRho lo hi
      have hρ := intervalRho_pos lo hi hlo hlt
      have hρ1 := intervalRho_lt_one lo hi hlo hlt
      have hq : ‖(-(ρ : ℂ))‖ < 1 := by simpa [ρ, norm_neg, Complex.norm_real, abs_of_pos hρ] using hρ1
      have h_interval_normalizations : (1 - intervalRho lo hi ^ 2) * intervalCenter lo hi =
          intervalGeometricMean lo hi * (1 + intervalRho lo hi ^ 2) ∧
        (1 - intervalRho lo hi ^ 2) * intervalHalfWidth lo hi =
          2 * intervalRho lo hi * intervalGeometricMean lo hi := by
        have hhi  := lt_trans hlo hlt
        have hu := Real.sqrt_pos.mpr hlo
        have hv := Real.sqrt_pos.mpr hhi
        have  := ne_of_gt (add_pos hv hu)
        unfold intervalRho intervalCenter intervalHalfWidth intervalGeometricMean
        rw [Real.sqrt_mul hlo.le]
        constructor <;> field_simp <;>
          nlinarith [Real.sq_sqrt hlo.le, Real.sq_sqrt hhi.le]
      have hn := h_interval_normalizations
      have hC := hn.1
      have hD := hn.2
      have h_interval_angular_pos : 0 < intervalCenter lo hi + intervalHalfWidth lo hi * Real.cos t := by
        have hc := Real.neg_one_le_cos t
        have hd : 0 < intervalHalfWidth lo hi := by unfold intervalHalfWidth; positivity
        have := mul_le_mul_of_nonneg_left hc hd.le
        unfold intervalCenter intervalHalfWidth at *
        nlinarith
      have hpositive := h_interval_angular_pos
      have hnonzero  := ne_of_gt hpositive
      have hgpositive  := Real.sqrt_pos.mpr (mul_pos hlo (lt_trans hlo hlt))
      have  := ne_of_gt hgpositive
      have hden :
          (1 - 2 * (-(ρ : ℂ)) * (Real.cos t : ℂ) + (-(ρ : ℂ)) ^ 2) *
          (intervalGeometricMean lo hi : ℂ) =
          (1 - (-(ρ : ℂ)) ^ 2) *
          (intervalCenter lo hi + intervalHalfWidth lo hi * Real.cos t : ℝ) := by
        exact_mod_cast (by linear_combination -hC - Real.cos t * hD)
      rw [cosineKernel_eq _ _ hq]
      have hdnonzero : (1 - 2 * (-(ρ : ℂ)) * (Real.cos t : ℂ) + (-(ρ : ℂ)) ^ 2) ≠ 0 := by
        have hA : (1 - ρ ^ 2 : ℝ) ≠ 0 := by nlinarith
        intro hz
        rw [hz, zero_mul] at hden
        have : ((1 - (-(ρ : ℂ)) ^ 2) *
          (intervalCenter lo hi + intervalHalfWidth lo hi * Real.cos t : ℝ)) ≠ 0 :=
          mul_ne_zero (by simpa only [neg_sq] using (show (1 - (ρ : ℂ) ^ 2) ≠ 0 by exact_mod_cast hA)) (by exact_mod_cast hnonzero)
        exact this hden.symm
      apply (div_eq_div_iff hdnonzero (by exact_mod_cast hnonzero)).mpr
      simpa only [mul_comm] using hden.symm
    rw [h_interval_reciprocal_angular]
    congr 1
    congr 1
    rw [hcos]
    have : intervalHalfWidth lo hi ≠ 0 := by unfold intervalHalfWidth; positivity
    field_simp
    ring
  have h := h_reciprocal_expansion_at_one
  unfold reciprocalSeries at h
  simp only [mul_one, ← Complex.ofReal_neg, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_tsum, ← Complex.ofReal_ofNat, ← Complex.ofReal_div] at h
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_add, Complex.ofReal_one] using h
theorem powerSeries_prod_summable_norm  [NormedCommRing R] [DecidableEq I]
    (s : Finset I) (f : I → PowerSeries R)
    (hf : ∀ i ∈ s, Summable (fun k => ‖PowerSeries.coeff k (f i)‖)) :
    Summable (fun k => ‖PowerSeries.coeff k (∏ i ∈ s, f i)‖) := by
  induction s using Finset.induction_on with
  | empty =>
    apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    simp only [Finset.mem_singleton] at hk
    simp [PowerSeries.coeff_one, hk]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm
      (hf a (Finset.mem_insert_self ..))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
    convert hs using 1
    funext k
    rw [PowerSeries.coeff_mul]
theorem powerSeries_prod_tsum  [NormedCommRing R] [CompleteSpace R] [DecidableEq I]
    (s : Finset I) (f : I → PowerSeries R)
    (hf : ∀ i ∈ s, Summable (fun k => ‖PowerSeries.coeff k (f i)‖)) :
    (∑' k, PowerSeries.coeff k (∏ i ∈ s, f i)) = ∏ i ∈ s, ∑' k, PowerSeries.coeff k (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [PowerSeries.coeff_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hc : (fun k => PowerSeries.coeff k (f a * ∏ i ∈ s, f i)) =
        RoughRegime.SeriesBounds.convolution
          (fun k => PowerSeries.coeff k (f a))
          (fun k => PowerSeries.coeff k (∏ i ∈ s, f i)) := by
      funext k
      exact PowerSeries.coeff_mul k _ _
    rw [hc, RoughRegime.SeriesBounds.convolution_tsum]
    · rw [ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]
    · exact hf a (Finset.mem_insert_self ..)
    · exact powerSeries_prod_summable_norm s f
        (fun i hi => hf i (Finset.mem_insert_of_mem hi))
theorem kernelSeries_det_summable_norm  [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (M : Matrix n n ℝ) (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) :
    Summable (fun k => ‖PowerSeries.coeff k (kernelSeries lo hi M).det‖) := by
  rw [kernelSeries_det_spectral lo hi M hM]
  apply powerSeries_prod_summable_norm
  intro i _
  exact scalarKernelSeries_summable_norm lo hi _ hlo hlt
    (hSpec (hM.eigenvalues_mem_spectrum_real i))
theorem kernelSeries_det_tsum  [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (M : Matrix n n ℝ) (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) :
    (∑' k, PowerSeries.coeff k (kernelSeries lo hi M).det) =
      intervalGeometricMean lo hi ^ Fintype.card n / M.det := by
  rw [kernelSeries_det_spectral lo hi M hM, powerSeries_prod_tsum]
  · simp_rw [scalarKernelSeries_tsum lo hi _ hlo hlt
      (hSpec (hM.eigenvalues_mem_spectrum_real _))]
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_univ]
    rw [hM.det_eq_prod_eigenvalues]
    rfl
  · intro i _
    exact scalarKernelSeries_summable_norm lo hi _ hlo hlt
      (hSpec (hM.eigenvalues_mem_spectrum_real i))
end RoughRegime.MatrixDeterminant
end
section
namespace RoughRegime.CombinedPolynomial
open RoughRegime.MatrixDeterminant RoughRegime.MatrixUpper RoughRegime.Upper
open scoped BigOperators
abbrev Variables {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) :=
  (Fin n0 × Fin n0) ⊕ ((i : Fin N) × (Fin (dims i) × Fin (dims i)))
def inverseVariableSeries {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) : PowerSeries (MvPolynomial (Variables n0 dims) ℝ) :=
  PowerSeries.map (MvPolynomial.rename
    (fun ab => (Sum.inl ab : Variables n0 dims))).toRingHom
    (variableKernelSeries lo hi a b)
def determinantVariableSeries {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (i : Fin N) : PowerSeries (MvPolynomial (Variables n0 dims) ℝ) :=
  PowerSeries.map (MvPolynomial.rename
    (fun ab => (Sum.inr ⟨i, ab⟩ : Variables n0 dims))).toRingHom
    (variableKernelSeries lo hi (n := Fin (dims i))).det
def combinedVariableSeries {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) : PowerSeries (MvPolynomial (Variables n0 dims) ℝ) :=
  inverseVariableSeries n0 dims lo hi a b * ∏ i, determinantVariableSeries n0 dims lo hi i
def combinedCoefficientPolynomial {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) (k : ℕ) : MvPolynomial (Variables n0 dims) ℝ :=
  PowerSeries.coeff k (combinedVariableSeries n0 dims lo hi a b)
lemma determinantVariableSeries_degree {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (i : Fin N) (k : ℕ) :
    (PowerSeries.coeff k (determinantVariableSeries n0 dims lo hi i)).totalDegree ≤ k := by
  rw [determinantVariableSeries, PowerSeries.coeff_map]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (by apply determinant_coefficient_totalDegree_le; intro i j t; simp only [variableKernelSeries, PowerSeries.coeff_mk]; exact (matrixEntryPolynomial_degree _ i j).trans (kernelCoefficientPolynomial_natDegree lo hi t))
theorem combinedCoefficientPolynomial_degree {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) (k : ℕ) :
    (combinedCoefficientPolynomial n0 dims lo hi a b k).totalDegree ≤ k := by
  apply coeff_totalDegree_mul_le
  · intro k
    rw [inverseVariableSeries, PowerSeries.coeff_map]
    apply (MvPolynomial.totalDegree_rename_le _ _).trans
    simp only [variableKernelSeries, PowerSeries.coeff_mk]
    exact (matrixEntryPolynomial_degree _ a b).trans (kernelCoefficientPolynomial_natDegree lo hi k)
  · intro j
    exact coeff_totalDegree_prod_le Finset.univ _
      (fun i _ => determinantVariableSeries_degree n0 dims lo hi i) j
def truncationEntryPolynomial {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) (m : ℕ) : MvPolynomial (Variables n0 dims) ℝ :=
  MvPolynomial.C ((intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹) *
    ∑ k ∈ Finset.range (m + 1), combinedCoefficientPolynomial n0 dims lo hi a b k
def entryValuation {N : ℕ} {n0 : ℕ} {dims : Fin N → ℕ}
    (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) : Variables n0 dims → ℝ
  | Sum.inl ab => M0 ab.1 ab.2
  | Sum.inr ⟨i, ab⟩ => M i ab.1 ab.2
lemma eval_renamed_series {V W : Type*} (f : V → W) (values : W → ℝ)
    (P : PowerSeries (MvPolynomial V ℝ)) :
    PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) values)
      (PowerSeries.map (MvPolynomial.rename f).toRingHom P) =
    PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (values ∘ f)) P := by
  ext k
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map]
  exact MvPolynomial.eval_rename f values _
theorem combinedCoefficientPolynomial_eval {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (M0 )
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) (a b : Fin n0) (k : ℕ) :
    MvPolynomial.eval (entryValuation M0 M)
      (combinedCoefficientPolynomial n0 dims lo hi a b k) =
      PowerSeries.coeff k (kernelSeries lo hi M0 a b * ∏ i, (kernelSeries lo hi (M i)).det) := by
  have h_combinedVariableSeries_eval : PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (entryValuation M0 M))
      (combinedVariableSeries n0 dims lo hi a b) =
      kernelSeries lo hi M0 a b * ∏ i, (kernelSeries lo hi (M i)).det := by
    have h_inverseVariableSeries_eval : PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (entryValuation M0 M))
        (inverseVariableSeries n0 dims lo hi a b) = kernelSeries lo hi M0 a b := by
      rw [inverseVariableSeries, eval_renamed_series]
      exact congrArg (fun A => A a b) (variableKernelSeries_map_eval lo hi M0)
    have h_determinantVariableSeries_eval (i : Fin N) : PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (entryValuation M0 M))
        (determinantVariableSeries n0 dims lo hi i) = (kernelSeries lo hi (M i)).det := by
      rw [determinantVariableSeries, eval_renamed_series]
      ext k
      rw [PowerSeries.coeff_map]
      have h_determinantCoefficientPolynomial_eval {n} [Fintype n] [DecidableEq n] (M) : MvPolynomial.eval (fun ij => M ij.1 ij.2)
          (determinantCoefficientPolynomial lo hi (n := n) k) =
          PowerSeries.coeff k (kernelSeries lo hi M).det := by
        have he := congrArg (fun f : PowerSeries ℝ => PowerSeries.coeff k f)
          ((PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun ij : n × n => M ij.1 ij.2))).map_det (variableKernelSeries lo hi (n := n)))
        rw [variableKernelSeries_map_eval] at he
        rw [PowerSeries.coeff_map] at he
        exact he
      exact h_determinantCoefficientPolynomial_eval (M i)
    simp only [combinedVariableSeries, map_mul, map_prod,
      h_inverseVariableSeries_eval, h_determinantVariableSeries_eval]
  have he := congrArg (fun P : PowerSeries ℝ => PowerSeries.coeff k P)
    h_combinedVariableSeries_eval
  rw [PowerSeries.coeff_map] at he
  exact he
end RoughRegime.CombinedPolynomial
namespace RoughRegime.MatrixKernel
open Polynomial RoughRegime.Upper RoughRegime.MatrixUpper RoughRegime.MatrixDeterminant
open scoped BigOperators Matrix.Norms.L2Operator
def matrixKernelCoefficient  [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℝ) (k : ℕ) : Matrix n n ℝ :=
  Polynomial.aeval M (kernelCoefficientPolynomial lo hi k)
theorem matrixKernelCoefficient_norm_le  [Fintype n] [DecidableEq n]
    (lo hi ) (hlo : 0 < lo) (hlt : lo < hi) (M : Matrix n n ℝ) (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) (k ) :
    ‖matrixKernelCoefficient lo hi M k‖ ≤ 2 * intervalRho lo hi ^ k := by
  have h_matrix_chebyshev_norm_le_one (k) : ‖Polynomial.aeval M (normalizedChebyshev lo hi k)‖ ≤ 1 := by
    rw [← cfc_polynomial _ M (Matrix.isHermitian_iff_isSelfAdjoint.mp hM)]
    apply norm_cfc_le (by norm_num)
    intro x hx
    rw [normalizedChebyshev_eval, Real.norm_eq_abs]
    exact chebyshev_abs_le_one _ (interval_argument_mem lo hi x hlo hlt (hSpec hx)) k
  have hr := intervalRho_pos lo hi hlo hlt
  have he : matrixKernelCoefficient lo hi M k =
      (if k = 0 then 1 else 2 * (-intervalRho lo hi) ^ k) •
        Polynomial.aeval M (normalizedChebyshev lo hi k) := by
    simp [matrixKernelCoefficient, kernelCoefficientPolynomial, Algebra.smul_def]
  rw [he, norm_smul]
  by_cases hk : k = 0
  · subst k
    simp only [ite_true, norm_one, one_mul, pow_zero]
    exact (h_matrix_chebyshev_norm_le_one 0).trans (by norm_num)
  · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_pow, abs_neg, abs_of_pos hr]
    simpa using mul_le_mul_of_nonneg_left
      (h_matrix_chebyshev_norm_le_one k)
      (by positivity)
theorem matrixKernelCoefficient_summable_norm  [Fintype n] [DecidableEq n]
    (lo hi ) (hlo : 0 < lo) (hlt : lo < hi) (M : Matrix n n ℝ) (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) :
    Summable (fun k => ‖matrixKernelCoefficient lo hi M k‖) := by
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (matrixKernelCoefficient_norm_le lo hi hlo hlt M hM hSpec)
  exact (summable_geometric_of_lt_one (intervalRho_pos lo hi hlo hlt).le
    (intervalRho_lt_one lo hi hlo hlt)).mul_left 2
theorem matrixKernelCoefficient_tsum  [Fintype n] [DecidableEq n]
    (lo hi ) (hlo : 0 < lo) (hlt : lo < hi) (M : Matrix n n ℝ) (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) :
    (∑' k, matrixKernelCoefficient lo hi M k) = intervalGeometricMean lo hi • M⁻¹ := by
  let U : Matrix n n ℝ := hM.eigenvectorUnitary
  have hd : Summable (fun k i => PowerSeries.coeff k (scalarKernelSeries lo hi (hM.eigenvalues i))) := by
    rw [Pi.summable]
    intro i
    exact (scalarKernelSeries_summable_norm lo hi _ hlo hlt
      (hSpec (hM.eigenvalues_mem_spectrum_real i))).of_norm
  have hds : (∑' k, fun i => PowerSeries.coeff k (scalarKernelSeries lo hi (hM.eigenvalues i))) =
      fun i => intervalGeometricMean lo hi / hM.eigenvalues i := by
    funext i
    rw [Pi.tsum_apply hd]
    exact scalarKernelSeries_tsum lo hi _ hlo hlt (hSpec (hM.eigenvalues_mem_spectrum_real i))
  have h_matrixKernelCoefficient_spectral k : matrixKernelCoefficient lo hi M k =
      (hM.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal (fun i => PowerSeries.coeff k (scalarKernelSeries lo hi (hM.eigenvalues i))) *
      star (hM.eigenvectorUnitary : Matrix n n ℝ) := by
    have he : matrixKernelCoefficient lo hi M k = coefficientMatrix k (kernelSeries lo hi M) := by
      ext i j
      simp only [matrixKernelCoefficient, coefficientMatrix, kernelSeries, PowerSeries.coeff_mk]
    rw [he, kernelSeries_spectral lo hi M hM, coefficientMatrix_mul_constant,
      coefficientMatrix_constant_mul, coefficientMatrix_diagonal]
  have hdmat  := hd.matrix_diagonal
  simp_rw [h_matrixKernelCoefficient_spectral]
  rw [(hdmat.mul_left (hM.eigenvectorUnitary : Matrix n n ℝ)).tsum_mul_right,
    hdmat.tsum_mul_left, ← Matrix.diagonal_tsum, hds]
  have h_matrix_inverse_spectral : M⁻¹ = (hM.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal (fun i => (hM.eigenvalues i)⁻¹) *
      star (hM.eigenvectorUnitary : Matrix n n ℝ) := by
    have hn  := fun i =>
    ne_of_gt (hlo.trans_le (hSpec (hM.eigenvalues_mem_spectrum_real i)).1)
    let U : Matrix n n ℝ := hM.eigenvectorUnitary
    have hU  := Unitary.star_mul_self_of_mem hM.eigenvectorUnitary.property
    have hU'  := Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.property
    have hM' : M = U * Matrix.diagonal hM.eigenvalues * star U := by
      simpa only [U, Unitary.conjStarAlgAut_apply, Function.comp_apply,
        RCLike.ofReal_real_eq_id, Function.id_comp] using hM.spectral_theorem
    apply Matrix.inv_eq_left_inv
    conv_lhs => arg 2; rw [hM']
    calc
      _ = U * Matrix.diagonal (fun i => (hM.eigenvalues i)⁻¹) *
          (star U * U) * Matrix.diagonal hM.eigenvalues * star U := by noncomm_ring
      _ = U * (Matrix.diagonal (fun i => (hM.eigenvalues i)⁻¹) *
          Matrix.diagonal hM.eigenvalues) * star U := by rw [hU, mul_one]; noncomm_ring
      _ = 1 := by
        rw [Matrix.diagonal_mul_diagonal]
        have hd : Matrix.diagonal (fun i => (hM.eigenvalues i)⁻¹ * hM.eigenvalues i) =
            (1 : Matrix n n ℝ) := by
          simp only [inv_mul_cancel₀ (hn _), Matrix.diagonal_one]
        rw [hd, mul_one, hU']
  rw [h_matrix_inverse_spectral, ← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
  congr 2
end RoughRegime.MatrixKernel
namespace RoughRegime.CombinedAnalytic
open RoughRegime.MatrixDeterminant RoughRegime.MatrixKernel RoughRegime.SeriesBounds RoughRegime.Upper RoughRegime.CombinedPolynomial
open scoped BigOperators Matrix.Norms.L2Operator
variable {N n0 : ℕ} {dims : Fin N → ℕ}
def matrixSeries  [Fintype n] [DecidableEq n] (K : Matrix n n (PowerSeries ℝ)) : PowerSeries (Matrix n n ℝ) :=
  PowerSeries.mk (fun k => coefficientMatrix k K)
lemma matrixSeries_coefficient  [Fintype n] [DecidableEq n]
    (K : Matrix n n (PowerSeries ℝ)) (k : ℕ) :
    PowerSeries.coeff k (matrixSeries K) = coefficientMatrix k K := PowerSeries.coeff_mk ..
theorem matrixSeries_scalar_mul  [Fintype n] [DecidableEq n]
    (K g) :
    matrixSeries (fun i j => K i j * g) =
      matrixSeries K * PowerSeries.map (Matrix.scalar n) g := by
  ext k i j
  simp only [matrixSeries, PowerSeries.coeff_mk, coefficientMatrix, PowerSeries.coeff_mul,
    PowerSeries.coeff_map, Matrix.sum_apply, Matrix.scalar_apply, Matrix.mul_diagonal]
theorem addFactors_eq_powerSeries_coeff  [Semiring R]
    (f ) (gs : List (PowerSeries R)) (k ) :
    addFactors (fun j => PowerSeries.coeff j f)
      (gs.map (fun g j => PowerSeries.coeff j g)) k =
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
theorem scalarMatrix_coefficient_norm  [Fintype n] [DecidableEq n] [Nonempty n]
    (g : PowerSeries ℝ) (k : ℕ) :
    ‖PowerSeries.coeff k (PowerSeries.map (Matrix.scalar n) g)‖ = ‖PowerSeries.coeff k g‖ := by
  rw [PowerSeries.coeff_map]
  exact norm_algebraMap' (Matrix n n ℝ) _
lemma mapped_scalar_prod_reverse  [Fintype n] [DecidableEq n]
    (gs : List (PowerSeries ℝ)) :
    (gs.map (PowerSeries.map (Matrix.scalar n))).reverse.prod =
      PowerSeries.map (Matrix.scalar n) gs.prod := by
  rw [← List.map_reverse, ← map_list_prod, List.prod_reverse]
def combinedSeries  
    (lo hi : ℝ) (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) :
    PowerSeries (Matrix (Fin n0) (Fin n0) ℝ) :=
  matrixSeries (kernelSeries lo hi M0) *
    PowerSeries.map (Matrix.scalar (Fin n0)) (∏ i, (kernelSeries lo hi (M i)).det)
theorem combinedSeries_coefficient_entry  
    (lo hi M0 M a b k) :
    (PowerSeries.coeff k (combinedSeries lo hi M0 M)) a b =
      MvPolynomial.eval (entryValuation M0 M)
        (combinedCoefficientPolynomial n0 dims lo hi a b k) := by
  rw [combinedCoefficientPolynomial_eval, combinedSeries, ← matrixSeries_scalar_mul]
  simp only [matrixSeries, PowerSeries.coeff_mk, coefficientMatrix]
def eigenvalueSeriesList  
    (lo hi : ℝ) (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (hM : ∀ i, (M i).IsHermitian) : List (PowerSeries ℝ) :=
  (Finset.univ : Finset ((i : Fin N) × Fin (dims i))).toList.map
    (fun ij => scalarKernelSeries lo hi ((hM ij.1).eigenvalues ij.2))
theorem combinedSeries_coefficient_eq_addFactors  
    (lo hi M0)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (hM : ∀ i, (M i).IsHermitian) (k : ℕ) :
    PowerSeries.coeff k (combinedSeries lo hi M0 M) =
      addFactors (matrixKernelCoefficient lo hi M0)
        ((eigenvalueSeriesList lo hi M hM).map
          (fun g j => (Matrix.scalar (Fin n0)) (PowerSeries.coeff j g))) k := by
  have he := addFactors_eq_powerSeries_coeff (matrixSeries (kernelSeries lo hi M0))
    ((eigenvalueSeriesList lo hi M hM).map (PowerSeries.map (Matrix.scalar (Fin n0)))) k
  have h_eigenvalueSeriesList_prod : (eigenvalueSeriesList lo hi M hM).prod = ∏ i, (kernelSeries lo hi (M i)).det := by
    rw [eigenvalueSeriesList, Finset.prod_map_toList, Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    exact (kernelSeries_det_spectral lo hi (M i) (hM i)).symm
  rw [mapped_scalar_prod_reverse, h_eigenvalueSeriesList_prod] at he
  have hf : (fun j => PowerSeries.coeff j (matrixSeries (kernelSeries lo hi M0))) =
      matrixKernelCoefficient lo hi M0 := by
    funext j
    ext a b
    simp only [matrixSeries, PowerSeries.coeff_mk, coefficientMatrix, kernelSeries,
      matrixKernelCoefficient]
  rw [hf] at he
  have hg : ((eigenvalueSeriesList lo hi M hM).map
      (PowerSeries.map (Matrix.scalar (Fin n0)))).map (fun g j => PowerSeries.coeff j g) =
      (eigenvalueSeriesList lo hi M hM).map
        (fun g j => (Matrix.scalar (Fin n0)) (PowerSeries.coeff j g)) := by
    rw [List.map_map]
    congr 1
  rw [hg] at he
  exact he.symm
theorem scalarMatrix_tsum {n : Type*} [Fintype n] [DecidableEq n]
    (f : ℕ → ℝ) (hf : Summable f) :
    (∑' k, (Matrix.scalar n) (f k)) = (Matrix.scalar n) (∑' k, f k) := by
  exact (hf.hasSum.map (Matrix.scalar n) (by change Continuous (fun x => Matrix.diagonal (fun _ => x)); exact (continuous_pi (fun _ => continuous_id)).matrix_diagonal)).tsum_eq
def truncationMatrix  
    (lo hi : ℝ) (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) (m : ℕ) :
    Matrix (Fin n0) (Fin n0) ℝ :=
  fun a b => MvPolynomial.eval (entryValuation M0 M) (truncationEntryPolynomial n0 dims lo hi a b m)
theorem truncationMatrix_eq_scaled_sum  
    (lo hi : ℝ) (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) (m : ℕ) :
    truncationMatrix lo hi M0 M m =
      (intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹ •
        ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k (combinedSeries lo hi M0 M) := by
  ext a b
  have h_truncationEntryPolynomial_eval (a : Fin n0) (b : Fin n0) (m : ℕ) : MvPolynomial.eval (entryValuation M0 M) (truncationEntryPolynomial n0 dims lo hi a b m) =
      (intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹ *
        ∑ k ∈ Finset.range (m + 1),
          PowerSeries.coeff k (kernelSeries lo hi M0 a b * ∏ i, (kernelSeries lo hi (M i)).det) := by
    simp [truncationEntryPolynomial, combinedCoefficientPolynomial_eval]
  simp only [truncationMatrix, h_truncationEntryPolynomial_eval, Matrix.smul_apply,
    smul_eq_mul, Matrix.sum_apply, combinedSeries_coefficient_entry,
    combinedCoefficientPolynomial_eval]
theorem matrix_determinant_truncation_error  [Nonempty (Fin n0)] 
    (lo hi ) (hlo : 0 < lo) (hlt : lo < hi)
    (M0 : Matrix (Fin n0) (Fin n0) ℝ) (hM0 : M0.IsHermitian)
    (hSpec0 : spectrum ℝ M0 ⊆ Set.Icc lo hi)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (hM : ∀ i, (M i).IsHermitian) (hSpec : ∀ i, spectrum ℝ (M i) ⊆ Set.Icc lo hi) (m : ℕ) :
    ‖(∏ i, (M i).det)⁻¹ • M0⁻¹ - truncationMatrix lo hi M0 M m‖ ≤
      2 ^ ((∑ i, dims i) + 1) * (intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹ *
        ((m + 1 : ℕ) : ℝ) ^ (∑ i, dims i) * intervalRho lo hi ^ m *
        ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (∑ i, dims i) * intervalRho lo hi ^ k := by
  let ν : ℕ := ∑ i, dims i
  let α : ℝ := (intervalGeometricMean lo hi ^ (ν + 1))⁻¹
  have hg : intervalGeometricMean lo hi ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (mul_pos hlo (hlo.trans hlt)))
  have hα : 0 ≤ α := by dsimp [α, intervalGeometricMean]; positivity
  have htarget : (∏ i, (M i).det)⁻¹ • M0⁻¹ =
      α • ∑' k, PowerSeries.coeff k (combinedSeries lo hi M0 M) := by
    have h_combinedSeries_tsum : (∑' k, PowerSeries.coeff k (combinedSeries lo hi M0 M)) =
      (intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1) / ∏ i, (M i).det) • M0⁻¹ := by
      let D : PowerSeries ℝ := ∏ i, (kernelSeries lo hi (M i)).det
      have hDn : Summable (fun k => ‖PowerSeries.coeff k D‖) := by
        exact powerSeries_prod_summable_norm Finset.univ _ (fun i _ =>
          kernelSeries_det_summable_norm lo hi hlo hlt (M i) (hM i) (hSpec i))
      have hDmn : Summable (fun k => ‖PowerSeries.coeff k
          (PowerSeries.map (Matrix.scalar (Fin n0)) D)‖) := by
        simpa only [scalarMatrix_coefficient_norm] using hDn
      have hcoef : (fun k => PowerSeries.coeff k (combinedSeries lo hi M0 M)) =
          convolution (matrixKernelCoefficient lo hi M0)
            (fun k => PowerSeries.coeff k (PowerSeries.map (Matrix.scalar (Fin n0)) D)) := by
        funext k
        rw [combinedSeries, PowerSeries.coeff_mul]
        apply Finset.sum_congr rfl
        intro ij _
        congr 1
        ext a b
        simp only [matrixSeries, PowerSeries.coeff_mk, coefficientMatrix, kernelSeries,
          matrixKernelCoefficient]
      rw [hcoef, convolution_tsum _ _
        (matrixKernelCoefficient_summable_norm lo hi hlo hlt M0 hM0 hSpec0) hDmn,
        matrixKernelCoefficient_tsum lo hi hlo hlt M0 hM0 hSpec0]
      simp only [PowerSeries.coeff_map]
      have h_determinantProduct_tsum : (∑' k, PowerSeries.coeff k (∏ i, (kernelSeries lo hi (M i)).det)) =
          intervalGeometricMean lo hi ^ (∑ i, dims i) / ∏ i, (M i).det := by
        rw [powerSeries_prod_tsum]
        · simp_rw [kernelSeries_det_tsum lo hi hlo hlt _ (hM _) (hSpec _), Fintype.card_fin]
          rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
        · intro i _
          exact kernelSeries_det_summable_norm lo hi hlo hlt (M i) (hM i) (hSpec i)
      rw [scalarMatrix_tsum _ hDn.of_norm, h_determinantProduct_tsum,
        Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal, smul_smul]
      congr 1
      rw [pow_succ, div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [h_combinedSeries_tsum, smul_smul]
    congr 1
    dsimp [α, ν]
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hg), one_mul]
  rw [htarget, truncationMatrix_eq_scaled_sum, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]
  have h_combinedSeries_coefficient_norm_le (k : ℕ) : ‖PowerSeries.coeff k (combinedSeries lo hi M0 M)‖ ≤
      2 ^ ((∑ i, dims i) + 1) * ((k + 1 : ℕ) : ℝ) ^ (∑ i, dims i) * intervalRho lo hi ^ k := by
    rw [combinedSeries_coefficient_eq_addFactors lo hi M0 M hM]
    have hg : ∀ g ∈ (eigenvalueSeriesList lo hi M hM).map
        (fun g j => (Matrix.scalar (Fin n0)) (PowerSeries.coeff j g)),
        ∀ j, ‖g j‖ ≤ 2 * intervalRho lo hi ^ j := by
      intro g hg j
      rcases List.mem_map.mp hg with ⟨q, hq, rfl⟩
      rcases List.mem_map.mp hq with ⟨ij, _, rfl⟩
      change ‖PowerSeries.coeff j (PowerSeries.map (Matrix.scalar (Fin n0))
        (scalarKernelSeries lo hi ((hM ij.1).eigenvalues ij.2)))‖ ≤ _
      rw [scalarMatrix_coefficient_norm]
      exact scalarKernelSeries_coefficient_norm_le lo hi _ hlo hlt
        (hSpec ij.1 ((hM ij.1).eigenvalues_mem_spectrum_real ij.2)) j
    have hh := addFactors_coefficient_bound (matrixKernelCoefficient lo hi M0)
      ((eigenvalueSeriesList lo hi M hM).map
        (fun g j => (Matrix.scalar (Fin n0)) (PowerSeries.coeff j g)))
      (intervalRho lo hi) 2 2 (intervalRho_pos lo hi hlo hlt) (by norm_num) (by norm_num)
      (matrixKernelCoefficient_norm_le lo hi hlo hlt M0 hM0 hSpec0) hg k
    have h_eigenvalueSeriesList_length : (eigenvalueSeriesList lo hi M hM).length = ∑ i, dims i := by
      simp only [eigenvalueSeriesList, List.length_map, Finset.length_toList, Finset.card_univ,
        Fintype.card_sigma, Fintype.card_fin]
    simpa only [List.length_map, h_eigenvalueSeriesList_length, pow_succ, mul_assoc,
      mul_left_comm, mul_comm] using hh
  have he := series_truncation_bound
    (fun k => PowerSeries.coeff k (combinedSeries lo hi M0 M)) ν m (intervalRho lo hi)
    (2 ^ (ν + 1)) (intervalRho_pos lo hi hlo hlt) (intervalRho_lt_one lo hi hlo hlt)
    (by positivity) h_combinedSeries_coefficient_norm_le
  apply (mul_le_mul_of_nonneg_left he hα).trans_eq
  ring
end RoughRegime.CombinedAnalytic
end
open MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
variable {n : Type*} {r : ℕ}
section
open Polynomial RoughRegime.Upper RoughRegime.MatrixUpper RoughRegime.CombinedPolynomial RoughRegime.CombinedAnalytic
open scoped BigOperators Matrix.Norms.L2Operator
abbrev parentInverseVariables (r : ℕ) := Variables r (fun _ : Fin 1 => r)
def parentInverseEntryPolynomial (a b : ℝ) (r m : ℕ) (i j : Fin r) :
    MvPolynomial (parentInverseVariables r) ℝ :=
  truncationEntryPolynomial r (fun _ : Fin 1 => r) a b i j m
def parentInversePolynomial  (a b : ℝ)
    (A C : Matrix (Fin r) (Fin r) ℝ) (m : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  truncationMatrix a b A (fun _ : Fin 1 => C) m
def parentInverseErrorConstant (a b : ℝ) (r : ℕ) : ℝ :=
  2 ^ (r + 1) * (intervalGeometricMean a b ^ (r + 1))⁻¹ *
    ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ r * intervalRho a b ^ k
theorem parentInverseErrorConstant_pos (a b : ℝ) (ha : 0 < a) (hab : a < b) (r : ℕ) :
    0 < parentInverseErrorConstant a b r := by
  have hr := intervalRho_pos a b ha hab
  have hr1 := intervalRho_lt_one a b ha hab
  have  :=
    Real.sqrt_pos.mpr (mul_pos ha (ha.trans hab))
  have hs := RoughRegime.SeriesBounds.weighted_geometric_summable r (intervalRho a b) hr hr1
  have : 0 < ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ r * intervalRho a b ^ k := by
    apply hs.tsum_pos (fun k => by positivity) 0
    simp
  unfold parentInverseErrorConstant
  positivity
def matrixSimilarity  [Fintype n] [DecidableEq n]
    (Q : (Matrix n n ℝ)ˣ) : Matrix n n ℝ →ₐ[ℝ] Matrix n n ℝ where
  toFun A := (Q : Matrix n n ℝ) * A * (↑Q⁻¹ : Matrix n n ℝ)
  map_one' := by simp
  map_mul' A B := by simp [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    simp
theorem aeval_matrixSimilarity  [Fintype n] [DecidableEq n]
    (Q : (Matrix n n ℝ)ˣ) (A : Matrix n n ℝ) (P : ℝ[X]) :
    Polynomial.aeval (matrixSimilarity Q A) P = matrixSimilarity Q (Polynomial.aeval A P) := Polynomial.aeval_algHom_apply (matrixSimilarity Q) A P
theorem matrixSimilarity_norm_le  [Fintype n] [DecidableEq n]
    (Q : (Matrix n n ℝ)ˣ) (A : Matrix n n ℝ) :
    ‖matrixSimilarity Q A‖ ≤ ‖(Q : Matrix n n ℝ)‖ * ‖(↑Q⁻¹ : Matrix n n ℝ)‖ * ‖A‖ := by
  calc
    _ ≤ ‖(Q : Matrix n n ℝ) * A‖ * ‖(↑Q⁻¹ : Matrix n n ℝ)‖ := norm_mul_le _ _
    _ ≤ ‖(Q : Matrix n n ℝ)‖ * ‖A‖ * ‖(↑Q⁻¹ : Matrix n n ℝ)‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = _ := by ring
theorem matrixSimilarity_inv  [Fintype n] [DecidableEq n]
    (Q : (Matrix n n ℝ)ˣ) (A : Matrix n n ℝ) :
    (matrixSimilarity Q A)⁻¹ = matrixSimilarity Q A⁻¹ := by
  change ((Q : Matrix n n ℝ) * A * (↑Q⁻¹ : Matrix n n ℝ))⁻¹ =
    (Q : Matrix n n ℝ) * A⁻¹ * (↑Q⁻¹ : Matrix n n ℝ)
  simp only [Matrix.mul_inv_rev, ← Matrix.coe_units_inv, inv_inv, Matrix.mul_assoc]
open RoughRegime.MatrixDeterminant
theorem kernelSeries_coefficient  [Fintype n] [DecidableEq n]
    (a b : ℝ) (A : Matrix n n ℝ) (k : ℕ) :
    coefficientMatrix k (kernelSeries a b A) =
      Polynomial.aeval A (kernelCoefficientPolynomial a b k) := by
  ext i j
  simp only [coefficientMatrix, kernelSeries, PowerSeries.coeff_mk]
theorem kernelSeries_det_matrixSimilarity  [Fintype n] [DecidableEq n]
    (a b : ℝ) (Q : (Matrix n n ℝ)ˣ) (A : Matrix n n ℝ) :
    (kernelSeries a b (matrixSimilarity Q A)).det = (kernelSeries a b A).det := by
  have h_kernelSeries_matrixSimilarity : kernelSeries a b (matrixSimilarity Q A) =
      PowerSeries.C.mapMatrix (Q : Matrix n n ℝ) * kernelSeries a b A *
        PowerSeries.C.mapMatrix (↑Q⁻¹ : Matrix n n ℝ) := by
    ext i j k
    change (coefficientMatrix k (kernelSeries a b (matrixSimilarity Q A))) i j =
      (coefficientMatrix k (_ * _ * _)) i j
    rw [coefficientMatrix_mul_constant, coefficientMatrix_constant_mul, kernelSeries_coefficient, kernelSeries_coefficient]
    exact congrArg (fun M : Matrix n n ℝ => M i j)
      (aeval_matrixSimilarity Q A (kernelCoefficientPolynomial a b k))
  rw [h_kernelSeries_matrixSimilarity]
  have h := Matrix.det_units_conj
    (Units.map (PowerSeries.C.mapMatrix : Matrix n n ℝ →+* Matrix n n (PowerSeries ℝ)).toMonoidHom Q)
    (kernelSeries a b A)
  simpa using h
theorem matrixSeries_kernel_matrixSimilarity 
    (a b : ℝ) (Q : (Matrix (Fin r) (Fin r) ℝ)ˣ) (A : Matrix (Fin r) (Fin r) ℝ) :
    matrixSeries (kernelSeries a b (matrixSimilarity Q A)) =
      PowerSeries.map (matrixSimilarity Q).toRingHom (matrixSeries (kernelSeries a b A)) := by
  apply PowerSeries.ext
  intro k
  rw [matrixSeries_coefficient, PowerSeries.coeff_map, matrixSeries_coefficient,
    kernelSeries_coefficient, kernelSeries_coefficient]
  exact aeval_matrixSimilarity Q A (kernelCoefficientPolynomial a b k)
theorem matrixSimilarity_scalar  [Fintype n] [DecidableEq n]
    (Q : (Matrix n n ℝ)ˣ) (x : ℝ) :
    matrixSimilarity Q (Matrix.scalar n x) = Matrix.scalar n x := (matrixSimilarity Q).commutes x
theorem combinedSeries_parent_matrixSimilarity 
    (a b : ℝ) (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) (A C : Matrix (Fin r) (Fin r) ℝ) :
    combinedSeries a b (matrixSimilarity Q A) (fun _ : Fin 1 => matrixSimilarity R C) =
      PowerSeries.map (matrixSimilarity Q).toRingHom (combinedSeries a b A (fun _ : Fin 1 => C)) := by
  rw [combinedSeries, combinedSeries, map_mul, matrixSeries_kernel_matrixSimilarity]
  simp only [Fin.prod_univ_one, kernelSeries_det_matrixSimilarity]
  congr 1
  apply PowerSeries.ext
  intro k
  simp only [PowerSeries.coeff_map]
  exact (matrixSimilarity_scalar Q _).symm
theorem parent_inverse_similar_error  [NeZero r]
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (A C : Matrix (Fin r) (Fin r) ℝ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : spectrum ℝ A ⊆ Set.Icc a b) (hSpecC : spectrum ℝ C ⊆ Set.Icc a b)
    (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) (χ : ℝ)
    (hχ : ‖(Q : Matrix (Fin r) (Fin r) ℝ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ)
    (m : ℕ) :
    ‖(matrixSimilarity R C).det⁻¹ • (matrixSimilarity Q A)⁻¹ -
      parentInversePolynomial a b (matrixSimilarity Q A) (matrixSimilarity R C) m‖ ≤
        χ * parentInverseErrorConstant a b r * ((m + 1 : ℕ) : ℝ) ^ r *
          Real.exp (-↑m * exteriorTau ((a + b) / (b - a))) := by
  have hdet : (matrixSimilarity R C).det = C.det := Matrix.det_units_conj R C
  have h_parentInversePolynomial_matrixSimilarity : parentInversePolynomial a b (matrixSimilarity Q A) (matrixSimilarity R C) m =
      matrixSimilarity Q (parentInversePolynomial a b A C m) := by
    rw [parentInversePolynomial, parentInversePolynomial,
      truncationMatrix_eq_scaled_sum, truncationMatrix_eq_scaled_sum]
    simp_rw [combinedSeries_parent_matrixSimilarity, PowerSeries.coeff_map]
    rw [map_smul, map_sum]
    rfl
  rw [hdet, matrixSimilarity_inv, h_parentInversePolynomial_matrixSimilarity, ← map_smul, ← map_sub]
  apply (matrixSimilarity_norm_le Q _).trans
  apply (mul_le_mul_of_nonneg_right hχ (norm_nonneg _)).trans
  have h_parent_inverse_polynomial_error : ‖C.det⁻¹ • A⁻¹ - parentInversePolynomial a b A C m‖ ≤
      parentInverseErrorConstant a b r * ((m + 1 : ℕ) : ℝ) ^ r *
        Real.exp (-↑m * exteriorTau ((a + b) / (b - a))) := by
    have h := matrix_determinant_truncation_error (N := 1) (dims := fun _ : Fin 1 => r)
      a b ha hab A hA hSpecA (fun _ : Fin 1 => C) (fun _ => hC) (fun _ => hSpecC) m
    simp only [Fin.sum_univ_one, Fin.prod_univ_one] at h
    apply h.trans_eq
    have h_inverse_ratio_pow : intervalRho a b ^ m = Real.exp (-↑m * exteriorTau ((a + b) / (b - a))) := by
      have h_inverse_ratio_exterior_exponent : intervalRho a b = Real.exp (-exteriorTau ((a + b) / (b - a))) := by
        have h_exp_neg_exteriorTau : Real.exp (-exteriorTau ((a + b) / (b - a))) =
            (Real.sqrt b - Real.sqrt a) / (Real.sqrt b + Real.sqrt a) := by
          have  := sub_pos.mpr (Real.sqrt_lt_sqrt (le_of_lt ha) hab)
          rw [exteriorTau_sqrt_ratio a b ha hab, Real.exp_neg, Real.exp_log (by have := ha.trans hab; positivity), inv_div]
        exact h_exp_neg_exteriorTau.symm
      rw [h_inverse_ratio_exterior_exponent, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [h_inverse_ratio_pow]
    unfold parentInverseErrorConstant
    ring
  apply (mul_le_mul_of_nonneg_left h_parent_inverse_polynomial_error ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hχ)).trans_eq
  ring
def incrementNumerator  [Fintype n] [DecidableEq n]
    (G C T : Matrix n n ℝ) (β βminus : n → ℝ) : n → ℝ :=
  C.det • β - G.mulVec (T.mulVec (C.adjugate.mulVec βminus))
theorem incrementNumerator_identity  [Fintype n] [DecidableEq n]
    (G C T : Matrix n n ℝ) (hG : G.det ≠ 0) (hC : C.det ≠ 0) (β βminus : n → ℝ) :
    C.det⁻¹ • G⁻¹.mulVec (incrementNumerator G C T β βminus) =
      G⁻¹.mulVec β - T.mulVec (C⁻¹.mulVec βminus) := by
  rw [incrementNumerator, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hG), Matrix.one_mulVec,
    smul_sub, smul_smul, inv_mul_cancel₀ hC, one_smul]
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mulVec, Matrix.mulVec_smul]
theorem incrementNumerator_factorization  [Fintype n] [DecidableEq n]
    (G C T : Matrix n n ℝ) (hG : G.det ≠ 0) (hC : C.det ≠ 0) (β βminus : n → ℝ) :
    incrementNumerator G C T β βminus =
      C.det • G.mulVec (G⁻¹.mulVec β - T.mulVec (C⁻¹.mulVec βminus)) := by
  simpa only [Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hC, one_smul,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hG), Matrix.one_mulVec] using (congrArg (fun v : n → ℝ => C.det • G.mulVec v) (incrementNumerator_identity G C T hG hC β βminus))
theorem spectral_det_ne_zero  [Fintype n] [DecidableEq n]
    (a b : ℝ) (ha : 0 < a) (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (hSpec : spectrum ℝ A ⊆ Set.Icc a b) : A.det ≠ 0 := by
  rw [hA.det_eq_prod_eigenvalues]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact ne_of_gt (ha.trans_le (hSpec (hA.eigenvalues_mem_spectrum_real i)).1)
theorem spectral_det_abs_le  [Fintype n] [DecidableEq n]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (hSpec : spectrum ℝ A ⊆ Set.Icc a b) : |A.det| ≤ b ^ Fintype.card n := by
  rw [hA.det_eq_prod_eigenvalues, Finset.abs_prod]
  calc
    ∏ i, |hA.eigenvalues i| ≤ ∏ _i : n, b := by
      apply Finset.prod_le_prod₀
      · intro i hi; exact abs_nonneg _
      · intro i hi
        have h := hSpec (hA.eigenvalues_mem_spectrum_real i)
        rw [abs_of_nonneg (ha.le.trans h.1)]
        exact h.2
    _ = _ := by simp
theorem increment_numerator_norm_le  [NeZero r]
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (A C T : Matrix (Fin r) (Fin r) ℝ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : spectrum ℝ A ⊆ Set.Icc a b) (hSpecC : spectrum ℝ C ⊆ Set.Icc a b)
    (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) (χ : ℝ)
    (hχ : ‖(Q : Matrix (Fin r) (Fin r) ℝ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ)
    (β βminus : Fin r → ℝ) :
    let G := matrixSimilarity Q A
    let Cminus := matrixSimilarity R C
    ‖(EuclideanSpace.equiv (Fin r) ℝ).symm (incrementNumerator G Cminus T β βminus)‖ ≤
      χ * b ^ (r + 1) * ‖(EuclideanSpace.equiv (Fin r) ℝ).symm
        (G⁻¹.mulVec β - T.mulVec (Cminus⁻¹.mulVec βminus))‖ := by
  let G := matrixSimilarity Q A
  let Cminus := matrixSimilarity R C
  let δ := G⁻¹.mulVec β - T.mulVec (Cminus⁻¹.mulVec βminus)
  have  := ha.trans hab
  change ‖(EuclideanSpace.equiv (Fin r) ℝ).symm (incrementNumerator G Cminus T β βminus)‖ ≤ _
  rw [incrementNumerator_factorization G Cminus T (by rw [show G.det = A.det from Matrix.det_units_conj Q A]; exact spectral_det_ne_zero a b ha A hA hSpecA) (by rw [show Cminus.det = C.det from Matrix.det_units_conj R C]; exact spectral_det_ne_zero a b ha C hC hSpecC)]
  change ‖Cminus.det • (EuclideanSpace.equiv (Fin r) ℝ).symm (G.mulVec δ)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  calc
    |Cminus.det| * ‖(EuclideanSpace.equiv (Fin r) ℝ).symm (G.mulVec δ)‖ ≤
        b ^ r * (‖G‖ * ‖(EuclideanSpace.equiv (Fin r) ℝ).symm δ‖) :=
      mul_le_mul (by rw [show Cminus.det = C.det from Matrix.det_units_conj R C]; simpa using spectral_det_abs_le a b ha hab C hC hSpecC) (G.l2_opNorm_mulVec ((EuclideanSpace.equiv (Fin r) ℝ).symm δ)) (norm_nonneg _) (by positivity)
    _ ≤ b ^ r * ((χ * b) * ‖(EuclideanSpace.equiv (Fin r) ℝ).symm δ‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by apply (matrixSimilarity_norm_le Q A).trans; apply (mul_le_mul_of_nonneg_right hχ (norm_nonneg A)).trans; have hs  := Matrix.isHermitian_iff_isSelfAdjoint.mp hA; exact mul_le_mul_of_nonneg_left (by rw [← cfc_id ℝ A hs]; apply norm_cfc_le (by linarith); intro x hx; have h := hSpecA hx; simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg (ha.le.trans h.1)] using h.2) ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hχ)) (norm_nonneg _)) (by positivity)
    _ = _ := by rw [pow_succ]; ring
theorem increment_polynomial_error  [NeZero r]
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (A C T : Matrix (Fin r) (Fin r) ℝ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : spectrum ℝ A ⊆ Set.Icc a b) (hSpecC : spectrum ℝ C ⊆ Set.Icc a b)
    (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) (χ : ℝ)
    (hχ : ‖(Q : Matrix (Fin r) (Fin r) ℝ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ)
    (β βminus : Fin r → ℝ) (m : ℕ) :
    let G := matrixSimilarity Q A
    let Cminus := matrixSimilarity R C
    let N := incrementNumerator G Cminus T β βminus
    ‖(EuclideanSpace.equiv (Fin r) ℝ).symm
      ((parentInversePolynomial a b G Cminus m).mulVec N -
        (G⁻¹.mulVec β - T.mulVec (Cminus⁻¹.mulVec βminus)))‖ ≤
      (χ * parentInverseErrorConstant a b r * ((m + 1 : ℕ) : ℝ) ^ r *
        Real.exp (-↑m * exteriorTau ((a + b) / (b - a)))) *
        ‖(EuclideanSpace.equiv (Fin r) ℝ).symm N‖ := by
  dsimp only
  let G := matrixSimilarity Q A
  let Cminus := matrixSimilarity R C
  let N := incrementNumerator G Cminus T β βminus
  change ‖(EuclideanSpace.equiv (Fin r) ℝ).symm
    ((parentInversePolynomial a b G Cminus m).mulVec N -
      (G⁻¹.mulVec β - T.mulVec (Cminus⁻¹.mulVec βminus)))‖ ≤ _
  rw [← (incrementNumerator_identity G Cminus T (by rw [show G.det = A.det from Matrix.det_units_conj Q A]; exact spectral_det_ne_zero a b ha A hA hSpecA) (by rw [show Cminus.det = C.det from Matrix.det_units_conj R C]; exact spectral_det_ne_zero a b ha C hC hSpecC) β βminus), ← Matrix.smul_mulVec, ← Matrix.sub_mulVec]
  have hn := (parentInversePolynomial a b G Cminus m - Cminus.det⁻¹ • G⁻¹).l2_opNorm_mulVec
    ((EuclideanSpace.equiv (Fin r) ℝ).symm N)
  apply hn.trans
  rw [norm_sub_rev]
  exact mul_le_mul_of_nonneg_right
    (parent_inverse_similar_error a b ha hab A C hA hC hSpecA hSpecC Q R χ hχ m)
    (norm_nonneg _)
theorem parentInverseEntryPolynomial_degree (a b : ℝ) (r m : ℕ) (i j : Fin r) :
    (parentInverseEntryPolynomial a b r m i j).totalDegree ≤ m :=
  have h_truncationEntryPolynomial_degree {N : ℕ} (dims : Fin N → ℕ) : (truncationEntryPolynomial r dims a b i j m).totalDegree ≤ m := by
    apply (MvPolynomial.totalDegree_mul _ _).trans
    simp only [MvPolynomial.totalDegree_C, zero_add]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro k hk
    exact (combinedCoefficientPolynomial_degree r dims a b i j k).trans
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  (h_truncationEntryPolynomial_degree (fun _ : Fin 1 => r))
end
abbrev incrementVariables (r : ℕ) := parentInverseVariables r ⊕ (Bool × Bool × Fin r)
def currentVariableMatrix (r ) : Matrix (Fin r) (Fin r) (MvPolynomial (parentInverseVariables r) ℝ) :=
  fun i j => X (Sum.inl (i, j))
def parentVariableMatrix (r ) : Matrix (Fin r) (Fin r) (MvPolynomial (parentInverseVariables r) ℝ) :=
  fun i j => X (Sum.inr ⟨0, (i, j)⟩)
def vectorMoment (r ) (parent response : Bool) (i : Fin r) :
    MvPolynomial (incrementVariables r) ℝ := X (Sum.inr (parent, response, i))
def rawNumeratorPolynomial (r ) (T : Matrix (Fin r) (Fin r) ℝ)
    (response : Bool) (i : Fin r) : MvPolynomial (incrementVariables r) ℝ :=
  rename Sum.inl (parentVariableMatrix r).det * vectorMoment r false response i -
    ∑ j, ∑ k, ∑ l,
      rename Sum.inl (currentVariableMatrix r i j) * C (T j k) *
      rename Sum.inl ((parentVariableMatrix r).adjugate k l) * vectorMoment r true response l
def numeratorPolynomial (r ) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (i : Fin r) :
    MvPolynomial (incrementVariables r) ℝ :=
  rawNumeratorPolynomial r T false i - C y * rawNumeratorPolynomial r T true i
def incrementEntryPolynomial (r ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (i : Fin r) : MvPolynomial (incrementVariables r) ℝ :=
  ∑ j, rename Sum.inl (parentInverseEntryPolynomial a b r m i j) * numeratorPolynomial r T y j
theorem determinant_degree_le {V n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (MvPolynomial V ℝ)) (hM : ∀ i j, (M i j).totalDegree ≤ 1) :
    M.det.totalDegree ≤ Fintype.card n := by
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ hσ
  simp only [Units.smul_def]
  apply (MvPolynomial.totalDegree_smul_le _ _).trans
  apply (MvPolynomial.totalDegree_finsetProd Finset.univ _).trans
  calc
    ∑ i, (M (σ i) i).totalDegree ≤ ∑ _i : n, 1 := Finset.sum_le_sum (fun i hi => hM _ _)
    _ = _ := by simp
theorem adjugate_degree_le  (r )
    (M : Matrix (Fin r) (Fin r) (MvPolynomial V ℝ))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) (i j : Fin r) :
    (M.adjugate i j).totalDegree ≤ r - 1 := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ k =>
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    apply (MvPolynomial.totalDegree_mul _ _).trans
    have hz : ((-1 : MvPolynomial V ℝ) ^ (j.val + i.val)).totalDegree ≤ 0 := by
      simpa using MvPolynomial.totalDegree_pow (-1 : MvPolynomial V ℝ) (j.val + i.val)
    have hd := determinant_degree_le (M.submatrix j.succAbove i.succAbove) (fun i j => hM _ _)
    simpa using Nat.add_le_add hz hd
theorem rawNumeratorPolynomial_degree (r ) [NeZero r]
    (T response i) :
    (rawNumeratorPolynomial r T response i).totalDegree ≤ r + 1 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    apply Nat.add_le_add
    · apply (MvPolynomial.totalDegree_rename_le _ _).trans
      simpa using determinant_degree_le (parentVariableMatrix r) (by simp [parentVariableMatrix])
    · simp [vectorMoment]
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    apply MvPolynomial.totalDegree_finsetSum_le
    intro k hk
    apply MvPolynomial.totalDegree_finsetSum_le
    intro l hl
    have := (MvPolynomial.totalDegree_rename_le
      (Sum.inl : parentInverseVariables r → incrementVariables r) _).trans (adjugate_degree_le r (parentVariableMatrix r) (by simp [parentVariableMatrix]) k l)
    have : (rename Sum.inl (currentVariableMatrix r i j) :
        MvPolynomial (incrementVariables r) ℝ).totalDegree ≤ 1 := by simp [currentVariableMatrix]
    have h1 := MvPolynomial.totalDegree_mul
      (rename Sum.inl (currentVariableMatrix r i j) : MvPolynomial (incrementVariables r) ℝ) (C (T j k))
    have := MvPolynomial.totalDegree_mul
      (rename Sum.inl (currentVariableMatrix r i j) * C (T j k) : MvPolynomial (incrementVariables r) ℝ)
      (rename Sum.inl ((parentVariableMatrix r).adjugate k l))
    have h3 := MvPolynomial.totalDegree_mul
      (rename Sum.inl (currentVariableMatrix r i j) * C (T j k) *
        rename Sum.inl ((parentVariableMatrix r).adjugate k l)) (vectorMoment r true response l)
    simp only [MvPolynomial.totalDegree_C, add_zero] at h1
    have hv : (vectorMoment r true response l).totalDegree = 1 := by simp [vectorMoment]
    rw [hv] at h3
    have  := NeZero.ne r
    omega
def rawIncrementEntryPolynomial (r ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (response : Bool) (m : ℕ) (i : Fin r) : MvPolynomial (incrementVariables r) ℝ :=
  ∑ j, rename Sum.inl (parentInverseEntryPolynomial a b r m i j) *
    rawNumeratorPolynomial r T response j
open RoughRegime.CombinedPolynomial
def incrementValuation {r : ℕ} (A C : Matrix (Fin r) (Fin r) ℝ)
    (U V : Bool → Fin r → ℝ) : incrementVariables r → ℝ
  | Sum.inl x => entryValuation A (fun _ : Fin 1 => C) x
  | Sum.inr (parent, response, i) => if parent then V response i else U response i
theorem rawNumeratorPolynomial_eval 
    (A C T : Matrix (Fin r) (Fin r) ℝ) (U V response i) :
    eval (incrementValuation A C U V) (rawNumeratorPolynomial r T response i) =
      incrementNumerator A C T (U response) (V response) i := by
  let f := MvPolynomial.eval₂Hom (RingHom.id ℝ) (entryValuation A (fun _ : Fin 1 => C))
  have hm : f.mapMatrix (parentVariableMatrix r) = C := by
    ext j k
    simp [f, parentVariableMatrix, entryValuation, RingHom.mapMatrix_apply]
  have hd : eval (incrementValuation A C U V)
      (rename Sum.inl (parentVariableMatrix r).det) = C.det := by
    rw [MvPolynomial.eval_rename]
    change f (parentVariableMatrix r).det = C.det
    rw [f.map_det, hm]
  have ha (k l : Fin r) : eval (incrementValuation A C U V)
      (rename Sum.inl ((parentVariableMatrix r).adjugate k l)) = C.adjugate k l := by
    rw [MvPolynomial.eval_rename]
    have h := congrArg (fun M => M k l) (f.map_adjugate (parentVariableMatrix r))
    rw [hm] at h
    exact h
  simp only [rawNumeratorPolynomial, eval_sub, eval_mul, eval_sum, eval_C, hd, ha]
  simp only [vectorMoment, eval_X, incrementValuation, Bool.false_eq_true, ↓reduceIte,
    currentVariableMatrix, rename_X, entryValuation]
  simp only [incrementNumerator, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
theorem numeratorPolynomial_eval 
    (A C T U V y i) :
    eval (incrementValuation A C U V) (numeratorPolynomial r T y i) =
      incrementNumerator A C T (U false - y • U true) (V false - y • V true) i := by
  rw [numeratorPolynomial, eval_sub, eval_mul, eval_C,
    rawNumeratorPolynomial_eval, rawNumeratorPolynomial_eval]
  simp only [incrementNumerator, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub, smul_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem incrementEntryPolynomial_eval  (a b A C T U V y m i) :
    eval (incrementValuation A C U V) (incrementEntryPolynomial r a b T y m i) =
      (parentInversePolynomial a b A C m).mulVec
        (incrementNumerator A C T (U false - y • U true) (V false - y • V true)) i := by
  simp only [incrementEntryPolynomial, eval_sum, eval_mul, numeratorPolynomial_eval]
  simp_rw [MvPolynomial.eval_rename]
  change ∑ j, eval (entryValuation A (fun _ => C))
    (parentInverseEntryPolynomial a b r m i j) *
    incrementNumerator A C T (U false - y • U true) (V false - y • V true) j = _
  rfl
open scoped Matrix.Norms.L2Operator
theorem incrementEntryPolynomial_error  [NeZero r]
    (a b ) (ha : 0 < a) (hab : a < b)
    (A C T : Matrix (Fin r) (Fin r) ℝ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : spectrum ℝ A ⊆ Set.Icc a b) (hSpecC : spectrum ℝ C ⊆ Set.Icc a b)
    (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) (χ : ℝ)
    (hχ : ‖(Q : Matrix (Fin r) (Fin r) ℝ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ)
    (U V : Bool → Fin r → ℝ) (y ε : ℝ)
    (hδ : ‖(EuclideanSpace.equiv (Fin r) ℝ).symm
      ((matrixSimilarity Q A)⁻¹.mulVec (U false - y • U true) -
        T.mulVec ((matrixSimilarity R C)⁻¹.mulVec (V false - y • V true)))‖ ≤ ε)
    (m : ℕ) :
    let G := matrixSimilarity Q A
    let Cminus := matrixSimilarity R C
    ‖(EuclideanSpace.equiv (Fin r) ℝ).symm
      ((fun i => eval (incrementValuation G Cminus U V)
          (incrementEntryPolynomial r a b T y m i)) -
        (G⁻¹.mulVec (U false - y • U true) -
          T.mulVec (Cminus⁻¹.mulVec (V false - y • V true))))‖ ≤
      χ ^ 2 * b ^ (r + 1) * parentInverseErrorConstant a b r * ε *
        ((m + 1 : ℕ) : ℝ) ^ r *
        Real.exp (-↑m * exteriorTau ((a + b) / (b - a))) := by
  simp_rw [incrementEntryPolynomial_eval]
  let β := U false - y • U true
  let βminus := V false - y • V true
  have  := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hχ
  have  := ha.trans hab
  have := parentInverseErrorConstant_pos a b ha hab r
  have hsmall  := (increment_numerator_norm_le a b ha hab A C T hA hC hSpecA hSpecC Q R χ hχ β βminus).trans
        (mul_le_mul_of_nonneg_left hδ (by positivity))
  apply (increment_polynomial_error a b ha hab A C T hA hC hSpecA hSpecC Q R χ hχ β βminus m).trans
  apply (mul_le_mul_of_nonneg_left hsmall (by positivity)).trans_eq
  ring
end NearlyMinimax
