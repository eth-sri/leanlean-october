module

public import Mathlib
public import NearlyMinimax.Chebyshev
public import RoughRegime.ComplexDerivativeBridge

@[expose] public section

noncomputable section
namespace NearlyMinimax

open MvPolynomial
open scoped BigOperators Polynomial Matrix.Norms.L2Operator
open RoughRegime.Upper RoughRegime.ComplexDerivativeBridge

set_option maxHeartbeats 1000000

-- 1. Weighted geometric series & Cauchy convolution bounds

private lemma weighted_geometric_summable (ν : ℕ) (ρ : ℝ) (hp : 0 < ρ) (h1 : ρ < 1) :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k) := by
  have hn : ‖ρ‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hp] using h1
  have hraw := summable_pow_mul_geometric_of_norm_lt_one ν hn
  have hshift : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ (k + 1)) :=
    (summable_nat_add_iff 1).mpr hraw
  convert hshift.mul_right ρ⁻¹ using 1
  ext k; rw [pow_succ]; field_simp

private theorem series_truncation_bound {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℕ → E) (ν m : ℕ) (ρ A : ℝ) (hp : 0 < ρ) (h1 : ρ < 1) (hA : 0 ≤ A)
    (hcoeff : ∀ k : ℕ, ‖f k‖ ≤ A * ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k) :
    ‖(∑' k : ℕ, f k) - ∑ k ∈ Finset.range (m + 1), f k‖ ≤
      A * ((m + 1 : ℕ) : ℝ) ^ ν * ρ ^ m * ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k := by
  let w : ℕ → ℝ := fun k => ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k
  have hw : Summable w := weighted_geometric_summable ν ρ hp h1
  have hcoeff' (k : ℕ) : ‖f k‖ ≤ A * w k := by simpa only [w, mul_assoc] using hcoeff k
  have hnorm : Summable (fun k : ℕ => ‖f k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcoeff' (hw.mul_left A)
  have hf : Summable f := (hw.mul_left A).of_norm_bounded hcoeff'
  have htail : (∑' k : ℕ, f k) - ∑ k ∈ Finset.range (m + 1), f k = ∑' k : ℕ, f (k + (m + 1)) := by
    rw [← hf.sum_add_tsum_nat_add (m + 1)]; abel
  have hn0 : Summable (fun k : ℕ => ‖f (k + m)‖) := (summable_nat_add_iff (f := fun k => ‖f k‖) m).mpr hnorm
  have hn1 : Summable (fun k : ℕ => ‖f (k + (m + 1))‖) := (summable_nat_add_iff (f := fun k => ‖f k‖) (m + 1)).mpr hnorm
  have htmono : (∑' k : ℕ, ‖f (k + (m + 1))‖) ≤ ∑' k : ℕ, ‖f (k + m)‖ := by
    have h := hn0.tsum_eq_zero_add
    simp only [zero_add, show (fun k : ℕ => ‖f (k + 1 + m)‖) = fun k => ‖f (k + (m + 1))‖ by
      ext k; congr 2; omega] at h
    rw [h]; exact le_add_of_nonneg_left (norm_nonneg _)
  let C := A * ((m + 1 : ℕ) : ℝ) ^ ν * ρ ^ m
  have htbound (k : ℕ) : ‖f (k + m)‖ ≤ C * w k := by
    refine (hcoeff (k + m)).trans ?_
    have hindex : (k + m + 1 : ℝ) ≤ (m + 1) * (k + 1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) m]
    have hpow' : (((k + m + 1 : ℕ) : ℝ)) ^ ν ≤ ((m + 1 : ℕ) : ℝ) ^ ν * ((k + 1 : ℕ) : ℝ) ^ ν := by
      simpa [mul_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ (k + m + 1 : ℝ)) hindex ν
    have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow' hA) (pow_nonneg hp.le (k + m))
    dsimp [C, w]; convert hmul using 1 <;> rw [pow_add] <;> ring
  rw [htail]
  exact ((norm_tsum_le_tsum_norm hn1).trans htmono).trans
    ((Summable.tsum_le_tsum htbound hn0 (hw.mul_left C)).trans_eq (tsum_mul_left ..))

private theorem convolution_coefficient_bound {R : Type*} [NormedRing R]
    (f g : ℕ → R) (ν k : ℕ) (ρ A B : ℝ) (hp : 0 < ρ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ i : ℕ, ‖f i‖ ≤ A * ((i + 1 : ℕ) : ℝ) ^ ν * ρ ^ i)
    (hg : ∀ j : ℕ, ‖g j‖ ≤ B * ρ ^ j) :
    ‖∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, f ij.1 * g ij.2‖ ≤
      A * B * ((k + 1 : ℕ) : ℝ) ^ (ν + 1) * ρ ^ k := by
  refine (norm_sum_le _ _).trans
    ((Finset.sum_le_sum (g := fun _ => A * B * ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k) fun ij hij => ?_).trans_eq ?_)
  · have he : ij.1 + ij.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hpow : (((ij.1 + 1 : ℕ) : ℝ)) ^ ν ≤ ((k + 1 : ℕ) : ℝ) ^ ν :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show ij.1 + 1 ≤ k + 1 by omega)) ν
    calc ‖f ij.1 * g ij.2‖ ≤ (A * ((ij.1 + 1 : ℕ) : ℝ) ^ ν * ρ ^ ij.1) * (B * ρ ^ ij.2) :=
          (norm_mul_le _ _).trans (mul_le_mul (hf ij.1) (hg ij.2) (norm_nonneg _) (by positivity))
      _ = A * B * ((ij.1 + 1 : ℕ) : ℝ) ^ ν * ρ ^ k := by rw [← he, pow_add]; ring
      _ ≤ A * B * ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (mul_nonneg hA hB)) (pow_nonneg hp.le k)
  · simp only [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]; rw [pow_succ]; ring

private theorem powerSeries_prod_geometric_bound {R I : Type*} [NormedCommRing R] [NormOneClass R]
    [DecidableEq I] (s : Finset I) (f : I → PowerSeries R)
    (q B : ℝ) (hq : 0 < q) (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, ∀ k, ‖PowerSeries.coeff k (f i)‖ ≤ B * q ^ k) (k : ℕ) :
    ‖PowerSeries.coeff k (∏ i ∈ s, f i)‖ ≤ B ^ s.card * ((k + 1 : ℕ) : ℝ) ^ s.card * q ^ k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, one_mul, PowerSeries.coeff_one]
    split_ifs with hk
    · subst k; simp
    · simp only [norm_zero]; positivity
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_comm, PowerSeries.coeff_mul]
    simpa only [Finset.card_insert_of_notMem ha, pow_succ] using
      convolution_coefficient_bound (fun j => PowerSeries.coeff j (∏ i ∈ s, f i))
        (fun j => PowerSeries.coeff j (f a)) s.card k q (B ^ s.card) B hq (by positivity) hB
        (fun j => ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) j)
        (hf a (Finset.mem_insert_self ..))

-- 2. Polynomial matrix & single-parent combined reciprocal series (unified over `Algebra ℝ S`)

def normalizedChebyshev (lo hi : ℝ) (k : ℕ) : ℝ[X] :=
  (Polynomial.Chebyshev.T ℝ (k : ℤ)).comp
    (Polynomial.C (intervalHalfWidth lo hi)⁻¹ * (Polynomial.X - Polynomial.C (intervalCenter lo hi)))

private lemma normalizedChebyshev_eval (lo hi x : ℝ) (k : ℕ) :
    (normalizedChebyshev lo hi k).eval x =
      (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval ((x - intervalCenter lo hi) / intervalHalfWidth lo hi) := by
  simp [normalizedChebyshev, div_eq_mul_inv, mul_comm]

def kernelCoefficientPolynomial (lo hi : ℝ) (k : ℕ) : ℝ[X] :=
  Polynomial.C (if k = 0 then 1 else 2 * (-intervalRho lo hi) ^ k) * normalizedChebyshev lo hi k

private lemma kernelCoefficientPolynomial_natDegree (lo hi : ℝ) (k : ℕ) :
    (kernelCoefficientPolynomial lo hi k).natDegree ≤ k := by
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  unfold normalizedChebyshev
  refine Polynomial.natDegree_comp_le.trans ?_
  calc (Polynomial.Chebyshev.T ℝ (k : ℤ)).natDegree * _ ≤ k * 1 :=
        Nat.mul_le_mul (by simp [Polynomial.Chebyshev.natDegree_T]) ((Polynomial.natDegree_C_mul_le _ _).trans (by simp))
    _ = k := Nat.mul_one k

def variableMatrix (n : Type*) : Matrix n n (MvPolynomial (n × n) ℝ) :=
  fun i j => MvPolynomial.X (i, j)

def matrixEntryPolynomial {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (i j : n) : MvPolynomial (n × n) ℝ :=
  ∑ k ∈ Finset.range (q.natDegree + 1), MvPolynomial.C (q.coeff k) * (variableMatrix n ^ k) i j

private lemma matrixEntryPolynomial_degree {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (i j : n) : (matrixEntryPolynomial q i j).totalDegree ≤ q.natDegree := by
  have hpow (k : ℕ) (a b : n) : ((variableMatrix n ^ k) a b).totalDegree ≤ k := by
    induction k generalizing a b with
    | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> simp
    | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      exact totalDegree_finsetSum_le fun c _ => (totalDegree_mul _ _).trans (Nat.add_le_add (ih a c) (by simp [variableMatrix]))
  exact totalDegree_finsetSum_le fun k hk =>
    (totalDegree_mul _ _).trans
      (((Nat.add_le_add (totalDegree_C _).le (hpow k i j)).trans_eq (Nat.zero_add k)).trans
        (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))

private lemma matrixEntryPolynomial_eval₂ {S n : Type*} [CommRing S] [Algebra ℝ S]
    [Fintype n] [DecidableEq n] (q : ℝ[X]) (A : Matrix n n S) (i j : n) :
    MvPolynomial.eval₂ (algebraMap ℝ S) (fun ij : n × n => A ij.1 ij.2)
      (matrixEntryPolynomial q i j) = (Polynomial.aeval A q) i j := by
  have hpow (k : ℕ) (a b : n) :
      MvPolynomial.eval₂ (algebraMap ℝ S) (fun ij : n × n => A ij.1 ij.2) ((variableMatrix n ^ k) a b) = (A ^ k) a b := by
    induction k generalizing a b with
    | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> simp
    | succ k ih =>
      simp only [pow_succ, Matrix.mul_apply, eval₂_sum, eval₂_mul, ih]
      simp [variableMatrix]
  rw [Polynomial.aeval_eq_sum_range]
  unfold matrixEntryPolynomial
  simp only [eval₂_sum, eval₂_mul, eval₂_C, hpow, Matrix.sum_apply, Matrix.smul_apply, ← Algebra.smul_def]

def variableKernelSeries (lo hi : ℝ) {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix n n (PowerSeries (MvPolynomial (n × n) ℝ)) :=
  fun i j => PowerSeries.mk fun k => matrixEntryPolynomial (kernelCoefficientPolynomial lo hi k) i j

def anyKernelSeries {S n : Type*} [CommRing S] [Algebra ℝ S] [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (A : Matrix n n S) : Matrix n n (PowerSeries S) :=
  fun i j => PowerSeries.mk fun k => (Polynomial.aeval A (kernelCoefficientPolynomial lo hi k)) i j

private lemma variableKernelSeries_eval₂ {S n : Type*} [CommRing S] [Algebra ℝ S]
    [Fintype n] [DecidableEq n] (lo hi : ℝ) (A : Matrix n n S) :
    (PowerSeries.map (MvPolynomial.eval₂Hom (algebraMap ℝ S) (fun ij : n × n => A ij.1 ij.2))).mapMatrix
      (variableKernelSeries lo hi (n := n)) = anyKernelSeries lo hi A := by
  ext i j k
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, PowerSeries.coeff_map]
  simp only [variableKernelSeries, anyKernelSeries, PowerSeries.coeff_mk]
  exact matrixEntryPolynomial_eval₂ _ A i j

private theorem coeff_totalDegree_mul_le {V : Type*} (f g : PowerSeries (MvPolynomial V ℝ))
    (hf : ∀ k, (PowerSeries.coeff k f).totalDegree ≤ k)
    (hg : ∀ k, (PowerSeries.coeff k g).totalDegree ≤ k) (k : ℕ) :
    (PowerSeries.coeff k (f * g)).totalDegree ≤ k := by
  rw [PowerSeries.coeff_mul]
  exact totalDegree_finsetSum_le fun ij hij => (totalDegree_mul _ _).trans
    ((Nat.add_le_add (hf ij.1) (hg ij.2)).trans_eq (Finset.HasAntidiagonal.mem_antidiagonal.mp hij))

private theorem coeff_totalDegree_prod_le {V I : Type*} [DecidableEq I] (s : Finset I)
    (f : I → PowerSeries (MvPolynomial V ℝ))
    (hf : ∀ i ∈ s, ∀ k, (PowerSeries.coeff k (f i)).totalDegree ≤ k) (k : ℕ) :
    (PowerSeries.coeff k (∏ i ∈ s, f i)).totalDegree ≤ k := by
  induction s using Finset.induction_on generalizing k with
  | empty => simp only [Finset.prod_empty, PowerSeries.coeff_one]; split_ifs <;> simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact coeff_totalDegree_mul_le _ _ (hf a (Finset.mem_insert_self ..))
      (fun j => ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) j) k

abbrev parentInverseVariables (r : ℕ) :=
  (Fin r × Fin r) ⊕ ((_ : Fin 1) × (Fin r × Fin r))

def parentValuation {S : Type*} {r : ℕ} (A C : Matrix (Fin r) (Fin r) S) : parentInverseVariables r → S
  | Sum.inl ij => A ij.1 ij.2
  | Sum.inr ⟨_, ij⟩ => C ij.1 ij.2

def parentInverseEntryPolynomial (lo hi : ℝ) (r m : ℕ) (i j : Fin r) :
    MvPolynomial (parentInverseVariables r) ℝ :=
  let invS := PowerSeries.map
    (MvPolynomial.rename (fun ab : Fin r × Fin r => (Sum.inl ab : parentInverseVariables r))).toRingHom
    (variableKernelSeries lo hi i j)
  let detS := PowerSeries.map
    (MvPolynomial.rename (fun ab : Fin r × Fin r => (Sum.inr ⟨0, ab⟩ : parentInverseVariables r))).toRingHom
    (variableKernelSeries lo hi (n := Fin r)).det
  MvPolynomial.C ((intervalGeometricMean lo hi ^ (r + 1))⁻¹) *
    ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k (invS * detS)

private theorem parentInverseEntryPolynomial_degree (lo hi : ℝ) (r m : ℕ) (i j : Fin r) :
    (parentInverseEntryPolynomial lo hi r m i j).totalDegree ≤ m := by
  have hinv (k : ℕ) : (PowerSeries.coeff k (PowerSeries.map
      (MvPolynomial.rename (fun ab : Fin r × Fin r => (Sum.inl ab : parentInverseVariables r))).toRingHom
      (variableKernelSeries lo hi i j))).totalDegree ≤ k := by
    rw [PowerSeries.coeff_map]; refine (totalDegree_rename_le _ _).trans ?_
    simp only [variableKernelSeries, PowerSeries.coeff_mk]
    exact (matrixEntryPolynomial_degree _ i j).trans (kernelCoefficientPolynomial_natDegree lo hi k)
  have hdet (k : ℕ) : (PowerSeries.coeff k (PowerSeries.map
      (MvPolynomial.rename (fun ab : Fin r × Fin r => (Sum.inr ⟨0, ab⟩ : parentInverseVariables r))).toRingHom
      (variableKernelSeries lo hi (n := Fin r)).det)).totalDegree ≤ k := by
    rw [PowerSeries.coeff_map]; refine (totalDegree_rename_le _ _).trans ?_
    rw [Matrix.det_apply, map_sum]
    refine totalDegree_finsetSum_le fun σ _ => ?_
    simp only [Units.smul_def]
    refine (totalDegree_smul_le _ _).trans
      (coeff_totalDegree_prod_le Finset.univ (fun a => variableKernelSeries lo hi (σ a) a) (fun a _ t => ?_) k)
    simp only [variableKernelSeries, PowerSeries.coeff_mk]
    exact (matrixEntryPolynomial_degree _ _ _).trans (kernelCoefficientPolynomial_natDegree lo hi t)
  unfold parentInverseEntryPolynomial
  refine (totalDegree_mul _ _).trans ?_
  simp only [totalDegree_C, zero_add]
  exact totalDegree_finsetSum_le fun k hk =>
    (coeff_totalDegree_mul_le _ _ hinv hdet k).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

private lemma eval₂_renamed_powerSeries {S V W : Type*} [CommRing S] [Algebra ℝ S]
    (f : V → W) (vals : W → S) (P : PowerSeries (MvPolynomial V ℝ)) :
    PowerSeries.map (MvPolynomial.eval₂Hom (algebraMap ℝ S) vals)
      (PowerSeries.map (MvPolynomial.rename f).toRingHom P) =
    PowerSeries.map (MvPolynomial.eval₂Hom (algebraMap ℝ S) (vals ∘ f)) P := by
  ext k; simp only [PowerSeries.coeff_map]; exact MvPolynomial.eval₂_rename _ _ _ _

private theorem parentInverseEntryPolynomial_eval₂ {S : Type*} [CommRing S] [Algebra ℝ S] {r : ℕ}
    (lo hi : ℝ) (A C : Matrix (Fin r) (Fin r) S) (i j : Fin r) (m : ℕ) :
    MvPolynomial.eval₂ (algebraMap ℝ S) (parentValuation A C)
      (parentInverseEntryPolynomial lo hi r m i j) =
      algebraMap ℝ S ((intervalGeometricMean lo hi ^ (r + 1))⁻¹) *
        ∑ k ∈ Finset.range (m + 1),
          PowerSeries.coeff k (anyKernelSeries lo hi A i j * (anyKernelSeries lo hi C).det) := by
  let φ := MvPolynomial.eval₂Hom (algebraMap ℝ S) (parentValuation A C)
  have hinv : PowerSeries.map φ (PowerSeries.map
      (MvPolynomial.rename (fun ab : Fin r × Fin r => (Sum.inl ab : parentInverseVariables r))).toRingHom
      (variableKernelSeries lo hi i j)) = anyKernelSeries lo hi A i j := by
    dsimp only [φ]; rw [eval₂_renamed_powerSeries]
    exact congrArg (fun K => K i j) (variableKernelSeries_eval₂ lo hi A)
  have hdet : PowerSeries.map φ (PowerSeries.map
      (MvPolynomial.rename (fun ab : Fin r × Fin r => (Sum.inr ⟨0, ab⟩ : parentInverseVariables r))).toRingHom
      (variableKernelSeries lo hi (n := Fin r)).det) = (anyKernelSeries lo hi C).det := by
    dsimp only [φ]; rw [eval₂_renamed_powerSeries]
    change PowerSeries.map (MvPolynomial.eval₂Hom (algebraMap ℝ S) (fun ij : Fin r × Fin r => C ij.1 ij.2))
      (variableKernelSeries lo hi).det = _
    rw [RingHom.map_det, variableKernelSeries_eval₂]
  have hprod : PowerSeries.map φ
      (PowerSeries.map (MvPolynomial.rename (fun ab : Fin r × Fin r => (Sum.inl ab : parentInverseVariables r))).toRingHom
        (variableKernelSeries lo hi i j) *
       PowerSeries.map (MvPolynomial.rename (fun ab : Fin r × Fin r => (Sum.inr ⟨0, ab⟩ : parentInverseVariables r))).toRingHom
        (variableKernelSeries lo hi (n := Fin r)).det) =
      anyKernelSeries lo hi A i j * (anyKernelSeries lo hi C).det := by
    rw [map_mul, hinv, hdet]
  unfold parentInverseEntryPolynomial
  simp only [eval₂_mul, eval₂_C, eval₂_sum]
  congr 1; refine Finset.sum_congr rfl fun k _ => ?_
  have hc := congrArg (PowerSeries.coeff k) hprod
  rwa [PowerSeries.coeff_map] at hc

-- 3. Real spectral convergence, similarity equivariance & `incrementEntryPolynomial`

def parentInversePolynomial {r : ℕ} (lo hi : ℝ) (A C : Matrix (Fin r) (Fin r) ℝ) (m : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => MvPolynomial.eval (parentValuation A C) (parentInverseEntryPolynomial lo hi r m i j)

def parentInverseErrorConstant (a b : ℝ) (r : ℕ) : ℝ :=
  2 ^ (r + 1) * (intervalGeometricMean a b ^ (r + 1))⁻¹ *
    ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ r * intervalRho a b ^ k

private theorem parentInverseErrorConstant_pos (a b : ℝ) (ha : 0 < a) (hab : a < b) (r : ℕ) :
    0 < parentInverseErrorConstant a b r := by
  have hr := intervalRho_pos a b ha hab
  have hr1 := intervalRho_lt_one a b ha hab
  have hg : 0 < intervalGeometricMean a b := Real.sqrt_pos.mpr (mul_pos ha (ha.trans hab))
  have hs := weighted_geometric_summable r (intervalRho a b) hr hr1
  have ht : 0 < ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ r * intervalRho a b ^ k :=
    hs.tsum_pos (fun k => by positivity) 0 (by simp)
  unfold parentInverseErrorConstant; positivity

private def scalarKernelSeries (lo hi x : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => (kernelCoefficientPolynomial lo hi k).eval x

private def coefficientMatrix {n : Type*} (k : ℕ) (M : Matrix n n (PowerSeries ℝ)) : Matrix n n ℝ :=
  fun i j => PowerSeries.coeff k (M i j)

private def matrixSeries {n : Type*} [Fintype n] [DecidableEq n] (K : Matrix n n (PowerSeries ℝ)) :
    PowerSeries (Matrix n n ℝ) := PowerSeries.mk fun k => coefficientMatrix k K

private theorem kernelSeries_spectral {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℝ) (hM : M.IsHermitian) :
    anyKernelSeries lo hi M =
      (PowerSeries.C.mapMatrix (hM.eigenvectorUnitary : Matrix n n ℝ)) *
      Matrix.diagonal (fun i => scalarKernelSeries lo hi (hM.eigenvalues i)) *
      (PowerSeries.C.mapMatrix (star (hM.eigenvectorUnitary : Matrix n n ℝ))) := by
  ext i j k
  change (coefficientMatrix k (anyKernelSeries lo hi M)) i j = (coefficientMatrix k (_ * _ * _)) i j
  have hcm1 (A : Matrix n n ℝ) (K : Matrix n n (PowerSeries ℝ)) :
      coefficientMatrix k ((PowerSeries.C.mapMatrix A) * K) = A * coefficientMatrix k K := by
    ext a b; simp [coefficientMatrix, Matrix.mul_apply, map_sum, PowerSeries.coeff_C_mul]
  have hcm2 (K : Matrix n n (PowerSeries ℝ)) (A : Matrix n n ℝ) :
      coefficientMatrix k (K * (PowerSeries.C.mapMatrix A)) = coefficientMatrix k K * A := by
    ext a b; simp [coefficientMatrix, Matrix.mul_apply, map_sum, PowerSeries.coeff_mul_C]
  have hdiag (d : n → PowerSeries ℝ) :
      coefficientMatrix k (Matrix.diagonal d) = Matrix.diagonal fun a => PowerSeries.coeff k (d a) := by
    ext a b; simp only [coefficientMatrix, Matrix.diagonal_apply]; split_ifs <;> simp
  rw [hcm2, hcm1, hdiag]
  simp only [coefficientMatrix, anyKernelSeries, scalarKernelSeries, PowerSeries.coeff_mk]
  have hp := Polynomial.aeval_algHom_apply
    (Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hM.eigenvectorUnitary)
    (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)) (kernelCoefficientPolynomial lo hi k)
  have had (q : ℝ[X]) (d : n → ℝ) : Polynomial.aeval (Matrix.diagonal d) q = Matrix.diagonal fun a => q.eval (d a) := by
    change Polynomial.aeval ((Matrix.diagonalAlgHom ℝ) d) q = _
    rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_pi_apply]; rfl
  rw [← hM.spectral_theorem, had] at hp
  exact congrArg (fun A : Matrix n n ℝ => A i j)
    (by simpa only [Unitary.conjStarAlgAut_apply, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq] using hp)

private theorem kernelSeries_det_spectral {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℝ) (hM : M.IsHermitian) :
    (anyKernelSeries lo hi M).det = ∏ i, scalarKernelSeries lo hi (hM.eigenvalues i) := by
  rw [kernelSeries_spectral lo hi M hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hu : (PowerSeries.C.mapMatrix (hM.eigenvectorUnitary : Matrix n n ℝ)).det *
      (PowerSeries.C.mapMatrix (star (hM.eigenvectorUnitary : Matrix n n ℝ))).det = 1 := by
    rw [← Matrix.det_mul, ← map_mul, Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.property, map_one, Matrix.det_one]
  calc _ = (∏ i, scalarKernelSeries lo hi (hM.eigenvalues i)) *
            ((PowerSeries.C.mapMatrix (hM.eigenvectorUnitary : Matrix n n ℝ)).det *
              (PowerSeries.C.mapMatrix (star (hM.eigenvectorUnitary : Matrix n n ℝ))).det) := by ring
    _ = _ := by rw [hu, mul_one]

private theorem parentInversePolynomial_eq_scaled_sum {r : ℕ} (lo hi : ℝ)
    (A C : Matrix (Fin r) (Fin r) ℝ) (m : ℕ) :
    parentInversePolynomial lo hi A C m =
      (intervalGeometricMean lo hi ^ (r + 1))⁻¹ •
        ∑ k ∈ Finset.range (m + 1),
          PowerSeries.coeff k (matrixSeries (anyKernelSeries lo hi A) *
            PowerSeries.map (Matrix.scalar (Fin r)) (anyKernelSeries lo hi C).det) := by
  ext i j
  have hev := parentInverseEntryPolynomial_eval₂ (S := ℝ) lo hi A C i j m
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hev
  change MvPolynomial.eval (parentValuation A C) (parentInverseEntryPolynomial lo hi r m i j) = _ at hev
  rw [parentInversePolynomial, hev, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  congr 1; refine Finset.sum_congr rfl fun k _ => ?_
  simp only [matrixSeries, PowerSeries.coeff_mk, coefficientMatrix, PowerSeries.coeff_mul,
    PowerSeries.coeff_map, Matrix.sum_apply, Matrix.scalar_apply, Matrix.mul_diagonal]

private theorem parent_inverse_polynomial_error {r : ℕ} [NeZero r]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (A C : Matrix (Fin r) (Fin r) ℝ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : spectrum ℝ A ⊆ Set.Icc lo hi) (hSpecC : spectrum ℝ C ⊆ Set.Icc lo hi) (m : ℕ) :
    ‖C.det⁻¹ • A⁻¹ - parentInversePolynomial lo hi A C m‖ ≤
      parentInverseErrorConstant lo hi r * ((m + 1 : ℕ) : ℝ) ^ r *
        Real.exp (-(m : ℝ) * exteriorTau ((lo + hi) / (hi - lo))) := by
  let ρ := intervalRho lo hi
  have hρ : 0 < ρ := intervalRho_pos lo hi hlo hlt
  have hρ1 : ρ < 1 := intervalRho_lt_one lo hi hlo hlt
  -- Scalar kernel norm & sum
  have hsc_norm (x : ℝ) (hx : x ∈ Set.Icc lo hi) (k : ℕ) :
      ‖PowerSeries.coeff k (scalarKernelSeries lo hi x)‖ ≤ 2 * ρ ^ k := by
    have ht : |(normalizedChebyshev lo hi k).eval x| ≤ 1 := by
      rw [normalizedChebyshev_eval]; exact chebyshev_abs_le_one _ (interval_argument_mem lo hi x hlo hlt hx) k
    simp only [scalarKernelSeries, PowerSeries.coeff_mk, kernelCoefficientPolynomial,
      Polynomial.eval_mul, Polynomial.eval_C]
    by_cases hk : k = 0
    · subst k; simp [normalizedChebyshev]
    · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_pow, abs_neg, abs_of_pos (intervalRho_pos lo hi hlo hlt)]
      exact (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2 * ρ ^ k)).trans_eq (mul_one _)
  have hsc_sum (x : ℝ) (hx : x ∈ Set.Icc lo hi) :
      Summable (fun k => ‖PowerSeries.coeff k (scalarKernelSeries lo hi x)‖) ∧
        (∑' k, PowerSeries.coeff k (scalarKernelSeries lo hi x)) = intervalGeometricMean lo hi / x := by
    have hsm : Summable (fun k => ‖PowerSeries.coeff k (scalarKernelSeries lo hi x)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hsc_norm x hx) ((summable_geometric_of_lt_one hρ.le hρ1).mul_left 2)
    refine ⟨hsm, ?_⟩
    rw [hsm.of_norm.tsum_eq_zero_add]
    simp only [scalarKernelSeries, PowerSeries.coeff_mk, kernelCoefficientPolynomial,
      Polynomial.eval_mul, Polynomial.eval_C, Nat.add_one_ne_zero, ↓reduceIte, normalizedChebyshev_eval,
      Int.natCast_zero, Polynomial.Chebyshev.T_zero, Polynomial.eval_one, one_mul]
    simp_rw [mul_assoc]; rw [tsum_mul_left]; exact reciprocal_real_series lo hi x hlo hlt hx
  -- Matrix kernel norm & sum for `A`
  have hmat_norm (k : ℕ) : ‖PowerSeries.coeff k (matrixSeries (anyKernelSeries lo hi A))‖ ≤ 2 * ρ ^ k := by
    have hc_eq : PowerSeries.coeff k (matrixSeries (anyKernelSeries lo hi A)) =
        (if k = 0 then 1 else 2 * (-ρ) ^ k) • Polynomial.aeval A (normalizedChebyshev lo hi k) := by
      ext i j; simp [matrixSeries, coefficientMatrix, anyKernelSeries, kernelCoefficientPolynomial, ← Algebra.smul_def, ρ]
    have hcfc : ‖Polynomial.aeval A (normalizedChebyshev lo hi k)‖ ≤ 1 := by
      have hs : IsSelfAdjoint A := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
      rw [← cfc_polynomial _ A hs]
      refine norm_cfc_le (by norm_num) fun x hx => ?_
      rw [normalizedChebyshev_eval, Real.norm_eq_abs]
      exact chebyshev_abs_le_one _ (interval_argument_mem lo hi x hlo hlt (hSpecA hx)) k
    rw [hc_eq, norm_smul]
    by_cases hk : k = 0
    · subst k; simpa using hcfc.trans (by norm_num)
    · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_pow, abs_neg, abs_of_pos hρ]
      simpa using mul_le_mul_of_nonneg_left hcfc (by positivity : 0 ≤ 2 * ρ ^ k)
  have hmat_sum : Summable (fun k => ‖PowerSeries.coeff k (matrixSeries (anyKernelSeries lo hi A))‖) ∧
      (∑' k, PowerSeries.coeff k (matrixSeries (anyKernelSeries lo hi A))) = intervalGeometricMean lo hi • A⁻¹ := by
    have hsm := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hmat_norm ((summable_geometric_of_lt_one hρ.le hρ1).mul_left 2)
    refine ⟨hsm, ?_⟩
    have hd : Summable (fun k i => PowerSeries.coeff k (scalarKernelSeries lo hi (hA.eigenvalues i))) :=
      Pi.summable.mpr fun i => (hsc_sum _ (hSpecA (hA.eigenvalues_mem_spectrum_real i))).1.of_norm
    have hds : (∑' k, fun i => PowerSeries.coeff k (scalarKernelSeries lo hi (hA.eigenvalues i))) =
        fun i => intervalGeometricMean lo hi / hA.eigenvalues i := funext fun i => by
      rw [Pi.tsum_apply hd]; exact (hsc_sum _ (hSpecA (hA.eigenvalues_mem_spectrum_real i))).2
    have hsp (k : ℕ) : PowerSeries.coeff k (matrixSeries (anyKernelSeries lo hi A)) =
        (hA.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) *
          Matrix.diagonal (fun i => PowerSeries.coeff k (scalarKernelSeries lo hi (hA.eigenvalues i))) *
          star (hA.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) := by
      simp only [matrixSeries, PowerSeries.coeff_mk]
      rw [kernelSeries_spectral lo hi A hA]
      ext a b; simp [coefficientMatrix, Matrix.mul_apply, Matrix.diagonal_apply, map_sum,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C]
    simp_rw [hsp]
    have hdmat := hd.matrix_diagonal
    rw [(hdmat.mul_left (hA.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ)).tsum_mul_right,
      hdmat.tsum_mul_left, ← Matrix.diagonal_tsum, hds]
    have hAinv : A⁻¹ = (hA.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) *
        Matrix.diagonal (fun i => (hA.eigenvalues i)⁻¹) * star (hA.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) := by
      let U : Matrix (Fin r) (Fin r) ℝ := hA.eigenvectorUnitary
      have hU : star U * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.property
      have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.property
      have hA' : A = U * Matrix.diagonal hA.eigenvalues * star U := by
        simpa only [U, Unitary.conjStarAlgAut_apply, Function.comp_apply, RCLike.ofReal_real_eq_id, Function.id_comp] using hA.spectral_theorem
      apply Matrix.inv_eq_left_inv
      change (U * _ * star U) * A = 1
      conv_lhs => arg 2; rw [hA']
      have hn (i : Fin r) : hA.eigenvalues i ≠ 0 := ne_of_gt (hlo.trans_le (hSpecA (hA.eigenvalues_mem_spectrum_real i)).1)
      have h1 : (U * Matrix.diagonal (fun i => (hA.eigenvalues i)⁻¹) * star U) * (U * Matrix.diagonal hA.eigenvalues * star U) =
          U * (Matrix.diagonal (fun i => (hA.eigenvalues i)⁻¹) * Matrix.diagonal hA.eigenvalues) * star U := by
        calc _ = U * Matrix.diagonal (fun i => (hA.eigenvalues i)⁻¹) * (star U * U) * Matrix.diagonal hA.eigenvalues * star U := by noncomm_ring
          _ = _ := by rw [hU, mul_one]; noncomm_ring
      rw [h1, Matrix.diagonal_mul_diagonal, show Matrix.diagonal (fun i => (hA.eigenvalues i)⁻¹ * hA.eigenvalues i) = 1 by
        simp [inv_mul_cancel₀ (hn _)], mul_one, hU']
    rw [hAinv, ← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul]; rfl
  -- Combined series coefficient bound & sum by induction over `Fin r`
  let eigS (i : Fin r) := scalarKernelSeries lo hi (hC.eigenvalues i)
  have hcomb_ind (s : Finset (Fin r)) :
      (∀ k, ‖PowerSeries.coeff k (matrixSeries (anyKernelSeries lo hi A) *
        PowerSeries.map (Matrix.scalar (Fin r)) (∏ i ∈ s, eigS i))‖ ≤
          2 * 2 ^ s.card * ((k + 1 : ℕ) : ℝ) ^ s.card * ρ ^ k) ∧
      Summable (fun k => ‖PowerSeries.coeff k (∏ i ∈ s, eigS i)‖) ∧
      (∑' k, PowerSeries.coeff k (∏ i ∈ s, eigS i)) = ∏ i ∈ s, (intervalGeometricMean lo hi / hC.eigenvalues i) := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨fun k => by simpa using hmat_norm k, ?_, by simp [PowerSeries.coeff_one]⟩
      refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
      simp only [Finset.mem_singleton] at hk
      simp [PowerSeries.coeff_one, hk]
    | @insert a s ha ih =>
      obtain ⟨hbd, hsm, hts⟩ := ih
      have ha_mem := hSpecC (hC.eigenvalues_mem_spectrum_real a)
      have ha_sm := (hsc_sum _ ha_mem).1
      have hsm_ins : Summable (fun k => ‖PowerSeries.coeff k (∏ i ∈ insert a s, eigS i)‖) := by
        rw [Finset.prod_insert ha]
        convert summable_norm_sum_mul_antidiagonal_of_summable_norm ha_sm hsm using 1
        funext k; rw [PowerSeries.coeff_mul]
      have hts_ins : (∑' k, PowerSeries.coeff k (∏ i ∈ insert a s, eigS i)) =
          ∏ i ∈ insert a s, (intervalGeometricMean lo hi / hC.eigenvalues i) := by
        rw [Finset.prod_insert ha, Finset.prod_insert ha]
        have hmul_eq : (fun k => PowerSeries.coeff k (eigS a * ∏ i ∈ s, eigS i)) =
            fun k => ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k,
              PowerSeries.coeff ij.1 (eigS a) * PowerSeries.coeff ij.2 (∏ i ∈ s, eigS i) :=
          funext fun k => PowerSeries.coeff_mul k _ _
        rw [hmul_eq, ← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha_sm hsm,
          (hsc_sum _ ha_mem).2, hts]
      refine ⟨fun k => ?_, hsm_ins, hts_ins⟩
      rw [Finset.prod_insert ha, mul_comm (eigS a),
        show PowerSeries.map (Matrix.scalar (Fin r)) ((∏ i ∈ s, eigS i) * eigS a) =
          PowerSeries.map (Matrix.scalar (Fin r)) (∏ i ∈ s, eigS i) *
            PowerSeries.map (Matrix.scalar (Fin r)) (eigS a) from map_mul _ _ _,
        ← mul_assoc, PowerSeries.coeff_mul]
      have hg (j : ℕ) : ‖PowerSeries.coeff j (PowerSeries.map (Matrix.scalar (Fin r)) (eigS a))‖ ≤ 2 * ρ ^ j := by
        rw [PowerSeries.coeff_map, show ‖Matrix.scalar (Fin r) (PowerSeries.coeff j (eigS a))‖ =
          ‖PowerSeries.coeff j (eigS a)‖ from norm_algebraMap' (Matrix (Fin r) (Fin r) ℝ) _]
        exact hsc_norm _ ha_mem j
      have hh := convolution_coefficient_bound _ _ s.card k ρ (2 * 2 ^ s.card) 2 hρ (by positivity) (by norm_num) hbd hg
      simpa only [Finset.card_insert_of_notMem ha, pow_succ, mul_assoc] using hh
  obtain ⟨hcomb_norm0, hdet_sm, hdet_ts⟩ := hcomb_ind Finset.univ
  let comb := matrixSeries (anyKernelSeries lo hi A) * PowerSeries.map (Matrix.scalar (Fin r)) (anyKernelSeries lo hi C).det
  have hdet_eq : (anyKernelSeries lo hi C).det = ∏ i : Fin r, eigS i := kernelSeries_det_spectral lo hi C hC
  have hcomb_norm (k : ℕ) : ‖PowerSeries.coeff k comb‖ ≤ 2 ^ (r + 1) * ((k + 1 : ℕ) : ℝ) ^ r * ρ ^ k := by
    simpa only [comb, hdet_eq, Finset.card_univ, Fintype.card_fin, pow_succ'] using hcomb_norm0 k
  -- Sum of `comb`
  have hsc_norm_eq (x : ℝ) : ‖Matrix.scalar (Fin r) x‖ = ‖x‖ := norm_algebraMap' (Matrix (Fin r) (Fin r) ℝ) x
  have hdet_mat_sm : Summable (fun k => ‖PowerSeries.coeff k (PowerSeries.map (Matrix.scalar (Fin r)) (anyKernelSeries lo hi C).det)‖) := by
    rw [hdet_eq]; simpa only [PowerSeries.coeff_map, hsc_norm_eq] using hdet_sm
  have hcomb_ts : (∑' k, PowerSeries.coeff k comb) = (intervalGeometricMean lo hi ^ (r + 1) / C.det) • A⁻¹ := by
    have hmul_eq : (fun k => PowerSeries.coeff k comb) = fun k =>
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k,
          PowerSeries.coeff ij.1 (matrixSeries (anyKernelSeries lo hi A)) *
            PowerSeries.coeff ij.2 (PowerSeries.map (Matrix.scalar (Fin r)) (anyKernelSeries lo hi C).det) :=
      funext fun k => PowerSeries.coeff_mul k _ _
    have hsc_cont : Continuous (Matrix.scalar (Fin r) : ℝ → Matrix (Fin r) (Fin r) ℝ) :=
      (continuous_pi fun _ => continuous_id).matrix_diagonal
    have hdet_sm' : Summable (fun k => ‖PowerSeries.coeff k (anyKernelSeries lo hi C).det‖) := by rwa [hdet_eq]
    have hsc_ts : (∑' k, (Matrix.scalar (Fin r)) (PowerSeries.coeff k (anyKernelSeries lo hi C).det)) =
        (Matrix.scalar (Fin r)) (intervalGeometricMean lo hi ^ r / C.det) := by
      have hmap := (hdet_sm'.of_norm.hasSum.map (Matrix.scalar (Fin r)) hsc_cont).tsum_eq
      dsimp only [Function.comp_def] at hmap
      rw [hmap, hdet_eq, hdet_ts, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        hC.det_eq_prod_eigenvalues]
      simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [hmul_eq, ← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hmat_sum.1 hdet_mat_sm, hmat_sum.2]
    simp only [PowerSeries.coeff_map]
    rw [hsc_ts, Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal, smul_smul]
    congr 1; rw [pow_succ, div_eq_mul_inv, div_eq_mul_inv]; ring
  -- Truncation tail bound
  let α : ℝ := (intervalGeometricMean lo hi ^ (r + 1))⁻¹
  have hg_ne : intervalGeometricMean lo hi ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hlo (hlo.trans hlt))).ne'
  have hα : 0 ≤ α := by dsimp [α, intervalGeometricMean]; positivity
  have htarget : C.det⁻¹ • A⁻¹ = α • ∑' k, PowerSeries.coeff k comb := by
    rw [hcomb_ts, smul_smul]; congr 1; dsimp [α]
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hg_ne), one_mul]
  rw [htarget, parentInversePolynomial_eq_scaled_sum, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]
  have he := series_truncation_bound (fun k => PowerSeries.coeff k comb) r m ρ (2 ^ (r + 1))
    hρ hρ1 (by positivity) hcomb_norm
  have hpow : ρ ^ m = Real.exp (-(m : ℝ) * exteriorTau ((lo + hi) / (hi - lo))) := by
    rw [show ρ = Real.exp (-exteriorTau ((lo + hi) / (hi - lo))) from (exp_neg_exteriorTau lo hi hlo hlt).symm,
      ← Real.exp_nat_mul]; congr 1; ring
  refine (mul_le_mul_of_nonneg_left he hα).trans_eq ?_
  rw [hpow]; unfold parentInverseErrorConstant; dsimp [α, ρ]; ring

def matrixSimilarity {n : Type*} [Fintype n] [DecidableEq n]
    (Q : (Matrix n n ℝ)ˣ) : Matrix n n ℝ →ₐ[ℝ] Matrix n n ℝ where
  toFun A := (Q : Matrix n n ℝ) * A * (↑Q⁻¹ : Matrix n n ℝ)
  map_one' := by simp
  map_mul' A B := by simp [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by rw [Algebra.algebraMap_eq_smul_one]; simp

theorem matrixSimilarity_norm_le {n : Type*} [Fintype n] [DecidableEq n]
    (Q : (Matrix n n ℝ)ˣ) (A : Matrix n n ℝ) :
    ‖matrixSimilarity Q A‖ ≤ ‖(Q : Matrix n n ℝ)‖ * ‖(↑Q⁻¹ : Matrix n n ℝ)‖ * ‖A‖ :=
  ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))).trans_eq (by ring)

private theorem parent_inverse_similar_error {r : ℕ} [NeZero r]
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (A C : Matrix (Fin r) (Fin r) ℝ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : spectrum ℝ A ⊆ Set.Icc a b) (hSpecC : spectrum ℝ C ⊆ Set.Icc a b)
    (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) (χ : ℝ)
    (hχ : ‖(Q : Matrix (Fin r) (Fin r) ℝ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ) (m : ℕ) :
    ‖(matrixSimilarity R C).det⁻¹ • (matrixSimilarity Q A)⁻¹ -
      parentInversePolynomial a b (matrixSimilarity Q A) (matrixSimilarity R C) m‖ ≤
        χ * parentInverseErrorConstant a b r * ((m + 1 : ℕ) : ℝ) ^ r *
          Real.exp (-(m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  have hdet : (matrixSimilarity R C).det = C.det := Matrix.det_units_conj R C
  have hinv : (matrixSimilarity Q A)⁻¹ = matrixSimilarity Q A⁻¹ := by
    change ((Q : Matrix (Fin r) (Fin r) ℝ) * A * (↑Q⁻¹ : Matrix (Fin r) (Fin r) ℝ))⁻¹ =
      (Q : Matrix (Fin r) (Fin r) ℝ) * A⁻¹ * (↑Q⁻¹ : Matrix (Fin r) (Fin r) ℝ)
    simp only [Matrix.mul_inv_rev, ← Matrix.coe_units_inv, inv_inv, Matrix.mul_assoc]
  have hkc (k : ℕ) (X : Matrix (Fin r) (Fin r) ℝ) :
      coefficientMatrix k (anyKernelSeries a b X) = Polynomial.aeval X (kernelCoefficientPolynomial a b k) := by
    ext x z; simp [coefficientMatrix, anyKernelSeries]
  have hker_sim {U : (Matrix (Fin r) (Fin r) ℝ)ˣ} {M : Matrix (Fin r) (Fin r) ℝ} :
      anyKernelSeries a b (matrixSimilarity U M) =
        PowerSeries.C.mapMatrix (U : Matrix (Fin r) (Fin r) ℝ) * anyKernelSeries a b M *
          PowerSeries.C.mapMatrix (↑U⁻¹ : Matrix (Fin r) (Fin r) ℝ) := by
    ext i j k
    have hcm1 (X : Matrix (Fin r) (Fin r) ℝ) (K : Matrix (Fin r) (Fin r) (PowerSeries ℝ)) :
        coefficientMatrix k ((PowerSeries.C.mapMatrix X) * K) = X * coefficientMatrix k K := by
      ext x z; simp [coefficientMatrix, Matrix.mul_apply, map_sum, PowerSeries.coeff_C_mul]
    have hcm2 (K : Matrix (Fin r) (Fin r) (PowerSeries ℝ)) (X : Matrix (Fin r) (Fin r) ℝ) :
        coefficientMatrix k (K * (PowerSeries.C.mapMatrix X)) = coefficientMatrix k K * X := by
      ext x z; simp [coefficientMatrix, Matrix.mul_apply, map_sum, PowerSeries.coeff_mul_C]
    change (coefficientMatrix k (anyKernelSeries a b (matrixSimilarity U M))) i j =
      (coefficientMatrix k (_ * _ * _)) i j
    rw [hcm2, hcm1, hkc, hkc]
    exact congrArg (fun X : Matrix (Fin r) (Fin r) ℝ => X i j)
      (Polynomial.aeval_algHom_apply (matrixSimilarity U) M (kernelCoefficientPolynomial a b k))
  have hdet_sim : (anyKernelSeries a b (matrixSimilarity R C)).det = (anyKernelSeries a b C).det := by
    rw [hker_sim]
    simpa using Matrix.det_units_conj
      (Units.map (PowerSeries.C.mapMatrix : Matrix (Fin r) (Fin r) ℝ →+* Matrix (Fin r) (Fin r) (PowerSeries ℝ)).toMonoidHom R)
      (anyKernelSeries a b C)
  have hm_sim : matrixSeries (anyKernelSeries a b (matrixSimilarity Q A)) =
      PowerSeries.map (matrixSimilarity Q).toRingHom (matrixSeries (anyKernelSeries a b A)) := by
    apply PowerSeries.ext; intro k
    rw [PowerSeries.coeff_map]
    simp only [matrixSeries, PowerSeries.coeff_mk, hkc]
    exact Polynomial.aeval_algHom_apply (matrixSimilarity Q) A (kernelCoefficientPolynomial a b k)
  have hcomb_sim : matrixSeries (anyKernelSeries a b (matrixSimilarity Q A)) *
      PowerSeries.map (Matrix.scalar (Fin r)) (anyKernelSeries a b (matrixSimilarity R C)).det =
      PowerSeries.map (matrixSimilarity Q).toRingHom
        (matrixSeries (anyKernelSeries a b A) * PowerSeries.map (Matrix.scalar (Fin r)) (anyKernelSeries a b C).det) := by
    rw [map_mul, hm_sim, hdet_sim]; congr 1
    apply PowerSeries.ext; intro k
    simp only [PowerSeries.coeff_map]
    change Matrix.scalar (Fin r) _ = matrixSimilarity Q (Matrix.scalar (Fin r) _)
    exact ((matrixSimilarity Q).commutes _).symm
  have hp_sim : parentInversePolynomial a b (matrixSimilarity Q A) (matrixSimilarity R C) m =
      matrixSimilarity Q (parentInversePolynomial a b A C m) := by
    rw [parentInversePolynomial_eq_scaled_sum, parentInversePolynomial_eq_scaled_sum, hcomb_sim]
    simp_rw [PowerSeries.coeff_map]; rw [map_smul, map_sum]; rfl
  rw [hdet, hinv, hp_sim, ← map_smul, ← map_sub]
  have hχ0 : 0 ≤ χ := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hχ
  exact ((matrixSimilarity_norm_le Q _).trans
    ((mul_le_mul_of_nonneg_right hχ (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (parent_inverse_polynomial_error a b ha hab A C hA hC hSpecA hSpecC m) hχ0))).trans_eq (by ring)

abbrev incrementVariables (r : ℕ) := parentInverseVariables r ⊕ (Bool × Bool × Fin r)

def parentVariableMatrix (r : ℕ) : Matrix (Fin r) (Fin r) (MvPolynomial (parentInverseVariables r) ℝ) :=
  fun a b => X (Sum.inr ⟨0, (a, b)⟩)

def rawNumeratorPolynomial (r : ℕ) (T : Matrix (Fin r) (Fin r) ℝ)
    (response : Bool) (i : Fin r) : MvPolynomial (incrementVariables r) ℝ :=
  rename Sum.inl (parentVariableMatrix r).det * X (Sum.inr (false, response, i)) -
    ∑ j, ∑ k, ∑ l,
      rename Sum.inl (X (Sum.inl (i, j)) : MvPolynomial (parentInverseVariables r) ℝ) * C (T j k) *
        rename Sum.inl ((parentVariableMatrix r).adjugate k l) * X (Sum.inr (true, response, l))

def numeratorPolynomial (r : ℕ) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (i : Fin r) :
    MvPolynomial (incrementVariables r) ℝ :=
  rawNumeratorPolynomial r T false i - C y * rawNumeratorPolynomial r T true i

def rawIncrementEntryPolynomial (r : ℕ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (response : Bool) (m : ℕ) (i : Fin r) : MvPolynomial (incrementVariables r) ℝ :=
  ∑ j, rename Sum.inl (parentInverseEntryPolynomial a b r m i j) * rawNumeratorPolynomial r T response j

def incrementEntryPolynomial (r : ℕ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (i : Fin r) : MvPolynomial (incrementVariables r) ℝ :=
  ∑ j, rename Sum.inl (parentInverseEntryPolynomial a b r m i j) * numeratorPolynomial r T y j

theorem incrementEntryPolynomial_affine (r : ℕ) (a b : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) (i : Fin r) :
    incrementEntryPolynomial r a b T y m i =
      rawIncrementEntryPolynomial r a b T false m i - C y * rawIncrementEntryPolynomial r a b T true m i := by
  unfold incrementEntryPolynomial numeratorPolynomial rawIncrementEntryPolynomial
  simp_rw [mul_sub, mul_left_comm _ (C y) _]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

private theorem determinant_totalDegree_le {V n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (MvPolynomial V ℝ)) (hM : ∀ a b, (M a b).totalDegree ≤ 1) :
    M.det.totalDegree ≤ Fintype.card n := by
  rw [Matrix.det_apply]
  refine totalDegree_finsetSum_le fun σ _ => ?_
  simp only [Units.smul_def]
  exact (totalDegree_smul_le _ _).trans ((totalDegree_finsetProd Finset.univ _).trans
    ((Finset.sum_le_sum fun a _ => hM _ _).trans_eq (by simp)))

theorem incrementEntryPolynomial_degree (r : ℕ) [NeZero r] (a b : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) (i : Fin r) :
    (incrementEntryPolynomial r a b T y m i).totalDegree ≤ m + r + 1 := by
  have hraw (resp : Bool) (j : Fin r) : (rawNumeratorPolynomial r T resp j).totalDegree ≤ r + 1 := by
    have hparM (x z : Fin r) : (parentVariableMatrix r x z).totalDegree ≤ 1 := by simp [parentVariableMatrix]
    have hadj_deg : ∀ {s : ℕ} (M : Matrix (Fin s) (Fin s) (MvPolynomial (parentInverseVariables r) ℝ)),
        (∀ x z, (M x z).totalDegree ≤ 1) → ∀ b c : Fin s, (M.adjugate b c).totalDegree ≤ s - 1 := by
      intro s M hM b c
      cases s with
      | zero => exact Fin.elim0 b
      | succ k =>
        rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
        refine (totalDegree_mul _ _).trans ?_
        have hz : ((-1 : MvPolynomial (parentInverseVariables r) ℝ) ^ (c.val + b.val)).totalDegree ≤ 0 := by
          simpa using totalDegree_pow (-1 : MvPolynomial (parentInverseVariables r) ℝ) (c.val + b.val)
        simpa using Nat.add_le_add hz (determinant_totalDegree_le (M.submatrix c.succAbove b.succAbove) fun _ _ => hM _ _)
    unfold rawNumeratorPolynomial
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_mul _ _).trans (Nat.add_le_add ?_ (totalDegree_X _).le)
      exact (totalDegree_rename_le _ _).trans (by simpa using determinant_totalDegree_le (parentVariableMatrix r) hparM)
    · refine totalDegree_finsetSum_le fun a _ => totalDegree_finsetSum_le fun b _ => totalDegree_finsetSum_le fun c _ => ?_
      have hadj' := (totalDegree_rename_le (Sum.inl : parentInverseVariables r → incrementVariables r) _).trans
        (hadj_deg (parentVariableMatrix r) hparM b c)
      let pA : MvPolynomial (incrementVariables r) ℝ := rename Sum.inl (X (Sum.inl (j, a)) : MvPolynomial (parentInverseVariables r) ℝ)
      let pAdj : MvPolynomial (incrementVariables r) ℝ := rename Sum.inl ((parentVariableMatrix r).adjugate b c)
      let pV : MvPolynomial (incrementVariables r) ℝ := X (Sum.inr (true, resp, c))
      have h1 := totalDegree_mul pA (C (T a b))
      have h2 := totalDegree_mul (pA * C (T a b)) pAdj
      have h3 := totalDegree_mul (pA * C (T a b) * pAdj) pV
      have hpA : pA.totalDegree ≤ 1 := by dsimp [pA]; rw [rename_X]; exact (totalDegree_X _).le
      have hpV : pV.totalDegree = 1 := totalDegree_X _
      simp only [totalDegree_C, add_zero, hpV] at h1 h3
      have hr : r ≠ 0 := NeZero.ne r
      change pAdj.totalDegree ≤ r - 1 at hadj'
      change (pA * C (T a b) * pAdj * pV).totalDegree ≤ r + 1
      omega
  have hnum (j : Fin r) : (numeratorPolynomial r T y j).totalDegree ≤ r + 1 :=
    (totalDegree_sub _ _).trans (max_le (hraw false j) ((totalDegree_mul _ _).trans (by simpa using hraw true j)))
  exact totalDegree_finsetSum_le fun j _ => (totalDegree_mul _ _).trans
    ((Nat.add_le_add ((totalDegree_rename_le _ _).trans (parentInverseEntryPolynomial_degree a b r m i j)) (hnum j)).trans_eq (by omega))

def incrementValuation {r : ℕ} (A C : Matrix (Fin r) (Fin r) ℝ)
    (U V : Bool → Fin r → ℝ) : incrementVariables r → ℝ
  | Sum.inl x => parentValuation A C x
  | Sum.inr (parent, response, i) => if parent then V response i else U response i

theorem incrementEntryPolynomial_error {r : ℕ} [NeZero r]
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (A C T : Matrix (Fin r) (Fin r) ℝ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : spectrum ℝ A ⊆ Set.Icc a b) (hSpecC : spectrum ℝ C ⊆ Set.Icc a b)
    (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) (χ : ℝ)
    (hχ : ‖(Q : Matrix (Fin r) (Fin r) ℝ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ)
    (U V : Bool → Fin r → ℝ) (y ε : ℝ)
    (hδ : ‖(EuclideanSpace.equiv (Fin r) ℝ).symm
      ((matrixSimilarity Q A)⁻¹.mulVec (U false - y • U true) -
        T.mulVec ((matrixSimilarity R C)⁻¹.mulVec (V false - y • V true)))‖ ≤ ε) (m : ℕ) :
    let G := matrixSimilarity Q A
    let Cm := matrixSimilarity R C
    ‖(EuclideanSpace.equiv (Fin r) ℝ).symm
      ((fun i => eval (incrementValuation G Cm U V) (incrementEntryPolynomial r a b T y m i)) -
        (G⁻¹.mulVec (U false - y • U true) - T.mulVec (Cm⁻¹.mulVec (V false - y • V true))))‖ ≤
      (χ ^ 2 * b ^ (r + 1) * parentInverseErrorConstant a b r) * ε *
        ((m + 1 : ℕ) : ℝ) ^ r * Real.exp (-(m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  dsimp only
  let G := matrixSimilarity Q A
  let Cm := matrixSimilarity R C
  let β := U false - y • U true
  let βm := V false - y • V true
  let N_vec : Fin r → ℝ := Cm.det • β - G.mulVec (T.mulVec (Cm.adjugate.mulVec βm))
  -- Evaluate `incrementEntryPolynomial` at `incrementValuation G Cm U V`
  have heval : (fun i => eval (incrementValuation G Cm U V) (incrementEntryPolynomial r a b T y m i)) =
      (parentInversePolynomial a b G Cm m).mulVec N_vec := by
    let f := MvPolynomial.eval₂Hom (RingHom.id ℝ) (parentValuation G Cm)
    have hm : f.mapMatrix (parentVariableMatrix r) = Cm := by
      ext x z; change eval (parentValuation G Cm) (parentVariableMatrix r x z) = Cm x z
      simp [parentVariableMatrix, parentValuation]
    have hd : eval (incrementValuation G Cm U V) (rename Sum.inl (parentVariableMatrix r).det) = Cm.det := by
      rw [eval_rename]; change f (parentVariableMatrix r).det = Cm.det; rw [f.map_det, hm]
    have ha_adj (k l : Fin r) : eval (incrementValuation G Cm U V) (rename Sum.inl ((parentVariableMatrix r).adjugate k l)) = Cm.adjugate k l := by
      rw [eval_rename]; change f ((parentVariableMatrix r).adjugate k l) = Cm.adjugate k l
      have h := congrArg (fun M => M k l) (f.map_adjugate (parentVariableMatrix r)); rwa [hm] at h
    have hraw_ev (resp : Bool) (j : Fin r) :
        eval (incrementValuation G Cm U V) (rawNumeratorPolynomial r T resp j) =
          (Cm.det • U resp - G.mulVec (T.mulVec (Cm.adjugate.mulVec (V resp)))) j := by
      simp only [rawNumeratorPolynomial, eval_sub, eval_mul, eval_sum, eval_C, hd, ha_adj,
        eval_X, incrementValuation, Bool.false_eq_true, ↓reduceIte, rename_X, parentValuation,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
        Finset.mul_sum, Finset.sum_mul, mul_assoc]
    ext i
    simp only [incrementEntryPolynomial, numeratorPolynomial, eval_sum, eval_mul, eval_sub, eval_C,
      hraw_ev, eval_rename]
    change ∑ j, eval (parentValuation G Cm) (parentInverseEntryPolynomial a b r m i j) * _ = _
    simp only [parentInversePolynomial, Matrix.mulVec, dotProduct, N_vec, β, βm,
      Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub, smul_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [heval]
  -- Spectral determinant & norm facts
  have hspec_det {M : Matrix (Fin r) (Fin r) ℝ} (hM : M.IsHermitian) (hSp : spectrum ℝ M ⊆ Set.Icc a b) :
      M.det ≠ 0 ∧ |M.det| ≤ b ^ r ∧ ‖M‖ ≤ b := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hM.det_eq_prod_eigenvalues]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => (ha.trans_le (hSp (hM.eigenvalues_mem_spectrum_real i)).1).ne'
    · rw [hM.det_eq_prod_eigenvalues]
      simp only [RCLike.ofReal_real_eq_id, id_eq]
      rw [Finset.abs_prod]
      refine (Finset.prod_le_prod₀ (g := fun _ => b) (fun _ _ => abs_nonneg _) fun i _ => ?_).trans_eq (by simp)
      have h := hSp (hM.eigenvalues_mem_spectrum_real i)
      rw [abs_of_nonneg (ha.le.trans h.1)]; exact h.2
    · have hs : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM
      rw [← cfc_id ℝ M hs]; refine norm_cfc_le (ha.trans hab).le fun x hx => ?_
      simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg (ha.le.trans (hSp hx).1)] using (hSp hx).2
  obtain ⟨hAdet, _, hAnorm⟩ := hspec_det hA hSpecA
  obtain ⟨hCdet, hCdet_le, _⟩ := hspec_det hC hSpecC
  have hGdet : G.det ≠ 0 := by rw [show G.det = A.det from Matrix.det_units_conj Q A]; exact hAdet
  have hCmdet : Cm.det ≠ 0 := by rw [show Cm.det = C.det from Matrix.det_units_conj R C]; exact hCdet
  have hunitG : IsUnit G.det := isUnit_iff_ne_zero.mpr hGdet
  have hid : Cm.det⁻¹ • G⁻¹.mulVec N_vec = G⁻¹.mulVec β - T.mulVec (Cm⁻¹.mulVec βm) := by
    dsimp [N_vec]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hunitG,
      Matrix.one_mulVec, smul_sub, smul_smul, inv_mul_cancel₀ hCmdet, one_smul]
    simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mulVec, Matrix.mulVec_smul]
  have hfac : N_vec = Cm.det • G.mulVec (G⁻¹.mulVec β - T.mulVec (Cm⁻¹.mulVec βm)) := by
    have h := congrArg (fun v : Fin r → ℝ => Cm.det • G.mulVec v) hid
    simpa only [Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hCmdet, one_smul,
      Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hunitG, Matrix.one_mulVec] using h
  have hχ0 : 0 ≤ χ := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hχ
  have hnG : ‖G‖ ≤ χ * b := (matrixSimilarity_norm_le Q A).trans
    ((mul_le_mul_of_nonneg_right hχ (norm_nonneg A)).trans (mul_le_mul_of_nonneg_left hAnorm hχ0))
  have hdCm : |Cm.det| ≤ b ^ r := by rw [show Cm.det = C.det from Matrix.det_units_conj R C]; exact hCdet_le
  have hN_le : ‖(EuclideanSpace.equiv (Fin r) ℝ).symm N_vec‖ ≤ χ * b ^ (r + 1) * ε := by
    rw [hfac]
    change ‖Cm.det • (EuclideanSpace.equiv (Fin r) ℝ).symm (G.mulVec _)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    have hv := G.l2_opNorm_mulVec ((EuclideanSpace.equiv (Fin r) ℝ).symm (G⁻¹.mulVec β - T.mulVec (Cm⁻¹.mulVec βm)))
    calc |Cm.det| * _ ≤ b ^ r * ((χ * b) * ε) :=
          mul_le_mul hdCm (hv.trans (mul_le_mul hnG hδ (norm_nonneg _) (mul_nonneg hχ0 (ha.trans hab).le)))
            (norm_nonneg _) (by have := ha.trans hab; positivity)
      _ = χ * b ^ (r + 1) * ε := by rw [pow_succ]; ring
  change ‖(EuclideanSpace.equiv (Fin r) ℝ).symm ((parentInversePolynomial a b G Cm m).mulVec N_vec -
    (G⁻¹.mulVec β - T.mulVec (Cm⁻¹.mulVec βm)))‖ ≤ _
  rw [← hid, ← Matrix.smul_mulVec, ← Matrix.sub_mulVec]
  have hn := (parentInversePolynomial a b G Cm m - Cm.det⁻¹ • G⁻¹).l2_opNorm_mulVec ((EuclideanSpace.equiv (Fin r) ℝ).symm N_vec)
  have hp_err : ‖Cm.det⁻¹ • G⁻¹ - parentInversePolynomial a b G Cm m‖ ≤
      χ * parentInverseErrorConstant a b r * ((m + 1 : ℕ) : ℝ) ^ r *
        Real.exp (-(m : ℝ) * exteriorTau ((a + b) / (b - a))) :=
    parent_inverse_similar_error a b ha hab A C hA hC hSpecA hSpecC Q R χ hχ m
  have hpe_pos := parentInverseErrorConstant_pos a b ha hab r
  have hb_pos : 0 < b := ha.trans hab
  apply hn.trans
  rw [norm_sub_rev]
  exact (mul_le_mul hp_err hN_le (norm_nonneg _) (by positivity)).trans_eq (by ring)

-- 4. Noncommutative Chebyshev Volterra perturbation & complex Cauchy derivative bounds

private def matrixChebyshevT {R : Type*} [Ring R] [Algebra ℝ R] (x : R) (n : ℕ) : R :=
  Polynomial.aeval x (Polynomial.Chebyshev.T ℝ (n : ℤ))

private def matrixChebyshevU {R : Type*} [Ring R] [Algebra ℝ R] (x : R) (n : ℤ) : R :=
  Polynomial.aeval x (Polynomial.Chebyshev.U ℝ n)

def perturbationConstant (η : ℝ) : ℝ := ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * η ^ k

private theorem perturbationConstant_pos (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    0 < perturbationConstant η := by
  have hs : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * η ^ k) := by
    simpa using weighted_geometric_summable 1 η hη hη1
  exact hs.tsum_pos (fun k => by positivity) 0 (by simp)

private theorem matrixChebyshevT_neighborhood_bound {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    [NormOneClass R] (x y : R) (hx : ∀ n, ‖matrixChebyshevT x n‖ ≤ 1) (η δ : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * perturbationConstant η ≤ 1) (hd : ‖y - x‖ ≤ δ) (n : ℕ) :
    η ^ n * ‖matrixChebyshevT y n‖ ≤ 2 := by
  let f (j : ℕ) : R := if j = 0 then y - x else 2 * (y - x) * matrixChebyshevT y j
  let resp (m : ℕ) : R := ∑ j ∈ Finset.range m, matrixChebyshevU x ((m : ℤ) - 1 - j) * f j
  -- Discrete variation of constants
  have hrecT (z : R) (m : ℕ) : matrixChebyshevT z (m + 2) = 2 * z * matrixChebyshevT z (m + 1) - matrixChebyshevT z m := by
    unfold matrixChebyshevT; rw [show ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 by omega, Polynomial.Chebyshev.T_add_two]; simp [map_ofNat]
  have hrecU (m : ℤ) : matrixChebyshevU x (m + 1) = 2 * x * matrixChebyshevU x m - matrixChebyshevU x (m - 1) := by
    unfold matrixChebyshevU; rw [Polynomial.Chebyshev.U_add_one]; simp [map_ofNat]
  have hpert (m : ℕ) : matrixChebyshevT y m - matrixChebyshevT x m = resp m := by
    induction m using Nat.twoStepInduction with
    | zero => simp [matrixChebyshevT, resp]
    | one => simp [matrixChebyshevT, resp, f, matrixChebyshevU]
    | more m hm hm1 =>
      have hresp_rec : resp (m + 2) = 2 * x * resp (m + 1) - resp m + f (m + 1) := by
        dsimp only [resp]; push_cast
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]; push_cast
        simp only [show (m : ℤ) + 2 - 1 - m = 1 by ring, show (m : ℤ) + 2 - 1 - (m + 1) = 0 by ring,
          show (m : ℤ) + 1 - 1 - m = 0 by ring, matrixChebyshevU, Polynomial.Chebyshev.U_zero,
          Polynomial.Chebyshev.U_one, map_one, map_mul, map_ofNat, Polynomial.aeval_X, one_mul]
        change (∑ j ∈ Finset.range m, matrixChebyshevU x ((m : ℤ) + 2 - 1 - j) * f j) + 2 * x * f m + f (m + 1) =
          2 * x * ((∑ j ∈ Finset.range m, matrixChebyshevU x ((m : ℤ) + 1 - 1 - j) * f j) + f m) -
            ∑ j ∈ Finset.range m, matrixChebyshevU x ((m : ℤ) - 1 - j) * f j + f (m + 1)
        simp_rw [show ∀ j : ℕ, (m : ℤ) + 2 - 1 - j = ((m : ℤ) + 1 - 1 - j) + 1 from fun _ => by ring, hrecU,
          show ∀ j : ℕ, (m : ℤ) + 1 - 1 - j - 1 = (m : ℤ) - 1 - j from fun _ => by ring]
        simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]; noncomm_ring
      rw [hrecT, hrecT, hresp_rec, ← hm, ← hm1]
      simp only [f, show m + 1 ≠ 0 by omega, ↓reduceIte]; noncomm_ring
  have h2R : ‖(2 : R)‖ = 2 := by
    rw [show (2 : R) = (2 : ℝ) • (1 : R) by norm_num [Algebra.smul_def, map_ofNat], norm_smul, norm_one, Real.norm_two, mul_one]
  have hUnorm (m : ℕ) : ‖matrixChebyshevU x (m : ℤ)‖ ≤ (m : ℝ) + 1 := by
    induction m using Nat.twoStepInduction with
    | zero => simp [matrixChebyshevU]
    | one =>
      have hx1 : ‖x‖ ≤ 1 := by simpa [matrixChebyshevT] using hx 1
      simp only [matrixChebyshevU, Nat.cast_one, Polynomial.Chebyshev.U_one, map_mul, map_ofNat, Polynomial.aeval_X]
      exact (norm_mul_le _ _).trans (by rw [h2R]; linarith)
    | more m hm _ =>
      have he : matrixChebyshevU x ((m + 2 : ℕ) : ℤ) = 2 * matrixChebyshevT x (m + 2) + matrixChebyshevU x (m : ℤ) := by
        unfold matrixChebyshevU matrixChebyshevT
        rw [show ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 by omega, Polynomial.Chebyshev.U_eq_two_mul_T_add_U]; simp [map_ofNat]
      rw [he]
      refine (norm_add_le _ _).trans ((add_le_add (by simpa only [h2R] using norm_mul_le (2 : R) _) hm).trans ?_)
      have := hx (m + 2); push_cast; linarith
  -- Volterra inequality & discrete Gronwall induction
  have hvol (m : ℕ) : ‖matrixChebyshevT y m‖ ≤
      1 + 2 * δ * ∑ j ∈ Finset.range m, ((m - j : ℕ) : ℝ) * ‖matrixChebyshevT y j‖ := by
    rw [sub_eq_iff_eq_add'.mp (hpert m)]
    refine (norm_add_le _ _).trans ((add_le_add (hx m) (norm_sum_le _ _)).trans ?_)
    rw [Finset.mul_sum]; refine add_le_add le_rfl (Finset.sum_le_sum fun j hj => ?_)
    have hjm := Finset.mem_range.mp hj
    have hfnorm : ‖f j‖ ≤ 2 * δ * ‖matrixChebyshevT y j‖ := by
      dsimp only [f]; split_ifs with hj0
      · subst j; simpa [matrixChebyshevT] using hd.trans (by linarith)
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans (by rw [h2R]; gcongr)) (norm_nonneg _))
    rw [show (m : ℤ) - 1 - j = ((m - 1 - j : ℕ) : ℤ) by omega]
    refine ((norm_mul_le _ _).trans (mul_le_mul (hUnorm _) hfnorm (norm_nonneg _) (by positivity))).trans_eq ?_
    rw [show ((m - 1 - j : ℕ) : ℝ) + 1 = ((m - j : ℕ) : ℝ) by exact_mod_cast (show m - 1 - j + 1 = m - j by omega)]; ring
  induction n using Nat.strong_induction_on with
  | h m ih =>
    have hs_conv : (∑ j ∈ Finset.range m, ((m - j : ℕ) : ℝ) * η ^ (m - j)) ≤ perturbationConstant η := by
      have hs : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * η ^ k) := by simpa using weighted_geometric_summable 1 η hη hη1
      rw [← Finset.sum_range_reflect]
      calc ∑ j ∈ Finset.range m, ((m - (m - 1 - j) : ℕ) : ℝ) * η ^ (m - (m - 1 - j))
        _ = ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) * η ^ (j + 1) :=
            Finset.sum_congr rfl fun j hj => by have := Finset.mem_range.mp hj; rw [show m - (m - 1 - j) = j + 1 by omega]
        _ ≤ ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) * η ^ j :=
            Finset.sum_le_sum fun j _ => by
              rw [pow_succ, ← mul_assoc]
              exact (mul_le_mul_of_nonneg_left hη1.le (by positivity : 0 ≤ ((j + 1 : ℕ) : ℝ) * η ^ j)).trans_eq (mul_one _)
        _ ≤ perturbationConstant η := hs.sum_le_tsum (Finset.range m) fun _ _ => by positivity
    have hsum : ∑ j ∈ Finset.range m, η ^ m * (((m - j : ℕ) : ℝ) * ‖matrixChebyshevT y j‖) ≤
        ∑ j ∈ Finset.range m, 2 * (((m - j : ℕ) : ℝ) * η ^ (m - j)) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjm := Finset.mem_range.mp hj
      have hp : η ^ m = η ^ (m - j) * η ^ j := by rw [← pow_add, Nat.sub_add_cancel hjm.le]
      calc η ^ m * (((m - j : ℕ) : ℝ) * ‖matrixChebyshevT y j‖)
        _ = (((m - j : ℕ) : ℝ) * η ^ (m - j)) * (η ^ j * ‖matrixChebyshevT y j‖) := by rw [hp]; ring
        _ ≤ (((m - j : ℕ) : ℝ) * η ^ (m - j)) * 2 := mul_le_mul_of_nonneg_left (ih j hjm) (by positivity)
        _ = _ := by ring
    calc η ^ m * ‖matrixChebyshevT y m‖
      _ ≤ η ^ m + 2 * δ * ∑ j ∈ Finset.range m, η ^ m * (((m - j : ℕ) : ℝ) * ‖matrixChebyshevT y j‖) := by
          refine (mul_le_mul_of_nonneg_left (hvol m) (pow_nonneg hη.le m)).trans_eq ?_
          rw [← Finset.mul_sum]; ring
      _ ≤ 1 + 4 * δ * ∑ j ∈ Finset.range m, ((m - j : ℕ) : ℝ) * η ^ (m - j) := by
          refine (add_le_add (pow_le_one₀ hη.le hη1.le) (mul_le_mul_of_nonneg_left hsum (by positivity))).trans_eq ?_
          rw [← Finset.mul_sum]; ring
      _ ≤ 1 + 4 * δ * perturbationConstant η :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hs_conv (by positivity))
      _ ≤ 2 := by linarith

theorem matrix_entry_norm_le_l2 {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ n := EuclideanSpace.single j 1
  have he : ‖e‖ = 1 := by simp [e]
  let T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A
  have hi := PiLp.norm_apply_le (T e) i
  have hentry : (T e) i = A i j := by
    simp [T, e, Matrix.toEuclideanCLM_toLp, EuclideanSpace.single, Matrix.mulVec, dotProduct]
  rw [hentry] at hi
  exact hi.trans (by simpa [he, T, Matrix.l2_opNorm_toEuclideanCLM] using T.le_opNorm e)

private def ofRealMatrixStarAlgHom {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix n n ℝ →⋆ₐ[ℝ] Matrix n n ℂ :=
  { Complex.ofRealHom.mapMatrix with
    commutes' := fun a => by
      ext i j; change ((if i = j then a else 0 : ℝ) : ℂ) = if i = j then (a : ℂ) else 0
      split_ifs <;> simp
    map_star' := fun A => by ext i j; simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] }

private theorem complexify_matrix_spectrum {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    spectrum ℝ (A.map Complex.ofReal) = spectrum ℝ A :=
  (Matrix.isHermitian_iff_isSelfAdjoint.mp hA).map_spectrum_real (ofRealMatrixStarAlgHom (n := n))
    (fun X Y h => by ext i j; exact Complex.ofReal_injective (congrArg (fun M : Matrix n n ℂ => M i j) h))
    (ofRealMatrixStarAlgHom (n := n)).toAlgHom.toLinearMap.continuous_of_finiteDimensional

theorem complexify_matrix_norm {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) : ‖A.map Complex.ofReal‖ = ‖A‖ := by
  let φ := ofRealMatrixStarAlgHom (n := n)
  change ‖φ A‖ = ‖A‖
  have hs : IsSelfAdjoint (star A * A) := .star_mul_self A
  have hspec : spectrum ℝ (φ (star A * A)) = spectrum ℝ (star A * A) :=
    complexify_matrix_spectrum (star A * A) (Matrix.isHermitian_iff_isSelfAdjoint.mpr hs)
  have hgR := IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) (star A * A) hs
  have hgC := IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) (φ (star A * A)) (hs.map φ)
  rw [hspec] at hgC
  have he : ‖φ (star A * A)‖ = ‖star A * A‖ := hgC.unique hgR
  rw [map_mul, map_star, CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self] at he
  exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp he

private def complexMatrixSimilarity {n : Type*} [Fintype n] [DecidableEq n]
    (Q : (Matrix n n ℂ)ˣ) : Matrix n n ℂ →ₐ[ℝ] Matrix n n ℂ where
  toFun A := (Q : Matrix n n ℂ) * A * (↑Q⁻¹ : Matrix n n ℂ)
  map_one' := by simp
  map_mul' A B := by simp [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by rw [Algebra.algebraMap_eq_smul_one]; simp

private def normalizeMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (intervalHalfWidth lo hi)⁻¹ • (A - intervalCenter lo hi • 1)

private theorem similar_complex_kernel_entry_bound {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (A B : Matrix n n ℂ) (Q : (Matrix n n ℂ)ˣ) (χ : ℝ) (hχ : 0 ≤ χ)
    (hQ : ‖(Q : Matrix n n ℂ)‖ * ‖(↑Q⁻¹ : Matrix n n ℂ)‖ ≤ χ)
    (hA : (complexMatrixSimilarity Q⁻¹ A).IsHermitian)
    (hSpec : spectrum ℝ (complexMatrixSimilarity Q⁻¹ A) ⊆ Set.Icc lo hi)
    (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hd : χ * ‖normalizeMatrix lo hi B - normalizeMatrix lo hi A‖ ≤ (4 * perturbationConstant η)⁻¹)
    (a b : n) (k : ℕ) :
    ‖PowerSeries.coeff k (anyKernelSeries lo hi B a b)‖ ≤ (4 * χ) * (intervalRho lo hi / η) ^ k := by
  let δ := (4 * perturbationConstant η)⁻¹
  have hδ : 0 ≤ δ := (inv_pos.mpr (mul_pos (by norm_num) (perturbationConstant_pos η hη hη1))).le
  have hsmall : 4 * δ * perturbationConstant η ≤ 1 := by
    dsimp [δ]; field_simp [(perturbationConstant_pos η hη hη1).ne']; norm_num
  have hsim_norm (U : (Matrix n n ℂ)ˣ) (M : Matrix n n ℂ) :
      ‖complexMatrixSimilarity U M‖ ≤ ‖(U : Matrix n n ℂ)‖ * ‖(↑U⁻¹ : Matrix n n ℂ)‖ * ‖M‖ :=
    ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))).trans_eq (by ring)
  have hd' : ‖normalizeMatrix lo hi (complexMatrixSimilarity Q⁻¹ B) -
      normalizeMatrix lo hi (complexMatrixSimilarity Q⁻¹ A)‖ ≤ δ := by
    have hn_sim (M : Matrix n n ℂ) : normalizeMatrix lo hi (complexMatrixSimilarity Q⁻¹ M) =
        complexMatrixSimilarity Q⁻¹ (normalizeMatrix lo hi M) := by simp [normalizeMatrix, map_sub, map_smul]
    rw [hn_sim, hn_sim, ← map_sub]
    exact (hsim_norm Q⁻¹ _).trans ((mul_le_mul_of_nonneg_right (by simpa only [inv_inv, mul_comm] using hQ) (norm_nonneg _)).trans hd)
  -- Center Chebyshev bound for Hermitian `A' := complexMatrixSimilarity Q⁻¹ A`
  let A' := complexMatrixSimilarity Q⁻¹ A
  let B' := complexMatrixSimilarity Q⁻¹ B
  have hcenter (m : ℕ) : ‖matrixChebyshevT (normalizeMatrix lo hi A') m‖ ≤ 1 := by
    have haev : Polynomial.aeval A' (normalizedChebyshev lo hi m) = matrixChebyshevT (normalizeMatrix lo hi A') m := by
      rw [normalizedChebyshev, Polynomial.aeval_comp]; congr 1; simp [normalizeMatrix, Algebra.smul_def]
    rw [← haev, ← cfc_polynomial _ A' (Matrix.isHermitian_iff_isSelfAdjoint.mp hA)]
    refine norm_cfc_le (by norm_num) fun x hx => ?_
    rw [normalizedChebyshev_eval, Real.norm_eq_abs]
    exact chebyshev_abs_le_one _ (interval_argument_mem lo hi x hlo hlt (hSpec hx)) m
  have hb := matrixChebyshevT_neighborhood_bound _ _ hcenter η δ hη hη1 hδ hsmall hd' k
  have hk_bd : ‖Polynomial.aeval B' (kernelCoefficientPolynomial lo hi k)‖ ≤ 4 * (intervalRho lo hi / η) ^ k := by
    have haev : Polynomial.aeval B' (normalizedChebyshev lo hi k) = matrixChebyshevT (normalizeMatrix lo hi B') k := by
      rw [normalizedChebyshev, Polynomial.aeval_comp]; congr 1; simp [normalizeMatrix, Algebra.smul_def]
    unfold kernelCoefficientPolynomial
    rw [map_mul, Polynomial.aeval_C, ← Algebra.smul_def, norm_smul, haev]
    split_ifs with hk0
    · subst k; simp [matrixChebyshevT]
    · have hr := intervalRho_pos lo hi hlo hlt
      rw [Real.norm_eq_abs, abs_mul, show |(2 : ℝ)| = 2 by norm_num, abs_pow, abs_neg, abs_of_pos hr,
        div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hη k)]
      calc _ = 2 * intervalRho lo hi ^ k * (η ^ k * ‖matrixChebyshevT (normalizeMatrix lo hi B') k‖) := by ring
        _ ≤ 2 * intervalRho lo hi ^ k * 2 := mul_le_mul_of_nonneg_left hb (by positivity)
        _ = _ := by ring
  have he : Polynomial.aeval B (kernelCoefficientPolynomial lo hi k) =
      complexMatrixSimilarity Q (Polynomial.aeval B' (kernelCoefficientPolynomial lo hi k)) := by
    rw [← Polynomial.aeval_algHom_apply]
    congr 1; simp [B', complexMatrixSimilarity, Matrix.mul_assoc]
  simp only [anyKernelSeries, PowerSeries.coeff_mk]
  refine (matrix_entry_norm_le_l2 _ a b).trans ?_
  rw [he]
  exact ((hsim_norm Q _).trans (mul_le_mul hQ hk_bd (norm_nonneg _) hχ)).trans_eq (by ring)

-- Coordinate operators & envelopes

def coordMatrixCLM (r : ℕ) (parent : Bool) : (incrementVariables r → ℂ) →L[ℂ] Matrix (Fin r) (Fin r) ℂ :=
  ({ toFun := fun z i j => if parent then z (Sum.inl (Sum.inr ⟨0, (i, j)⟩)) else z (Sum.inl (Sum.inl (i, j)))
     map_add' := fun x y => by ext i j; split_ifs <;> rfl
     map_smul' := fun c x => by ext i j; split_ifs <;> rfl } :
    (incrementVariables r → ℂ) →ₗ[ℂ] Matrix (Fin r) (Fin r) ℂ).toContinuousLinearMap

def similarInverseCoordinateRadius (r : ℕ) (lo hi η χ : ℝ) : ℝ :=
  min 1 ((4 * perturbationConstant η)⁻¹ /
    (χ * max 1 (|(intervalHalfWidth lo hi)⁻¹| * (‖coordMatrixCLM r false‖ + ‖coordMatrixCLM r true‖))))

private theorem similarInverseCoordinateRadius_pos (r : ℕ) (lo hi η χ : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (hχ : 0 < χ) :
    0 < similarInverseCoordinateRadius r lo hi η χ := by
  have := perturbationConstant_pos η hη hη1
  unfold similarInverseCoordinateRadius
  exact lt_min zero_lt_one (div_pos (by positivity) (mul_pos hχ (zero_lt_one.trans_le (le_max_left _ _))))

def polynomialCoordinateBound {V : Type*} [Fintype V] [DecidableEq V] (P : MvPolynomial V ℝ) (R : ℝ) : ℝ :=
  ∑ α ∈ P.support, ‖P.coeff α‖ * ∏ j : V, R ^ α j

def similarIncrementEnvelope (r : ℕ) (lo hi q χ L Y : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  (|(intervalGeometricMean lo hi ^ (r + 1))⁻¹| *
    ((Fintype.card (Equiv.Perm (Fin r)) : ℝ) * (4 * χ) ^ (r + 1)) *
    ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (r + 1) * q ^ k) *
  ∑ j : Fin r, (polynomialCoordinateBound (rawNumeratorPolynomial r T false j) (L + 1) +
    Y * polynomialCoordinateBound (rawNumeratorPolynomial r T true j) (L + 1))

def incrementFinPolynomial (r : ℕ) (lo hi : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (i : Fin r) : MvPolynomial (Fin (Fintype.card (incrementVariables r))) ℝ :=
  MvPolynomial.rename (Fintype.equivFin (incrementVariables r)) (incrementEntryPolynomial r lo hi T y m i)

def currentRealCoordinateMatrix (r : ℕ) (u : incrementVariables r → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => u (Sum.inl (Sum.inl (i, j)))

def parentRealCoordinateMatrix (r : ℕ) (u : incrementVariables r → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => u (Sum.inl (Sum.inr ⟨0, (i, j)⟩))

structure InverseDerivativeCenter (r : ℕ) (lo hi χ L : ℝ) where
  moments : incrementVariables r → ℝ
  normBound : ‖moments‖ ≤ L
  currentChart : (Matrix (Fin r) (Fin r) ℝ)ˣ
  parentChart : (Matrix (Fin r) (Fin r) ℝ)ˣ
  currentCondition : ‖(currentChart : Matrix (Fin r) (Fin r) ℝ)‖ * ‖(↑currentChart⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ
  parentCondition : ‖(parentChart : Matrix (Fin r) (Fin r) ℝ)‖ * ‖(↑parentChart⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ
  currentHermitian : (matrixSimilarity currentChart⁻¹ (currentRealCoordinateMatrix r moments)).IsHermitian
  parentHermitian : (matrixSimilarity parentChart⁻¹ (parentRealCoordinateMatrix r moments)).IsHermitian
  currentSpectrum : spectrum ℝ (matrixSimilarity currentChart⁻¹ (currentRealCoordinateMatrix r moments)) ⊆ Set.Icc lo hi
  parentSpectrum : spectrum ℝ (matrixSimilarity parentChart⁻¹ (parentRealCoordinateMatrix r moments)) ⊆ Set.Icc lo hi

def inverseDerivativeRate (r : ℕ) (lo hi η χ : ℝ) : ℝ :=
  Real.exp 1 / similarInverseCoordinateRadius r lo hi η χ

theorem inverseDerivativeRate_pos (r : ℕ) (lo hi η χ : ℝ) (hη : 0 < η) (hη1 : η < 1) (hχ : 0 < χ) :
    0 < inverseDerivativeRate r lo hi η χ :=
  div_pos (Real.exp_pos _) (similarInverseCoordinateRadius_pos r lo hi η χ hη hη1 hχ)

def incrementFinVector (r : ℕ) (lo hi : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) :
    (Fin (Fintype.card (incrementVariables r)) → ℝ) → Fin r → ℝ :=
  fun x i => MvPolynomial.eval x (incrementFinPolynomial r lo hi T y m i)

theorem incrementFinVector_contDiff (r : ℕ) (lo hi : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) :
    ContDiff ℝ ⊤ (incrementFinVector r lo hi T y m) :=
  contDiff_pi.mpr fun _ => RoughRegime.PolynomialDerivatives.polynomial_contDiff _

theorem paper_inverse_vector_derivative_bound (r : ℕ) [NeZero r]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (η : ℝ) (hρη : intervalRho lo hi < η) (hη1 : η < 1)
    (χ : ℝ) (hχ : 0 < χ) (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (hy : |y| ≤ Y)
    (c : InverseDerivativeCenter r lo hi χ L) (m k : ℕ)
    (v : Fin k → Fin (Fintype.card (incrementVariables r)) → ℝ) :
    ‖iteratedFDeriv ℝ k (incrementFinVector r lo hi T y m)
      (fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j)) v‖ ≤
      similarIncrementEnvelope r lo hi (intervalRho lo hi / η) χ L Y T * (k.factorial : ℝ) *
        inverseDerivativeRate r lo hi η χ ^ k * ∏ j, ‖v j‖ := by
  have hρ := intervalRho_pos lo hi hlo hlt
  have hη : 0 < η := hρ.trans hρη
  let q := intervalRho lo hi / η
  have hq : 0 < q := div_pos hρ hη
  have hq1 : q < 1 := (div_lt_one hη).mpr hρη
  have hrad := similarInverseCoordinateRadius_pos r lo hi η χ hη hη1 hχ
  have hRate := inverseDerivativeRate_pos r lo hi η χ hη hη1 hχ
  have hM_nn : 0 ≤ similarIncrementEnvelope r lo hi q χ L Y T := by
    unfold similarIncrementEnvelope polynomialCoordinateBound
    exact mul_nonneg (mul_nonneg (by positivity) (tsum_nonneg fun _ => by positivity))
      (Finset.sum_nonneg fun _ _ => add_nonneg (by positivity) (mul_nonneg hY (by positivity)))
  -- Complexified charts indexed by `parent : Bool`
  let z₀ : incrementVariables r → ℂ := fun j => (c.moments j : ℂ)
  have hz₀ : ‖z₀‖ ≤ L := (pi_norm_le_iff_of_nonneg hL).mpr fun j =>
    (show ‖z₀ j‖ ≤ ‖c.moments‖ by simpa [z₀] using norm_le_pi_norm c.moments j).trans c.normBound
  let chartC (parent : Bool) : (Matrix (Fin r) (Fin r) ℂ)ˣ :=
    Units.map Complex.ofRealHom.mapMatrix.toMonoidHom (if parent then c.parentChart else c.currentChart)
  have hchart_facts (parent : Bool) :
      ‖(chartC parent : Matrix (Fin r) (Fin r) ℂ)‖ * ‖(↑(chartC parent)⁻¹ : Matrix (Fin r) (Fin r) ℂ)‖ ≤ χ ∧
      (complexMatrixSimilarity (chartC parent)⁻¹ (coordMatrixCLM r parent z₀)).IsHermitian ∧
      spectrum ℝ (complexMatrixSimilarity (chartC parent)⁻¹ (coordMatrixCLM r parent z₀)) ⊆ Set.Icc lo hi := by
    let U := if parent then c.parentChart else c.currentChart
    let M_real := if parent then parentRealCoordinateMatrix r c.moments else currentRealCoordinateMatrix r c.moments
    have hcond : ‖(U : Matrix (Fin r) (Fin r) ℝ)‖ * ‖(↑U⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ := by
      cases parent
      · exact c.currentCondition
      · exact c.parentCondition
    have hH_real : (matrixSimilarity U⁻¹ M_real).IsHermitian := by
      cases parent
      · exact c.currentHermitian
      · exact c.parentHermitian
    have hSp_real : spectrum ℝ (matrixSimilarity U⁻¹ M_real) ⊆ Set.Icc lo hi := by
      cases parent
      · exact c.currentSpectrum
      · exact c.parentSpectrum
    have hU_eq : (chartC parent : Matrix (Fin r) (Fin r) ℂ) = (U : Matrix (Fin r) (Fin r) ℝ).map Complex.ofReal := rfl
    have hUinv_eq : (↑(chartC parent)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = (↑U⁻¹ : Matrix (Fin r) (Fin r) ℝ).map Complex.ofReal := rfl
    have hM_eq : coordMatrixCLM r parent z₀ = M_real.map Complex.ofReal := by
      ext a b; cases parent <;> rfl
    have hsim_eq : complexMatrixSimilarity (chartC parent)⁻¹ (coordMatrixCLM r parent z₀) =
        (matrixSimilarity U⁻¹ M_real).map Complex.ofReal := by
      rw [hM_eq]
      change Complex.ofRealHom.mapMatrix (↑U⁻¹ : Matrix (Fin r) (Fin r) ℝ) * Complex.ofRealHom.mapMatrix M_real *
        Complex.ofRealHom.mapMatrix (U : Matrix (Fin r) (Fin r) ℝ) =
        Complex.ofRealHom.mapMatrix ((↑U⁻¹ : Matrix (Fin r) (Fin r) ℝ) * M_real * (U : Matrix (Fin r) (Fin r) ℝ))
      rw [map_mul, map_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [hU_eq, hUinv_eq, complexify_matrix_norm, complexify_matrix_norm]; exact hcond
    · rw [hsim_eq]; exact hH_real.map _ fun _ => by simp
    · rw [hsim_eq, complexify_matrix_spectrum _ hH_real]; exact hSp_real
  -- Complex neighborhood bound at any `z` with `‖z - z₀‖ < radius`
  have hnbhd (z : incrementVariables r → ℂ)
      (hz : ‖z - z₀‖ < similarInverseCoordinateRadius r lo hi η χ) (i : Fin r) :
      ‖MvPolynomial.eval₂ Complex.ofRealHom z (incrementEntryPolynomial r lo hi T y m i)‖ ≤
        similarIncrementEnvelope r lo hi q χ L Y T := by
    have hpert_op (parent : Bool) :
        χ * ‖normalizeMatrix lo hi (coordMatrixCLM r parent z) - normalizeMatrix lo hi (coordMatrixCLM r parent z₀)‖ ≤
          (4 * perturbationConstant η)⁻¹ := by
      let D := max 1 (|(intervalHalfWidth lo hi)⁻¹| * (‖coordMatrixCLM r false‖ + ‖coordMatrixCLM r true‖))
      have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
      have hz' : ‖z - z₀‖ ≤ (4 * perturbationConstant η)⁻¹ / (χ * D) := hz.le.trans (min_le_right _ _)
      have hsub : normalizeMatrix lo hi (coordMatrixCLM r parent z) - normalizeMatrix lo hi (coordMatrixCLM r parent z₀) =
          (intervalHalfWidth lo hi)⁻¹ • (coordMatrixCLM r parent (z - z₀)) := by
        rw [normalizeMatrix, normalizeMatrix, ← smul_sub, sub_sub_sub_cancel_right, ← map_sub]
      have hF_le : ‖coordMatrixCLM r parent‖ ≤ ‖coordMatrixCLM r false‖ + ‖coordMatrixCLM r true‖ := by
        cases parent
        · exact le_add_of_nonneg_right (norm_nonneg _)
        · exact le_add_of_nonneg_left (norm_nonneg _)
      rw [hsub, norm_smul, Real.norm_eq_abs]
      have hc_le : |(intervalHalfWidth lo hi)⁻¹| * ‖coordMatrixCLM r parent‖ ≤ D :=
        (mul_le_mul_of_nonneg_left hF_le (abs_nonneg _)).trans (le_max_right _ _)
      calc χ * (|(intervalHalfWidth lo hi)⁻¹| * ‖coordMatrixCLM r parent (z - z₀)‖)
        _ ≤ χ * (|(intervalHalfWidth lo hi)⁻¹| * (‖coordMatrixCLM r parent‖ * ‖z - z₀‖)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((coordMatrixCLM r parent).le_opNorm _) (abs_nonneg _)) hχ.le
        _ ≤ (χ * D) * ‖z - z₀‖ := by
            nlinarith [mul_le_mul_of_nonneg_right hc_le (mul_nonneg hχ.le (norm_nonneg (z - z₀)))]
        _ ≤ (4 * perturbationConstant η)⁻¹ := by simpa only [mul_comm] using (le_div_iff₀ (mul_pos hχ hD)).mp hz'
    have hcoeff_bd (parent : Bool) (a b : Fin r) (t : ℕ) :
        ‖PowerSeries.coeff t (anyKernelSeries lo hi (coordMatrixCLM r parent z) a b)‖ ≤ (4 * χ) * q ^ t := by
      obtain ⟨hQc, hQH, hQSp⟩ := hchart_facts parent
      exact similar_complex_kernel_entry_bound lo hi hlo hlt _ _ (chartC parent) χ hχ.le hQc hQH hQSp η hη hη1 (hpert_op parent) a b t
    -- Truncated `K i j * L.det` bound
    have hinv_bd (j : Fin r) :
        ‖MvPolynomial.eval₂ Complex.ofRealHom z (MvPolynomial.rename Sum.inl (parentInverseEntryPolynomial lo hi r m i j))‖ ≤
          |(intervalGeometricMean lo hi ^ (r + 1))⁻¹| * ((Fintype.card (Equiv.Perm (Fin r)) : ℝ) * (4 * χ) ^ (r + 1)) *
            ∑' t : ℕ, ((t + 1 : ℕ) : ℝ) ^ (r + 1) * q ^ t := by
      have hz_inl : z ∘ Sum.inl = parentValuation (coordMatrixCLM r false z) (coordMatrixCLM r true z) := by
        funext w; rcases w with ij | ⟨t, ij⟩
        · rfl
        · rw [Subsingleton.elim t 0]; rfl
      rw [MvPolynomial.eval₂_rename, hz_inl]
      have hev := parentInverseEntryPolynomial_eval₂ (S := ℂ) lo hi (coordMatrixCLM r false z) (coordMatrixCLM r true z) i j m
      change ‖MvPolynomial.eval₂ (algebraMap ℝ ℂ) _ _‖ ≤ _
      rw [hev, norm_mul, show algebraMap ℝ ℂ ((intervalGeometricMean lo hi ^ (r + 1))⁻¹) =
        (((intervalGeometricMean lo hi ^ (r + 1))⁻¹ : ℝ) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs]
      refine (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)).trans_eq (mul_assoc _ _ _).symm
      let L_ser := anyKernelSeries lo hi (coordMatrixCLM r true z)
      have hdet_bd (t : ℕ) : ‖PowerSeries.coeff t L_ser.det‖ ≤
          (Fintype.card (Equiv.Perm (Fin r)) : ℝ) * (4 * χ) ^ r * ((t + 1 : ℕ) : ℝ) ^ r * q ^ t := by
        rw [Matrix.det_apply, map_sum]
        refine (norm_sum_le _ _).trans
          ((Finset.sum_le_sum (g := fun _ => (4 * χ) ^ r * ((t + 1 : ℕ) : ℝ) ^ r * q ^ t) fun σ _ => ?_).trans_eq
            (by simp [mul_assoc]))
        have hsign : ‖PowerSeries.coeff t (Equiv.Perm.sign σ • ∏ a, L_ser (σ a) a)‖ =
            ‖PowerSeries.coeff t (∏ a, L_ser (σ a) a)‖ := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs, Units.smul_def]
        rw [hsign]
        simpa using powerSeries_prod_geometric_bound Finset.univ (fun a => L_ser (σ a) a) q (4 * χ)
          hq (by positivity) (fun a _ => hcoeff_bd true (σ a) a) t
      let A_c : ℝ := (Fintype.card (Equiv.Perm (Fin r)) : ℝ) * (4 * χ) ^ (r + 1)
      have hKL_bd (t : ℕ) : ‖PowerSeries.coeff t (anyKernelSeries lo hi (coordMatrixCLM r false z) i j * L_ser.det)‖ ≤
          A_c * ((t + 1 : ℕ) : ℝ) ^ (r + 1) * q ^ t := by
        rw [mul_comm, PowerSeries.coeff_mul]
        simpa [A_c, pow_succ, mul_assoc] using convolution_coefficient_bound
          (fun s => PowerSeries.coeff s L_ser.det)
          (fun s => PowerSeries.coeff s (anyKernelSeries lo hi (coordMatrixCLM r false z) i j))
          r t q ((Fintype.card (Equiv.Perm (Fin r)) : ℝ) * (4 * χ) ^ r) (4 * χ) hq (by positivity) (by positivity)
          hdet_bd (hcoeff_bd false i j)
      have hs := (weighted_geometric_summable (r + 1) q hq hq1).mul_left A_c
      exact ((norm_sum_le _ _).trans
        ((Finset.sum_le_sum (g := fun t => A_c * (((t + 1 : ℕ) : ℝ) ^ (r + 1) * q ^ t)) fun t _ =>
          by simpa only [mul_assoc] using hKL_bd t).trans
          (hs.sum_le_tsum (Finset.range (m + 1)) fun _ _ => by dsimp [A_c]; positivity))).trans_eq
        (tsum_mul_left ..)
    -- Numerator coordinate bound on `‖z j‖ ≤ L + 1`
    have hzR (j : incrementVariables r) : ‖z j‖ ≤ L + 1 :=
      (norm_le_pi_norm z j).trans ((norm_le_norm_sub_add z z₀).trans
        ((add_le_add (hz.le.trans (min_le_left _ _)) hz₀).trans_eq (add_comm _ _)))
    have hpoly_bd (P : MvPolynomial (incrementVariables r) ℝ) :
        ‖MvPolynomial.eval₂ Complex.ofRealHom z P‖ ≤ polynomialCoordinateBound P (L + 1) := by
      rw [MvPolynomial.eval₂_eq']
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
      rw [norm_mul, norm_prod, show ‖Complex.ofRealHom (P.coeff α)‖ = ‖P.coeff α‖ from Complex.norm_real _]
      refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_) (norm_nonneg _)
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hzR j) _
    have hnum_bd (j : Fin r) : ‖MvPolynomial.eval₂ Complex.ofRealHom z (numeratorPolynomial r T y j)‖ ≤
        polynomialCoordinateBound (rawNumeratorPolynomial r T false j) (L + 1) +
          Y * polynomialCoordinateBound (rawNumeratorPolynomial r T true j) (L + 1) := by
      simp only [numeratorPolynomial, eval₂_sub, eval₂_mul, eval₂_C]
      refine (norm_sub_le _ _).trans (add_le_add (hpoly_bd _) ?_)
      rw [norm_mul, show ‖Complex.ofRealHom y‖ = |y| by change ‖(y : ℂ)‖ = |y|; rw [Complex.norm_real, Real.norm_eq_abs]]
      exact mul_le_mul hy (hpoly_bd _) (norm_nonneg _) hY
    simp only [incrementEntryPolynomial, eval₂_sum, eval₂_mul, similarIncrementEnvelope, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (hinv_bd j) (hnum_bd j) (norm_nonneg _)
      (mul_nonneg (by positivity) (tsum_nonneg fun _ => by positivity))
  -- Coordinatewise Cauchy derivative bound
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  let uFin := fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j)
  have hd := (ContinuousLinearMap.proj i : (Fin r → ℝ) →L[ℝ] ℝ).iteratedFDeriv_comp_left (x := uFin)
    (incrementFinVector_contDiff r lo hi T y m).contDiffAt (show (k : WithTop ℕ∞) ≤ ⊤ from le_top)
  have he := congrArg (fun D => D v) hd
  change iteratedFDeriv ℝ k (fun x => MvPolynomial.eval x (incrementFinPolynomial r lo hi T y m i)) uFin v =
    (iteratedFDeriv ℝ k (incrementFinVector r lo hi T y m) uFin v) i at he
  rw [← he]
  cases k with
  | zero =>
    simp only [iteratedFDeriv_zero_apply, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one,
      Fin.prod_univ_zero, incrementFinPolynomial, eval_rename]
    have hu_eq : uFin ∘ Fintype.equivFin (incrementVariables r) = c.moments := by funext j; simp [uFin]
    rw [hu_eq]
    have hc := hnbhd z₀ (by simpa using hrad) i
    rwa [show MvPolynomial.eval₂ Complex.ofRealHom z₀ (incrementEntryPolynomial r lo hi T y m i) =
      (MvPolynomial.eval c.moments (incrementEntryPolynomial r lo hi T y m i) : ℂ) from
        (MvPolynomial.eval₂_comp Complex.ofRealHom c.moments _).symm, Complex.norm_real] at hc
  | succ k =>
    refine real_polynomial_derivative_bound _ uFin _ _ hrad (fun z hz => ?_) (by omega) v
    rw [complexify, MvPolynomial.eval_map, incrementFinPolynomial, MvPolynomial.eval₂_rename]
    refine hnbhd (z ∘ Fintype.equivFin (incrementVariables r)) ?_ i
    have heq_sub : z ∘ Fintype.equivFin (incrementVariables r) - z₀ =
        (z - fun j => (uFin j : ℂ)) ∘ Fintype.equivFin (incrementVariables r) := by funext j; simp [z₀, uFin]
    rw [heq_sub]
    exact ((pi_norm_le_iff_of_nonneg (norm_nonneg (z - fun j => (uFin j : ℂ)))).mpr
      fun j => norm_le_pi_norm _ _).trans_lt hz

end NearlyMinimax
