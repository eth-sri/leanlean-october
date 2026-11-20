module

public import NearlyMinimax.FactorialSeriesTail

public import NearlyMinimax.FiniteBounds

public import NearlyMinimax.LowSmoothness

@[expose] public section

/-! # Product Taylor estimates and small-count energy

Analytic and counting estimates for the low-smoothness score. Bounds on
individual response probabilities and their derivatives are propagated
through the actual product likelihood; no score-energy bound is assumed.
-/

namespace NearlyMinimax

noncomputable section

/-- First derivative of a finite product, in the product-rule representation. -/
def finiteProductFirst {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q d : ι → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ s, (∏ j ∈ s.erase i, q j z) * d i z

/-- Second derivative obtained by differentiating that product rule. -/
def finiteProductSecond {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q d e : ι → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ s, (finiteProductFirst (s.erase i) q d z * d i z +
    (∏ j ∈ s.erase i, q j z) * e i z)

section
variable {ι : Type*}

section
variable [DecidableEq ι] (s : Finset ι)

/-- This is the actual first derivative, rather than just a formal expression. -/
theorem finite_product_hasDerivAt
    (q d : ι → ℝ → ℝ) (z : ℝ) (hq : ∀ i ∈ s, HasDerivAt (q i) (d i z) z) :
    HasDerivAt (fun u => ∏ i ∈ s, q i u) (finiteProductFirst s q d z) z := by
  simpa [finiteProductFirst, smul_eq_mul] using HasDerivAt.fun_finset_prod hq

/-- This is the actual derivative of the first product derivative. -/
theorem finite_product_first_hasDerivAt
    (q d e : ι → ℝ → ℝ) (z : ℝ)
    (hq : ∀ i ∈ s, HasDerivAt (q i) (d i z) z)
    (hd : ∀ i ∈ s, HasDerivAt (d i) (e i z) z) :
    HasDerivAt (finiteProductFirst s q d) (finiteProductSecond s q d e z) z := by
  unfold finiteProductFirst finiteProductSecond
  apply HasDerivAt.fun_sum
  intro i hi
  exact (finite_product_hasDerivAt (s.erase i) q d z
    (fun j hj => hq j (Finset.mem_of_mem_erase hj))).mul (hd i hi)

/-- Product derivative bound, including the dependence on the number of factors. -/
theorem finite_product_first_abs_bound
    (q d : ι → ℝ → ℝ) (z B : ℝ)
    (hq : ∀ i ∈ s, |q i z| ≤ 1) (hd : ∀ i ∈ s, |d i z| ≤ B) :
    |finiteProductFirst s q d z| ≤ s.card * B := by
  apply abs_sum_le_card_mul
  intro i hi
  have hp : |∏ j ∈ s.erase i, q j z| ≤ 1 := abs_prod_le_one fun j hj => hq j (Finset.mem_of_mem_erase hj)
  rw [abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) hp).trans (hd i hi)

/-- A second product derivative has at most a quadratic factor-count cost. -/
theorem finite_product_second_abs_bound
    (q d e : ι → ℝ → ℝ) (z B1 B2 : ℝ) (hB1 : 0 ≤ B1)
    (hq : ∀ i ∈ s, |q i z| ≤ 1) (hd : ∀ i ∈ s, |d i z| ≤ B1)
    (he : ∀ i ∈ s, |e i z| ≤ B2) :
    |finiteProductSecond s q d e z| ≤ s.card * (s.card * B1 ^ 2 + B2) := by
  apply abs_sum_le_card_mul
  intro i hi
  have hfirst := finite_product_first_abs_bound (s.erase i) q d z B1
    (fun j hj => hq j (Finset.mem_of_mem_erase hj)) (fun j hj => hd j (Finset.mem_of_mem_erase hj))
  have hcard : ((s.erase i).card : ℝ) ≤ s.card := by gcongr; exact Finset.erase_subset i s
  have hp : |∏ j ∈ s.erase i, q j z| ≤ 1 := abs_prod_le_one fun j hj => hq j (Finset.mem_of_mem_erase hj)
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, pow_two, ← mul_assoc]
  exact add_le_add (mul_le_mul (hfirst.trans (by gcongr)) (hd i hi) (abs_nonneg _) (by positivity))
    ((mul_le_of_le_one_left (abs_nonneg _) hp).trans (he i hi))

end

end

/-- A bound on the second derivative controls the affine remainder on a convex subset of `[-1,1]`. -/
theorem affine_remainder_abs_bound {s : Set ℝ} (hs : Convex ℝ s) (hzero : 0 ∈ s)
    (hunit : ∀ z ∈ s, |z| ≤ 1) (H D E : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ z ∈ s, HasDerivAt H (D z) z)
    (hD : ∀ z ∈ s, HasDerivAt D (E z) z)
    (hE : ∀ z ∈ s, |E z| ≤ B) (z : ℝ) (hz : z ∈ s) : |H z - H 0 - z * D 0| ≤ B := by
  have dev {F F' : ℝ → ℝ} (hF : ∀ z ∈ s, HasDerivAt F (F' z) z)
      (hb : ∀ z ∈ s, |F' z| ≤ B) (z : ℝ) (hz : z ∈ s) : |F z - F 0| ≤ B := by
    have h := hs.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hF x hx).hasDerivWithinAt) (by simpa using hb) hzero hz
    simpa using h.trans (mul_le_of_le_one_right hB (by simpa using hunit z hz))
  have h := dev (F := fun t => H t - H 0 - t * D 0)
    (fun t ht => (((hH t ht).sub_const _).sub ((hasDerivAt_id t).mul_const _)).congr_deriv
      (by simp)) (dev hD hE) z hz
  simpa using h

theorem symmetric_difference_abs_bound (H D E : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ z ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt H (D z) z)
    (hD : ∀ z ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt D (E z) z)
    (hE : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |E z| ≤ B) :
    |symmetricDifference H| ≤ B := by
  have h := affine_remainder_abs_bound (convex_Icc (-1 : ℝ) 1) (by norm_num)
    (fun _ hz => abs_le.mpr hz) H D E B hB hH hD hE
  have hp := abs_le.mp (h 1 (by norm_num))
  grind [symmetricDifference.eq_1]

section
variable {n : ℕ} (a V : ℝ) (f δ : Fin n → ℝ) (y : Fin n → Fin 3)

/-- The common affine response line for the two likelihood constructions. -/
def ternaryLineMass (i : Fin n) (z : ℝ) : ℝ := ternaryMass a (f i + z * δ i) V (y i)

def ternaryLineFirst (i : Fin n) (z : ℝ) : ℝ :=
  δ i * ternaryMeanDerivative a (f i + z * δ i) (y i)

def ternaryLineSecond (i : Fin n) (_z : ℝ) : ℝ :=
  (δ i)^2 * ternaryMeanSecondDerivative a (y i)

def ternaryProductFirst := finiteProductFirst Finset.univ (ternaryLineMass a V f δ y)
  (ternaryLineFirst a f δ y)

def ternaryProductSecond := finiteProductSecond Finset.univ (ternaryLineMass a V f δ y)
  (ternaryLineFirst a f δ y) (ternaryLineSecond a δ y)

section
variable (z : ℝ)

theorem ternary_product_hasDerivAt :
    HasDerivAt (fun u => ∏ i, ternaryLineMass a V f δ y i u) (ternaryProductFirst a V f δ y z) z :=
  finite_product_hasDerivAt _ _ _ z (fun i _ => ternary_hasDerivAt_line a (f i) V (δ i) z (y i))

theorem ternary_product_first_hasDerivAt :
    HasDerivAt (ternaryProductFirst a V f δ y) (ternaryProductSecond a V f δ y z) z :=
  finite_product_first_hasDerivAt _ _ _ _ z
    (fun i _ => ternary_hasDerivAt_line a (f i) V (δ i) z (y i))
    (fun i _ => ternary_hasDerivAt_line_first a (f i) (δ i) z (y i))

end

/-- Uniform bounds on the factors and their derivatives control the product's curvature. -/
theorem ternary_product_second_abs_bound (z B M N : ℝ)
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hN : 0 ≤ N) (hδ : ∀ i, |δ i| ≤ B)
    (hq : ∀ i, |ternaryLineMass a V f δ y i z| ≤ 1)
    (hfirst : ∀ i, |ternaryMeanDerivative a (f i + z * δ i) (y i)| ≤ M)
    (hsecond : ∀ i, |ternaryMeanSecondDerivative a (y i)| ≤ N) :
    |ternaryProductSecond a V f δ y z| ≤ ((n : ℝ)^2 * M^2 + n * N) * B^2 := by
  have hd (i : Fin n) : |ternaryLineFirst a f δ y i z| ≤ B * M := by
    rw [ternaryLineFirst, abs_mul]
    exact mul_le_mul (hδ i) (hfirst i) (abs_nonneg _) hB
  have he (i : Fin n) : |ternaryLineSecond a δ y i z| ≤ B^2 * N := by
    rw [ternaryLineSecond, abs_mul, abs_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hδ i) 2) (hsecond i) (abs_nonneg _) (sq_nonneg _)
  refine (finite_product_second_abs_bound Finset.univ _ _ _ z (B*M) (B^2*N)
    (by positivity) (fun i _ => hq i) (fun i _ => hd i) (fun i _ => he i)).trans_eq ?_
  simp only [Finset.card_univ, Fintype.card_fin]
  ring

end

section
variable (n : ℕ)

/-- The quadratic-in-count Taylor bound for the actual response product. -/
theorem patch_product_symmetric_difference_bound (a V η M N : ℝ)
    (g w : Fin n → ℝ) (y : Fin n → Fin 3) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hw : ∀ i, |w i| ≤ 1)
    (hq : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |ternaryMass a (g i + η * w i * z) V (y i)| ≤ 1)
    (hfirst : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |ternaryMeanDerivative a (g i + η * w i * z) (y i)| ≤ M)
    (hsecond : ∀ i, |ternaryMeanSecondDerivative a (y i)| ≤ N) :
    |symmetricDifference (patchResponseProduct n a V η g w y)| ≤
      ((n : ℝ) ^ 2 * M ^ 2 + n * N) * η ^ 2 := by
  let δ := fun i => η * w i
  have hδ (i : Fin n) : |δ i| ≤ |η| := by
    simpa [δ, abs_mul] using mul_le_mul_of_nonneg_left (hw i) (abs_nonneg η)
  rw [show patchResponseProduct n a V η g w y = fun z => ∏ i, ternaryLineMass a V g δ y i z by
    funext z
    unfold patchResponseProduct
    apply Finset.prod_congr rfl
    intro i _
    rw [ternaryLineMass, mul_comm z]]
  apply symmetric_difference_abs_bound _ (ternaryProductFirst a V g δ y) (ternaryProductSecond a V g δ y) _
    (by positivity) (fun z _ => ternary_product_hasDerivAt a V g δ y z)
    (fun z _ => ternary_product_first_hasDerivAt a V g δ y z)
  intro z hz
  rw [← sq_abs η]
  exact ternary_product_second_abs_bound a V g δ y z |η| M N (abs_nonneg _) hM hN hδ
    (by simpa [ternaryLineMass, δ, mul_comm] using hq z hz)
    (by simpa [δ, mul_comm] using hfirst z hz) hsecond

/-- The variance correction grows at most linearly in the patch count. -/
theorem patch_variance_correction_abs_bound (a V η z B : ℝ)
    (g w : Fin n → ℝ) (y : Fin n → Fin 3) (hw : ∀ i, |w i| ≤ 1)
    (hq : ∀ i, |ternaryMass a (g i + η * w i * z) V (y i)| ≤ 1)
    (hvariance : ∀ i, |ternaryVarianceDerivative a (y i)| ≤ B) :
    |∑ i, (w i) ^ 2 * patchVarianceTerm n a V η g w y z i| ≤ n * B := by
  apply (abs_sum_le_card_mul (B := B) (s := Finset.univ) ?_).trans_eq (by simp)
  intro i _
  unfold patchVarianceTerm
  rw [abs_mul, abs_mul, abs_pow]
  have hwi : |w i| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) (hw i)
  have hprod : |∏ k ∈ (Finset.univ : Finset (Fin n)).erase i,
      ternaryMass a (g k + η * w k * z) V (y k)| ≤ 1 := abs_prod_le_one fun k _ => hq k
  exact (mul_le_of_le_one_left (by positivity) hwi).trans
    ((mul_le_of_le_one_right (abs_nonneg _) hprod).trans (hvariance i))

/-- The actual score numerator has the paper's `k^2*eta^2` bound, with
constants determined by individual response derivative bounds. -/
theorem patch_score_numerator_abs_bound (a V η z M N B : ℝ)
    (g w : Fin n → ℝ) (y : Fin n → Fin 3) (hn : 1 ≤ n)
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) (hM : 0 ≤ M) (hN : 0 ≤ N) (hB : 0 ≤ B)
    (hw : ∀ i, |w i| ≤ 1)
    (hq : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |ternaryMass a (g i + η * w i * u) V (y i)| ≤ 1)
    (hfirst : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |ternaryMeanDerivative a (g i + η * w i * u) (y i)| ≤ M)
    (hsecond : ∀ i, |ternaryMeanSecondDerivative a (y i)| ≤ N)
    (hvariance : ∀ i, |ternaryVarianceDerivative a (y i)| ≤ B) :
    |patchScoreNumerator n a V η g w y z| ≤
      (M ^ 2 + N + B) * (n : ℝ) ^ 2 * η ^ 2 := by
  have hD := patch_product_symmetric_difference_bound n a V η M N g w y hM hN
    hw hq hfirst hsecond
  have hV := patch_variance_correction_abs_bound n a V η z B g w y hw (hq z hz) hvariance
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hNB : (n : ℝ) * (N + B) ≤ (n : ℝ) ^ 2 * (N + B) :=
    mul_le_mul_of_nonneg_right hnn (by positivity)
  have htriangle : |patchScoreNumerator n a V η g w y z| ≤
      |symmetricDifference (patchResponseProduct n a V η g w y)| +
        η ^ 2 * |∑ i, (w i) ^ 2 * patchVarianceTerm n a V η g w y z i| := by
    unfold patchScoreNumerator
    have h := abs_sub_le (symmetricDifference (patchResponseProduct n a V η g w y)) 0
      (η ^ 2 * ∑ i, (w i) ^ 2 * patchVarianceTerm n a V η g w y z i)
    simpa [sub_zero, zero_sub, abs_neg, abs_mul, abs_pow, sq_abs] using h
  calc
    _ ≤ |symmetricDifference (patchResponseProduct n a V η g w y)| +
        η ^ 2 * |∑ i, (w i) ^ 2 * patchVarianceTerm n a V η g w y z i| := htriangle
    _ ≤ ((n : ℝ) ^ 2 * M ^ 2 + n * N) * η ^ 2 + η ^ 2 * (n * B) :=
      add_le_add hD (mul_le_mul_of_nonneg_left hV (sq_nonneg η))
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hNB (sq_nonneg η)]

/-- A uniform positive mass bound propagates to the actual product denominator. -/
theorem patch_response_lower_bound (a V η z c : ℝ)
    (g w : Fin n → ℝ) (y : Fin n → Fin 3) (hc : 0 ≤ c)
    (hq : ∀ i, c ≤ ternaryMass a (g i + η * w i * z) V (y i)) :
    c ^ n ≤ patchResponseProduct n a V η g w y z := by
  calc
    _ = ∏ _i : Fin n, c := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hc) (fun i _ => hq i)

/-- Explicit score-square bound for `n` observations in the patch. It displays
both the polynomial count factor and the exponential likelihood denominator. -/
theorem patch_score_square_bound (a V η z M N B c : ℝ)
    (g w : Fin n → ℝ) (y : Fin n → Fin 3) (hn : 1 ≤ n)
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) (hM : 0 ≤ M) (hN : 0 ≤ N) (hB : 0 ≤ B) (hc : 0 < c)
    (hw : ∀ i, |w i| ≤ 1)
    (hq : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |ternaryMass a (g i + η * w i * u) V (y i)| ≤ 1)
    (hfirst : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |ternaryMeanDerivative a (g i + η * w i * u) (y i)| ≤ M)
    (hsecond : ∀ i, |ternaryMeanSecondDerivative a (y i)| ≤ N)
    (hvariance : ∀ i, |ternaryVarianceDerivative a (y i)| ≤ B)
    (hlower : ∀ i, c ≤ ternaryMass a (g i + η * w i * z) V (y i)) :
    (patchObservableScore n a V η g w y z) ^ 2 ≤
      (M ^ 2 + N + B) ^ 2 * (n : ℝ) ^ 4 * η ^ 4 / c ^ (2 * n) := by
  have hnum := patch_score_numerator_abs_bound n a V η z M N B g w y hn hz hM hN hB
    hw hq hfirst hsecond hvariance
  have hden := patch_response_lower_bound n a V η z c g w y hc.le hlower
  have hcp := pow_pos hc n
  have hL := hcp.trans_le hden
  have hscore : |patchObservableScore n a V η g w y z| ≤
      (M ^ 2 + N + B) * (n : ℝ) ^ 2 * η ^ 2 / c ^ n := by
    unfold patchObservableScore
    rw [abs_div, abs_of_pos hL]
    exact div_le_div₀ (by positivity) hnum hcp hden
  have hs := mul_self_le_mul_self (abs_nonneg _) hscore
  rw [← sq, sq_abs] at hs
  convert hs using 1
  ring

/-- Polynomial count growth can be absorbed into a fixed exponential. -/
theorem fourth_power_count_le_exponential : (n : ℝ) ^ 4 ≤ (16 : ℝ) ^ n := by
  have hn : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have h := pow_le_pow_left₀ (Nat.cast_nonneg n) hn 4
  calc
    _ ≤ ((2 : ℝ) ^ n) ^ 4 := h
    _ = (16 : ℝ) ^ n := by rw [← pow_mul, Nat.mul_comm n 4, pow_mul]; norm_num

/-- The precise polynomial/denominator score bound implies the `C^k*eta^4`
bound used in the paper, with an explicit constant depending only on `K,c`. -/
theorem score_bound_exponential_absorption (K c η r : ℝ) (hn : 1 ≤ n) (hc : 0 < c)
    (hr : r ^ 2 ≤ K ^ 2 * (n : ℝ) ^ 4 * η ^ 4 / c ^ (2 * n)) :
    r ^ 2 ≤ (16 * max 1 (K ^ 2) / c ^ 2) ^ n * η ^ 4 := by
  have hK := by
    exact (le_max_right 1 (K ^ 2)).trans (by
      simpa using pow_le_pow_right₀ (le_max_left 1 (K ^ 2)) hn)
  have hn4 := fourth_power_count_le_exponential n
  have hnum : K ^ 2 * (n : ℝ) ^ 4 * η ^ 4 ≤
      (max 1 (K ^ 2)) ^ n * (16 : ℝ) ^ n * η ^ 4 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hK hn4 (by positivity) (by positivity)) (by positivity)
  calc
    _ ≤ K ^ 2 * (n : ℝ) ^ 4 * η ^ 4 / c ^ (2 * n) := hr
    _ ≤ (max 1 (K ^ 2)) ^ n * (16 : ℝ) ^ n * η ^ 4 / c ^ (2 * n) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = _ := by ring

end

/-- Finite exponential-series tail from order two, uniformly in its cutoff. -/
theorem finite_exponential_tail_bound (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2), if 2 ≤ k then x ^ k / (k.factorial : ℝ) else 0) ≤
      x ^ 2 * Real.exp x := by
  rw [Nat.add_comm n 2, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]
  exact (finite_poissonCountWeight_tail_le hx 2 n).trans (by
    rw [poissonCountWeight, mul_comm (Real.exp x)]
    gcongr
    norm_num [Nat.factorial]
    nlinarith [sq_nonneg x])

/-- The binomial count law, represented by its actual finite masses. -/
def binomialCountMass (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

section
variable (n : ℕ)

theorem binomial_count_mass_nonnegative (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ binomialCountMass n p k := by
  unfold binomialCountMass
  positivity

/-- Weighted probability of a count at least two has quadratic small-mean
behavior. This is the count-tail bound used for the low-smoothness energy. -/
theorem binomial_count_tail_energy (p C : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hC : 0 ≤ C) (hmean : n * p ≤ 1) :
    (∑ k ∈ Finset.range (n + 1), if 2 ≤ k then binomialCountMass n p k * C ^ k else 0) ≤
      C ^ 2 * Real.exp C * (n * p) ^ 2 := by
  have hx : 0 ≤ C * n * p := by positivity
  have hterm (k : ℕ) : binomialCountMass n p k * C ^ k ≤
      (C * n * p) ^ k / (k.factorial : ℝ) := by
    have hremaining : (1 - p) ^ (n - k) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hchoose := Nat.choose_le_pow_div (α := ℝ) k n
    calc
      _ ≤ ((n.choose k : ℝ) * p ^ k * 1) * C ^ k := by
        unfold binomialCountMass
        gcongr
      _ ≤ (((n : ℝ) ^ k / (k.factorial : ℝ)) * p ^ k * 1) * C ^ k := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), if 2 ≤ k then (C * n * p) ^ k / (k.factorial : ℝ) else 0 := by
      apply Finset.sum_le_sum
      grind
    _ ≤ ∑ k ∈ Finset.range (n + 2), if 2 ≤ k then (C * n * p) ^ k / (k.factorial : ℝ) else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (by intros; positivity)
    _ ≤ (C * n * p) ^ 2 * Real.exp (C * n * p) := finite_exponential_tail_bound _ hx n
    _ ≤ C ^ 2 * Real.exp C * (n * p) ^ 2 := by
      have hexp : Real.exp (C * n * p) ≤ Real.exp C := by
        apply Real.exp_le_exp.mpr
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hexp (sq_nonneg (C * n * p))]

end

/-- Uniform regression-direction derivative bound on an admissible bounded field. -/
theorem ternary_mean_derivative_abs_bound (a f ρ : ℝ) (ha : 0 < a) (hρ : 0 ≤ ρ)
    (hf : |f| ≤ ρ) (y : Fin 3) :
    |ternaryMeanDerivative a f y| ≤ (2 * ρ + a) / a ^ 2 := by
  have ha2 := sq_pos_of_pos ha
  have hA : 0 ≤ 2 * ρ + a := by positivity
  have hm : |2 * f - a| ≤ 2 * ρ + a := by
    grind
  have hp : |2 * f + a| ≤ 2 * ρ + a := by
    grind
  have hhalf : (2 * ρ + a) / (2 * a ^ 2) ≤ (2 * ρ + a) / a ^ 2 :=
    div_le_div₀ hA le_rfl ha2 (by nlinarith)
  fin_cases y
  · change |(2 * f - a) / (2 * a ^ 2)| ≤ _
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * a ^ 2)]
    exact (div_le_div_of_nonneg_right hm (by positivity)).trans hhalf
  · change |-(2 * f) / a ^ 2| ≤ _
    rw [abs_div, abs_neg, abs_mul, abs_of_pos ha2]
    norm_num
    exact div_le_div_of_nonneg_right (by linarith) ha2.le
  · change |(2 * f + a) / (2 * a ^ 2)| ≤ _
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * a ^ 2)]
    exact (div_le_div_of_nonneg_right hp (by positivity)).trans hhalf

section
variable (a : ℝ) (ha : 0 < a) (y : Fin 3)
include ha

/-- Uniform second derivative bound, independent of the regression value. -/
theorem ternary_mean_second_derivative_abs_bound :
    |ternaryMeanSecondDerivative a y| ≤ 2 / a ^ 2 := by
  have ha2 := sq_pos_of_pos ha
  fin_cases y
  · change |1 / a ^ 2| ≤ _
    simpa using div_le_div_of_nonneg_right (show (1 : ℝ) ≤ 2 by norm_num) ha2.le
  · change |-2 / a ^ 2| ≤ _
    simp [abs_div, abs_of_pos ha2]
  · change |1 / a ^ 2| ≤ _
    simpa using div_le_div_of_nonneg_right (show (1 : ℝ) ≤ 2 by norm_num) ha2.le

/-- Uniform variance derivative bound. -/
theorem ternary_variance_derivative_abs_bound :
    |ternaryVarianceDerivative a y| ≤ 1 / a ^ 2 := by
  have h := ternary_mean_second_derivative_abs_bound a ha y
  rw [ternary_heat_identity, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
  rw [show 2 / a ^ 2 = 2 * (1 / a ^ 2) by ring] at h
  linarith

end

/-- Response-averaged squared observable patch score. -/
def patchExpectedScoreEnergy (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ) (z : ℝ) : ℝ :=
  ∑ y : Fin n → Fin 3,
    patchResponseProduct n a V η g w y z * (patchObservableScore n a V η g w y z) ^ 2

/-- An explicit exponential constant for the admissible ternary score bound. -/
def ternaryScoreExponentialConstant (a ρ c : ℝ) : ℝ :=
  16 * max 1 ((((2 * ρ + a) / a ^ 2) ^ 2 + 3 / a ^ 2) ^ 2) / c ^ 2

/-- The binomial count-tail bound integrates any countwise exponential energy
bound that vanishes at counts zero and one. -/
theorem binomial_collision_energy_bound (n : ℕ) (p C η : ℝ) (e : ℕ → ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hC : 0 ≤ C) (hmean : n * p ≤ 1)
    (he0 : e 0 = 0) (he1 : e 1 = 0)
    (he : ∀ k, 2 ≤ k → e k ≤ C ^ k * η ^ 4) :
    (∑ k ∈ Finset.range (n + 1), binomialCountMass n p k * e k) ≤
      C ^ 2 * Real.exp C * η ^ 4 * (n * p) ^ 2 := by
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        if 2 ≤ k then binomialCountMass n p k * (C ^ k * η ^ 4) else 0 := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : 2 ≤ k
      · rw [if_pos hk]
        exact mul_le_mul_of_nonneg_left (he k hk) (binomial_count_mass_nonnegative n p hp hp1 k)
      · rw [if_neg hk]
        have hk' : k = 0 ∨ k = 1 := by omega
        rcases hk' with rfl | rfl <;> simp [he0, he1]
    _ = η ^ 4 * (∑ k ∈ Finset.range (n + 1),
        if 2 ≤ k then binomialCountMass n p k * C ^ k else 0) := by
      rw [Finset.mul_sum]
      grind
    _ ≤ η ^ 4 * (C ^ 2 * Real.exp C * (n * p) ^ 2) :=
      mul_le_mul_of_nonneg_left (binomial_count_tail_energy n p C hp hp1 hC hmean) (by positivity)
    _ = _ := by ring

end

end NearlyMinimax
