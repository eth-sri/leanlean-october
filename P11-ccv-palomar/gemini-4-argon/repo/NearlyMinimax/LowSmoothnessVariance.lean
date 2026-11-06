module
public import NearlyMinimax.Ternary
@[expose] public section
noncomputable section
namespace NearlyMinimax
def activationPriorMass (t : ℝ) : Fin 3 → ℝ := ![t / 2, 1 - t, t / 2]
def activationPriorDerivative : Fin 3 → ℝ := ![1 / 2 , -1, 1 / 2]
theorem activation_prior_normalized (t ) : ∑ y, activationPriorMass t y = 1 := by
  simp [Fin.sum_univ_succ, activationPriorMass]
  ring
theorem activation_prior_nonnegative (t ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ y, 0 ≤ activationPriorMass t y := by
  intro y
  fin_cases y <;> simp [activationPriorMass] <;> linarith
theorem activation_prior_hasDerivAt (t y) :
    HasDerivAt (fun u => activationPriorMass u y) (activationPriorDerivative y) t := by
  fin_cases y
  · exact (hasDerivAt_id t).div_const 2
  · change HasDerivAt (fun u => 1 - u) (-1) t
    exact ((hasDerivAt_const t 1).sub (hasDerivAt_id t)).congr_deriv (by norm_num)
  · exact (hasDerivAt_id t).div_const 2
def activationProductPrior (m ) (t : ℝ) (ξ : Fin m → Fin 3) : ℝ :=
  ∏ j, activationPriorMass t (ξ j)
def activationProductPriorDerivative (m ) (t : ℝ) (ξ : Fin m → Fin 3) : ℝ :=
  ∑ j, activationPriorDerivative (ξ j) *
    ∏ k ∈ (Finset.univ : Finset (Fin m)).erase j, activationPriorMass t (ξ k)
theorem activation_product_prior_normalized (m t) :
    ∑ ξ, activationProductPrior m t ξ = 1 := by
  unfold activationProductPrior
  rw [← Fintype.prod_sum]
  simp [activation_prior_normalized]
theorem activation_product_prior_hasDerivAt (m t ξ) :
    HasDerivAt (fun u => activationProductPrior m u ξ)
      (activationProductPriorDerivative m t ξ) t := by
  have h := HasDerivAt.fun_finset_prod (u := (Finset.univ : Finset (Fin m)))
    (fun j _ => activation_prior_hasDerivAt t (ξ j))
  simpa [activationProductPrior, activationProductPriorDerivative, smul_eq_mul,
    mul_comm] using h
def latentDifference (m ) (j : Fin m) (F : (Fin m → Fin 3) → ℝ)
    (ξ : Fin m → Fin 3) : ℝ :=
  (1 / 2 ) * F (Function.update ξ j 2) +
    (1 / 2 ) * F (Function.update ξ j 0) - F (Function.update ξ j 1)
theorem activation_prior_factor (m t ξ j) :
    activationProductPrior m t ξ = activationPriorMass t (ξ j) *
      ∏ k ∈ (Finset.univ : Finset (Fin m)).erase j, activationPriorMass t (ξ k) := (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
def symmetricDifference (H : ℝ → ℝ) : ℝ :=
  (1 / 2 ) * H 1 + (1 / 2 ) * H (-1) - H 0
def patchResponseProduct (n ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) : ℝ :=
  ∏ i, ternaryMass a (g i + η * w i * z) V (y i)
def patchVarianceTerm (n ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) (i : Fin n) : ℝ :=
  ternaryVarianceDerivative a (y i) *
    ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i,
      ternaryMass a (g k + η * w k * z) V (y k)
def patchScoreNumerator (n ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) : ℝ :=
  symmetricDifference (patchResponseProduct n a V η g w y) -
    η ^ 2 * ∑ i, (w i) ^ 2 * patchVarianceTerm n a V η g w y z i
def patchObservableScore (n ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) : ℝ :=
  patchScoreNumerator n a V η g w y z / patchResponseProduct n a V η g w y z
theorem patch_response_normalized (n a V η g w z) (ha : a ≠ 0) :
    ∑ y, patchResponseProduct n a V η g w y z = 1 := by
  unfold patchResponseProduct
  rw [← Fintype.prod_sum]
  simp [ternary_normalized a _ V ha]
theorem patch_score_cancel_zero (n a V η g w y z) (hw : ∀ i, w i = 0) :
    patchScoreNumerator n a V η g w y z = 0 := by
  simp [patchScoreNumerator, symmetricDifference, patchResponseProduct, hw]
  ring
theorem patch_variance_term_sum_zero (n a V η g w z i) :
    ∑ y : Fin n → Fin 3, patchVarianceTerm n a V η g w y z i = 0 := by
  have h_patch_variance_term_eq_product (y) (z) (i) : patchVarianceTerm n a V η g w y z i =
      ∏ k : Fin n, if k = i then ternaryVarianceDerivative a (y k)
        else ternaryMass a (g k + η * w k * z) V (y k) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [ite_true]
    unfold patchVarianceTerm
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    rw [if_neg (Finset.ne_of_mem_erase hk)]
  simp_rw [h_patch_variance_term_eq_product]
  rw [← Fintype.prod_sum (fun k (yk : Fin 3) =>
    if k = i then ternaryVarianceDerivative a yk
      else ternaryMass a (g k + η * w k * z) V yk)]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [Fin.sum_univ_succ, ternaryVarianceDerivative]
  ring
def finiteResponseLikelihood (m n ) (a V : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) : ℝ :=
  ∏ i, ternaryMass a (f ξ i) V (y i)
def finiteResponseVarianceTerm (m n ) (a V : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3)
    (y : Fin n → Fin 3) (i : Fin n) : ℝ :=
  ternaryVarianceDerivative a (y i) *
    ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, ternaryMass a (f ξ k) V (y k)
theorem finite_response_variance_hasDerivAt (m n a V f ξ y) :
    HasDerivAt (fun W => finiteResponseLikelihood m n a W f ξ y)
      (∑ i, finiteResponseVarianceTerm m n a V f ξ y i) V := by
  have h := HasDerivAt.fun_finset_prod (u := (Finset.univ : Finset (Fin n)))
    (fun i _ => ternary_hasDerivAt_variance a (f ξ i) V (y i))
  simpa [finiteResponseLikelihood, finiteResponseVarianceTerm, smul_eq_mul,
    mul_comm] using h
def finiteExperimentExpectation (m n ) (a v η t : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (T : (Fin n → Fin 3) → ℝ) : ℝ :=
  ∑ ξ, activationProductPrior m t ξ *
    ∑ y, finiteResponseLikelihood m n a (v - η ^ 2 * t) f ξ y * T y
def finiteExperimentScoreNumerator (m n ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) : ℝ :=
  (∑ j, latentDifference m j (fun ξ' => finiteResponseLikelihood m n a V f ξ' y) ξ) -
    η ^ 2 * ∑ i, finiteResponseVarianceTerm m n a V f ξ y i
def finiteExperimentScore (m n ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) : ℝ :=
  finiteExperimentScoreNumerator m n a V η f ξ y /
    finiteResponseLikelihood m n a V f ξ y
theorem latent_difference_response_sum (m n j)
    (F : (Fin m → Fin 3) → (Fin n → Fin 3) → ℝ) (T : (Fin n → Fin 3) → ℝ)
    (ξ : Fin m → Fin 3) :
    latentDifference m j (fun ξ' => ∑ y, F ξ' y * T y) ξ =
      ∑ y, latentDifference m j (fun ξ' => F ξ' y) ξ * T y := by
  simp [latentDifference, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
theorem finite_response_normalized (m n a V f ξ) (ha : a ≠ 0) :
    ∑ y, finiteResponseLikelihood m n a V f ξ y = 1 := by
  unfold finiteResponseLikelihood
  rw [← Fintype.prod_sum]
  simp [ternary_normalized a _ V ha]
theorem finite_response_variance_term_sum_zero (m n a V f ξ i) :
    ∑ y, finiteResponseVarianceTerm m n a V f ξ y i = 0 := by
  simpa [patchVarianceTerm, finiteResponseVarianceTerm] using
    patch_variance_term_sum_zero n a V 0 (f ξ) (fun _ => 0) 0 i
theorem finite_experiment_score_centered (m n a V η f ξ) (ha : a ≠ 0)
    (hpositive : ∀ y, 0 < finiteResponseLikelihood m n a V f ξ y) :
    ∑ y : Fin n → Fin 3,
      finiteResponseLikelihood m n a V f ξ y * finiteExperimentScore m n a V η f ξ y = 0 := by
  have heq (y : Fin n → Fin 3) :
      finiteResponseLikelihood m n a V f ξ y * finiteExperimentScore m n a V η f ξ y =
        finiteExperimentScoreNumerator m n a V η f ξ y := by
    unfold finiteExperimentScore
    field_simp [ne_of_gt (hpositive y)]
  simp_rw [heq]
  have hD (j : Fin m) :
      ∑ y : Fin n → Fin 3,
        latentDifference m j (fun ξ' => finiteResponseLikelihood m n a V f ξ' y) ξ = 0 := by
    unfold latentDifference
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    simp [finite_response_normalized m n a V f _ ha]
    ring
  unfold finiteExperimentScoreNumerator
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  conv_lhs => lhs; rw [Finset.sum_comm]
  conv_lhs => rhs; arg 2; rw [Finset.sum_comm]
  simp [hD, finite_response_variance_term_sum_zero]
def latentRegression (m n ) (η : ℝ) (base : Fin n → ℝ)
    (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3) (i : Fin n) : ℝ :=
  base i + η * ∑ j, w i j * ternaryValue 1 (ξ j)
def latentRegressionWithout (m n ) (η : ℝ) (base : Fin n → ℝ)
    (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3) (j : Fin m) (i : Fin n) : ℝ :=
  base i + η * ∑ k ∈ (Finset.univ : Finset (Fin m)).erase j, w i k * ternaryValue 1 (ξ k)
theorem latent_regression_update (m n η base w ξ j i z) :
    latentRegression m n η base w (Function.update ξ j z) i =
      latentRegressionWithout m n η base w ξ j i + η * w i j * ternaryValue 1 z := by
  unfold latentRegression latentRegressionWithout
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  have heq : (∑ k ∈ (Finset.univ : Finset (Fin m)).erase j,
      w i k * ternaryValue 1 (Function.update ξ j z k)) =
      ∑ k ∈ (Finset.univ : Finset (Fin m)).erase j, w i k * ternaryValue 1 (ξ k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [heq]
  ring
theorem latent_regression_decomposition (m n η base w ξ j i) :
    latentRegression m n η base w ξ i =
      latentRegressionWithout m n η base w ξ j i + η * w i j * ternaryValue 1 (ξ j) := by
  simpa using latent_regression_update m n η base w ξ j i (ξ j)
def finiteCoordinateScoreNumerator (m n ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (w : Fin n → Fin m → ℝ)
    (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) (j : Fin m) : ℝ :=
  latentDifference m j (fun ξ' => finiteResponseLikelihood m n a V f ξ' y) ξ -
    η ^ 2 * ∑ i, (w i j) ^ 2 * finiteResponseVarianceTerm m n a V f ξ y i
def finiteCoordinateScore (m n ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (w : Fin n → Fin m → ℝ)
    (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) (j : Fin m) : ℝ :=
  finiteCoordinateScoreNumerator m n a V η f w ξ y j / finiteResponseLikelihood m n a V f ξ y
variable {ι : Type*}
def finiteProductFirst  [DecidableEq ι] (s : Finset ι)
    (q d : ι → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ s, (∏ j ∈ s.erase i, q j z) * d i z
def finiteProductSecond  [DecidableEq ι] (s : Finset ι)
    (q d e : ι → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ s, ((∑ j ∈ s.erase i, (∏ k ∈ (s.erase i).erase j, q k z) * d j z) * d i z +
    (∏ j ∈ s.erase i, q j z) * e i z)
theorem finite_product_hasDerivAt  [DecidableEq ι] (s : Finset ι)
    (q d : ι → ℝ → ℝ) (z : ℝ) (hq : ∀ i ∈ s, HasDerivAt (q i) (d i z) z) :
    HasDerivAt (fun u => ∏ i ∈ s, q i u) (finiteProductFirst s q d z) z := by
  simpa [finiteProductFirst, smul_eq_mul] using HasDerivAt.fun_finset_prod hq
theorem finite_product_first_hasDerivAt  [DecidableEq ι] (s : Finset ι)
    (q d e : ι → ℝ → ℝ) (z : ℝ)
    (hq : ∀ i ∈ s, HasDerivAt (q i) (d i z) z)
    (hd : ∀ i ∈ s, HasDerivAt (d i) (e i z) z) :
    HasDerivAt (finiteProductFirst s q d) (finiteProductSecond s q d e z) z := by
  apply HasDerivAt.fun_sum
  intro i hi
  have hrest : HasDerivAt (fun u => ∏ j ∈ s.erase i, q j u)
      (∑ j ∈ s.erase i, (∏ k ∈ (s.erase i).erase j, q k z) * d j z) z := by
    simpa [smul_eq_mul] using HasDerivAt.fun_finset_prod
      (fun j hj => hq j (Finset.mem_of_mem_erase hj))
  exact hrest.mul (hd i hi)
theorem abs_finite_product_le_one  (s : Finset ι) (q : ι → ℝ)
    (hq : ∀ i ∈ s, |q i| ≤ 1) : |∏ i ∈ s, q i| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun i _ => abs_nonneg (q i)) hq
theorem finite_product_second_abs_bound  [DecidableEq ι] (s : Finset ι)
    (q d e : ι → ℝ → ℝ) (z B1 B2 : ℝ) (hB1 : 0 ≤ B1) (_hB2 : 0 ≤ B2)
    (hq : ∀ i ∈ s, |q i z| ≤ 1) (hd : ∀ i ∈ s, |d i z| ≤ B1)
    (he : ∀ i ∈ s, |e i z| ≤ B2) :
    |finiteProductSecond s q d e z| ≤ s.card * (s.card * B1 ^ 2 + B2) := by
  unfold finiteProductSecond
  calc
    _ ≤ ∑ i ∈ s, |(∑ j ∈ s.erase i, (∏ k ∈ (s.erase i).erase j, q k z) * d j z) * d i z +
        (∏ j ∈ s.erase i, q j z) * e i z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, (↑s.card * B1 ^ 2 + B2) := by
      apply Finset.sum_le_sum
      intro i hi
      have h_finite_product_first_abs_bound (s : Finset ι) (hq : ∀ i ∈ s, |q i z| ≤ 1) (hd : ∀ i ∈ s, |d i z| ≤ B1) : |finiteProductFirst s q d z| ≤ s.card * B1 := by
        calc
          _ ≤ ∑ i ∈ s, |(∏ j ∈ s.erase i, q j z) * d i z| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i ∈ s, B1 := by
            apply Finset.sum_le_sum
            intro i hi
            rw [abs_mul]
            calc
              _ ≤ 1 * B1 := mul_le_mul (abs_finite_product_le_one _ _ (fun j hj => hq j (Finset.mem_of_mem_erase hj))) (hd i hi) (abs_nonneg _) (by norm_num)
              _ = B1 := one_mul B1
          _ = _ := by simp
      have hfirst' : |∑ j ∈ s.erase i, (∏ k ∈ (s.erase i).erase j, q k z) * d j z| ≤ s.card * B1 :=
        (h_finite_product_first_abs_bound (s.erase i) (fun j hj => hq j (Finset.mem_of_mem_erase hj)) (fun j hj => hd j (Finset.mem_of_mem_erase hj))).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card (Finset.erase_subset i s)) hB1)
      calc
        _ ≤ |(∑ j ∈ s.erase i, (∏ k ∈ (s.erase i).erase j, q k z) * d j z) * d i z| +
            |(∏ j ∈ s.erase i, q j z) * e i z| := abs_add_le _ _
        _ ≤ s.card * B1 * B1 + 1 * B2 := by
          rw [abs_mul, abs_mul]
          exact add_le_add
            (mul_le_mul hfirst' (hd i hi) (abs_nonneg _) (by positivity))
            (mul_le_mul (abs_finite_product_le_one _ _ (fun j hj => hq j (Finset.mem_of_mem_erase hj))) (he i hi) (abs_nonneg _) (by norm_num))
        _ = _ := by ring
    _ = _ := by simp; ring
theorem symmetric_difference_abs_bound (H D E : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ z ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt H (D z) z)
    (hD : ∀ z ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt D (E z) z)
    (hE : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |E z| ≤ B) :
    |symmetricDifference H| ≤ B := by
  have hzero : ↑0 ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have hDdiff (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) : |D z - D 0| ≤ B := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hD x hx).hasDerivWithinAt)
      (fun x hx => by simpa only [Real.norm_eq_abs] using hE x hx)
      (convex_Icc (-1 : ℝ) 1) hzero hz
    simp only [Real.norm_eq_abs, sub_zero] at h
    have  := abs_le.mpr hz
    exact h.trans (by nlinarith)
  let G : ℝ → ℝ := fun z => H z - H 0 - z * D 0
  have hG (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
      HasDerivAt G (D z - D 0) z := by
    exact (((hH z hz).sub_const (H 0)).sub
      ((hasDerivAt_id z).mul_const (D 0))).congr_deriv (by ring)
  have hGbound (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) : |G z| ≤ B * |z| := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hG x hx).hasDerivWithinAt)
      (fun x hx => by simpa only [Real.norm_eq_abs] using hDdiff x hx)
      (convex_Icc (-1 : ℝ) 1) hzero hz
    simpa [G, Real.norm_eq_abs] using h
  have heq : symmetricDifference H =
      (1 / 2 : ℝ) * (H 1 - H 0 - D 0) + (1 / 2 : ℝ) * (H (-1) - H 0 + D 0) := by
    unfold symmetricDifference
    ring
  rw [heq]
  calc
    _ ≤ |(1 / 2 : ℝ) * (H 1 - H 0 - D 0)| +
        |(1 / 2 : ℝ) * (H (-1) - H 0 + D 0)| := abs_add_le _ _
    _ ≤ (1 / 2 : ℝ) * B + (1 / 2 : ℝ) * B := by
      rw [abs_mul, abs_mul]
      norm_num only [abs_of_pos (by norm_num : ↑0 < 1 / 2)]
      exact add_le_add (mul_le_mul_of_nonneg_left (by simpa [G] using hGbound 1 (by norm_num)) (by norm_num))
        (mul_le_mul_of_nonneg_left (by simpa [G] using hGbound (-1) (by norm_num)) (by norm_num))
    _ = B := by ring
theorem finite_product_symmetric_difference_bound  [DecidableEq ι]
    (s : Finset ι) (q d e : ι → ℝ → ℝ) (B1 B2 : ℝ)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hq : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i ∈ s, HasDerivAt (q i) (d i z) z)
    (hd : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i ∈ s, HasDerivAt (d i) (e i z) z)
    (h0 : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i ∈ s, |q i z| ≤ 1)
    (h1 : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i ∈ s, |d i z| ≤ B1)
    (h2 : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i ∈ s, |e i z| ≤ B2) :
    |symmetricDifference (fun z => ∏ i ∈ s, q i z)| ≤
      s.card * (s.card * B1 ^ 2 + B2) := by
  apply symmetric_difference_abs_bound _ (finiteProductFirst s q d)
    (finiteProductSecond s q d e)
  · positivity
  · intro z hz
    exact finite_product_hasDerivAt s q d z (hq z hz)
  · intro z hz
    exact finite_product_first_hasDerivAt s q d e z (hq z hz) (hd z hz)
  · intro z hz
    exact finite_product_second_abs_bound s q d e z B1 B2 hB1 hB2
      (h0 z hz) (h1 z hz) (h2 z hz)
def patchFactorFirst (n : ℕ) (a _V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (i : Fin n) (z : ℝ) : ℝ :=
  η * w i * ternaryMeanDerivative a (g i + η * w i * z) (y i)
def patchFactorSecond (n : ℕ) (a η : ℝ) (w : Fin n → ℝ)
    (y : Fin n → Fin 3) (i : Fin n) (_z : ℝ) : ℝ :=
  (η * w i) ^ 2 * ternaryMeanSecondDerivative a (y i)
theorem patch_factor_hasDerivAt (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (i : Fin n) (z : ℝ) :
    HasDerivAt (fun u => ternaryMass a (g i + η * w i * u) V (y i))
      (patchFactorFirst n a V η g w y i z) z := by
  have hx : HasDerivAt (fun u : ℝ => g i + η * w i * u) (η * w i) z := by
    simpa using ((hasDerivAt_id z).const_mul (η * w i)).const_add (g i)
  have h := (ternary_hasDerivAt_mean a (g i + η * w i * z) V (y i)).comp z hx
  exact h.congr_deriv (by unfold patchFactorFirst; ring)
theorem patch_factor_first_hasDerivAt (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (i : Fin n) (z : ℝ) :
    HasDerivAt (patchFactorFirst n a V η g w y i)
      (patchFactorSecond n a η w y i z) z := by
  have hx : HasDerivAt (fun u : ℝ => g i + η * w i * u) (η * w i) z := by
    simpa using ((hasDerivAt_id z).const_mul (η * w i)).const_add (g i)
  have h := ((ternary_hasDerivAt_mean_derivative a (g i + η * w i * z) (y i)).comp z hx).const_mul (η * w i)
  exact h.congr_deriv (by unfold patchFactorSecond; ring)
theorem patch_product_symmetric_difference_bound (n : ℕ) (a V η M N : ℝ)
    (g w : Fin n → ℝ) (y : Fin n → Fin 3) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hw : ∀ i, |w i| ≤ 1)
    (hq : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |ternaryMass a (g i + η * w i * z) V (y i)| ≤ 1)
    (hfirst : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |ternaryMeanDerivative a (g i + η * w i * z) (y i)| ≤ M)
    (hsecond : ∀ i, |ternaryMeanSecondDerivative a (y i)| ≤ N) :
    |symmetricDifference (patchResponseProduct n a V η g w y)| ≤
      (↑n ^ 2 * M ^ 2 + n * N) * η ^ 2 := by
  have hd : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |patchFactorFirst n a V η g w y i z| ≤ |η| * M := by
    intro z hz i
    unfold patchFactorFirst
    rw [abs_mul, abs_mul]
    calc
      _ ≤ |η| * 1 * M :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hw i) (abs_nonneg η))
          (hfirst z hz i) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have he : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |patchFactorSecond n a η w y i z| ≤ η ^ 2 * N := by
    intro z _ i
    unfold patchFactorSecond
    rw [abs_mul, abs_pow, abs_mul, mul_pow, sq_abs]
    have hwi : |w i| ^ 2 ≤ 1 := by nlinarith [hw i, abs_nonneg (w i)]
    calc
      _ ≤ η ^ 2 * 1 * N :=
        mul_le_mul (mul_le_mul_of_nonneg_left hwi (sq_nonneg η))
          (hsecond i) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have h := finite_product_symmetric_difference_bound
    (Finset.univ : Finset (Fin n))
    (fun i z => ternaryMass a (g i + η * w i * z) V (y i))
    (patchFactorFirst n a V η g w y) (patchFactorSecond n a η w y)
    (|η| * M) (η ^ 2 * N) (by positivity) (by positivity)
    (fun z _ i _ => patch_factor_hasDerivAt n a V η g w y i z)
    (fun z _ i _ => patch_factor_first_hasDerivAt n a V η g w y i z)
    (fun z hz i _ => hq z hz i) (fun z hz i _ => hd z hz i) (fun z hz i _ => he z hz i)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  convert h using 1
  · rfl
  · rw [mul_pow, sq_abs]
    ring
theorem patch_response_lower_bound (n : ℕ) (a V η z c : ℝ)
    (g w : Fin n → ℝ) (y : Fin n → Fin 3) (hc : 0 ≤ c)
    (hq : ∀ i, c ≤ ternaryMass a (g i + η * w i * z) V (y i)) :
    c ^ n ≤ patchResponseProduct n a V η g w y z := by
  calc
    _ = ∏ _i : Fin n, c := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hc) (fun i _ => hq i)
theorem patch_score_square_bound (n : ℕ) (a V η z M N B c : ℝ)
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
      (M ^ 2 + N + B) ^ 2 * ↑n ^ 4 * η ^ 4 / c ^ (2 * n) := by
  have h_patch_score_numerator_abs_bound : |patchScoreNumerator n a V η g w y z| ≤
      (M ^ 2 + N + B) * ↑n ^ 2 * η ^ 2 := by
    have hD := patch_product_symmetric_difference_bound n a V η M N g w y hM hN
      hw hq hfirst hsecond
    have h_patch_variance_correction_abs_bound : |∑ i, (w i) ^ 2 * patchVarianceTerm n a V η g w y z i| ≤ n * B := by
      have hq  := hq z hz
      calc
        _ ≤ ∑ i : Fin n, |(w i) ^ 2 * patchVarianceTerm n a V η g w y z i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, B := by
          apply Finset.sum_le_sum
          intro i _
          unfold patchVarianceTerm
          rw [abs_mul, abs_pow, abs_mul]
          have hwi : |w i| ^ 2 ≤ 1 := by nlinarith [hw i, abs_nonneg (w i)]
          have hprod : |∏ k ∈ (Finset.univ : Finset (Fin n)).erase i,
              ternaryMass a (g k + η * w k * z) V (y k)| ≤ 1 :=
            abs_finite_product_le_one _ _ (fun k _ => hq k)
          calc
            _ ≤ 1 * (B * 1) := mul_le_mul hwi
              (mul_le_mul (hvariance i) hprod (abs_nonneg _) hB)
              (by positivity) (by norm_num)
            _ = B := by ring
        _ = _ := by simp
    have hV := h_patch_variance_correction_abs_bound
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
      rw [sub_zero, zero_sub, abs_neg, abs_mul, abs_pow, sq_abs] at h
      exact h
    calc
      _ ≤ |symmetricDifference (patchResponseProduct n a V η g w y)| +
          η ^ 2 * |∑ i, (w i) ^ 2 * patchVarianceTerm n a V η g w y z i| := htriangle
      _ ≤ (↑n ^ 2 * M ^ 2 + n * N) * η ^ 2 + η ^ 2 * (n * B) :=
        add_le_add hD (mul_le_mul_of_nonneg_left hV (sq_nonneg η))
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hNB (sq_nonneg η)]
  have hden := patch_response_lower_bound n a V η z c g w y hc.le hlower
  have hcp  := pow_pos hc n
  have hscore : |patchObservableScore n a V η g w y z| ≤
      (M ^ 2 + N + B) * ↑n ^ 2 * η ^ 2 / c ^ n := by
    unfold patchObservableScore
    rw [abs_div, abs_of_pos (hcp.trans_le hden)]
    exact div_le_div₀ (by positivity) (h_patch_score_numerator_abs_bound) hcp hden
  have hs := mul_self_le_mul_self (abs_nonneg _) hscore
  rw [← sq, sq_abs] at hs
  convert hs using 1
  rw [show 2 * n = n * 2 by omega, pow_mul]
  ring
theorem score_bound_exponential_absorption (n : ℕ) (K c η r : ℝ) (hn : 1 ≤ n) (hc : 0 < c)
    (hr : r ^ 2 ≤ K ^ 2 * (n : ℝ) ^ 4 * η ^ 4 / c ^ (2 * n)) :
    r ^ 2 ≤ (16 * max 1 (K ^ 2) / c ^ 2) ^ n * η ^ 4 := by
  have hK  := (le_max_right 1 (K ^ 2)).trans (by
      simpa using pow_le_pow_right₀ (le_max_left 1 (K ^ 2)) hn)
  have h_fourth_power_count_le_exponential : (n : ℝ) ^ 4 ≤ (16 : ℝ) ^ n := by
    have hn : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
    have h := pow_le_pow_left₀ (Nat.cast_nonneg n) hn 4
    calc
      _ ≤ ((2 : ℝ) ^ n) ^ 4 := h
      _ = (16 : ℝ) ^ n := by rw [← pow_mul, Nat.mul_comm n 4, pow_mul]; norm_num
  have hn4 := h_fourth_power_count_le_exponential
  have hnum : K ^ 2 * ↑n ^ 4 * η ^ 4 ≤
      (max 1 (K ^ 2)) ^ n * (16 : ℝ) ^ n * η ^ 4 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hK hn4 (by positivity) (by positivity)) (by positivity)
  calc
    _ ≤ K ^ 2 * ↑n ^ 4 * η ^ 4 / c ^ (2 * n) := hr
    _ ≤ (max 1 (K ^ 2)) ^ n * ↑16 ^ n * η ^ 4 / c ^ (2 * n) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = _ := by rw [div_pow, mul_pow, ← pow_mul]; ring
theorem finite_exponential_tail_bound (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2), if 2 ≤ k then x ^ k / ↑k.factorial else 0) ≤
      x ^ 2 * Real.exp x := by
  rw [Nat.add_comm n 2, Finset.sum_range_add]
  have hsmall : (∑ k ∈ Finset.range 2, if 2 ≤ k then x ^ k / ↑k.factorial else 0) = 0 := by
    norm_num [Finset.sum_range_succ]
  rw [hsmall, zero_add]
  simp only [show ∀ k : ℕ, 2 ≤ 2 + k by omega, ↓reduceIte]
  calc
    _ ≤ ∑ k ∈ Finset.range n, x ^ 2 * (x ^ k / ↑k.factorial) := by
      apply Finset.sum_le_sum
      intro k _
      calc
        _ ≤ x ^ (2 + k) / ↑k.factorial :=
          div_le_div₀ (by positivity) le_rfl (by positivity) (by exact_mod_cast Nat.factorial_le (show k ≤ 2 + k by omega))
        _ = _ := by rw [pow_add]; ring
    _ = x ^ 2 * (∑ k ∈ Finset.range n, x ^ k / ↑k.factorial) := by rw [Finset.mul_sum]
    _ ≤ x ^ 2 * Real.exp x :=
      mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hx n) (sq_nonneg x)
def binomialCountMass (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
theorem binomial_count_tail_energy (n : ℕ) (p C : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hC : 0 ≤ C) (hmean : n * p ≤ 1) :
    (∑ k ∈ Finset.range (n + 1), if 2 ≤ k then binomialCountMass n p k * C ^ k else 0) ≤
      C ^ 2 * Real.exp C * (n * p) ^ 2 := by
  have hterm (k : ℕ) : binomialCountMass n p k * C ^ k ≤
      (C * n * p) ^ k / (k.factorial : ℝ) := by
    have hremaining : (1 - p) ^ (n - k) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have := Nat.choose_le_pow_div (α := ℝ) k n
    calc
      _ ≤ (n.choose k : ℝ) * p ^ k * 1 * C ^ k := by
        unfold binomialCountMass
        gcongr
      _ ≤ ((n : ℝ) ^ k / (k.factorial : ℝ)) * p ^ k * 1 * C ^ k := by gcongr
      _ = _ := by rw [mul_pow, mul_pow]; ring
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), if 2 ≤ k then (C * n * p) ^ k / (k.factorial : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro k _
      split_ifs <;> simp_all only [le_refl]
    _ ≤ ∑ k ∈ Finset.range (n + 2), if 2 ≤ k then (C * n * p) ^ k / ↑k.factorial else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (by intros; positivity)
    _ ≤ (C * n * p) ^ 2 * Real.exp (C * n * p) := finite_exponential_tail_bound _ (by positivity) n
    _ ≤ C ^ 2 * Real.exp C * (n * p) ^ 2 := by
      have hexp : Real.exp (C * n * p) ≤ Real.exp C := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hmean hC]
      nlinarith [mul_le_mul_of_nonneg_left hexp (sq_nonneg (C * n * p))]
theorem ternary_mean_derivative_abs_bound (a f ρ : ℝ) (ha : 0 < a) (hρ : 0 ≤ ρ)
    (hf : |f| ≤ ρ) (y : Fin 3) :
    |ternaryMeanDerivative a f y| ≤ (2 * ρ + a) / a ^ 2 := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hhalf : (2 * ρ + a) / (2 * a ^ 2) ≤ (2 * ρ + a) / a ^ 2 :=
    div_le_div₀ (by positivity) le_rfl ha2 (by nlinarith)
  fin_cases y
  · change |(2 * f - a) / (2 * a ^ 2)| ≤ _
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * a ^ 2)]
    exact (div_le_div_of_nonneg_right (by have h := abs_sub_le (2 * f) 0 a; rw [sub_zero, zero_sub, abs_neg, abs_mul, abs_of_pos ha] at h; norm_num at h; linarith) (by positivity)).trans hhalf
  · change |-(2 * f) / a ^ 2| ≤ _
    rw [abs_div, abs_neg, abs_mul, abs_of_pos ha2]
    norm_num
    exact div_le_div_of_nonneg_right (by linarith) ha2.le
  · change |(2 * f + a) / (2 * a ^ 2)| ≤ _
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * a ^ 2)]
    exact (div_le_div_of_nonneg_right (by have h := abs_add_le (2 * f) a; rw [abs_mul, abs_of_pos ha] at h; norm_num at h; linarith) (by positivity)).trans hhalf
theorem ternary_mean_second_derivative_abs_bound (a : ℝ) (ha : 0 < a) (y : Fin 3) :
    |ternaryMeanSecondDerivative a y| ≤ 2 / a ^ 2 := by
  have ha2  := sq_pos_of_pos ha
  fin_cases y
  · change |1 / a ^ 2| ≤ _
    rw [abs_div, abs_of_pos ha2, abs_one]
    exact div_le_div_of_nonneg_right (show (1 : ℝ) ≤ 2 by norm_num) ha2.le
  · change |-2 / a ^ 2| ≤ _
    simp [abs_div, abs_of_pos ha2]
  · change |1 / a ^ 2| ≤ _
    rw [abs_div, abs_of_pos ha2, abs_one]
    exact div_le_div_of_nonneg_right (show (1 : ℝ) ≤ 2 by norm_num) ha2.le
theorem ternary_variance_derivative_abs_bound (a : ℝ) (ha : 0 < a) (y : Fin 3) :
    |ternaryVarianceDerivative a y| ≤ 1 / a ^ 2 := by
  have ha2  := sq_pos_of_pos ha
  fin_cases y
  · change |1 / (2 * a ^ 2)| ≤ _
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * a ^ 2), abs_one]
    exact div_le_div₀ (show (0 : ℝ) ≤ 1 by norm_num) le_rfl ha2
      (show a ^ 2 ≤ 2 * a ^ 2 by nlinarith)
  · change |-1 / a ^ 2| ≤ _
    simp [abs_div, abs_of_pos ha2]
  · change |1 / (2 * a ^ 2)| ≤ _
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * a ^ 2), abs_one]
    exact div_le_div₀ (show (0 : ℝ) ≤ 1 by norm_num) le_rfl ha2
      (show a ^ 2 ≤ 2 * a ^ 2 by nlinarith)
def patchExpectedScoreEnergy (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ) (z : ℝ) : ℝ :=
  ∑ y : Fin n → Fin 3,
    patchResponseProduct n a V η g w y z * (patchObservableScore n a V η g w y z) ^ 2
def ternaryScoreExponentialConstant (a ρ c : ℝ) : ℝ :=
  16 * max 1 ((((2 * ρ + a) / a ^ 2) ^ 2 + 3 / a ^ 2) ^ 2) / c ^ 2
theorem patch_expected_score_energy_zero (a V η z : ℝ) (g w : Fin 0 → ℝ) :
    patchExpectedScoreEnergy 0 a V η g w z = 0 := by
  apply Finset.sum_eq_zero
  intro y _
  simp [patchObservableScore, patch_score_cancel_zero 0 a V η g w y z (fun i => Fin.elim0 i)]
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
        have : 0 ≤ 1 - p := by linarith
        exact mul_le_mul_of_nonneg_left (he k hk) (by unfold binomialCountMass; positivity)
      · rw [if_neg hk]
        have hk' : k = 0 ∨ k = 1 := by omega
        rcases hk' with rfl | rfl <;> simp [he0, he1]
    _ = η ^ 4 * (∑ k ∈ Finset.range (n + 1),
        if 2 ≤ k then binomialCountMass n p k * C ^ k else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> ring
    _ ≤ η ^ 4 * (C ^ 2 * Real.exp C * (n * p) ^ 2) :=
      mul_le_mul_of_nonneg_left (binomial_count_tail_energy n p C hp hp1 hC hmean) (by positivity)
    _ = _ := by ring
end NearlyMinimax
