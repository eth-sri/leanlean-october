module

public import NearlyMinimax.Ternary

@[expose] public section

/-! # Finite low-smoothness experiment

This file constructs the activation prior and finite conditional response
likelihood used in the paper's small-smoothness lower bound. It proves the
prior derivative, the exact zero/one-observation cancellation, and centering
of the observable score. All expectations below are actual finite sums.
-/

namespace NearlyMinimax

noncomputable section

/-- The prior `(t/2, 1-t, t/2)` on the latent values `(-1,0,1)`. -/
def activationPriorMass (t : ℝ) : Fin 3 → ℝ := ![t / 2, 1 - t, t / 2]

/-- Its signed derivative, `(1/2,-1,1/2)`. -/
def activationPriorDerivative : Fin 3 → ℝ := ![(1 / 2 : ℝ), -1, 1 / 2]

section
variable (t : ℝ)

theorem activation_prior_normalized : ∑ y, activationPriorMass t y = 1 := by
  simp [Fin.sum_univ_succ, activationPriorMass]
  ring

theorem activation_prior_nonnegative (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ y, 0 ≤ activationPriorMass t y := by
  intro y
  fin_cases y <;> simp [activationPriorMass] <;> linarith

theorem activation_prior_hasDerivAt (y : Fin 3) :
    HasDerivAt (fun u => activationPriorMass u y) (activationPriorDerivative y) t := by
  fin_cases y
  · exact (hasDerivAt_id t).div_const 2
  · change HasDerivAt (fun u => 1 - u) (-1) t
    exact ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).congr_deriv (by norm_num)
  · exact (hasDerivAt_id t).div_const 2

end

/-- The independent activation prior on `m` latent coordinates. -/
def activationProductPrior (m : ℕ) (t : ℝ) (ξ : Fin m → Fin 3) : ℝ :=
  ∏ j, activationPriorMass t (ξ j)

/-- Differentiating the product replaces one factor by its signed derivative. -/
def activationProductPriorDerivative (m : ℕ) (t : ℝ) (ξ : Fin m → Fin 3) : ℝ :=
  ∑ j, activationPriorDerivative (ξ j) *
    ∏ k ∈ (Finset.univ : Finset (Fin m)).erase j, activationPriorMass t (ξ k)

section
variable (m : ℕ) (t : ℝ)

theorem activation_product_prior_normalized :
    ∑ ξ, activationProductPrior m t ξ = 1 := by
  unfold activationProductPrior
  rw [← Fintype.prod_sum]
  simp [activation_prior_normalized]

theorem activation_product_prior_hasDerivAt (ξ : Fin m → Fin 3) :
    HasDerivAt (fun u => activationProductPrior m u ξ)
      (activationProductPriorDerivative m t ξ) t := by
  have h := HasDerivAt.fun_finset_prod (u := (Finset.univ : Finset (Fin m)))
    (fun j _ => activation_prior_hasDerivAt t (ξ j))
  simpa [activationProductPrior, activationProductPriorDerivative, smul_eq_mul,
    mul_comm] using h

end

/-- A finite expectation under the product activation prior. -/
def activationExpectation (m : ℕ) (t : ℝ) (F : ℝ → (Fin m → Fin 3) → ℝ) : ℝ :=
  ∑ ξ, activationProductPrior m t ξ * F t ξ

/-- The finite-mixture derivative includes both prior and observable derivatives. -/
theorem activation_expectation_hasDerivAt (m : ℕ) (t : ℝ)
    (F : ℝ → (Fin m → Fin 3) → ℝ) (dF : (Fin m → Fin 3) → ℝ)
    (hF : ∀ ξ, HasDerivAt (fun u => F u ξ) (dF ξ) t) :
    HasDerivAt (fun u => activationExpectation m u F)
      (∑ ξ : (Fin m → Fin 3), (activationProductPriorDerivative m t ξ * F t ξ +
        activationProductPrior m t ξ * dF ξ)) t := by
  exact HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin m → Fin 3)))
    (fun ξ _ =>
    (activation_product_prior_hasDerivAt m t ξ).mul (hF ξ))

/-- The coordinate replacement operator `D_j` in the paper. -/
def latentDifference (m : ℕ) (j : Fin m) (F : (Fin m → Fin 3) → ℝ)
    (ξ : Fin m → Fin 3) : ℝ :=
  (1 / 2 : ℝ) * F (Function.update ξ j 2) +
    (1 / 2 : ℝ) * F (Function.update ξ j 0) - F (Function.update ξ j 1)

section
variable (m : ℕ)

/-- Replacement is integration against the signed derivative of the prior. -/
theorem latent_difference_eq_signed_sum (j : Fin m)
    (F : (Fin m → Fin 3) → ℝ) (ξ : Fin m → Fin 3) :
    latentDifference m j F ξ =
      ∑ z : Fin 3, activationPriorDerivative z * F (Function.update ξ j z) := by
  simp [latentDifference, Fin.sum_univ_succ, activationPriorDerivative]
  ring

section
variable (t : ℝ)

private theorem activation_prior_factor (ξ : Fin m → Fin 3) (j : Fin m) :
    activationProductPrior m t ξ = activationPriorMass t (ξ j) *
      ∏ k ∈ (Finset.univ : Finset (Fin m)).erase j, activationPriorMass t (ξ k) := (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm

section
variable (j : Fin m)

private theorem activation_coordinate_sum
    (r : Fin 3 → ℝ) (F : (Fin m → Fin 3) → ℝ) :
    (∑ ξ : Fin m → Fin 3, r (ξ j) *
      (∏ k ∈ (Finset.univ : Finset (Fin m)).erase j, activationPriorMass t (ξ k)) * F ξ) =
      ∑ u : ({k : Fin m // k ≠ j} → Fin 3),
        (∏ k : {k : Fin m // k ≠ j}, activationPriorMass t (u k)) *
          ∑ z : Fin 3, r z * F ((Equiv.funSplitAt j (Fin 3)).symm (z, u)) := by
  have hrest (z : Fin 3) (u : {k : Fin m // k ≠ j} → Fin 3) :
      (∏ k ∈ (Finset.univ : Finset (Fin m)).erase j,
        activationPriorMass t ((Equiv.funSplitAt j (Fin 3)).symm (z, u) k)) =
        ∏ k : {k : Fin m // k ≠ j}, activationPriorMass t (u k) := by
    rw [Finset.prod_subtype (p := fun k : Fin m => k ≠ j) _ (by simp)]
    apply Finset.prod_congr rfl
    intro k _
    simp [Equiv.funSplitAt_symm_apply, k.property]
  rw [← (Equiv.funSplitAt j (Fin 3)).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp_rw [hrest]
  simp only [Equiv.funSplitAt_symm_apply, dite_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- Differentiation of a coordinate prior is the weighted expectation of
its replacement operator, with no division by a possibly zero prior mass. -/
theorem activation_coordinate_replacement
    (F : (Fin m → Fin 3) → ℝ) :
    (∑ ξ : Fin m → Fin 3, activationPriorDerivative (ξ j) *
      (∏ k ∈ (Finset.univ : Finset (Fin m)).erase j, activationPriorMass t (ξ k)) * F ξ) =
      ∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ * latentDifference m j F ξ := by
  have hupdate (z z' : Fin 3) (u : {k : Fin m // k ≠ j} → Fin 3) :
      Function.update ((Equiv.funSplitAt j (Fin 3)).symm (z, u)) j z' =
        (Equiv.funSplitAt j (Fin 3)).symm (z', u) := by
    funext k
    by_cases h : k = j
    all_goals (simp_all)
  have hD (z : Fin 3) (u : {k : Fin m // k ≠ j} → Fin 3) :
      latentDifference m j F ((Equiv.funSplitAt j (Fin 3)).symm (z, u)) =
        ∑ z' : Fin 3, activationPriorDerivative z' *
          F ((Equiv.funSplitAt j (Fin 3)).symm (z', u)) := by
    simp [latent_difference_eq_signed_sum, hupdate]
  simp_rw [activation_prior_factor m t _ j]
  rw [activation_coordinate_sum m t j activationPriorDerivative F,
    activation_coordinate_sum m t j (activationPriorMass t) (latentDifference m j F)]
  apply Finset.sum_congr rfl
  intro u _
  simp_rw [hD]
  norm_num [← Finset.sum_mul, activation_prior_normalized]

end

/-- The full prior derivative is represented by the sum of observable
coordinate replacements. -/
theorem activation_prior_derivative_replacement
    (F : (Fin m → Fin 3) → ℝ) :
    (∑ ξ : Fin m → Fin 3, activationProductPriorDerivative m t ξ * F ξ) =
      ∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ * ∑ j, latentDifference m j F ξ := by
  unfold activationProductPriorDerivative
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  solve_by_elim [Finset.sum_congr, activation_coordinate_replacement]

end

end

/-- Symmetric replacement of one real latent coordinate by `+1,-1,0`. -/
def symmetricDifference (H : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * H 1 + (1 / 2 : ℝ) * H (-1) - H 0

/-- Response likelihood of one patch, with all other latent coordinates
absorbed into the regression vector `g`. -/
def patchResponseProduct (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) : ℝ :=
  ∏ i, ternaryMass a (g i + η * w i * z) V (y i)

/-- Differentiation in the variance of observation `i` only. -/
def patchVarianceTerm (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) (i : Fin n) : ℝ :=
  ternaryVarianceDerivative a (y i) *
    ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i,
      ternaryMass a (g k + η * w k * z) V (y k)

/-- The numerator of the observable patch score in equation (small-s-score). -/
def patchScoreNumerator (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) : ℝ :=
  symmetricDifference (patchResponseProduct n a V η g w y) -
    η ^ 2 * ∑ i, (w i) ^ 2 * patchVarianceTerm n a V η g w y z i

/-- The observable patch score itself. -/
def patchObservableScore (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) : ℝ :=
  patchScoreNumerator n a V η g w y z / patchResponseProduct n a V η g w y z

section
variable (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)

/-- Each conditional sample likelihood sums to one. -/
theorem patch_response_normalized
    (z : ℝ) (ha : a ≠ 0) :
    ∑ y, patchResponseProduct n a V η g w y z = 1 := by
  unfold patchResponseProduct
  rw [← Fintype.prod_sum]
  simp [ternary_normalized a _ V]

section
variable (y : Fin n → Fin 3) (z : ℝ)

private theorem patch_product_singleton (i : Fin n) (hw : ∀ k, k ≠ i → w k = 0) :
    patchResponseProduct n a V η g w y z =
      ternaryMass a (g i + η * w i * z) V (y i) *
        ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, ternaryMass a (g k) V (y k) := by
  unfold patchResponseProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  congr 1
  apply Finset.prod_congr rfl
  grind

/-- A patch containing no effective observation has zero score numerator. -/
theorem patch_score_cancel_zero (hw : ∀ i, w i = 0) :
    patchScoreNumerator n a V η g w y z = 0 := by
  simp [patchScoreNumerator, symmetricDifference, patchResponseProduct, hw]
  ring

/-- The exact heat cancellation for a patch containing at most one effective
observation. It holds for every current value `z` of the latent coordinate. -/
theorem patch_score_cancel_singleton (ha : a ≠ 0) (i : Fin n)
    (hw : ∀ k, k ≠ i → w k = 0) :
    patchScoreNumerator n a V η g w y z = 0 := by
  have hterm : ∑ k, (w k) ^ 2 * patchVarianceTerm n a V η g w y z k =
      (w i) ^ 2 * patchVarianceTerm n a V η g w y z i := by
    apply Finset.sum_eq_single i <;> simp_all
  have hvar : patchVarianceTerm n a V η g w y z i =
      ternaryVarianceDerivative a (y i) *
        ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, ternaryMass a (g k) V (y k) := by
    unfold patchVarianceTerm
    congr 1
    apply Finset.prod_congr rfl
    grind
  unfold patchScoreNumerator symmetricDifference
  rw [hterm, hvar, patch_product_singleton n a V η g w y 1 i hw,
    patch_product_singleton n a V η g w y (-1) i hw,
    patch_product_singleton n a V η g w y 0 i hw]
  simp only [mul_one, mul_neg_one, mul_zero, add_zero]
  have hheat := ternary_finite_difference a (g i) V η (w i) (y i)
  grind

private theorem patch_variance_term_eq_product (i : Fin n) :
    patchVarianceTerm n a V η g w y z i =
      ∏ k : Fin n, if k = i then ternaryVarianceDerivative a (y k)
        else ternaryMass a (g k + η * w k * z) V (y k) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true]
  unfold patchVarianceTerm
  congr 1
  grind [Finset.prod_congr]

end

/-- A variance derivative has zero total mass, observation by observation. -/
theorem patch_variance_term_sum_zero
    (z : ℝ) (i : Fin n) :
    ∑ y : Fin n → Fin 3, patchVarianceTerm n a V η g w y z i = 0 := by
  simp_rw [patch_variance_term_eq_product]
  rw [← Fintype.prod_sum (fun k (yk : Fin 3) =>
    if k = i then ternaryVarianceDerivative a yk
      else ternaryMass a (g k + η * w k * z) V yk)]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [Fin.sum_univ_succ, ternaryVarianceDerivative]
  ring

end

/-- A finite conditional experiment, with regression depending on the latent
activation vector. The design points can be absorbed into `f`. -/
def finiteResponseLikelihood (m n : ℕ) (a V : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) : ℝ :=
  ∏ i, ternaryMass a (f ξ i) V (y i)

/-- The partial variance derivative of its `i`th observation. -/
def finiteResponseVarianceTerm (m n : ℕ) (a V : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3)
    (y : Fin n → Fin 3) (i : Fin n) : ℝ :=
  ternaryVarianceDerivative a (y i) *
    ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, ternaryMass a (f ξ k) V (y k)

/-- The full variance derivative is the sum of the observation derivatives. -/
theorem finite_response_variance_hasDerivAt (m n : ℕ) (a V : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) :
    HasDerivAt (fun W => finiteResponseLikelihood m n a W f ξ y)
      (∑ i, finiteResponseVarianceTerm m n a V f ξ y i) V := by
  have h := HasDerivAt.fun_finset_prod (u := (Finset.univ : Finset (Fin n)))
    (fun i _ => ternary_hasDerivAt_variance a (f ξ i) V (y i))
  simpa [finiteResponseLikelihood, finiteResponseVarianceTerm, smul_eq_mul,
    mul_comm] using h

/-- The observation expectation along the path `V(t)=v-eta^2*t`. -/
def finiteExperimentExpectation (m n : ℕ) (a v η t : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (T : (Fin n → Fin 3) → ℝ) : ℝ :=
  ∑ ξ, activationProductPrior m t ξ *
    ∑ y, finiteResponseLikelihood m n a (v - η ^ 2 * t) f ξ y * T y

/-- The unnormalized observable derivative for the full finite experiment. -/
def finiteExperimentScoreNumerator (m n : ℕ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) : ℝ :=
  (∑ j, latentDifference m j (fun ξ' => finiteResponseLikelihood m n a V f ξ' y) ξ) -
    η ^ 2 * ∑ i, finiteResponseVarianceTerm m n a V f ξ y i

/-- The score uses only the data likelihood denominator, never a prior denominator. -/
def finiteExperimentScore (m n : ℕ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) : ℝ :=
  finiteExperimentScoreNumerator m n a V η f ξ y /
    finiteResponseLikelihood m n a V f ξ y

section
variable (m n : ℕ)

section
variable (a V : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3)

theorem finite_response_normalized (ha : a ≠ 0) :
    ∑ y, finiteResponseLikelihood m n a V f ξ y = 1 := by
  unfold finiteResponseLikelihood
  rw [← Fintype.prod_sum]
  simp [ternary_normalized a _ V]

/-- The conditional response derivative in any observation has zero total mass. -/
theorem finite_response_variance_term_sum_zero (i : Fin n) :
    ∑ y, finiteResponseVarianceTerm m n a V f ξ y i = 0 := by
  simpa [patchVarianceTerm, finiteResponseVarianceTerm] using
    patch_variance_term_sum_zero n a V 0 (f ξ) (fun _ => 0) 0 i

end

section
variable (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3)

section
variable (ha : a ≠ 0)
include ha

/-- The experiment's unnormalized score is centered conditionally on the latent state. -/
theorem finite_experiment_score_numerator_centered :
    ∑ y, finiteExperimentScoreNumerator m n a V η f ξ y = 0 := by
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

/-- Actual conditional centering of the experiment's score. -/
theorem finite_experiment_score_centered
    (hpositive : ∀ y, 0 < finiteResponseLikelihood m n a V f ξ y) :
    ∑ y : Fin n → Fin 3,
      finiteResponseLikelihood m n a V f ξ y * finiteExperimentScore m n a V η f ξ y = 0 := by
  have heq (y : Fin n → Fin 3) :
      finiteResponseLikelihood m n a V f ξ y * finiteExperimentScore m n a V η f ξ y =
        finiteExperimentScoreNumerator m n a V η f ξ y := by
    unfold finiteExperimentScore
    grind
  simp_rw [heq]
  apply finite_experiment_score_numerator_centered <;> assumption

end

end

end

/-- The finite-design version of the random regression field. -/
def latentRegression (m n : ℕ) (η : ℝ) (base : Fin n → ℝ)
    (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3) (i : Fin n) : ℝ :=
  base i + η * ∑ j, w i j * ternaryValue 1 (ξ j)

/-- Regression with coordinate `j` excluded from the field. -/
def latentRegressionWithout (m n : ℕ) (η : ℝ) (base : Fin n → ℝ)
    (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3) (j : Fin m) (i : Fin n) : ℝ :=
  base i + η * ∑ k ∈ (Finset.univ : Finset (Fin m)).erase j, w i k * ternaryValue 1 (ξ k)

section
variable (m n : ℕ)

section
variable (η : ℝ) (base : Fin n → ℝ)
    (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3) (j : Fin m) (i : Fin n)

/-- Replacing a latent coordinate changes the field only through its own window. -/
theorem latent_regression_update (z : Fin 3) :
    latentRegression m n η base w (Function.update ξ j z) i =
      latentRegressionWithout m n η base w ξ j i + η * w i j * ternaryValue 1 z := by
  unfold latentRegression latentRegressionWithout
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  have heq : (∑ k ∈ (Finset.univ : Finset (Fin m)).erase j,
      w i k * ternaryValue 1 (Function.update ξ j z k)) =
      ∑ k ∈ (Finset.univ : Finset (Fin m)).erase j, w i k * ternaryValue 1 (ξ k) := by
    apply Finset.sum_congr rfl
    simp_all
  rw [heq]
  ring

/-- The current field has the same excluded-coordinate decomposition. -/
theorem latent_regression_decomposition :
    latentRegression m n η base w ξ i =
      latentRegressionWithout m n η base w ξ j i + η * w i j * ternaryValue 1 (ξ j) := by
  simpa using latent_regression_update m n η base w ξ j i (ξ j)

end

section
variable (a V η : ℝ)
    (base : Fin n → ℝ) (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3)
    (j : Fin m) (y : Fin n → Fin 3)

/-- The actual coordinate likelihood replacement equals the one-dimensional
patch finite difference used in the cancellation proof. -/
theorem latent_regression_likelihood_difference :
    latentDifference m j
      (fun ξ' => finiteResponseLikelihood m n a V (latentRegression m n η base w) ξ' y) ξ =
      symmetricDifference (patchResponseProduct n a V η
        (latentRegressionWithout m n η base w ξ j) (fun i => w i j) y) := by
  simp [latentDifference, finiteResponseLikelihood, symmetricDifference,
    patchResponseProduct, latent_regression_update, ternaryValue]

/-- The observation variance terms also agree under this patch representation. -/
theorem latent_regression_variance_term (i : Fin n) :
    finiteResponseVarianceTerm m n a V (latentRegression m n η base w) ξ y i =
      patchVarianceTerm n a V η (latentRegressionWithout m n η base w ξ j)
        (fun k => w k j) y (ternaryValue 1 (ξ j)) i := by
  simp [finiteResponseVarianceTerm, patchVarianceTerm, latent_regression_decomposition m n η base w ξ j]

end

end

/-- One coordinate's unnormalized observable score in the full finite experiment. -/
def finiteCoordinateScoreNumerator (m n : ℕ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (w : Fin n → Fin m → ℝ)
    (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) (j : Fin m) : ℝ :=
  latentDifference m j (fun ξ' => finiteResponseLikelihood m n a V f ξ' y) ξ -
    η ^ 2 * ∑ i, (w i j) ^ 2 * finiteResponseVarianceTerm m n a V f ξ y i

/-- One coordinate's observable score, as in equation (small-s-score). -/
def finiteCoordinateScore (m n : ℕ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (w : Fin n → Fin m → ℝ)
    (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) (j : Fin m) : ℝ :=
  finiteCoordinateScoreNumerator m n a V η f w ξ y j / finiteResponseLikelihood m n a V f ξ y

section
variable (m n : ℕ)

section
variable (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (w : Fin n → Fin m → ℝ)
    (ξ : Fin m → Fin 3)

section
variable (y : Fin n → Fin 3)
    (hw : ∀ i, ∑ j, (w i j) ^ 2 = 1)
include hw

/-- The sum-of-squares window identity decomposes the full score numerator
into the paper's coordinate numerators. -/
theorem finite_experiment_score_numerator_decomposition :
    finiteExperimentScoreNumerator m n a V η f ξ y =
      ∑ j, finiteCoordinateScoreNumerator m n a V η f w ξ y j := by
  unfold finiteExperimentScoreNumerator finiteCoordinateScoreNumerator
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  simp_all [← Finset.sum_mul]

/-- The observable full score equals the sum of its coordinate scores. -/
theorem finite_experiment_score_decomposition :
    finiteExperimentScore m n a V η f ξ y =
      ∑ j, finiteCoordinateScore m n a V η f w ξ y j := by
  unfold finiteExperimentScore finiteCoordinateScore
  rw [finite_experiment_score_numerator_decomposition m n a V η f w ξ y hw,
    Finset.sum_div]

end

section
variable (j : Fin m) (ha : a ≠ 0)
include ha

/-- A coordinate score is centered over responses for every fixed latent state. -/
theorem finite_coordinate_score_numerator_centered :
    ∑ y, finiteCoordinateScoreNumerator m n a V η f w ξ y j = 0 := by
  unfold finiteCoordinateScoreNumerator latentDifference
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, finite_response_variance_term_sum_zero]
  simp [finite_response_normalized m n a V f _ ha]
  ring

theorem finite_coordinate_score_centered
    (hpositive : ∀ y, 0 < finiteResponseLikelihood m n a V f ξ y) :
    ∑ y : Fin n → Fin 3,
      finiteResponseLikelihood m n a V f ξ y * finiteCoordinateScore m n a V η f w ξ y j = 0 := by
  have heq (y : Fin n → Fin 3) :
      finiteResponseLikelihood m n a V f ξ y * finiteCoordinateScore m n a V η f w ξ y j =
        finiteCoordinateScoreNumerator m n a V η f w ξ y j := by
    unfold finiteCoordinateScore
    grind
  simp_rw [heq]
  apply finite_coordinate_score_numerator_centered <;> assumption

end

end

section
variable (a V t : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ)

/-- The finite latent-response joint law normalizes. -/
theorem finite_experiment_joint_normalized (ha : a ≠ 0) :
    ∑ ξ : Fin m → Fin 3, ∑ y : Fin n → Fin 3,
      activationProductPrior m t ξ * finiteResponseLikelihood m n a V f ξ y = 1 := by
  simp_rw [← Finset.mul_sum, finite_response_normalized m n a V f _ ha, mul_one]
  exact activation_product_prior_normalized m t

/-- Its masses are nonnegative in the probability range of the activation prior. -/
theorem finite_experiment_joint_nonnegative (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hresponse : ∀ ξ i y, 0 ≤ ternaryMass a (f ξ i) V y) :
    ∀ ξ y, 0 ≤ activationProductPrior m t ξ * finiteResponseLikelihood m n a V f ξ y := by
  intro ξ y
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun j _ => activation_prior_nonnegative t ht ht1 (ξ j))
  · solve_by_elim [Finset.prod_nonneg]

end

end

end

end NearlyMinimax
