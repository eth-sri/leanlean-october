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
def activationPriorDerivative : Fin 3 → ℝ := ![(1 / 2), -1, 1 / 2]

section
variable {m : ℕ} (t : ℝ)

theorem activation_prior_normalized : ∑ y, activationPriorMass t y = 1 := by
  simp [Fin.sum_univ_succ, activationPriorMass]
  ring

theorem activation_prior_nonnegative {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ y, 0 ≤ activationPriorMass t y := by
  intro y
  fin_cases y <;> simp [activationPriorMass] <;> linarith

theorem activation_prior_hasDerivAt (y : Fin 3) :
    HasDerivAt (fun u => activationPriorMass u y) (activationPriorDerivative y) t := by
  fin_cases y
  · exact HasDerivAt.div_const (hasDerivAt_id t) 2
  · change HasDerivAt _ (-1) t
    exact ((hasDerivAt_const t 1).sub (hasDerivAt_id t)).congr_deriv (by norm_num)
  · exact HasDerivAt.div_const (hasDerivAt_id t) 2

/-- The independent activation prior on `m` latent coordinates. -/
def activationProductPrior (ξ : TernaryVector m) : ℝ :=
  ∏ j, activationPriorMass t (ξ j)

/-- Differentiating the product replaces one factor by its signed derivative. -/
def activationProductPriorDerivative (ξ : TernaryVector m) : ℝ :=
  ∑ j, activationPriorDerivative (ξ j) *
    ∏ k ∈ Finset.univ.erase j, activationPriorMass t (ξ k)

theorem activation_product_prior_normalized (m : ℕ) (t : ℝ) :
    ∑ ξ, activationProductPrior (m := m) t ξ = 1 := by
  unfold activationProductPrior
  rw [← Fintype.prod_sum]
  simp [activation_prior_normalized]

theorem activation_product_prior_hasDerivAt (ξ : TernaryVector m) :
    HasDerivAt (fun u => activationProductPrior u ξ)
      (activationProductPriorDerivative t ξ) t := by
  have h := HasDerivAt.fun_finset_prod (u := Finset.univ)
    (fun j _ => activation_prior_hasDerivAt t (ξ j))
  simpa [activationProductPrior, activationProductPriorDerivative, 
    mul_comm] using h

/-- The coordinate replacement operator `D_j` in the paper. -/
def latentDifference (j : Fin m) (F : (TernaryVector m) → ℝ)
    (ξ : TernaryVector m) : ℝ :=
  (1 / 2) * F (Function.update ξ j 2) +
    (1 / 2) * F (Function.update ξ j 0) - F (Function.update ξ j 1)

/-- Replacement is integration against the signed derivative of the prior. -/
theorem latent_difference_eq_signed_sum (m : ℕ) (j : Fin m)
    (F : (TernaryVector m) → ℝ) (ξ : TernaryVector m) :
    latentDifference j F ξ =
      ∑ z, activationPriorDerivative z * F (Function.update ξ j z) := by
  simp [latentDifference, Fin.sum_univ_succ, activationPriorDerivative]
  ring

private theorem activation_prior_factor (ξ : TernaryVector m) (j : Fin m) :
    activationProductPrior t ξ = activationPriorMass t (ξ j) *
      ∏ k ∈ Finset.univ.erase j, activationPriorMass t (ξ k) := (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm

private theorem activation_coordinate_sum (j : Fin m)
    (r : Fin 3 → ℝ) (F : (TernaryVector m) → ℝ) :
    (∑ ξ, r (ξ j) *
      (∏ k ∈ Finset.univ.erase j, activationPriorMass t (ξ k)) * F ξ) =
      ∑ u,
        (∏ k, activationPriorMass t (u k)) *
          ∑ z, r z * F ((Equiv.funSplitAt j (Fin 3)).symm (z, u)) := by
  have hrest z u :
      (∏ k ∈ Finset.univ.erase j,
        activationPriorMass t ((Equiv.funSplitAt j (Fin 3)).symm (z, u) k)) =
        ∏ k, activationPriorMass t (u k) := by
    rw [Finset.prod_subtype (p := fun k => k ≠ j) _ (by simp)]
    apply Finset.prod_congr rfl
    simp_all
  rw [← (Equiv.funSplitAt j (Fin 3)).symm.sum_comp, Fintype.sum_prod_type]
  simp_rw [hrest]
  simp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

end

section
variable (m : ℕ) (t : ℝ)

/-- Differentiation of a coordinate prior is the weighted expectation of
its replacement operator, with no division by a possibly zero prior mass. -/
theorem activation_coordinate_replacement (j : Fin m)
    (F : (TernaryVector m) → ℝ) :
    (∑ ξ, activationPriorDerivative (ξ j) *
      (∏ k ∈ Finset.univ.erase j, activationPriorMass t (ξ k)) * F ξ) =
      ∑ ξ, activationProductPrior t ξ * latentDifference j F ξ := by
  have hupdate z z' u :
      Function.update ((Equiv.funSplitAt j (Fin 3)).symm (z, u)) j z' =
        (Equiv.funSplitAt j (Fin 3)).symm (z', u) := by
    funext k
    by_cases h : k = j
    · subst k
      simp
    · simp_all
  have hD z u :
      latentDifference j F ((Equiv.funSplitAt j (Fin 3)).symm (z, u)) =
        ∑ z', activationPriorDerivative z' *
          F ((Equiv.funSplitAt j (Fin 3)).symm (z', u)) := by
    rw [latent_difference_eq_signed_sum]
    simp_rw [hupdate]
  simp_rw [activation_prior_factor t _ j]
  rw [activation_coordinate_sum t j activationPriorDerivative F,
    activation_coordinate_sum t j (activationPriorMass t) (latentDifference j F)]
  apply Finset.sum_congr rfl
  intro u _
  simp_rw [hD]
  rw [← Finset.sum_mul, activation_prior_normalized]
  simp

/-- The full prior derivative is represented by the sum of observable
coordinate replacements. -/
theorem activation_prior_derivative_replacement
    (F : (TernaryVector m) → ℝ) :
    (∑ ξ, activationProductPriorDerivative t ξ * F ξ) =
      ∑ ξ, activationProductPrior t ξ * ∑ j, latentDifference j F ξ := by
  unfold activationProductPriorDerivative
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  solve_by_elim [activation_coordinate_replacement]

end

section
variable {n : ℕ} (a V η : ℝ) (g w : Fin n → ℝ) (y : TernaryVector n) (z : ℝ) (H : ℝ → ℝ)

/-- Symmetric replacement of one real latent coordinate by `+1,-1,0`. -/
def symmetricDifference : ℝ :=
  (1 / 2) * H 1 + (1 / 2) * H (-1) - H 0

/-- Response likelihood of one patch, with all other latent coordinates
absorbed into the regression vector `g`. -/
def patchResponseProduct : ℝ :=
  ∏ i, ternaryMass a (g i + η * w i * z) V (y i)

/-- Differentiation in the variance of observation `i` only. -/
def patchVarianceTerm (i : Fin n) : ℝ :=
  ternaryVarianceDerivative a (y i) *
    ∏ k ∈ Finset.univ.erase i,
      ternaryMass a (g k + η * w k * z) V (y k)

/-- The numerator of the observable patch score in equation (small-s-score). -/
def patchScoreNumerator : ℝ :=
  symmetricDifference (patchResponseProduct a V η g w y) -
    η ^ 2 * ∑ i, (w i) ^ 2 * patchVarianceTerm a V η g w y z i

/-- The observable patch score itself. -/
def patchObservableScore : ℝ :=
  patchScoreNumerator a V η g w y z / patchResponseProduct a V η g w y z

end

section
variable {m n : ℕ} (a V v η : ℝ) (g w : Fin n → ℝ) (t : ℝ) (f : (TernaryVector m) → Fin n → ℝ)
    (T : (TernaryVector n) → ℝ) (z : ℝ)

/-- Each conditional sample likelihood sums to one. -/
theorem patch_response_normalized (ha : a ≠ 0) :
    ∑ y, patchResponseProduct a V η g w y z = 1 := by
  unfold patchResponseProduct
  rw [← Fintype.prod_sum]
  simp [ternary_normalized _ V ha]

private theorem patch_product_singleton
    (y : TernaryVector n) (z : ℝ) {i : Fin n} (hw : ∀ k, k ≠ i → w k = 0) :
    patchResponseProduct a V η g w y z =
      ternaryMass a (g i + η * w i * z) V (y i) *
        ∏ k ∈ Finset.univ.erase i, ternaryMass a (g k) V (y k) := by
  unfold patchResponseProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  congr 1
  apply Finset.prod_congr rfl
  aesop

/-- A patch containing no effective observation has zero score numerator. -/
theorem patch_score_cancel_zero
    (y : TernaryVector n) (z : ℝ) (hw : ∀ i, w i = 0) :
    patchScoreNumerator a V η g w y z = 0 := by
  simp [patchScoreNumerator, symmetricDifference, patchResponseProduct, hw]
  ring

/-- The exact heat cancellation for a patch containing at most one effective
observation. It holds for every current value `z` of the latent coordinate. -/
theorem patch_score_cancel_singleton
    (y : TernaryVector n) (z : ℝ) (ha : a ≠ 0) (i : Fin n)
    (hw : ∀ k, k ≠ i → w k = 0) :
    patchScoreNumerator a V η g w y z = 0 := by
  have hterm : ∑ k, (w k) ^ 2 * patchVarianceTerm a V η g w y z k =
      (w i) ^ 2 * patchVarianceTerm a V η g w y z i := by
    apply Finset.sum_eq_single i <;> simp_all
  have hvar : patchVarianceTerm a V η g w y z i =
      ternaryVarianceDerivative a (y i) *
        ∏ k ∈ Finset.univ.erase i, ternaryMass a (g k) V (y k) := by
    unfold patchVarianceTerm
    congr 1
    apply Finset.prod_congr rfl
    aesop
  unfold patchScoreNumerator symmetricDifference
  rw [  patch_product_singleton a V η g w y 1 hw,
    patch_product_singleton a V η g w y (-1) hw,
    patch_product_singleton a V η g w y 0 hw]
  grind [ternary_finite_difference a (g i) V η (w i) ha (y i)]

private theorem patch_variance_term_eq_product (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : TernaryVector n) (z : ℝ) (i : Fin n) :
    patchVarianceTerm a V η g w y z i =
      ∏ k, if k = i then ternaryVarianceDerivative a (y k)
        else ternaryMass a (g k + η * w k * z) V (y k) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp
  unfold patchVarianceTerm
  congr 1
  apply Finset.prod_congr rfl
  aesop

/-- A variance derivative has zero total mass, observation by observation. -/
theorem patch_variance_term_sum_zero (i : Fin n) :
    ∑ y, patchVarianceTerm a V η g w y z i = 0 := by
  simp_rw [patch_variance_term_eq_product]
  rw [← Fintype.prod_sum (fun k yk =>
    if k = i then ternaryVarianceDerivative a yk
      else ternaryMass a (g k + η * w k * z) V yk)]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [Fin.sum_univ_succ, ternaryVarianceDerivative]
  ring

/-- A finite conditional experiment, with regression depending on the latent
activation vector. The design points can be absorbed into `f`. -/
def finiteResponseLikelihood (ξ : TernaryVector m) (y : TernaryVector n) : ℝ :=
  ∏ i, ternaryMass a (f ξ i) V (y i)

/-- The partial variance derivative of its `i`th observation. -/
def finiteResponseVarianceTerm (ξ : TernaryVector m)
    (y : TernaryVector n) (i : Fin n) : ℝ :=
  ternaryVarianceDerivative a (y i) *
    ∏ k ∈ Finset.univ.erase i, ternaryMass a (f ξ k) V (y k)

/-- The full variance derivative is the sum of the observation derivatives. -/
theorem finite_response_variance_hasDerivAt (ξ : TernaryVector m) (y : TernaryVector n) :
    HasDerivAt (fun W => finiteResponseLikelihood a W f ξ y)
      (∑ i, finiteResponseVarianceTerm a V f ξ y i) V := by
  have h := HasDerivAt.fun_finset_prod (u := Finset.univ)
    (fun i _ => ternary_hasDerivAt_variance a (f ξ i) V (y i))
  simpa [finiteResponseLikelihood, finiteResponseVarianceTerm, 
    mul_comm] using h

/-- The observation expectation along the path `V(t)=v-eta^2*t`. -/
def finiteExperimentExpectation : ℝ :=
  ∑ ξ, activationProductPrior t ξ *
    ∑ y, finiteResponseLikelihood a (v - η ^ 2 * t) f ξ y * T y

/-- The unnormalized observable derivative for the full finite experiment. -/
def finiteExperimentScoreNumerator (ξ : TernaryVector m) (y : TernaryVector n) : ℝ :=
  (∑ j, latentDifference j (fun ξ' => finiteResponseLikelihood a V f ξ' y) ξ) -
    η ^ 2 * ∑ i, finiteResponseVarianceTerm a V f ξ y i

/-- The score uses only the data likelihood denominator, never a prior denominator. -/
def finiteExperimentScore (ξ : TernaryVector m) (y : TernaryVector n) : ℝ :=
  finiteExperimentScoreNumerator a V η f ξ y /
    finiteResponseLikelihood a V f ξ y

end

private theorem latent_difference_response_sum (m n : ℕ) (j : Fin m)
    (F : (TernaryVector m) → (TernaryVector n) → ℝ) (T : (TernaryVector n) → ℝ)
    (ξ : TernaryVector m) :
    latentDifference j (fun ξ' => ∑ y, F ξ' y * T y) ξ =
      ∑ y, latentDifference j (fun ξ' => F ξ' y) ξ * T y := by
  simp [latentDifference, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

/-- Exact observable score representation of the derivative of every data
observable in the finite latent/response experiment. -/
theorem finite_experiment_observable_score_hasDerivAt {m n : ℕ} {a v η t : ℝ}
    {f : (TernaryVector m) → Fin n → ℝ} (T : (TernaryVector n) → ℝ)
    (hpositive : ∀ ξ y, 0 < finiteResponseLikelihood a (v - η ^ 2 * t) f ξ y) :
    HasDerivAt (fun u => finiteExperimentExpectation a v η u f T)
      (∑ ξ, activationProductPrior t ξ *
        ∑ y, finiteResponseLikelihood a (v - η ^ 2 * t) f ξ y *
          T y * finiteExperimentScore a (v - η ^ 2 * t) η f ξ y) t := by
  let V := v - η ^ 2 * t
  let L  :=
    finiteResponseLikelihood a V f
  let U  :=
    fun ξ y => ∑ i, finiteResponseVarianceTerm a V f ξ y i
  have hV : HasDerivAt (fun u => v - η ^ 2 * u) (-η ^ 2) t :=
    ((hasDerivAt_const t v).sub ((hasDerivAt_id t).const_mul (η ^ 2))).congr_deriv (by ring)
  have hF : ∀ ξ,
      HasDerivAt (fun u => ∑ y,
        finiteResponseLikelihood a (v - η ^ 2 * u) f ξ y * T y)
        (-η ^ 2 * ∑ y, U ξ y * T y) t := by
    intro ξ
    have hy : ∀ y,
        HasDerivAt (fun u => finiteResponseLikelihood a (v - η ^ 2 * u) f ξ y * T y)
          ((-η ^ 2 * U ξ y) * T y) t := by
      intro y
      have hcomp : HasDerivAt
          (fun u => finiteResponseLikelihood a (v - η ^ 2 * u) f ξ y)
          (-η ^ 2 * U ξ y) t :=
        (by
          have hcomp0 := (finite_response_variance_hasDerivAt a
            (V) f ξ y).comp t hV
          exact hcomp0.congr_deriv (by ring))
      exact hcomp.mul_const (T y)
    convert HasDerivAt.fun_sum
      (fun y _ => hy y) using 1
    rw [Finset.mul_sum]
    ring
  apply (HasDerivAt.fun_sum (u := Finset.univ) (fun ξ _ => (activation_product_prior_hasDerivAt _ ξ).mul (hF ξ))).congr_deriv
  have hprior := activation_prior_derivative_replacement m t
    (fun ξ => ∑ y, L ξ y * T y)
  have hscore : ∀ ξ y,
      L ξ y * T y * finiteExperimentScore a V η f ξ y =
        ((∑ j, latentDifference j (fun ξ' => L ξ' y) ξ) - η ^ 2 * U ξ y) * T y := by
    grind [finiteExperimentScore, finiteExperimentScoreNumerator]
  change _ =
      ∑ ξ, activationProductPrior t ξ *
        ∑ y, L ξ y * T y * finiteExperimentScore a V η f ξ y
  rw [Finset.sum_add_distrib, hprior]
  have hDsum ξ :
      (∑ j, latentDifference j (fun ξ' => ∑ y, L ξ' y * T y) ξ) =
        ∑ y, (∑ j, latentDifference j (fun ξ' => L ξ' y) ξ) * T y := by
    simp_rw [latent_difference_response_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_mul]
  simp_rw [hDsum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ξ _
  simp_rw [hscore]
  rw [← mul_add]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring

section
variable (m n : ℕ) (a V η : ℝ) (f : (TernaryVector m) → Fin n → ℝ) (ξ : TernaryVector m)

/-- Every conditional response distribution of the full experiment normalizes. -/
theorem finite_response_normalized (ha : a ≠ 0) :
    ∑ y, finiteResponseLikelihood a V f ξ y = 1 := by
  unfold finiteResponseLikelihood
  rw [← Fintype.prod_sum]
  simp [ternary_normalized _ V ha]

/-- The conditional response derivative in any observation has zero total mass. -/
theorem finite_response_variance_term_sum_zero (i : Fin n) :
    ∑ y, finiteResponseVarianceTerm a V f ξ y i = 0 := by
  simpa [patchVarianceTerm, finiteResponseVarianceTerm] using
    patch_variance_term_sum_zero a V 0 (f ξ) (fun _ => 0) 0 i

/-- The experiment's unnormalized score is centered conditionally on the latent state. -/
theorem finite_experiment_score_numerator_centered (ha : a ≠ 0) :
    ∑ y, finiteExperimentScoreNumerator a V η f ξ y = 0 := by
  have hD j :
      ∑ y,
        latentDifference j (fun ξ' => finiteResponseLikelihood a V f ξ' y) ξ = 0 := by
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

end

section
variable {m n : ℕ} (a V η : ℝ) (base : Fin n → ℝ) (f : (TernaryVector m) → Fin n → ℝ)
    (w : Fin n → Fin m → ℝ) (ξ : TernaryVector m)

/-- Actual conditional centering of the experiment's score. -/
theorem finite_experiment_score_centered (ha : a ≠ 0)
    (hpositive : ∀ y, 0 < finiteResponseLikelihood a V f ξ y) :
    ∑ y,
      finiteResponseLikelihood a V f ξ y * finiteExperimentScore a V η f ξ y = 0 := by
  have heq y :
      finiteResponseLikelihood a V f ξ y * finiteExperimentScore a V η f ξ y =
        finiteExperimentScoreNumerator a V η f ξ y := by
    grind [finiteExperimentScore]
  simp_rw [heq]
  solve_by_elim [finite_experiment_score_numerator_centered]

/-- The finite-design version of the random regression field. -/
def latentRegression (i : Fin n) : ℝ :=
  base i + η * ∑ j, w i j * ternaryValue 1 (ξ j)

/-- Regression with coordinate `j` excluded from the field. -/
def latentRegressionWithout (j : Fin m) (i : Fin n) : ℝ :=
  base i + η * ∑ k ∈ Finset.univ.erase j, w i k * ternaryValue 1 (ξ k)

/-- Replacing a latent coordinate changes the field only through its own window. -/
theorem latent_regression_update (j : Fin m) (i : Fin n) (z : Fin 3) :
    latentRegression η base w (Function.update ξ j z) i =
      latentRegressionWithout η base w ξ j i + η * w i j * ternaryValue 1 z := by
  unfold latentRegression latentRegressionWithout
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  have heq : (∑ k ∈ Finset.univ.erase j,
      w i k * ternaryValue 1 (Function.update ξ j z k)) =
      ∑ k ∈ Finset.univ.erase j, w i k * ternaryValue 1 (ξ k) := by
    apply Finset.sum_congr rfl
    aesop
  rw [heq]
  ring

/-- The current field has the same excluded-coordinate decomposition. -/
theorem latent_regression_decomposition (j : Fin m) (i : Fin n) :
    latentRegression η base w ξ i =
      latentRegressionWithout η base w ξ j i + η * w i j * ternaryValue 1 (ξ j) := by
  simpa using latent_regression_update η base w ξ j i (ξ j)

/-- The actual coordinate likelihood replacement equals the one-dimensional
patch finite difference used in the cancellation proof. -/
theorem latent_regression_likelihood_difference (m n : ℕ) (a V η : ℝ)
    (base : Fin n → ℝ) (w : Fin n → Fin m → ℝ) (ξ : TernaryVector m)
    (j : Fin m) (y : TernaryVector n) :
    latentDifference j
      (fun ξ' => finiteResponseLikelihood a V (latentRegression η base w) ξ' y) ξ =
      symmetricDifference (patchResponseProduct a V η
        (latentRegressionWithout η base w ξ j) (fun i => w i j) y) := by
  simp [latentDifference, finiteResponseLikelihood, symmetricDifference,
    patchResponseProduct, latent_regression_update, ternaryValue]

/-- One coordinate's unnormalized observable score in the full finite experiment. -/
def finiteCoordinateScoreNumerator (y : TernaryVector n) (j : Fin m) : ℝ :=
  latentDifference j (fun ξ' => finiteResponseLikelihood a V f ξ' y) ξ -
    η ^ 2 * ∑ i, (w i j) ^ 2 * finiteResponseVarianceTerm a V f ξ y i

/-- One coordinate's observable score, as in equation (small-s-score). -/
def finiteCoordinateScore (y : TernaryVector n) (j : Fin m) : ℝ :=
  finiteCoordinateScoreNumerator a V η f w ξ y j / finiteResponseLikelihood a V f ξ y

end

section
variable {m n : ℕ} (a V η : ℝ) (f : (TernaryVector m) → Fin n → ℝ) {w : Fin n → Fin m → ℝ}
    (ξ : TernaryVector m) (y : TernaryVector n) (hw : ∀ i, ∑ j, (w i j) ^ 2 = 1)
include hw

/-- The sum-of-squares window identity decomposes the full score numerator
into the paper's coordinate numerators. -/
theorem finite_experiment_score_numerator_decomposition :
    finiteExperimentScoreNumerator a V η f ξ y =
      ∑ j, finiteCoordinateScoreNumerator a V η f w ξ y j := by
  unfold finiteExperimentScoreNumerator finiteCoordinateScoreNumerator
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul, hw]
  simp

/-- The observable full score equals the sum of its coordinate scores. -/
theorem finite_experiment_score_decomposition :
    finiteExperimentScore a V η f ξ y =
      ∑ j, finiteCoordinateScore a V η f w ξ y j := by
  unfold finiteExperimentScore finiteCoordinateScore
  rw [finite_experiment_score_numerator_decomposition a V η f ξ y hw,
    Finset.sum_div]

end

section
variable (m n : ℕ) (a V η : ℝ) (f : (TernaryVector m) → Fin n → ℝ) (w : Fin n → Fin m → ℝ)
    (ξ : TernaryVector m) (j : Fin m) (ha : a ≠ 0)
include ha

/-- A coordinate score is centered over responses for every fixed latent state. -/
theorem finite_coordinate_score_numerator_centered :
    ∑ y, finiteCoordinateScoreNumerator a V η f w ξ y j = 0 := by
  unfold finiteCoordinateScoreNumerator latentDifference
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, finite_response_variance_term_sum_zero]
  simp [finite_response_normalized m n a V f _ ha]
  ring

theorem finite_coordinate_score_centered
    (hpositive : ∀ y, 0 < finiteResponseLikelihood a V f ξ y) :
    ∑ y,
      finiteResponseLikelihood a V f ξ y * finiteCoordinateScore a V η f w ξ y j = 0 := by
  have heq y :
      finiteResponseLikelihood a V f ξ y * finiteCoordinateScore a V η f w ξ y j =
        finiteCoordinateScoreNumerator a V η f w ξ y j := by
    grind [finiteCoordinateScore]
  simp_rw [heq]
  solve_by_elim [finite_coordinate_score_numerator_centered]

end

variable {m n : ℕ}

/-- Its masses are nonnegative in the probability range of the activation prior. -/
theorem finite_experiment_joint_nonnegative {a V t : ℝ}
    {f : (TernaryVector m) → Fin n → ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hresponse : ∀ ξ i y, 0 ≤ ternaryMass a (f ξ i) V y) :
    ∀ ξ y, 0 ≤ activationProductPrior t ξ * finiteResponseLikelihood a V f ξ y := by
  intro ξ y
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun j _ => activation_prior_nonnegative ht ht1 _)
  · solve_by_elim [Finset.prod_nonneg]

end

end NearlyMinimax
