module

public import NearlyMinimax.Ternary
public import RoughRegime.Macro
public import RoughRegime.Notation

@[expose] public section

/-! # Finite low-smoothness experiment

This file constructs the activation prior and finite conditional response
likelihood used in the paper's small-smoothness lower bound. It proves the
prior derivative, the exact zero/one-observation cancellation, and centering
of the observable score. All expectations below are actual finite sums.
-/

𝚨

noncomputable section

𝗇 𝕼 Fin 3 → ℝ
/-- The prior `(t/2, 1-t, t/2)` on the latent values `(-1,0,1)`. -/
def activationPriorMass (t : ℝ) : 𝕼 := ![t / 2, 1 - t, t / 2]

𝗇 𝔖 (𝙖 : ℝ)
/-- Its signed derivative, `(1/2,-1,1/2)`. -/
def activationPriorDerivative : 𝕼 := ![𝔖, -1, 𝙖]

theorem activation_prior_normalized t : ∑ y, activationPriorMass t y = 1 := by
  simp [Fin.sum_univ_succ, activationPriorMass]
  ring

theorem activation_prior_nonnegative t (ht : 𝘈) (ht1 : t ≤ 1) :
    ∀ y, 0 ≤ activationPriorMass t y := by
  intro y
  fin_cases y <;> simp [activationPriorMass] <;> linarith

theorem activation_prior_hasDerivAt t y :
    HasDerivAt (fun u => activationPriorMass u y) (activationPriorDerivative y) t := by
  fin_cases y
  · exact (hasDerivAt_id t).div_const 2
  · change HasDerivAt (fun u => 1 - u) (-1) t
    exact ((hasDerivAt_const t 1).sub $ hasDerivAt_id t ).congr_deriv 𝖠₄
  · exact (hasDerivAt_id t).div_const 2

𝗇 𝔄 Fin m → Fin 3
𝗃 𝖂 activationPriorMass t $ ξ ἀ
/-- The independent activation prior on `m` latent coordinates. -/
def activationProductPrior (m : ℕ) (t : ℝ) (ξ : 𝔄) : ℝ :=
  ∏ j, 𝖂 j

𝗃 𝖇 (Finset.univ : Finset $ Fin ἀ ).erase
𝗇 𝕯 𝖇 m j
𝗇 𝔉 ∏ k ∈ 𝕯, 𝖂 k
/-- Differentiating the product replaces one factor by its signed derivative. -/
def activationProductPriorDerivative (m : ℕ) (t : ℝ) (ξ : 𝔄) : ℝ :=
  ∑ j, activationPriorDerivative (ξ j) *
    𝔉

𝗃 𝖆 ἀ m t
𝗇 𝔐 𝖆 activationProductPrior ξ
theorem activation_product_prior_normalized m t :
    ∑ ξ, 𝔐 = 1 := by
  unfold activationProductPrior
  rw [← Fintype.prod_sum]
  simp [activation_prior_normalized]

𝗇 𝔩 𝖆 activationProductPriorDerivative ξ
theorem activation_product_prior_hasDerivAt m t ξ :
    HasDerivAt (fun u => activationProductPrior m u ξ)
      𝔩 t := by
  have h := HasDerivAt.fun_finset_prod (u := Finset.univ)
     fun j _ => activation_prior_hasDerivAt t $ ξ j
  simpa [activationProductPrior, activationProductPriorDerivative, smul_eq_mul,
    mul_comm] using h

𝗇 𝕽 𝔄 → ℝ
/-- A finite expectation under the product activation prior. -/
def activationExpectation (m : ℕ) (t : ℝ) (F : ℝ → 𝕽) : ℝ :=
  ∑ ξ, 𝔐 * F t ξ

/-- The finite-mixture derivative includes both prior and observable derivatives. -/
theorem activation_expectation_hasDerivAt m t
    F (dF : 𝕽)
    (hF : ∀ ξ, HasDerivAt (fun u => F u ξ) (dF ξ) t) :
    HasDerivAt (fun u => activationExpectation m u F)
      (∑ ξ : 𝔄, (𝔩 * F t ξ +
        𝔐 * dF ξ)) t := HasDerivAt.fun_sum
     fun ξ _ =>
    (𝖆 activation_product_prior_hasDerivAt ξ).mul $ hF ξ

𝗇 𝔶 Function.update ξ j
/-- The coordinate replacement operator `D_j` in the paper. -/
def latentDifference (m : ℕ) (j : Fin m) (F : 𝕽)
    (ξ : 𝔄) : ℝ :=
  𝔖 * F (𝔶 2) +
    𝔖 * F (𝔶 0) - F (𝔶 1)

𝗇 𝔲 latentDifference m j
/-- Replacement is integration against the signed derivative of the prior. -/
theorem latent_difference_eq_signed_sum m j
    F ξ :
    𝔲 F ξ =
      ∑ z : Fin 3, activationPriorDerivative z * F (𝔶 z) := by
  simp [latentDifference, Fin.sum_univ_succ, activationPriorDerivative]
  ring

𝗇 𝔍 (Equiv.funSplitAt j $ Fin 3 ).symm
𝗇 𝔧 (z, u)
section

variable (m : ℕ)
    (t : ℝ)

private theorem activation_prior_factor (ξ : 𝔄) (j : Fin m) :
    𝔐 = 𝖂 j *
      𝔉 := (Finset.mul_prod_erase _ _ $ Finset.mem_univ j ).symm

𝗇 𝕰 {k : Fin m // k ≠ j}
𝗇 𝔙 ∏ k : 𝕰, activationPriorMass t (u k)
private theorem activation_coordinate_sum (j : Fin m)
    (r : 𝕼) (F : 𝕽) :
     ∑ ξ : 𝔄, r (ξ j) *
      𝔉 * F ξ =
      ∑ u : 𝕰 → Fin 3 ,
        𝔙 *
          ∑ z : Fin 3, r z * F (𝔍 𝔧) := by
  have hrest z u :
       ∏ k ∈ Finset.univ.erase j,
        activationPriorMass t (𝔍 𝔧 k) =
        𝔙 := by
    rw [Finset.prod_subtype (p := fun k => k ≠ j) _ 𝖢₄ ]
    apply Finset.prod_congr rfl
    simp_all
  rw [← (Equiv.funSplitAt j $ Fin 3 ).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp_rw [hrest]
  simp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  grind

end

𝗇 𝕹 𝔍 (z', u)
/-- Differentiation of a coordinate prior is the weighted expectation of
its replacement operator, with no division by a possibly zero prior mass. -/
theorem activation_coordinate_replacement m t j
    F :
     ∑ ξ : 𝔄, activationPriorDerivative (ξ j) *
      (∏ k ∈ Finset.univ.erase j, 𝖂 k) * F ξ =
      ∑ ξ : 𝔄, 𝔐 * 𝔲 F ξ := by
  have hupdate z z' u :
      Function.update (𝔍 𝔧) j z' =
        𝕹 := by
    aesop
  have hD z u :
      𝔲 F (𝔍 𝔧) =
        ∑ z' : Fin 3, activationPriorDerivative z' *
          F 𝕹 := by
    rw [latent_difference_eq_signed_sum]
    simp_all
  simp_rw [𝖆 activation_prior_factor _ j]
  rw [𝖆 activation_coordinate_sum j activationPriorDerivative F,
    𝖆 activation_coordinate_sum j (activationPriorMass t) $ 𝔲 F ]
  apply Finset.sum_congr rfl
  intro u _
  simp_rw [hD]
  rw [← Finset.sum_mul, activation_prior_normalized]
  simp

/-- The full prior derivative is represented by the sum of observable
coordinate replacements. -/
theorem activation_prior_derivative_replacement m t
    F :
     ∑ ξ : 𝔄, 𝔩 * F ξ =
      ∑ ξ : 𝔄, 𝔐 * ∑ j, 𝔲 F ξ := by
  unfold activationProductPriorDerivative
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact 𝖆 activation_coordinate_replacement j F

/-- Symmetric replacement of one real latent coordinate by `+1,-1,0`. -/
def symmetricDifference (H : 𝘓) : ℝ :=
  𝔖 * H 1 + 𝔖 * H (-1) - H 0

𝗇 𝔅 𝙈
𝗇 𝔊 𝙔
𝗇 𝔡 ternaryMass a (g i + 𝗌₂ * z) V $ y i
/-- Response likelihood of one patch, with all other latent coordinates
absorbed into the regression vector `g`. -/
def patchResponseProduct (n : ℕ) (a V η : ℝ) (g w : 𝔊)
    (y : 𝔅) (z : ℝ) : ℝ :=
  ∏ i, 𝔡

𝗇 𝔚 𝚢₁
𝗇 𝔛 𝖇 n i
𝗇 𝔫 𝙿
𝗇 𝕺 ternaryMass a 𝔚 V $ y k
/-- Differentiation in the variance of observation `i` only. -/
def patchVarianceTerm (n : ℕ) (a V η : ℝ) (g w : 𝔊)
    (y : 𝔅) (z : ℝ) (i : Fin n) : ℝ :=
  𝔫 *
    ∏ k ∈ 𝔛,
      𝕺

𝗃 𝕵 ἀ n a V η g w y
𝗇 𝔏 𝕵 patchVarianceTerm z i
𝗇 𝔗 𝙎
𝗇 𝕲 𝕵 patchResponseProduct
𝗇 𝕻 𝖩 * 𝔏
/-- The numerator of the observable patch score in equation (small-s-score). -/
def patchScoreNumerator (n : ℕ) (a V η : ℝ) (g w : 𝔊)
    (y : 𝔅) (z : ℝ) : ℝ :=
  symmetricDifference 𝕲 -
    𝔗 * ∑ i, 𝕻

𝗇 𝔢 𝕵 patchScoreNumerator z
𝗇 𝔣 𝕲 z
/-- The observable patch score itself. -/
def patchObservableScore (n : ℕ) (a V η : ℝ) (g w : 𝔊)
    (y : 𝔅) (z : ℝ) : ℝ :=
  𝔢 / 𝔣

𝗇 𝔥 𝙞
𝗃 𝕿 ∑ y, ἀ
/-- Each conditional sample likelihood sums to one. -/
theorem patch_response_normalized n a V η g w
    z (ha : 𝔥) :
    𝕿 𝔣 = 1 := by
  unfold patchResponseProduct
  rw [← Fintype.prod_sum]
  simp [ternary_normalized a _ V ha]

𝗇 𝔬 ∀ k, k ≠ i → w k = 0
𝗇 𝔭 ternaryMass a (g k) V $ y k
𝗇 𝕾 𝗑₂
private theorem patch_product_singleton (n : ℕ) (a V η : ℝ) (g w : 𝔊)
    (y : 𝔅) (z : ℝ) (i : Fin n) (hw : 𝔬) :
    𝔣 =
      𝔡 *
        ∏ k ∈ 𝔛, 𝔭 := by
  unfold patchResponseProduct
  rw [← 𝕾]
  congr 1
  apply Finset.prod_congr rfl
  simp_all

/-- A patch containing no effective observation has zero score numerator. -/
theorem patch_score_cancel_zero n a V η g w
    y z (hw : ∀ i, w i = 0) :
    𝔢 = 0 := by
  simp [patchScoreNumerator, symmetricDifference, patchResponseProduct, hw]
  ring

𝗇 𝔴 𝕵 patch_product_singleton
/-- The exact heat cancellation for a patch containing at most one effective
observation. It holds for every current value `z` of the latent coordinate. -/
theorem patch_score_cancel_singleton n a V η g w
    y z (ha : 𝔥) i
    (hw : 𝔬) :
    𝔢 = 0 := by
  have hterm : ∑ k, w k ^ 2 * 𝕵 patchVarianceTerm z k =
      𝕻 := by
    apply Finset.sum_eq_single i
    all_goals simp_all
  have hvar : 𝔏 =
      𝔫 *
        ∏ k ∈ Finset.univ.erase i, 𝔭 := by
    unfold patchVarianceTerm
    congr 1
    apply Finset.prod_congr rfl
    simp_all
  unfold patchScoreNumerator symmetricDifference
  rw [hterm, hvar, 𝔴 1 i hw,
    𝔴 (-1) i hw,
    𝔴 0 i hw]
  have hheat := ternary_finite_difference a (g i) V η (w i) ha $ y i
  grind

private theorem patch_variance_term_eq_product (n : ℕ) (a V η : ℝ) (g w : 𝔊)
    (y : 𝔅) (z : ℝ) (i : Fin n) :
    𝔏 =
      ∏ k : Fin n, if k = i then ternaryVarianceDerivative a $ y k
        else 𝕺 := by
  rw [← 𝕾]
  simp
  unfold patchVarianceTerm
  congr 1
  apply Finset.prod_congr rfl
  simp_all

𝗃 𝖃 ∑ y : 𝔅, ἀ
/-- A variance derivative has zero total mass, observation by observation. -/
theorem patch_variance_term_sum_zero n a V η g w
    z i :
    𝖃 𝔏 = 0 := by
  simp_rw [patch_variance_term_eq_product]
  rw [← Fintype.prod_sum fun k yk =>
    if k = i then ternaryVarianceDerivative a yk
      else ternaryMass a 𝔚 V yk ]
  apply 𝗈₁
  simp [Fin.sum_univ_succ, ternaryVarianceDerivative]
  ring

𝗇 𝔮 f ξ i
𝗇 𝔵 𝔄 → 𝔊
/-- A finite conditional experiment, with regression depending on the latent
activation vector. The design points can be absorbed into `f`. -/
def finiteResponseLikelihood (m n : ℕ) (a V : ℝ)
    (f : 𝔵) (ξ : 𝔄) (y : 𝔅) : ℝ :=
  ∏ i, ternaryMass a 𝔮 V (y i)

/-- The partial variance derivative of its `i`th observation. -/
def finiteResponseVarianceTerm (m n : ℕ) (a V : ℝ)
    (f : 𝔵) (ξ : 𝔄)
    (y : 𝔅) (i : Fin n) : ℝ :=
  𝔫 *
    ∏ k ∈ 𝔛, ternaryMass a (f ξ k) V (y k)

𝗃 𝖀 ἀ m n a
𝗇 𝔑 𝖀 finiteResponseVarianceTerm V f ξ y i
𝗇 𝕳 𝖀 finiteResponseLikelihood
𝗇 𝔳 𝕳
𝗇 𝕶 ∑ i, 𝔑
/-- The full variance derivative is the sum of the observation derivatives. -/
theorem finite_response_variance_hasDerivAt m n a V
    f ξ y :
    HasDerivAt (fun W => 𝔳 W f ξ y)
      𝕶 V := by
  have h := HasDerivAt.fun_finset_prod (u := Finset.univ)
     fun i _ => ternary_hasDerivAt_variance a 𝔮 V $ y i
  simpa [finiteResponseLikelihood, finiteResponseVarianceTerm, smul_eq_mul,
    mul_comm] using h

𝗇 𝔎 v - 𝙎 * t
𝗇 𝕷 𝔳 𝔎 f ξ y
𝗃 𝖄 ἀ * T y
/-- The observation expectation along the path `V(t)=v-eta^2*t`. -/
def finiteExperimentExpectation (m n : ℕ) (a v η t : ℝ)
    (f : 𝔵) (T : 𝔅 → ℝ) : ℝ :=
  ∑ ξ, 𝔐 *
    ∑ y, 𝖄 𝕷

𝗇 𝔒 latentDifference m j (fun ξ' => 𝕳 V f ξ' y) ξ
/-- The unnormalized observable derivative for the full finite experiment. -/
def finiteExperimentScoreNumerator (m n : ℕ) (a V η : ℝ)
    (f : 𝔵) (ξ : 𝔄) (y : 𝔅) : ℝ :=
   ∑ j, 𝔒 -
    𝔗 * 𝕶

𝗇 𝔇 𝕳 V f ξ y
𝗃 𝕴 𝖀 ἀ V η f
𝗇 𝔘 𝕴 finiteExperimentScoreNumerator ξ y
/-- The score uses only the data likelihood denominator, never a prior denominator. -/
def finiteExperimentScore (m n : ℕ) (a V η : ℝ)
    (f : 𝔵) (ξ : 𝔄) (y : 𝔅) : ℝ :=
  𝔘 /
    𝔇

𝗃 𝖁 𝔲 (fun ξ' => ∑ y, ἀ ξ' y * T y) ξ
𝗃 𝖈 fun ξ' => ἀ ξ' y
private theorem latent_difference_response_sum (m n : ℕ) (j : Fin m)
    (F : 𝔄 → 𝔅 → ℝ) (T : 𝔅 → ℝ)
    (ξ : 𝔄) :
    𝖁 F =
      ∑ y, 𝔲 𝖈 F ξ * T y := by
  simp [latentDifference, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

𝗇 𝔈 𝕳 (v - 𝙎 * u) f ξ y
𝗇 𝔓 𝕴 finiteExperimentScore ξ y
𝗇 𝔞 ∑ j, latentDifference m j 𝖈 L ξ
𝗇 𝔤 L ξ y * T y
𝗇 𝔯 U ξ y * T y
𝗇 𝔷 -𝔗 * 𝖃 𝔯
𝗇 𝕭 -𝔗 * U ξ y
𝗇 𝕸 ∑ y : 𝔅, 𝖄 𝔈
/-- Exact observable score representation of the derivative of every data
observable in the finite latent/response experiment. -/
theorem finite_experiment_observable_score_hasDerivAt m n a v η t
    f T
    (hpositive : ∀ ξ y, 0 < 𝕷) :
    HasDerivAt (fun u => 𝖀 finiteExperimentExpectation v η u f T)
      (∑ ξ : 𝔄, 𝔐 *
        ∑ y : 𝔅, 𝖄 𝕷 * 𝖀 finiteExperimentScore 𝔎 η f ξ y) t := by
  let V := 𝔎
  let L :=
    𝔳 V f
  let U :=
    fun ξ y => 𝕶
  have hV : HasDerivAt (fun u => v - 𝔗 * u) (-𝔗) t :=
    ((hasDerivAt_const t v).sub $ (hasDerivAt_id t).const_mul 𝔗 ).congr_deriv 𝖢₃
  have hF : ∀ ξ ,
      HasDerivAt (fun u => 𝕸)
        𝔷 t := by
    intro ξ
    have hy : ∀ y ,
        HasDerivAt (fun u => 𝖄 𝔈)
          𝖄 𝕭 t := by
      intro y
      have hcomp : HasDerivAt
          (fun u => 𝔈)
          𝕭 t :=
         by
          have hcomp0 := (𝖀 finite_response_variance_hasDerivAt
            𝔎 f ξ y).comp t hV
          exact hcomp0.congr_deriv 𝖢₃
      exact hcomp.mul_const $ T y
    convert HasDerivAt.fun_sum
      𝘖₂ using 1
    rw [Finset.mul_sum]
    ring
  have h := 𝖆 activation_expectation_hasDerivAt
    (fun u ξ => 𝕸)
    (fun ξ => 𝔷) hF
  apply h.congr_deriv
  have hprior := 𝖆 activation_prior_derivative_replacement
     fun ξ => 𝖃 𝔤
  have hscore : ∀ ξ y,
      𝔤 * 𝔓 =
        (𝔞 - 𝔗 * U ξ y) * T y := by
    dsimp [finiteExperimentScore, finiteExperimentScoreNumerator]
    grind
  change ∑ ξ : 𝔄,
      (𝔩 * 𝕿 𝔤 +
        𝔐 * (-𝔗 * 𝕿 𝔯)) =
      ∑ ξ : 𝔄, 𝔐 *
        ∑ y : 𝔅, 𝔤 * 𝔓
  rw [Finset.sum_add_distrib, hprior]
  have hDsum ξ :
       ∑ j, 𝖁 L =
        ∑ y, 𝖄 𝔞 := by
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
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  grind

/-- Every conditional response distribution of the full experiment normalizes. -/
theorem finite_response_normalized m n a V
    f ξ (ha : 𝔥) :
    𝕿 𝔇 = 1 := by
  unfold finiteResponseLikelihood
  rw [← Fintype.prod_sum]
  simp [ternary_normalized a _ V ha]

/-- The conditional response derivative in any observation has zero total mass. -/
theorem finite_response_variance_term_sum_zero m n a V
    f ξ i :
    𝕿 𝔑 = 0 := by
  simpa [patchVarianceTerm, finiteResponseVarianceTerm] using
    patch_variance_term_sum_zero n a V 0 (f ξ) 𝖾 0 i

𝗇 𝔦 𝖀 finite_response_normalized V f _ ha
/-- The experiment's unnormalized score is centered conditionally on the latent state. -/
theorem finite_experiment_score_numerator_centered m n a V η
    f ξ (ha : 𝔥) :
    𝕿 𝔘 = 0 := by
  have hD j :
      𝖃 𝔒 = 0 := by
    unfold latentDifference
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    simp [𝔦]
    ring
  unfold finiteExperimentScoreNumerator
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  conv_lhs => lhs; rw [Finset.sum_comm]
  conv_lhs => rhs; arg 2; rw [Finset.sum_comm]
  simp [hD, finite_response_variance_term_sum_zero]

𝗃 𝖉 ∑ y : 𝔅, 𝔇 * ἀ = 0
/-- Actual conditional centering of the experiment's score. -/
theorem finite_experiment_score_centered m n a V η
    f ξ (ha : 𝔥)
    (hpositive : ∀ y, 0 < 𝔇) :
    𝖉 𝔓 := by
  have heq y :
      𝔇 * 𝔓 =
        𝔘 := by
    unfold finiteExperimentScore
    grind
  simp_rw [heq]
  exact 𝕴 finite_experiment_score_numerator_centered ξ ha

𝗇 𝔟 Fin n → Fin m → ℝ
𝗇 𝔠 w i j
𝗇 𝔨 𝚣₁
/-- The finite-design version of the random regression field. -/
def latentRegression (m n : ℕ) (η : ℝ) (base : 𝔊)
    (w : 𝔟) (ξ : 𝔄) (i : Fin n) : ℝ :=
  base i + η * ∑ j, 𝔠 * 𝔨

𝗇 𝔰 w i k * ternaryValue 1 (ξ k)
/-- Regression with coordinate `j` excluded from the field. -/
def latentRegressionWithout (m n : ℕ) (η : ℝ) (base : 𝔊)
    (w : 𝔟) (ξ : 𝔄) (j : Fin m) (i : Fin n) : ℝ :=
  base i + η * ∑ k ∈ 𝕯, 𝔰

𝗃 𝖅 ἀ m n η base w ξ j
𝗇 𝕮 𝖅 latentRegressionWithout
𝗇 𝕱 latentRegression m n η base w
/-- Replacing a latent coordinate changes the field only through its own window. -/
theorem latent_regression_update m n η base
    w ξ j i z :
    𝕱 (𝔶 z) i =
      𝕮 i + η * 𝔠 * ternaryValue 1 z := by
  unfold latentRegression latentRegressionWithout
  rw [← Finset.add_sum_erase _ _ $ Finset.mem_univ j ]
  have heq : ∑ k ∈ Finset.univ.erase j,
      w i k * ternaryValue 1 (𝔶 z k) =
      ∑ k ∈ Finset.univ.erase j, 𝔰 := by
    apply Finset.sum_congr rfl
    simp_all
  grind

/-- The current field has the same excluded-coordinate decomposition. -/
theorem latent_regression_decomposition m n η base
    w ξ j i :
    𝕱 ξ i =
      𝕮 i + η * 𝔠 * 𝔨 := by
  simpa using 𝖅 latent_regression_update i $ ξ j

𝗇 𝔪 𝕮
𝗇 𝔱 𝕱
/-- The actual coordinate likelihood replacement equals the one-dimensional
patch finite difference used in the cancellation proof. -/
theorem latent_regression_likelihood_difference m n a V η
    base w ξ
    j y :
    𝔲
      (fun ξ' => 𝔳 V 𝔱 ξ' y) ξ =
      symmetricDifference (patchResponseProduct n a V η
        𝔪 (fun i => 𝔠) y) := by
  simp [latentDifference, finiteResponseLikelihood, symmetricDifference,
    patchResponseProduct, latent_regression_update, ternaryValue]

/-- The observation variance terms also agree under this patch representation. -/
theorem latent_regression_variance_term m n a V η
    base w ξ
    j y i :
    𝖀 finiteResponseVarianceTerm V 𝔱 ξ y i =
      patchVarianceTerm n a V η 𝔪
        (fun k => w k j) y 𝔨 i := by
  simp [finiteResponseVarianceTerm, patchVarianceTerm, 𝖅 latent_regression_decomposition]

/-- One coordinate's unnormalized observable score in the full finite experiment. -/
def finiteCoordinateScoreNumerator (m n : ℕ) (a V η : ℝ)
    (f : 𝔵) (w : 𝔟)
    (ξ : 𝔄) (y : 𝔅) (j : Fin m) : ℝ :=
  𝔒 -
    𝔗 * ∑ i, 𝔠 ^ 2 * 𝔑

𝗇 𝔔 𝕴 finiteCoordinateScoreNumerator w ξ y j
/-- One coordinate's observable score, as in equation (small-s-score). -/
def finiteCoordinateScore (m n : ℕ) (a V η : ℝ)
    (f : 𝔵) (w : 𝔟)
    (ξ : 𝔄) (y : 𝔅) (j : Fin m) : ℝ :=
  𝔔 / 𝔇

𝗇 𝕬 ∀ i, ∑ j, 𝔠 ^ 2 = 1
/-- The sum-of-squares window identity decomposes the full score numerator
into the paper's coordinate numerators. -/
theorem finite_experiment_score_numerator_decomposition m n a V η
    f w
    ξ y
    (hw : 𝕬) :
    𝔘 =
      ∑ j, 𝔔 := by
  unfold finiteExperimentScoreNumerator finiteCoordinateScoreNumerator
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul, hw]
  simp

𝗇 𝔜 𝕴 finiteCoordinateScore w ξ y j
/-- The observable full score equals the sum of its coordinate scores. -/
theorem finite_experiment_score_decomposition m n a V η
    f w
    ξ y
    (hw : 𝕬) :
    𝔓 =
      ∑ j, 𝔜 := by
  unfold finiteExperimentScore finiteCoordinateScore
  rw [𝕴 finite_experiment_score_numerator_decomposition w ξ y hw,
    Finset.sum_div]

/-- A coordinate score is centered over responses for every fixed latent state. -/
theorem finite_coordinate_score_numerator_centered m n a V η
    f w
    ξ j (ha : 𝔥) :
    𝕿 𝔔 = 0 := by
  unfold finiteCoordinateScoreNumerator latentDifference
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, finite_response_variance_term_sum_zero]
  simp [𝔦]
  ring

theorem finite_coordinate_score_centered m n a V η
    f w
    ξ j (ha : 𝔥)
    (hpositive : ∀ y, 0 < 𝔇) :
    𝖉 𝔜 := by
  have heq y :
      𝔇 * 𝔜 =
        𝔔 := by
    unfold finiteCoordinateScore
    grind
  simp_rw [heq]
  exact 𝕴 finite_coordinate_score_numerator_centered w ξ j ha

/-- The finite latent-response joint law normalizes. -/
theorem finite_experiment_joint_normalized m n a V t
    f (ha : 𝔥) :
    ∑ ξ : 𝔄, ∑ y : 𝔅,
      𝔐 * 𝔇 = 1 := by
  simp_rw [← Finset.mul_sum, 𝔦, mul_one]
  exact 𝖆 activation_product_prior_normalized

/-- Its masses are nonnegative in the probability range of the activation prior. -/
theorem finite_experiment_joint_nonnegative m n a V t
    f (ht : 𝘈) (ht1 : t ≤ 1)
    (hresponse : ∀ ξ i y, 0 ≤ ternaryMass a 𝔮 V y) :
    ∀ ξ y, 0 ≤ 𝔐 * 𝔇 := by
  intro ξ y
  apply mul_nonneg
  · exact Finset.prod_nonneg fun j _ => activation_prior_nonnegative t ht ht1 $ ξ j
  · exact Finset.prod_nonneg fun i _ => hresponse ξ i $ y i
