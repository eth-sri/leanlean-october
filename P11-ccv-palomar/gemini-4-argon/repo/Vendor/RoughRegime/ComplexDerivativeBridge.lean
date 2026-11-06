module
public import Mathlib
public import RoughRegime.PolynomialDerivatives
@[expose] public section
noncomputable section
namespace RoughRegime.Cauchy
open Complex Metric
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
theorem norm_fderiv_le_div (f : E → F) (hf : Differentiable ℂ f)
    (x : E) (R A : ℝ) (hR : 0 < R)
    (hbound : ∀ y ∈ closedBall x R, ‖f y‖ ≤ A) :
    ‖fderiv ℂ f x‖ ≤ A / R := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg ((norm_nonneg (f x)).trans (hbound x (mem_closedBall_self hR.le))) hR.le)
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hvpos  := norm_pos_iff.mpr hv
  let g : ℂ → F := fun z => f (x + z • v)
  have hd : deriv g 0 = (fderiv ℂ f x) v := by
    have hline : HasDerivAt (fun z : ℂ => x + z • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
    have hfx : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • v) := by
      simpa using (hf x).hasFDerivAt
    have hh := hfx.comp_hasDerivAt 0 hline
    simpa [g, Function.comp_def] using hh.deriv
  have hc : ‖deriv g 0‖ ≤ A / (R / ‖v‖) := by
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (div_pos hR hvpos) (hf.comp ((differentiable_const x).add (differentiable_id.smul_const v))).diffContOnCl
    intro z hz
    apply hbound
    rw [mem_closedBall, dist_eq_norm]
    change ‖x + z • v - x‖ ≤ R
    rw [add_sub_cancel_left, norm_smul]
    have hz' : ‖z‖ = R / ‖v‖ := by simpa [mem_sphere, dist_eq_norm] using hz
    rw [hz']
    exact le_of_eq (div_mul_cancel₀ R (ne_of_gt hvpos))
  rw [hd] at hc
  convert hc using 1
  field_simp
theorem iteratedFDeriv_closedBall_aux {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (n : ℕ) (f : E → F) (hf : AnalyticOnNhd ℂ f Set.univ)
    (x : E) (δ A : ℝ) (hδ : 0 < δ)
    (hbound : ∀ y ∈ closedBall x ((n : ℝ) * δ), ‖f y‖ ≤ A) :
    ‖iteratedFDeriv ℂ n f x‖ ≤ A / δ ^ n := by
  induction n generalizing F A with
  | zero =>
    simp only [norm_iteratedFDeriv_zero, pow_zero, div_one]
    apply hbound
    simp
  | succ n ih =>
    have hgbound : ∀ y ∈ closedBall x (↑n * δ), ‖fderiv ℂ f y‖ ≤ A / δ := by
      intro y hy
      apply norm_fderiv_le_div f (fun y => (hf y (Set.mem_univ y)).differentiableAt) y δ A hδ
      intro z hz
      apply hbound
      rw [mem_closedBall] at *
      have := dist_triangle z y x
      push_cast
      linarith
    have h := ih (A := A / δ) (fderiv ℂ f) hf.fderiv hgbound
    rw [norm_iteratedFDeriv_fderiv] at h
    convert h using 1
    rw [pow_succ]
    field_simp
theorem iteratedFDeriv_direction_bound {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (n : ℕ) (hn : 0 < n) (f : E → F) (hf : AnalyticOnNhd ℂ f Set.univ)
    (x : E) (ε A : ℝ) (hε : 0 < ε)
    (hbound : ∀ y ∈ ball x ε, ‖f y‖ ≤ A) (v : Fin n → E) :
    ‖iteratedFDeriv ℂ n f x v‖ ≤
      A * ↑n.factorial * (Real.exp 1 / ε) ^ n * ∏ i, ‖v i‖ := by
  have h_iteratedFDeriv_openBall : ‖iteratedFDeriv ℂ n f x‖ ≤ A * (↑n / ε) ^ n := by
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hinner (R : ℝ) (hR : 0 < R) (hRε : R < ε) :
        ‖iteratedFDeriv ℂ n f x‖ ≤ A * ((n : ℝ) / R) ^ n := by
      have hδ  := div_pos hR hnreal
      have h := iteratedFDeriv_closedBall_aux n f hf x (R / n) A hδ (by
        intro y hy
        apply hbound
        rw [mem_closedBall] at hy
        rw [mem_ball]
        have heq : ↑n * (R / n) = R := by field_simp
        rw [heq] at hy
        exact hy.trans_lt hRε)
      convert h using 1
      simp_rw [div_pow]
      field_simp
    have hc : ContinuousAt (fun R : ℝ => A * ((n : ℝ) / R) ^ n) ε := by
      fun_prop (disch := positivity)
    have hl : Filter.Tendsto (fun R : ℝ => A * (↑n / R) ^ n)
        (nhdsWithin ε (Set.Iio ε)) (nhds (A * (↑n / ε) ^ n)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hl
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hε),
      (self_mem_nhdsWithin : Set.Iio ε ∈ nhdsWithin ε (Set.Iio ε))] with R hR hRε
    exact hinner R hR hRε
  have h_pow_le_factorial_exp : ↑n ^ n ≤ ↑n.factorial * Real.exp 1 ^ n := by
    have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n)
    have he : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
      simp
    rw [he] at h
    simpa [mul_comm] using h
  have h := mul_le_mul_of_nonneg_left h_pow_le_factorial_exp
    (div_nonneg ((norm_nonneg (f x)).trans (hbound x (mem_ball_self hε))) (pow_nonneg hε.le n))
  exact (ContinuousMultilinearMap.le_opNorm _ v).trans
    (mul_le_mul_of_nonneg_right ((h_iteratedFDeriv_openBall).trans (by convert h using 1 <;> rw [div_pow] <;> ring)) (Finset.prod_nonneg (fun i _ => norm_nonneg _)))
theorem polynomial_derivative_bound {p : ℕ} (P : MvPolynomial (Fin p) ℂ)
    (x : Fin p → ℂ) (ε A : ℝ) (hε : 0 < ε)
    (hbound : ∀ y : Fin p → ℂ, ‖y - x‖ < ε → ‖MvPolynomial.eval y P‖ ≤ A)
    (n : ℕ) (hn : 0 < n) (v : Fin n → (Fin p → ℂ)) :
    ‖iteratedFDeriv ℂ n (fun y => MvPolynomial.eval y P) x v‖ ≤
      A * ↑n.factorial * (Real.exp 1 / ε) ^ n * ∏ i, ‖v i‖ := by
  apply iteratedFDeriv_direction_bound n hn _ (AnalyticOnNhd.eval_mvPolynomial P) x ε A hε
  intro y hy
  exact hbound y (by simpa [mem_ball, dist_eq_norm] using hy)
end RoughRegime.Cauchy
namespace RoughRegime.ComplexDerivativeBridge

variable {p q r : ℕ}
def complexMonomial  (σ : Fin q → Fin p) (x : Fin p → ℂ) : ℂ := ∏ i, x (σ i)
def complexSlotMap  (σ : Fin q → Fin p) : (Fin p → ℂ) →L[ℂ] (Fin q → ℂ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (σ i))
@[simp] lemma complexSlotMap_apply  (σ : Fin q → Fin p) (x : Fin p → ℂ) (i : Fin q) :
    complexSlotMap σ x i = x (σ i) := rfl
@[fun_prop] lemma complexMonomial_contDiff  (σ : Fin q → Fin p) :
    ContDiff ℂ ⊤ (complexMonomial σ) := by unfold complexMonomial; fun_prop
lemma complexMonomial_iteratedFDeriv  (σ : Fin q → Fin p)
    (m : Fin p → ℂ) (v : Fin r → Fin p → ℂ) :
    iteratedFDeriv ℂ r (complexMonomial σ) m v =
      ∑ a : Fin r ↪ Fin q, ∏ j : Fin q,
        if h : j ∈ Set.range a then v (a.toEquivRange.symm ⟨j, h⟩) (σ j) else m (σ j) := by
  let H := ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin q) ℂ
  have he : complexMonomial σ = H ∘ complexSlotMap σ := by funext x; simp [complexMonomial, H]
  rw [he, (complexSlotMap σ).iteratedFDeriv_comp_right H.contDiff m
    (show (r : WithTop ℕ∞) ≤ ⊤ from le_top), H.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.iteratedFDeriv, sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply, H,
    ContinuousMultilinearMap.mkPiAlgebra_apply, complexSlotMap_apply, Pi.compRightL_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro j _
  split_ifs with h
  · rcases h with ⟨k, rfl⟩
    simp
  · rfl
lemma monomial_derivative_ofReal  (σ : Fin q → Fin p)
    (m : Fin p → ℝ) (v : Fin r → Fin p → ℝ) :
    iteratedFDeriv ℂ r (complexMonomial σ) (fun j => (m j : ℂ))
        (fun i j => (v i j : ℂ)) =
      (iteratedFDeriv ℝ r (RoughRegime.PolynomialDerivatives.monomial σ) m v : ℂ) := by
  rw [complexMonomial_iteratedFDeriv, RoughRegime.PolynomialDerivatives.monomial_iteratedFDeriv]
  simp only [Complex.ofReal_sum, Complex.ofReal_prod]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro j _
  split_ifs <;> rfl
def complexify  (F : MvPolynomial (Fin p) ℝ) : MvPolynomial (Fin p) ℂ :=
  MvPolynomial.map Complex.ofRealHom F
lemma complexify_iteratedFDeriv  (F : MvPolynomial (Fin p) ℝ)
    (m v) :
    iteratedFDeriv ℂ r (fun x => MvPolynomial.eval x (complexify F))
        (fun j => (m j )) (fun i j => (v i j )) =
      (iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x F) m v : ℂ) := by
  have h_complexify_eval_monomials : (fun x => MvPolynomial.eval x (complexify F)) =
      fun x => ∑ α ∈ F.support, (F.coeff α ) *
        complexMonomial (RoughRegime.Upper.exponentCoordinates α) x := by
    funext x
    rw [complexify, MvPolynomial.eval_map, MvPolynomial.eval₂_eq']
    apply Finset.sum_congr rfl
    intro α _
    have h_complex_exponentCoordinates_prod (α : Fin p →₀ ℕ) (x : Fin p → ℂ) : (∏ j, x (RoughRegime.Upper.exponentCoordinates α j)) = ∏ i : Fin p, x i ^ α i := by
      change (∏ j : Fin (Fintype.card (RoughRegime.Upper.ExponentSlots α)),
        x (((Fintype.equivFin (RoughRegime.Upper.ExponentSlots α)).symm j).1)) = _
      rw [Fintype.prod_equiv (Fintype.equivFin (RoughRegime.Upper.ExponentSlots α)).symm
        (fun j => x (((Fintype.equivFin (RoughRegime.Upper.ExponentSlots α)).symm j).1))
        (fun s => x s.1) (fun _ => rfl)]
      unfold RoughRegime.Upper.ExponentSlots
      rw [Fintype.prod_sigma]
      simp
    rw [complexMonomial, h_complex_exponentCoordinates_prod]
    rfl
  rw [h_complexify_eval_monomials, iteratedFDeriv_fun_sum_apply]
  · rw [RoughRegime.PolynomialDerivatives.polynomial_iteratedFDeriv_monomial_sum]
    simp only [sum_apply, Complex.ofReal_sum, Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro α _
    change (iteratedFDeriv ℂ r ((F.coeff α : ℂ) • complexMonomial
      (RoughRegime.Upper.exponentCoordinates α)) _ _) = _
    rw [iteratedFDeriv_const_smul_apply ((complexMonomial_contDiff _).contDiffAt.of_le (show (r : WithTop ℕ∞) ≤ ⊤ from le_top)), smul_apply, smul_eq_mul, monomial_derivative_ofReal]
  · intro α _
    exact (contDiff_const.mul (complexMonomial_contDiff _)).contDiffAt.of_le
      (show (r : WithTop ℕ∞) ≤ ⊤ from le_top)
lemma norm_ofReal_pi  (v : Fin p → ℝ) : ‖fun j => (v j : ℂ)‖ = ‖v‖ := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg v)]
    intro j
    rw [Complex.norm_real]
    exact norm_le_pi_norm v j
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg (fun j => (v j : ℂ)))]
    intro j
    simpa only [Complex.norm_real] using norm_le_pi_norm (fun j => (v j : ℂ)) j
theorem real_polynomial_derivative_bound  (F m ε A) (hε : 0 < ε)
    (hbound : ∀ y : Fin p → ℂ, ‖y - (fun j => (m j : ℂ))‖ < ε →
      ‖MvPolynomial.eval y (complexify F)‖ ≤ A)
    (hr : 0 < r) (v ) :
    ‖iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x F) m v‖ ≤
      A * r.factorial * (Real.exp 1 / ε) ^ r * ∏ i, ‖v i‖ := by
  have hc := RoughRegime.Cauchy.polynomial_derivative_bound (complexify F)
    (fun j => (m j )) ε A hε hbound r hr (fun i j => (v i j : ℂ))
  rw [complexify_iteratedFDeriv, Complex.norm_real] at hc
  simpa only [norm_ofReal_pi] using hc
theorem real_polynomial_derivative_norm_bound  (F m ε A) (hε : 0 < ε) (hA : 0 ≤ A)
    (hbound : ∀ y : Fin p → ℂ, ‖y - (fun j => (m j : ℂ))‖ < ε →
      ‖MvPolynomial.eval y (complexify F)‖ ≤ A) (hr : 0 < r) :
    ‖iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x F) m‖ ≤
      A * r.factorial * (Real.exp 1 / ε) ^ r := by
  apply ContinuousMultilinearMap.opNorm_le_bound
  · positivity
  · exact real_polynomial_derivative_bound F m ε A hε hbound hr
end RoughRegime.ComplexDerivativeBridge
