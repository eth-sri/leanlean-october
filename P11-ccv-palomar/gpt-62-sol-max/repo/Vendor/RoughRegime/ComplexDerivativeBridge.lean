module

public import Mathlib
public import RoughRegime.Cauchy
public import RoughRegime.PolynomialDerivatives


@[expose] public section

/-! Real derivatives of a real polynomial obey the complex Cauchy bound of Lemma 5(c). -/
noncomputable section
namespace RoughRegime.ComplexDerivativeBridge

/-- Canonical complexification of the paper's real polynomial. -/
def complexify {p : ℕ} (F : MvPolynomial (Fin p) ℝ) : MvPolynomial (Fin p) ℂ :=
  MvPolynomial.map Complex.ofRealHom F

/-- Restrict the complex derivative along the real coordinate inclusion. -/
lemma complexify_iteratedFDeriv {p r : ℕ} (F : MvPolynomial (Fin p) ℝ)
    (m : Fin p → ℝ) (v : Fin r → Fin p → ℝ) :
    iteratedFDeriv ℂ r (fun x => MvPolynomial.eval x (complexify F))
        (fun j => (m j : ℂ)) (fun i j => (v i j : ℂ)) =
      (iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x F) m v : ℂ) := by
  let L : (Fin p → ℝ) →L[ℝ] (Fin p → ℂ) :=
    ContinuousLinearMap.pi fun j => Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)
  let f (x : Fin p → ℝ) := MvPolynomial.eval x F
  let g (z : Fin p → ℂ) := MvPolynomial.eval z (complexify F)
  have h : Complex.ofRealCLM ∘ f = g ∘ L :=
    funext fun x => MvPolynomial.map_eval Complex.ofRealHom x F
  have hf : ContDiffAt ℝ (r : WithTop ℕ∞) f m := (AnalyticOnNhd.eval_mvPolynomial F).contDiff.contDiffAt
  have hg : ContDiff ℂ (r : WithTop ℕ∞) g := (AnalyticOnNhd.eval_mvPolynomial (complexify F)).contDiff
  have he := Complex.ofRealCLM.iteratedFDeriv_comp_left hf (i := r) le_rfl
  rw [h, L.iteratedFDeriv_comp_right (hg.restrict_scalars ℝ) m le_rfl,
    ← hg.contDiffAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ)] at he
  exact congrArg (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℂ => D v) he

lemma norm_ofReal_pi {p : ℕ} (v : Fin p → ℝ) : ‖fun j => (v j : ℂ)‖ = ‖v‖ := by
  have h : Pi.map (fun _ : Fin p => Complex.ofReal) (0 : Fin p → ℝ) = 0 := by ext; simp [Pi.map]
  change ‖Pi.map (fun _ : Fin p => Complex.ofReal) v‖ = ‖v‖
  simpa only [dist_eq_norm, h, sub_zero] using
    (Isometry.piMap (fun _ : Fin p => Complex.ofReal) (fun _ => Complex.isometry_ofReal)).dist_eq v 0

section
variable {p r : ℕ} (F : MvPolynomial (Fin p) ℝ)
    (m : Fin p → ℝ) (ε A : ℝ) (hε : 0 < ε)
include hε

/-- Actual real polynomial derivatives satisfy the source Cauchy direction bound. -/
theorem real_polynomial_derivative_bound
    (hbound : ∀ y : Fin p → ℂ, ‖y - (fun j => (m j : ℂ))‖ < ε →
      ‖MvPolynomial.eval y (complexify F)‖ ≤ A)
    (v : Fin r → Fin p → ℝ) :
    ‖iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x F) m v‖ ≤
      A * (r.factorial : ℝ) * (Real.exp 1 / ε) ^ r * ∏ i, ‖v i‖ := by
  cases r with
  | zero =>
    have hc := hbound (fun j => (m j : ℂ)) (by simpa)
    have he := complexify_iteratedFDeriv F m v
    simp only [iteratedFDeriv_zero_apply] at he
    rw [he, Complex.norm_real] at hc
    simpa using hc
  | succ r =>
    have hc := RoughRegime.Cauchy.polynomial_derivative_bound (complexify F)
      (fun j => (m j : ℂ)) ε A hε hbound (r+1) (Nat.succ_pos _) (fun i j => (v i j : ℂ))
    rw [complexify_iteratedFDeriv, Complex.norm_real] at hc
    simpa only [norm_ofReal_pi] using hc

/-- The corresponding operator norm bound used in Lemma 8. -/
theorem real_polynomial_derivative_norm_bound (hA : 0 ≤ A)
    (hbound : ∀ y : Fin p → ℂ, ‖y - (fun j => (m j : ℂ))‖ < ε →
      ‖MvPolynomial.eval y (complexify F)‖ ≤ A) :
    ‖iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x F) m‖ ≤
      A * (r.factorial : ℝ) * (Real.exp 1 / ε) ^ r := by
  apply ContinuousMultilinearMap.opNorm_le_bound
  · positivity
  · exact real_polynomial_derivative_bound F m ε A hε hbound

end

end RoughRegime.ComplexDerivativeBridge
