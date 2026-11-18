module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Setting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdaptersCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic

/-- Product of scalar position and velocity cutoffs with a physical test function. -/
def spatialCutoffTest (chi psi : ℝ → ℝ) (phi : Point → ℝ) (p : Point) : ℝ :=
  chi (p.position 0)*psi (p.velocity 0)*phi p

/-- Scalar second-derivative Leibniz rule for C² factors. -/
theorem second_deriv_product (f g : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (v : ℝ) :
    deriv (deriv (fun w => f w*g w)) v =
      deriv (deriv f) v*g v+2*deriv f v*deriv g v+f v*deriv (deriv g) v := by
  have hd := hf.differentiable (by norm_num)
  have he := hg.differentiable (by norm_num)
  have heq : deriv (fun w => f w*g w) =
      fun w => deriv f w*g w+f w*deriv g w := by
    funext w
    exact deriv_fun_mul (hd w) (he w)
  have h₁ : DifferentiableAt ℝ (fun w => deriv f w*g w) v :=
    (hf.differentiable_deriv_two v).mul (he v)
  have h₂ : DifferentiableAt ℝ (fun w => f w*deriv g w) v :=
    (hd v).mul (hg.differentiable_deriv_two v)
  rw [heq, deriv_fun_add h₁ h₂,
    deriv_fun_mul (hf.differentiable_deriv_two v) (he v),
    deriv_fun_mul (hd v) (hg.differentiable_deriv_two v)]
  ring

/-- Exact physical cutoff product rule, with only the actual slice regularity. -/
theorem spatialCutoffTest_operator (a : ℝ → ℝ → ℝ) (chi psi : ℝ → ℝ)
    (hchi : ContDiff ℝ 2 chi) (hpsi : ContDiff ℝ 2 psi)
    (phi : Point → ℝ) (p : Point)
    (ht : DifferentiableAt ℝ (fun t => phi ⟨t, p.position, p.velocity⟩) p.time)
    (hx : DifferentiableAt ℝ (fun x => phi ⟨p.time, fun _ => x, p.velocity⟩)
      (p.position 0))
    (hv : ContDiff ℝ 2 (fun v => phi ⟨p.time, p.position, fun _ => v⟩)) :
    forwardScalarOperator a (spatialCutoffTest chi psi phi) p =
      chi (p.position 0)*psi (p.velocity 0)*forwardScalarOperator a phi p+
      p.velocity 0*deriv chi (p.position 0)*psi (p.velocity 0)*phi p+
      a (p.position 0) (p.velocity 0)*chi (p.position 0)*
        deriv (deriv psi) (p.velocity 0)*phi p+
      2*a (p.position 0) (p.velocity 0)*chi (p.position 0)*deriv psi (p.velocity 0)*
        kineticVelocityGradient phi p 0 := by
  have hc := hchi.differentiable (by norm_num)
  have htime : kineticTimeDerivative (spatialCutoffTest chi psi phi) p =
      chi (p.position 0)*psi (p.velocity 0)*kineticTimeDerivative phi p := by
    change deriv (fun t => (chi (p.position 0)*psi (p.velocity 0))*
      phi ⟨t, p.position, p.velocity⟩) p.time = _
    exact deriv_const_mul _ ht
  have hposition : kineticPositionGradient (spatialCutoffTest chi psi phi) p 0 =
      deriv chi (p.position 0)*psi (p.velocity 0)*phi p+
        chi (p.position 0)*psi (p.velocity 0)*kineticPositionGradient phi p 0 := by
    rw [kineticPositionGradient_scalar, kineticPositionGradient_scalar]
    change deriv (fun x => (chi x*psi (p.velocity 0))*
      phi ⟨p.time, fun _ => x, p.velocity⟩) (p.position 0) = _
    rw [deriv_fun_mul ((hc _).mul_const _) hx, deriv_mul_const (hc _) _]
    have he : phi ⟨p.time, fun _ => p.position 0, p.velocity⟩ = phi p := by
      congr 1
      ext i
      · rfl
      · rw [Fin.eq_zero i]
      · rfl
    rw [he]
  have hvelocity : kineticVelocityHessian (spatialCutoffTest chi psi phi) p 0 0 =
      chi (p.position 0)*
        (deriv (deriv psi) (p.velocity 0)*phi p+
          2*deriv psi (p.velocity 0)*kineticVelocityGradient phi p 0+
          psi (p.velocity 0)*kineticVelocityHessian phi p 0 0) := by
    rw [kineticVelocityHessian_scalar, kineticVelocityHessian_scalar,
      kineticVelocityGradient_scalar]
    have he : (fun v => spatialCutoffTest chi psi phi
        ⟨p.time, p.position, fun _ => v⟩) =
        fun v => chi (p.position 0)*(psi v*phi ⟨p.time, p.position, fun _ => v⟩) := by
      funext v
      dsimp [spatialCutoffTest]
      ring
    rw [he, deriv_const_mul_field', deriv_const_mul_field,
      second_deriv_product psi _ hpsi hv]
    have he' : phi ⟨p.time, p.position, fun _ => p.velocity 0⟩ = phi p := by
      congr 1
      ext i
      · rfl
      · rfl
      · rw [Fin.eq_zero i]
    rw [he']
  dsimp [forwardScalarOperator]
  rw [htime, hposition, hvelocity]
  ring


/-- Bound the three product-error terms from scalar cutoff and barrier bounds. -/
theorem cutoff_error_abs_le (a Lam v chi psi dx dv dvv phi phiv DX DV DVV B0 B1 : ℝ)
    (ha : 0 ≤ a) (haL : a ≤ Lam) (hc : |chi| ≤ 1) (hp : |psi| ≤ 1)
    (hx : |dx| ≤ DX) (hv : |dv| ≤ DV) (hvv : |dvv| ≤ DVV)
    (hb : |phi| ≤ B0) (hbv : |phiv| ≤ B1) :
    |v*dx*psi*phi+a*chi*dvv*phi+2*a*chi*dv*phiv| ≤
      |v| *DX*B0+Lam*DVV*B0+2*Lam*DV*B1 := by
  have hDX := (abs_nonneg dx).trans hx
  have hDV := (abs_nonneg dv).trans hv
  have hDVV := (abs_nonneg dvv).trans hvv
  have hLam := ha.trans haL
  have ha' : |a| ≤ Lam := by rwa [abs_of_nonneg ha]
  have h₁ : |v*dx*psi*phi| ≤ |v| *DX*B0 := by
    simp
    calc
      _ ≤ |v| *DX*1*B0 := by gcongr
      _ = _ := by ring
  have h₂ : |a*chi*dvv*phi| ≤ Lam*DVV*B0 := by
    simp
    calc
      _ ≤ Lam*1*DVV*B0 := by gcongr
      _ = _ := by ring
  have h₃ : |2*a*chi*dv*phiv| ≤ 2*Lam*DV*B1 := by
    simp
    calc
      _ ≤ 2*Lam*1*DV*B1 := by gcongr
      _ = _ := by ring
  linarith only [(abs_add_le (v*dx*psi*phi+a*chi*dvv*phi) (2*a*chi*dv*phiv)).trans (add_le_add (abs_add_le _ _) le_rfl), h₁, h₂, h₃]


/-- Rescale a scalar cutoff by its physical radius. -/
def scaledScalarCutoff (chi : ℝ → ℝ) (R : ℝ) : ℝ → ℝ := fun s => chi (s/R)

/-- Scalar rescaling preserves C² regularity. -/
theorem scaledScalarCutoff_contDiff (chi : ℝ → ℝ) (hchi : ContDiff ℝ 2 chi)
    (R : ℝ) : ContDiff ℝ 2 (scaledScalarCutoff chi R) :=
  hchi.comp (contDiff_id.div_const R)

/-- The first derivative has the exact inverse-radius factor. -/
theorem scaledScalarCutoff_deriv (chi : ℝ → ℝ) (hchi : ContDiff ℝ 2 chi)
    (R s : ℝ) :
    deriv (scaledScalarCutoff chi R) s = deriv chi (s/R)/R := by
  change deriv (chi ∘ (fun t => t/R)) s = _
  simpa [one_div, div_eq_mul_inv] using (((hchi.differentiable (by norm_num) (s/R)).hasDerivAt).comp s ((hasDerivAt_id s).div_const R)).deriv

/-- The second derivative has the exact inverse-square radius factor. -/
theorem scaledScalarCutoff_second_deriv (chi : ℝ → ℝ) (hchi : ContDiff ℝ 2 chi)
    {R : ℝ} (hR : R ≠ 0) (s : ℝ) :
    deriv (deriv (scaledScalarCutoff chi R)) s = deriv (deriv chi) (s/R)/R^2 := by
  have he : deriv (scaledScalarCutoff chi R) = fun t => deriv chi (t/R)/R := by
    funext t
    exact scaledScalarCutoff_deriv chi hchi R t
  rw [he]
  have hd : deriv (fun t => deriv chi (t/R)/R) s =
      (deriv (deriv chi) (s/R)*(1/R))/R := by
    simpa using ((((hchi.differentiable_deriv_two (s/R)).hasDerivAt).comp s ((hasDerivAt_id s).div_const R)).div_const R).deriv
  rw [hd]
  field_simp

/-- Uniform first-derivative bounds acquire one inverse-radius factor. -/
theorem scaledScalarCutoff_deriv_bound (chi : ℝ → ℝ) (hchi : ContDiff ℝ 2 chi)
    {R : ℝ} (hR : 0 < R) (C : ℝ) (hC : ∀ s, |deriv chi s| ≤ C) (s : ℝ) :
    |deriv (scaledScalarCutoff chi R) s| ≤ C/R := by
  rw [scaledScalarCutoff_deriv chi hchi, abs_div, abs_of_pos hR]
  exact div_le_div_of_nonneg_right (hC _) hR.le

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

