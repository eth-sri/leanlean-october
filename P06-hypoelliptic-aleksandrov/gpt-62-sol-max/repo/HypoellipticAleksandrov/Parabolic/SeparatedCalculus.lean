module

public import HypoellipticAleksandrov.Parabolic.Derivatives
public import HypoellipticAleksandrov.Parabolic.SpatialCoordinateDerivatives
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # Calculus of separated space-time products -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic
open Set

/-- The support of a separated product is the product of the supports. -/
theorem tsupport_separated_mul {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → ℝ) (g : Y → ℝ) :
    tsupport (fun z : X × Y => f z.1 * g z.2) = tsupport f ×ˢ tsupport g := by
  have he : Function.support (fun z : X × Y => f z.1 * g z.2) =
      Function.support f ×ˢ Function.support g := by
    ext z
    simp [Function.mem_support]
  unfold tsupport
  rw [he, closure_prod_eq]

/-- A separated product differentiates by applying the derivatives to the two projections. -/
theorem fderiv_separated_mul {d : ℕ} {f : ℝ → ℝ} {g : PDE.Vec d → ℝ}
    {z : TimeVelocity d} (hf : DifferentiableAt ℝ f z.1) (hg : DifferentiableAt ℝ g z.2)
    (w : TimeVelocity d) :
    fderiv ℝ (fun p : TimeVelocity d => f p.1 * g p.2) z w =
      f z.1 * fderiv ℝ g z.2 w.2 + g z.2 * fderiv ℝ f z.1 w.1 := by
  let f₁ : TimeVelocity d → ℝ := f ∘ Prod.fst
  let g₂ : TimeVelocity d → ℝ := g ∘ Prod.snd
  change fderiv ℝ (f₁ * g₂) z w = _
  have h₁ := hf.comp z (differentiableAt_fst (𝕜 := ℝ))
  have h₂ := hg.comp z (differentiableAt_snd (𝕜 := ℝ))
  rw [fderiv_mul h₁ h₂]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  change f z.1 * fderiv ℝ g₂ z w + g z.2 * fderiv ℝ f₁ z w = _
  dsimp only [g₂, f₁]
  rw [fderiv_comp z hg differentiableAt_snd, fderiv_comp z hf differentiableAt_fst,
    fderiv_snd, fderiv_fst]
  rfl

section
variable {d : ℕ} {f : ℝ → ℝ} {g : PDE.Vec d → ℝ} {z : TimeVelocity d}
  (hf : DifferentiableAt ℝ f z.1) (hg : DifferentiableAt ℝ g z.2)
include hf hg

/-- The time derivative of the separated product acts on the time factor. -/
theorem timeDerivative_separated_mul :
    timeDerivative (fun p : TimeVelocity d => f p.1 * g p.2) z = deriv f z.1 * g z.2 := by
  rw [timeDerivative, fderiv_separated_mul hf hg]
  change f z.1 * (fderiv ℝ g z.2) 0 + g z.2 * (fderiv ℝ f z.1) 1 = _
  rw [map_zero, mul_zero, zero_add, fderiv_apply_one_eq_deriv, mul_comm]

/-- The spatial derivative of the separated product acts on the spatial factor. -/
theorem velocityGradient_separated_mul
    (i : Fin d) :
    velocityGradient (fun p : TimeVelocity d => f p.1 * g p.2) z i = f z.1 * spatialPartial i g z.2 := by
  rw [velocityGradient, fderiv_separated_mul hf hg]
  change f z.1 * fderiv ℝ g z.2 (PDE.basisVec i) + g z.2 * (fderiv ℝ f z.1) 0 = _
  rw [map_zero, mul_zero, add_zero]
  rfl

end

end HypoellipticAleksandrov.Parabolic
