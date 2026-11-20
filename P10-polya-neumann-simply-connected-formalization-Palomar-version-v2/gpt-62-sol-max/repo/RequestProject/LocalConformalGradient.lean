module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import RequestProject.LocalConformalPullback

/-!
# The actual weak gradient pairing under conformal pullback

The already proved all-H¹ gradient energy identity is polarized over ℂ.
This gives the full sesquilinear gradient form, including nonsmooth H¹
solutions tested against physical inverse-coordinate test functions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric
open scoped InnerProductSpace

theorem inner_eq_of_linear_norm_sq
    {V E F : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (A : V →ₗ[ℂ] E) (B : V →ₗ[ℂ] F)
    (h : ∀ u, ‖A u‖ ^ 2 = ‖B u‖ ^ 2) (u v : V) :
    ⟪A u, A v⟫_ℂ = ⟪B u, B v⟫_ℂ := by
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  simp only [← map_add, ← map_sub, ← map_smul, ← RCLike.ofReal_pow, h]

def h1GradientVector (Ω : Set ℂ) :
    NeumannH1 Ω →L[ℂ] PiLp 2 (fun _ : Fin 2 => L2 Ω) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => L2 Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => h1Gradient Ω i))

@[simp] theorem h1GradientVector_apply (Ω : Set ℂ) (u : NeumannH1 Ω) (i : Fin 2) :
    h1GradientVector Ω u i = h1Gradient Ω i u := rfl

theorem norm_sq_h1GradientVector (Ω : Set ℂ) (u : NeumannH1 Ω) :
    ‖h1GradientVector Ω u‖ ^ 2 = ∑ i : Fin 2, ‖h1Gradient Ω i u‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ _

section

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
local notation "D" => ball (0 : ℂ) 1
local notation "Ω" => F '' D

theorem localConformalH1Pullback_gradient_inner (u v : NeumannH1 Ω) :
    (∑ i : Fin 2, ⟪h1Gradient D i (coords.pullback u), h1Gradient D i (coords.pullback v)⟫_ℂ) =
      ∑ i : Fin 2, ⟪h1Gradient Ω i u, h1Gradient Ω i v⟫_ℂ := by
  let A := (h1GradientVector D).comp coords.pullback
  have hn (w : NeumannH1 Ω) : ‖A w‖ ^ 2 = ‖h1GradientVector Ω w‖ ^ 2 := by
    simpa only [A, ContinuousLinearMap.comp_apply, norm_sq_h1GradientVector] using
      localConformalH1Pullback_gradient_energy coords w
  simpa only [A, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, PiLp.inner_apply,
    h1GradientVector_apply] using
    inner_eq_of_linear_norm_sq A.toLinearMap (h1GradientVector Ω).toLinearMap hn u v

end

end PolyaNeumann

end
