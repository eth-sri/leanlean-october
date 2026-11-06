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


noncomputable section

namespace PolyaNeumann

open Set Metric
open scoped InnerProductSpace ContDiff

private theorem inner_eq_of_linear_norm_sq
    {V E F : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (A : V →ₗ[ℂ] E) (B : V →ₗ[ℂ] F)
    (h : ∀ u, ‖A u‖ ^ 2 = ‖B u‖ ^ 2) u v :
    ⟪A u, A v⟫_ℂ = ⟪B u, B v⟫_ℂ := by
  apply Complex.ext
  · change RCLike.re ⟪A u, A v⟫_ℂ = RCLike.re ⟪B u, B v⟫_ℂ
    simp only [re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four,
      ← map_add, ← map_sub, ← sq, h]
  · change RCLike.im ⟪A u, A v⟫_ℂ = RCLike.im ⟪B u, B v⟫_ℂ
    simp only [im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four,
      ← map_smul, ← map_add, ← map_sub, ← sq, h]

def h1GradientVector Ω :
    NeumannH1 Ω →L[ℂ] PiLp 2 (fun _ : Fin 2 => L2 Ω) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => L2 Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => h1Gradient Ω i))

@[simp] theorem h1GradientVector_apply Ω u i :
    h1GradientVector Ω u i = h1Gradient Ω i u := rfl

theorem norm_sq_h1GradientVector (Ω : Set ℂ) u :
    ‖h1GradientVector Ω u‖ ^ 2 = ∑ i : Fin 2, ‖h1Gradient Ω i u‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ _

local notation "Φ0" => ball 0 1

theorem localConformalH1Pullback_gradient_inner {R : ℝ} (hR : 1 < R) F
    hFs
    (hb : Bornology.IsBounded (F '' Φ0))
    hL
    (hhol : DifferentiableOn ℂ F (Φ0))
    (hinj : InjOn F (Φ0)) {C : ℝ}
    (hC : ∀ z ∈ Φ0, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (u v : NeumannH1 (F '' Φ0)) :
    (∑ i : Fin 2, ⟪h1Gradient (Φ0) i (localConformalH1Pullback hR F hFs hL u),
      h1Gradient (Φ0) i (localConformalH1Pullback hR F hFs hL v)⟫_ℂ) =
      ∑ i : Fin 2, ⟪h1Gradient (F '' Φ0) i u,
        h1Gradient (F '' Φ0) i v⟫_ℂ := by
  let A := (h1GradientVector (Φ0)).comp (localConformalH1Pullback hR F hFs hL)
  let B := h1GradientVector (F '' Φ0)
  have hn (w : NeumannH1 (F '' Φ0)) : ‖A w‖ ^ 2 = ‖B w‖ ^ 2 := by
    change ‖h1GradientVector (Φ0) (localConformalH1Pullback hR F hFs hL w)‖ ^ 2 = _
    rw [norm_sq_h1GradientVector, norm_sq_h1GradientVector]
    exact localConformalH1Pullback_gradient_energy hR F hFs hb hL hhol hinj hC w
  have hi := inner_eq_of_linear_norm_sq A.toLinearMap B.toLinearMap hn u v
  change ⟪h1GradientVector (Φ0) (localConformalH1Pullback hR F hFs hL u),
    h1GradientVector (Φ0) (localConformalH1Pullback hR F hFs hL v)⟫_ℂ =
      ⟪h1GradientVector (F '' Φ0) u, h1GradientVector (F '' Φ0) v⟫_ℂ at hi
  simpa [PiLp.inner_apply] using hi

end PolyaNeumann

end
