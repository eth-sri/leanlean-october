module

public import RequestProject.LocalConformalH1
public import RequestProject.ConformalDiskCoordinates
public import Mathlib.Topology.Order.Compact

/-!
# Dense extension of the actual local conformal H¹ pullback

The norm bound is proved from the geometric Jacobian lower bound, rather
than assumed for an H¹ composition operator. Agreement on every smooth
restriction determines the resulting continuous linear map uniquely.
Gradient energy invariance extends to all genuine H¹ vectors.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped Real ContDiff Topology ENNReal

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
include R hR F hFs

def smoothDiskPullbackH1Lin  :
    smoothTraceTests →ₗ[ℂ] NeumannH1 (ball (0 : ℂ) 1) :=
  (smoothTraceH1Lin isOpen_ball).comp (smoothDiskCompositionLin hR F hFs)

def localConformalH1Pullback 
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1)) :
    NeumannH1 (F '' ball (0 : ℂ) 1) →L[ℂ] NeumannH1 (ball (0 : ℂ) 1) :=
  (smoothDiskPullbackH1Lin hR F hFs).extendOfNorm (smoothTraceH1Lin hL.1.1)

theorem localConformalH1Pullback_smooth 
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (f : smoothTraceTests) :
    localConformalH1Pullback hR F hFs hL (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) =
      smoothTraceH1 (ball (0 : ℂ) 1) (smoothDiskCompositionLin hR F hFs f) := by
  exact LinearMap.extendOfNorm_eq (denseRange_smoothTraceH1Lin hb hL)
    ⟨Real.sqrt (max C 1), norm_smoothDiskCompositionH1_le hR F hFs hhol hinj hC⟩ f

end

abbrev ConformalDiskCoordinates.pullback {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F) :
    NeumannH1 (F '' ball 0 1) →L[ℂ] NeumannH1 (ball 0 1) :=
  localConformalH1Pullback coords.one_lt_radius F coords.smooth coords.lipschitz

theorem ConformalDiskCoordinates.real_fderiv_apply {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
    {z : ℂ} (hz : z ∈ closedBall 0 1) (v : ℂ) : fderiv ℝ F z v = deriv F z * v := by
  rw [(coords.differentiableAt_closed hz).fderiv_restrictScalars ℝ]
  exact fderiv_eq_deriv_mul

theorem gradient_energy_smoothTraceH1 (U : Set ℂ) (f : smoothTraceTests) :
    (∑ i : Fin 2, ‖h1Gradient U i (smoothTraceH1 U f)‖ ^ 2) =
      ∫ z in U, gradSq (f : ℂ → ℂ) z := by
  rw [Fin.sum_univ_two]
  simp only [h1Gradient_smoothTraceH1, norm_sq_toLp_eq_integral]
  have h0 := (smoothTraceTests_memLp_deriv U f 0).integrable_norm_pow
    (by decide : (2 : ℕ) ≠ 0)
  have h1 := (smoothTraceTests_memLp_deriv U f 1).integrable_norm_pow
    (by decide : (2 : ℕ) ≠ 0)
  rw [← integral_add h0 h1]
  rfl

section

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
local notation "D" => ball (0 : ℂ) 1
local notation "Ω" => F '' D

theorem localConformalH1Pullback_gradient_energy (u : NeumannH1 Ω) :
    (∑ i : Fin 2, ‖h1Gradient D i (coords.pullback u)‖ ^ 2) =
      ∑ i : Fin 2, ‖h1Gradient Ω i u‖ ^ 2 := by
  refine (denseRange_smoothTraceH1Lin coords.bounded coords.lipschitz).induction_on
    (p := fun w => (∑ i : Fin 2, ‖h1Gradient D i (coords.pullback w)‖ ^ 2) =
      ∑ i : Fin 2, ‖h1Gradient Ω i w‖ ^ 2) u ?_ ?_
  · apply isClosed_eq <;> fun_prop
  · intro f
    change (∑ i : Fin 2, ‖h1Gradient D i (coords.pullback (smoothTraceH1 Ω f))‖ ^ 2) =
      ∑ i : Fin 2, ‖h1Gradient Ω i (smoothTraceH1 Ω f)‖ ^ 2
    rw [localConformalH1Pullback_smooth coords.one_lt_radius F coords.smooth coords.bounded
      coords.lipschitz coords.holomorphic coords.injOn coords.lower,
      gradient_energy_smoothTraceH1, gradient_energy_smoothTraceH1]
    exact integral_gradSq_smoothDiskComposition coords.one_lt_radius F coords.smooth
      coords.holomorphic coords.injOn f

end

end PolyaNeumann

end
