module

public import RequestProject.LocalConformalH1
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

variable {R : ℝ} {C : ℝ}

local notation "Φ0" => ball 0 1

def localConformalH1Pullback  (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hL : IsLipschitzDomain (F '' Φ0)) :
    NeumannH1 (F '' Φ0) →L[ℂ] NeumannH1 (Φ0) :=
  ((smoothTraceH1Lin isOpen_ball).comp (smoothDiskCompositionLin hR F hFs)).extendOfNorm (smoothTraceH1Lin hL.1.1)

theorem localConformalH1Pullback_smooth  (hR : 1 < R) F
    hFs
    (hb : Bornology.IsBounded (F '' Φ0))
    hL
    (hhol : DifferentiableOn ℂ F (Φ0))
    (hinj : InjOn F (Φ0)) 
    (hC : ∀ z ∈ Φ0, 1 ≤ C * ‖deriv F z‖ ^ 2)
    f :
    localConformalH1Pullback hR F hFs hL (smoothTraceH1 (F '' Φ0) f) =
      smoothTraceH1 (Φ0) (smoothDiskCompositionLin hR F hFs f) := by
  exact LinearMap.extendOfNorm_eq (denseRange_smoothTraceH1Lin hb hL)
    ⟨Real.sqrt (max C 1), norm_smoothDiskCompositionH1_le hR F hFs hhol hinj hC⟩ f

theorem gradient_energy_smoothTraceH1 (U : Set ℂ) f :
    (∑ i : Fin 2, ‖h1Gradient U i (smoothTraceH1 U f)‖ ^ 2) =
      ∫ z in U, gradSq (f : ℂ → ℂ) z := by
  rw [Fin.sum_univ_two]
  simp only [h1Gradient_smoothTraceH1, norm_sq_toLp_eq_integral]
  rw [← integral_add ((smoothTraceTests_memLp_deriv U f 0).integrable_norm_pow (by decide : 2 ≠ 0)) ((smoothTraceTests_memLp_deriv U f 1).integrable_norm_pow (by decide : 2 ≠ 0))]
  rfl

theorem localConformalH1Pullback_gradient_energy  (hR : 1 < R) F
    hFs
    (hb : Bornology.IsBounded (F '' Φ0))
    hL
    (hhol : DifferentiableOn ℂ F (Φ0))
    (hinj : InjOn F (Φ0)) 
    (hC : ∀ z ∈ Φ0, 1 ≤ C * ‖deriv F z‖ ^ 2)
    u :
    (∑ i : Fin 2, ‖h1Gradient (Φ0) i (localConformalH1Pullback hR F hFs hL u)‖ ^ 2) =
      ∑ i : Fin 2, ‖h1Gradient (F '' Φ0) i u‖ ^ 2 := by
  exact congrFun (show (fun u => ∑ i : Fin 2, ‖h1Gradient (Φ0) i (localConformalH1Pullback hR F hFs hL u)‖ ^ 2) = (fun u => ∑ i : Fin 2, ‖h1Gradient (F '' Φ0) i u‖ ^ 2) by
    apply (denseRange_smoothTraceH1Lin hb hL).equalizer
    · exact continuous_finset_sum _ (fun i _ =>
        (((h1Gradient (Φ0) i).continuous.comp
          (localConformalH1Pullback hR F hFs hL).continuous).norm.pow 2))
    · exact continuous_finset_sum _ (fun i _ =>
        ((h1Gradient (F '' Φ0) i).continuous.norm.pow 2))
    · funext f
      change (∑ i : Fin 2, ‖h1Gradient (Φ0) i
        (localConformalH1Pullback hR F hFs hL (smoothTraceH1 (F '' Φ0) f))‖ ^ 2) =
        ∑ i : Fin 2, ‖h1Gradient (F '' Φ0) i
          (smoothTraceH1 (F '' Φ0) f)‖ ^ 2
      rw [localConformalH1Pullback_smooth hR F hFs hb hL hhol hinj hC f,
        gradient_energy_smoothTraceH1, gradient_energy_smoothTraceH1]
      exact integral_gradSq_smoothDiskComposition hR F hFs hhol hinj f) u

end PolyaNeumann

end
