module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

def smoothDiskPullbackH1Lin {R : ℝ} (hR : 1 < R) (F : PlaneMap)
    (hFs : RealSmoothOnBall F R) :
    smoothTraceTests →ₗ[ℂ] NeumannH1 unitDisk :=
  (smoothTraceH1Lin isOpen_ball).comp (smoothDiskCompositionLin hR F hFs)

def localConformalH1Pullback {R : ℝ} (hR : 1 < R) (F : PlaneMap)
    (hFs : RealSmoothOnBall F R)
    (hL : IsLipschitzDomain (F '' unitDisk)) :
    NeumannH1 (F '' unitDisk) →L[ℂ] NeumannH1 unitDisk :=
  (smoothDiskPullbackH1Lin hR F hFs).extendOfNorm (smoothTraceH1Lin hL.1.1)

section
variable {R } (hR : 1 < R) (F ) (hFs : RealSmoothOnBall F R) (hb : Bornology.IsBounded (F '' unitDisk)) (hL : IsLipschitzDomain (F '' unitDisk)) (hhol : DifferentiableOn ℂ F unitDisk) (hinj : InjOn F unitDisk) {C } (hC : DiskInverseJacobianBound F C)

include R hR F hFs hb hL hhol hinj C hC in
theorem localConformalH1Pullback_smooth
    f :
    localConformalH1Pullback hR F hFs hL (smoothTraceH1 (F '' unitDisk) f) =
      smoothTraceH1 unitDisk (smoothDiskCompositionLin hR F hFs f) := LinearMap.extendOfNorm_eq (denseRange_smoothTraceH1Lin hb hL)
    ⟨Real.sqrt (max C 1), norm_smoothDiskCompositionH1_le hR F hFs hhol hinj hC⟩ f

theorem gradient_energy_smoothTraceH1 U f :
    (∑ i : Coord, ‖h1Gradient U i (smoothTraceH1 U f)‖ ^ 2) =
      ∫ z in U, gradSq (f : PlaneMap) z := by
  rw [Fin.sum_univ_two]
  simp only [h1Gradient_smoothTraceH1, norm_sq_toLp_eq_integral]
  have h0 := (smoothTraceTests_memLp_deriv U f 0).integrable_norm_pow
    (by decide)
  have h1 := (smoothTraceTests_memLp_deriv U f 1).integrable_norm_pow
    (by decide)
  rw [← integral_add h0 h1]
  rfl

include R hR F hFs hb hL hhol hinj C hC in
theorem localConformalH1Pullback_gradient_energy
    u :
    (∑ i : Coord, ‖h1Gradient unitDisk i (localConformalH1Pullback hR F hFs hL u)‖ ^ 2) =
      ∑ i : Coord, ‖h1Gradient (F '' unitDisk) i u‖ ^ 2 := by
  have heq : (fun u => ∑ i : Coord,
      ‖h1Gradient unitDisk i (localConformalH1Pullback hR F hFs hL u)‖ ^ 2) =
      (fun u => ∑ i : Coord, ‖h1Gradient (F '' unitDisk) i u‖ ^ 2) := by
    apply (denseRange_smoothTraceH1Lin hb hL).equalizer
    · fun_prop
    · fun_prop
    · funext f
      change (∑ i : Coord, ‖h1Gradient (ball 0 1) i
        (localConformalH1Pullback hR F hFs hL (smoothTraceH1 (F '' ball 0 1) f))‖ ^ 2) =
        ∑ i : Coord, ‖h1Gradient (F '' ball 0 1) i
          (smoothTraceH1 (F '' ball 0 1) f)‖ ^ 2
      rw [localConformalH1Pullback_smooth hR F hFs hb hL hhol hinj hC f,
        gradient_energy_smoothTraceH1, gradient_energy_smoothTraceH1]
      exact integral_gradSq_smoothDiskComposition hR F hFs hhol hinj f
  exact congrFun heq u

end


end PolyaNeumann

end
