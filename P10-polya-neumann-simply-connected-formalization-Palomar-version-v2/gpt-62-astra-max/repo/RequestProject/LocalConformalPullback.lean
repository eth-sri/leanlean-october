module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalH1
public import Mathlib.Topology.Order.Compact
public import RequestProject.PlanarNotation

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

variable (Φ : ConformalDiskMap) (U : Set ℂ) (f : smoothTraceTests)

def smoothDiskPullbackH1Lin (Φ : SmoothDiskMap) :
    smoothTraceTests →ₗ[ℂ] NeumannH1 unitDisk :=
  (smoothTraceH1Lin isOpen_ball).comp (smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth)

def SmoothDiskMap.h1Pullback (Φ : SmoothDiskMap)
    (hL : IsLipschitzDomain Φ.domain) :
    NeumannH1 Φ.domain →L[ℂ] NeumannH1 unitDisk :=
  (smoothDiskPullbackH1Lin Φ).extendOfNorm (smoothTraceH1Lin hL.1.1)

theorem localConformalH1Pullback_smooth :
    Φ.h1Pullback Φ.lipschitzDomain (smoothTraceH1 Φ.domain f) =
      smoothTraceH1 unitDisk (smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f) := LinearMap.extendOfNorm_eq (denseRange_smoothTraceH1Lin Φ.bounded Φ.lipschitzDomain)
    ⟨Real.sqrt (max Φ.C 1), norm_smoothDiskCompositionH1_le Φ Φ.holomorphic Φ.inj Φ.deriv_lower⟩ f

theorem gradient_energy_smoothTraceH1 :
    (∑ i : Fin 2, ‖h1Gradient U i (smoothTraceH1 U f)‖ ^ 2) =
      ∫ z in U, gradSq (f : ℂ → ℂ) z := by
  rw [Fin.sum_univ_two]
  simp only [h1Gradient_smoothTraceH1, norm_sq_toLp_eq_integral]
  have h0 := (smoothTraceTests_memLp_deriv U f 0).integrable_norm_pow
    (by decide : 2 ≠ 0)
  have h1 := (smoothTraceTests_memLp_deriv U f 1).integrable_norm_pow
    (by decide : 2 ≠ 0)
  rw [← integral_add h0 h1]
  rfl

theorem localConformalH1Pullback_gradient_energy
    (u : NeumannH1 Φ.domain) :
    (∑ i : Fin 2, ‖h1Gradient unitDisk i (Φ.h1Pullback Φ.lipschitzDomain u)‖ ^ 2) =
      ∑ i : Fin 2, ‖h1Gradient Φ.domain i u‖ ^ 2 := by
  have heq : (fun u => ∑ i : Fin 2,
      ‖h1Gradient unitDisk i (Φ.h1Pullback Φ.lipschitzDomain u)‖ ^ 2) =
      (fun u => ∑ i : Fin 2, ‖h1Gradient Φ.domain i u‖ ^ 2) := by
    apply (denseRange_smoothTraceH1Lin Φ.bounded Φ.lipschitzDomain).equalizer
    · exact continuous_finset_sum _ (fun i _ =>
        (((h1Gradient unitDisk i).continuous.comp
          (Φ.h1Pullback Φ.lipschitzDomain).continuous).norm.pow 2))
    · fun_prop
    · funext f
      change (∑ i : Fin 2, ‖h1Gradient unitDisk i
        (Φ.h1Pullback Φ.lipschitzDomain (smoothTraceH1 Φ.domain f))‖ ^ 2) =
        ∑ i : Fin 2, ‖h1Gradient Φ.domain i
          (smoothTraceH1 Φ.domain f)‖ ^ 2
      rw [localConformalH1Pullback_smooth Φ f,
        gradient_energy_smoothTraceH1, gradient_energy_smoothTraceH1]
      exact integral_gradSq_smoothDiskComposition Φ Φ.holomorphic Φ.inj f
  exact congrFun heq u

end

end PolyaNeumann

end
