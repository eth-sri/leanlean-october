module
public import Glennie.Compact.NativeDefectReadoutR01

/- Composed generic cyclic-trace compatible target, with concrete specializations.
Source norm and response bindings use existing proved native producers.
No unit preservation, surjectivity or small-defect assumption is imposed on f. -/
@[expose] public section
namespace Glennie.Compact.CompatibleDefectReadoutR01
open Glennie.Compact.MultiplicationDefectR01
open Glennie.Compact.CyclicTraceNullR01
open Glennie.Compact.NativeNormKernel
open Glennie.Compact.NativeDefectReadoutR01
open Glennie.Compact.ReadoutRobustnessR01

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Ring M] [Algebra ℝ M]

 theorem native_compatible_defect_response
    (jE : Product E) (f : Albert →ₗᵢ[ℝ] E)
    (hE : ∀ a b, ‖jE a b‖ ≤ ‖a‖*‖b‖)
    (hUE : ∀ a b, ‖Q jE a b‖ ≤ ‖a‖^2*‖b‖)
    (ρ : E →ₗ[ℝ] M) (τ : M →ₗ[ℝ] ℝ)
    (hj : ∀ a b, ρ (jE a b) = symmProd (ρ a) (ρ b))
    (hB : ∀ a b, Inner.inner ℝ a b = τ (ρ a*ρ b))
    (hcyclic : ∀ a b : M, τ (a*b) = τ (b*a))
    (μ R : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hdef : ∀ a b : Albert, ‖f (jordan a b)-jE (f a) (f b)‖ ≤ μ*‖a‖*‖b‖)
    (x y z : Albert) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |phi x y z| ≤ 38*μ*R^9 := by
  have h := response_bound_of_compatible_trace jordanLinear jE f jordan_norm hE U_norm hUE
    ρ τ hj hB hcyclic μ hμ hdef R hR x y z hx hy hz
  simpa [native_response_eq] using h

 /-- Actual-frame six-readout measured margin for every compatible target and isometry.
The uniform defect premise ranges over ALL native inputs, not only observed marks. -/
 theorem frame_noisy_compatible_defect_lower
    (jE : Product E) (f : Albert →ₗᵢ[ℝ] E)
    (hE : ∀ a b, ‖jE a b‖ ≤ ‖a‖*‖b‖)
    (hUE : ∀ a b, ‖Q jE a b‖ ≤ ‖a‖^2*‖b‖)
    (ρ : E →ₗ[ℝ] M) (τ : M →ₗ[ℝ] ℝ)
    (hj : ∀ a b, ρ (jE a b) = symmProd (ρ a) (ρ b))
    (hB : ∀ a b, Inner.inner ℝ a b = τ (ρ a*ρ b))
    (hcyclic : ∀ a b : M, τ (a*b) = τ (b*a))
    (T : Glennie.Compact.Affine20.Triple) (hT : ∀ a : Fin 3, Frame (T a))
    (noisy : Readouts) (ε μ : ℝ) (hμ : 0 ≤ μ)
    (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hdef : ∀ a b : Albert, ‖f (jordan a b)-jE (f a) (f b)‖ ≤ μ*‖a‖*‖b‖) :
    (|weightedScore noisy|-12*ε)/(1216*Real.sqrt 2) ≤ μ :=
  frame_readout_lower T hT noisy ε μ hreadout
    (native_compatible_defect_response jE f hE hUE ρ τ hj hB hcyclic μ _ hμ (Real.sqrt_nonneg 2) hdef)

end Glennie.Compact.CompatibleDefectReadoutR01
