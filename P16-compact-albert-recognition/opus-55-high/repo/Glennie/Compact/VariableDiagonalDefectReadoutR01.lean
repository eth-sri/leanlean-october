/- A composed noisy-readout obstruction for every isometric map into a
   dimension-parametric coordinatewise Euclidean special target. -/
module
public import Glennie.Compact.VariableDiagonalNullTargetR01
public import Glennie.Compact.NativeDefectReadoutR01

@[expose] public section
namespace Glennie.Compact.VariableDiagonalDefectReadoutR01
open Glennie.Compact.MultiplicationDefectR01
open Glennie.Compact.NativeDefectReadoutR01
open Glennie.Compact.VariableDiagonalNullTargetR01
open Glennie.Compact.NativeNormKernel
open Glennie.Compact.ReadoutRobustnessR01

def diagonalNProductLinear (n : ℕ) : Product (DiagonalN n) where
  toFun a := {
    toFun := diagonalNProduct a
    map_add' b c := by ext i; exact mul_add (a i) (b i) (c i)
    map_smul' r b := by ext i; exact mul_left_comm (a i) r (b i)
  }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    ext i
    exact add_mul (a i) (b i) (c i)
  map_smul' r a := by
    apply LinearMap.ext
    intro c
    ext i
    exact mul_assoc r (a i) (c i)

@[simp] theorem diagonalNProductLinear_apply {n : ℕ} (a b : DiagonalN n) :
    diagonalNProductLinear n a b = diagonalNProduct a b := rfl

theorem diagonalN_response_zero {n : ℕ} (x y z : DiagonalN n) :
    response (diagonalNProductLinear n) x y z = 0 := by
  simpa [response, diagonalNProductLinear_apply] using
    diagonalN_phi_zero x y z

/-- Uniform all-input product defect for any linear isometry into the
coordinatewise target, without a unitality or surjectivity premise. -/
theorem native_diagonalN_defect_response {n : ℕ}
    (f : Albert →ₗᵢ[ℝ] DiagonalN n) (μ R : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hdef : ∀ a b : Albert,
      ‖f (jordan a b) - diagonalNProduct (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖)
    (x y z : Albert) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |phi x y z| ≤ 38 * μ * R^9 := by
  have h := response_discrepancy_radius jordanLinear (diagonalNProductLinear n)
    f jordan_norm diagonalN_product_norm U_norm diagonalN_quadratic_norm μ hμ hdef R hR x y z hx hy hz
  rwa [native_response_eq, diagonalN_response_zero, sub_zero] at h

/-- For actual ordered frames, six errors and any isometry to a concrete
coordinatewise null target give a lower bound on its uniform product defect. -/
theorem frame_noisy_diagonalN_defect_lower {n : ℕ}
    (f : Albert →ₗᵢ[ℝ] DiagonalN n)
    (T : Glennie.Compact.Affine20.Triple)
    (hT : ∀ a : Fin 3, Frame (T a))
    (noisy : Readouts) (ε μ : ℝ) (hμ : 0 ≤ μ)
    (hreadout : ErrorsAtMost noisy (exactReadouts T) ε)
    (hdef : ∀ a b : Albert,
      ‖f (jordan a b) - diagonalNProduct (f a) (f b)‖ ≤
        μ * ‖a‖ * ‖b‖) :
    (|weightedScore noisy|-12*ε)/(1216*Real.sqrt 2) ≤ μ :=
  frame_readout_lower T hT noisy ε μ hreadout (native_diagonalN_defect_response f μ _ hμ (Real.sqrt_nonneg 2) hdef)

end Glennie.Compact.VariableDiagonalDefectReadoutR01
