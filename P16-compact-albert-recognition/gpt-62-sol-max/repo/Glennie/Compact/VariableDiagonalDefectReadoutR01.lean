/- A composed noisy-readout obstruction for every isometric map into a
   dimension-parametric coordinatewise Euclidean special target. -/
module
public import Glennie.Compact.VariableDiagonalNullTargetR01
public import Glennie.Compact.NativeDefectReadoutR01
@[expose] public section
namespace Glennie.Compact.VariableDiagonalDefectReadoutR01
open Glennie
open Glennie.Compact.CyclicTraceNullR01
open Glennie.Compact.MultiplicationDefectR01
open Glennie.Compact.NativeDefectReadoutR01
open Glennie.Compact.VariableDiagonalNullTargetR01
open Glennie.Compact.NativeNormKernel
open Glennie.Compact.ReadoutRobustnessR01
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

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
  simpa only [response, diagonalNProductLinear_apply] using
    diagonalN_phi_zero x y z

/-- Uniform all-input product defect for any linear isometry into the
coordinatewise target, without a unitality or surjectivity premise. -/
theorem native_diagonalN_defect_response {n : ℕ}
    (f : Albert →ₗᵢ[ℝ] DiagonalN n) (μ R : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hdef : ∀ a b : Albert,
      ‖f (jordan a b) - diagonalNProduct (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖)
    (x y z : Albert) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |phi x y z| ≤ 38 * μ * R^9 := by
  exact native_defect_response (diagonalNProductLinear n) f diagonalN_product_norm
    diagonalN_quadratic_norm μ R hμ hR hdef x y z hx hy hz (diagonalN_response_zero (f x) (f y) (f z))


end
end Glennie.Compact.VariableDiagonalDefectReadoutR01
