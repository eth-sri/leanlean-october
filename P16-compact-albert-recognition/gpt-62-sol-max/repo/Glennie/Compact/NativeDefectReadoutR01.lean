module
public import Glennie.Compact.MultiplicationDefectR01
public import Glennie.Compact.NormCompatibleNullTargetR01
public import Glennie.Compact.MeasuredMarginR01
public import Glennie.Theorems.Frames

@[expose] public section
namespace Glennie.Compact.NativeDefectReadoutR01
open Glennie
open Glennie.Compact.MultiplicationDefectR01
open Glennie.Compact.CyclicTraceNullR01
open Glennie.Compact.NormCompatibleNullTargetR01
open Glennie.Compact.MeasuredMarginR01
open Glennie.Compact.NativeNormKernel
open Glennie.Compact.ReadoutRobustnessR01
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def diagonalProductLinear : Product Diagonal27 where
  toFun a := {
    toFun := diagonalProduct a
    map_add' b c := by
      rw [diagonal_product_comm a (b+c), diagonal_product_add_left,
        diagonal_product_comm b a, diagonal_product_comm c a]
    map_smul' r b := by
      simp only [RingHom.id_apply]
      rw [diagonal_product_comm a (r • b), diagonal_product_smul_left,
        diagonal_product_comm b a]
  }
  map_add' a b := LinearMap.ext fun c => diagonal_product_add_left a b c
  map_smul' r a := LinearMap.ext fun c => diagonal_product_smul_left r a c

@[simp] theorem diagonalProductLinear_apply (a b : Diagonal27) :
    diagonalProductLinear a b = diagonalProduct a b := rfl

@[simp] theorem native_Q_eq (a b : Albert) : Q jordanLinear a b = U a b := rfl
@[simp] theorem native_quadraticWith_eq (a b : Albert) :
    quadraticWith (fun u v => jordanLinear u v) a b = U a b := by
  simp only [quadraticWith, jordanLinear_apply, U]

@[simp] theorem native_response_eq (x y z : Albert) :
    response jordanLinear x y z = phi x y z := by
  rw [response, phiWith, phi]
  simp only [jordanLinear_apply, hilbert_inner_eq_native, quadraticWith, U]

end
end Glennie.Compact.NativeDefectReadoutR01
