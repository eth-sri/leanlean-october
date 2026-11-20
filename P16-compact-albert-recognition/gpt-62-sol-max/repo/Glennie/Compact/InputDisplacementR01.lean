module
public import Glennie.Compact.SharpPolarizationR01
public import Glennie.Compact.MultiplicationDefectR01
public import Glennie.Compact.GlennieDerivativeR01
public import Glennie.Covariance
/- Input displacement using the native raw trace norm. -/
@[expose] public section
namespace Glennie.Compact.NativeNormKernel
open Glennie
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

open GlennieDerivativeR01 GlennieScalarPotentialR01

private theorem phi_sub_third (x y z z' : Albert) (R : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) (hz' : ‖z'‖ ≤ R) :
    |phi x y z-phi x y z'| ≤ 6*R^8*‖z-z'‖ := by
  let L := commUContinuous x y
  let J := jordan x y
  have u (a b : Albert) (ha : ‖a‖ ≤ R) : ‖U a b‖ ≤ R^2*‖b‖ := by grw [U_norm, ha]
  have hL (w : Albert) : ‖L w‖ ≤ 2*(R^2*(R^2*‖w‖)) := by
    simp only [L, commUContinuous_apply, commU, two_mul]
    grw [norm_sub_le, u x _ hx, u y _ hy, u y _ hy, u x _ hx]
  have p (w : Albert) : phi x y w = Inner.inner ℝ (L w) (U w J) := by
    dsimp only [L]
    rw [commUContinuous_apply]; rfl
  rw [p z, p z']
  grw [MultiplicationDefectR01.pairing_error, ← map_sub, hL, u _ _ hz, hL,
    U_sub_base_radius _ _ _ R hz hz', jordan_norm, hx, hy, hz']
  ring_nf
  rfl


 theorem phi_displacement_18 (x y z x' y' z' : Albert) (R δ : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R)
    (hx' : ‖x'‖ ≤ R) (hy' : ‖y'‖ ≤ R) (hz' : ‖z'‖ ≤ R)
    (hdx : ‖x-x'‖ ≤ δ) (hdy : ‖y-y'‖ ≤ δ) (hdz : ‖z-z'‖ ≤ δ) :
    |phi x y z-phi x' y' z'| ≤ 18*R^8*δ := by
  have h₁ := phi_sub_third y z x x' R hR hy hz hx hx'
  have h₂ := phi_sub_third z x' y y' R hR hz hx' hy hy'
  rw [phi_cyclic x y z, phi_cyclic x' y z] at h₁
  rw [phi_cyclic y z x', phi_cyclic y' z x', phi_cyclic x' y z, phi_cyclic x' y' z] at h₂
  calc
    _ ≤ (|phi x y z - phi x' y z| + |phi x' y z - phi x' y' z|) + |phi x' y' z - phi x' y' z'| := by
      grw [abs_sub_le _ (phi x' y' z) _, abs_sub_le _ (phi x' y z) (phi x' y' z)]
    _ ≤ (6*R^8*δ + 6*R^8*δ) + 6*R^8*δ := by
      grw [h₁, h₂, phi_sub_third x' y' z z' R hR hx' hy' hz hz', hdx, hdy, hdz]
    _ = _ := by ring

end
end Glennie.Compact.NativeNormKernel
