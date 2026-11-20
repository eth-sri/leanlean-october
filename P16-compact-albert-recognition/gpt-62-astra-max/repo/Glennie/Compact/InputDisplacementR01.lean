module
public import Glennie.Compact.SharpPolarizationR01
public import Glennie.Covariance
public import Glennie.Compact.InnerBounds

/- Input displacement using the native raw trace norm. -/
@[expose] public section
namespace Glennie.Compact.NativeNormKernel
open Glennie
noncomputable section
set_option autoImplicit false

private theorem first_change (x x' y z : Albert) (R δ : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hx' : ‖x'‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) (hd : ‖x-x'‖ ≤ δ) :
    |phi x y z - phi x' y z| ≤ 6*R^8*δ := by
  have hδ := (norm_nonneg _).trans hd
  have hr : U z (jordan x y) - U z (jordan x' y) = U z (jordan (x-x') y) := by
    rw [jordan_sub_left,U_sub_argument]
  unfold phi
  simp only [← hilbert_inner_eq_native]
  grw [pair_difference]
  rw [sub_sub_sub_comm, ← U_sub_argument, hr]
  grw [norm_sub_le (U x (U y z) - _) _, norm_sub_le (U x' (U y z)) _]
  repeat first | grw [U_sub_base_norm] | grw [U_norm] | grw [jordan_norm]
  repeat first | grw [hd] | grw [hx] | grw [hx'] | grw [hy] | grw [hz]
  exact le_of_eq (by ring)

 theorem phi_displacement_18 (x y z x' y' z' : Albert) (R δ : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R)
    (hx' : ‖x'‖ ≤ R) (hy' : ‖y'‖ ≤ R) (hz' : ‖z'‖ ≤ R)
    (hdx : ‖x-x'‖ ≤ δ) (hdy : ‖y-y'‖ ≤ δ) (hdz : ‖z-z'‖ ≤ δ) :
    |phi x y z-phi x' y' z'| ≤ 18*R^8*δ := by
  have h1 := first_change x x' y z R δ hR hx hx' hy hz hdx
  have h2 := first_change y y' x' z R δ hR hy hy' hx' hz hdy
  have h3 := first_change z z' y' x' R δ hR hz hz' hy' hx' hdz
  rw [phi_swap_first_two x' y,phi_swap_first_two x' y'] at h2
  rw [phi_swap_first_third x' y' z,phi_swap_first_third x' y' z'] at h3
  grind
end
end Glennie.Compact.NativeNormKernel
