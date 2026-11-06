module
public import Glennie.Compact.MultiplicationDefectR01
public import Mathlib.Tactic.GRewrite
public import Glennie.Compact.SharpPolarizationR01
public import Glennie.Covariance

/- Input displacement using the native raw trace norm. -/
@[expose] public section
namespace Glennie.Compact.NativeNormKernel
open Glennie
noncomputable section
 def F (x y z : Albert) : Albert := U x (U y z) - U y (U x z)
 def H (x y z : Albert) : Albert := U z (jordan x y)









 theorem F_norm_radius (x y z : Albert) (R : ℝ)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    ‖F x y z‖ ≤ 2*R^5 := by
  change ‖U x (U y z) - U y (U x z)‖ ≤ _
  grw [norm_sub_le, U_norm, U_norm, U_norm, U_norm, hx, hy, hz]
  ring_nf
  rfl

 theorem H_norm_radius (x y z : Albert) (R : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    ‖H x y z‖ ≤ R^4 := by
  change ‖U z (jordan x y)‖ ≤ _
  grw [U_norm, jordan_norm, hx, hy, hz]
  ring_nf
  rfl

 theorem F_sub_first (x x' y z : Albert) :
    F x y z - F x' y z =
      (U x (U y z) - U x' (U y z)) - U y (U x z - U x' z) := by
  simp only [F, U_sub_argument]
  abel

 theorem F_sub_first_radius (x x' y z : Albert) (R : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hx' : ‖x'‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    ‖F x y z-F x' y z‖ ≤ 4*R^4*‖x-x'‖ := by
  rw [F_sub_first]
  grw [norm_sub_le, U_sub_base_norm, U_norm, U_norm, U_sub_base_norm,
    hx, hx', hy, hz]
  ring_nf
  rfl

 theorem H_sub_first_radius (x x' y z : Albert) (R : ℝ) (hR : 0 ≤ R)
    (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    ‖H x y z-H x' y z‖ ≤ R^3*‖x-x'‖ := by
  have he : H x y z-H x' y z = U z (jordan (x-x') y) := by
    simp only [H, jordan_sub_left, U_sub_argument]
  rw [he]
  grw [U_norm, jordan_norm, hy, hz]
  ring_nf
  rfl

 theorem phi_sub_first_radius (x x' y z : Albert) (R : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hx' : ‖x'‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |phi x y z-phi x' y z| ≤ 6*R^8*‖x-x'‖ := by
  change |Inner.inner ℝ (F x y z) (H x y z)-Inner.inner ℝ (F x' y z) (H x' y z)| ≤ _
  grw [MultiplicationDefectR01.pairing_difference, F_sub_first_radius _ _ _ _ _ hR hx hx' hy hz,
    H_norm_radius _ _ _ _ hR hx hy hz, F_norm_radius _ _ _ _ hx' hy hz,
    H_sub_first_radius _ _ _ _ _ hR hy hz]
  ring_nf
  rfl

 theorem phi_sub_second_radius (x y y' z : Albert) (R : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hy' : ‖y'‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |phi x y z-phi x y' z| ≤ 6*R^8*‖y-y'‖ := by
  have he : phi x y z-phi x y' z = -(phi y x z-phi y' x z) := by
    rw [phi_swap_first_two y x, phi_swap_first_two y' x]; ring
  rw [he, abs_neg]
  exact phi_sub_first_radius _ _ _ _ _ hR hy hy' hx hz

 theorem phi_sub_third_radius (x y z z' : Albert) (R : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) (hz' : ‖z'‖ ≤ R) :
    |phi x y z-phi x y z'| ≤ 6*R^8*‖z-z'‖ := by
  have he : phi x y z-phi x y z' = -(phi z y x-phi z' y x) := by
    rw [phi_swap_first_third z y x, phi_swap_first_third z' y x]; ring
  rw [he, abs_neg]
  exact phi_sub_first_radius _ _ _ _ _ hR hz hz' hy hx

 theorem phi_displacement_18 (x y z x' y' z' : Albert) (R δ : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R)
    (hx' : ‖x'‖ ≤ R) (hy' : ‖y'‖ ≤ R) (hz' : ‖z'‖ ≤ R)
    (hdx : ‖x-x'‖ ≤ δ) (hdy : ‖y-y'‖ ≤ δ) (hdz : ‖z-z'‖ ≤ δ) :
    |phi x y z-phi x' y' z'| ≤ 18*R^8*δ := by
  have he : phi x y z - phi x' y' z' =
      (phi x y z - phi x' y z) + (phi x' y z - phi x' y' z) +
      (phi x' y' z - phi x' y' z') := by ring
  rw [he]
  grw [abs_add_le, abs_add_le,
    phi_sub_first_radius _ _ _ _ _ hR hx hx' hy hz,
    phi_sub_second_radius _ _ _ _ _ hR hx' hy hy' hz,
    phi_sub_third_radius _ _ _ _ _ hR hx' hy' hz hz', hdx, hdy, hdz]
  ring_nf
  rfl

end
end Glennie.Compact.NativeNormKernel
