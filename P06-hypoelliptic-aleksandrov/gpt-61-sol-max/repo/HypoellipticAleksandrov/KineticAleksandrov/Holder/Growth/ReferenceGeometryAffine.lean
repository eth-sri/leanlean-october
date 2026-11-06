module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryStack
import Mathlib.Tactic

/-! # General affine cylinder and stack images from the exact unit identities -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

variable {d : ℕ} (P0 P : KineticPoint d) (R r : ℝ) (hR : 0 < R) (hr : 0 < r)

include hR hr
/-- Composing kinetic affine maps transports an arbitrary source cylinder exactly. -/
theorem kineticAffine_image_cylinder  :
    kineticAffine P0 R '' backwardCylinder P r =
      backwardCylinder (kineticAffine P0 R P) (R * r) := by
  rw [← kineticAffine_image_unitCylinder P hr, image_image, ← Function.comp_def,
    kineticAffine_comp,
    kineticAffine_image_unitCylinder _ (mul_pos hR hr)]

/-- The exact source stack identity is preserved by arbitrary affine composition. -/
theorem kineticAffine_image_stack  (m : ℕ) :
    kineticAffine P0 R '' forwardStack P r m =
      forwardStack (kineticAffine P0 R P) (R * r) m := by
  rw [← kineticAffine_image_forwardStack P hr m, image_image, ← Function.comp_def,
    kineticAffine_comp,
    kineticAffine_image_forwardStack _ (mul_pos hR hr) m]

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
