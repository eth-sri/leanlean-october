/- Third-slot noncriticality implies native unital Jordan generation.
All exposition and Lean code are AI-generated under Robert MacGregor's direction.
No novelty is asserted.
-/
module

public import Glennie.Compact.GlennieDerivativeR01
public import Glennie.NativeGenerationEndpointR01
@[expose] public section
namespace Glennie.Compact.GlennieDerivativeGenerationR01

open Glennie
open Glennie.Compact.GlennieScalarPotentialR01
open Glennie.Compact.GlennieDerivativeR01
open Glennie.NativeGenerationEndpointR01

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
-- Keep the native/Hilbert inherited-instance convention of the provider.
set_option backward.isDefEq.respectTransparency false

/-- The gradient is a Jordan polynomial in its three arguments. -/
private theorem glennieVector_mem (K : Submodule ℝ Albert)
    (hJ : JordanClosed K)
    {x y z : Albert} (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    glennieVector x y z ∈ K := by repeat' first | assumption | apply hJ | apply K.sub_mem | apply K.add_mem | apply K.smul_mem

/-- Differentiate the identically zero affine curve in the native G8 direction.
Its derivative is the raw positive pairing of G8 with itself. -/
theorem glennieVector_eq_zero_of_ne_top
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : JordanClosed K) (hK : K ≠ ⊤)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    glennieVector x y z = 0 := by
  have hcurve : (fun t : ℝ => phi x y (z + t • glennieVector x y z)) = fun _ => 0 := by
    funext t
    by_contra h
    exact hK (eq_top_of_phi_ne_zero K h1 hJ x y _ hx hy
      (K.add_mem hz (K.smul_mem t (glennieVector_mem K hJ hx hy hz))) h)
  have hd := hasDerivAt_phi_third_affine x y z (glennieVector x y z)
  rw [hcurve] at hd
  exact (inner_self_eq_zero _).mp (hd.unique (hasDerivAt_const _ _))

end
end Glennie.Compact.GlennieDerivativeGenerationR01
