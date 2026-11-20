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

/-! Polynomial closure uses only the submodule laws and native Jordan closure.
The unit enters later, through the existing scalar-generation theorem. -/

/-- The actual native gradient vector stays in any Jordan-product-closed
real submodule containing its three arguments. -/
theorem glennieVector_mem (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    glennieVector x y z ∈ K := by
  unfold glennieVector commU doubledTriple U
  repeat first | assumption | apply K.smul_mem | apply K.add_mem | apply K.sub_mem | apply hJ

/-! Proper unital submodules force scalar and third-slot gradient vanishing. -/

/-- Vanishing is deduced from the retained scalar-generation theorem.
It is not supplied as a property of the submodule. -/
theorem phi_eq_zero_of_ne_top
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K) (hK : K ≠ ⊤)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    phi x y z = 0 := by
  by_contra hphi
  exact hK (eq_top_of_phi_ne_zero K h1 hJ x y z hx hy hz hphi)

/-- Differentiate the identically zero affine curve in the native G8 direction.
Its derivative is the raw positive pairing of G8 with itself. -/
theorem glennieVector_eq_zero_of_ne_top
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K) (hK : K ≠ ⊤)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    glennieVector x y z = 0 := by
  have hg := glennieVector_mem K hJ x y z hx hy hz
  have hcurve :
      (fun t : ℝ => phi x y (z + t • glennieVector x y z)) =
      (fun _ : ℝ => (0 : ℝ)) := by
    funext t
    exact phi_eq_zero_of_ne_top K h1 hJ hK x y
      (z + t • glennieVector x y z) hx hy (K.add_mem hz (K.smul_mem t hg))
  have hd := hasDerivAt_phi_third_affine x y z (glennieVector x y z)
  rw [hcurve] at hd
  have hzero : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 (0 : ℝ) :=
    hasDerivAt_const (0 : ℝ) (0 : ℝ)
  exact (inner_self_eq_zero (glennieVector x y z)).mp (hd.unique hzero)

/-! Definition-free generation endpoints for arbitrary native triples. -/

end
end Glennie.Compact.GlennieDerivativeGenerationR01
