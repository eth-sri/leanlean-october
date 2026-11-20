/- Consequences of native unital generation.
No generation/span premise. -/
module
public import Glennie.NativeGenerationEndpointR01
public import Glennie.Compact.InnerDerivation
public import Mathlib.Algebra.Module.Submodule.EqLocus
@[expose] public section
namespace Glennie.NativeGenerationStabilizersR01
noncomputable section
open Glennie.NativeGenerationEndpointR01
open Glennie.Compact

section Equalizers
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (j : E → E → E)

/-- An equalizer of product-preserving maps is product-closed. -/
theorem eqLocus_closed (f g : E →ₗ[ℝ] E)
    (hf : ∀ x y, f (j x y) = j (f x) (f y)) (hg : ∀ x y, g (j x y) = j (g x) (g y)) :
    ∀ x ∈ f.eqLocus g, ∀ y ∈ f.eqLocus g, j x y ∈ f.eqLocus g := by simp_all

/-- The kernel of a derivation is product-closed. -/
theorem derivation_ker_closed (D : E →ₗ[ℝ] E)
    (h : ∀ x y, D (j x y) = j (D x) y + j x (D y))
    (h₁ : ∀ x, j 0 x = 0) (h₂ : ∀ x, j x 0 = 0) :
    ∀ x ∈ D.ker, ∀ y ∈ D.ker, j x y ∈ D.ker := by simp_all
end Equalizers

theorem automorphism_eq_refl_of_phi_ne_zero (g : CompactAutomorphism) (x y z : Albert)
    (hphi : phi x y z ≠ 0) (hx : g.equiv x = x) (hy : g.equiv y = y) (hz : g.equiv z = z) :
    g.equiv = LinearEquiv.refl ℝ Albert := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.eqLocus_eq_top.mp
  exact eq_top_of_phi_ne_zero _ g.map_unit (eqLocus_closed jordan g.equiv.toLinearMap LinearMap.id g.map_jordan (by simp))
    x y z hx hy hz hphi

theorem derivation_eq_zero_of_phi_ne_zero (D : Albert →ₗ[ℝ] Albert) (hD : IsJordanDerivation D)
    (x y z : Albert) (hphi : phi x y z ≠ 0) (hx : D x = 0) (hy : D y = 0) (hz : D z = 0) : D = 0 :=
  LinearMap.ker_eq_top.mp (eq_top_of_phi_ne_zero _ hD.map_one
    (derivation_ker_closed jordan D hD jordan_zero_left jordan_zero_right) x y z hx hy hz hphi)

end
end Glennie.NativeGenerationStabilizersR01
