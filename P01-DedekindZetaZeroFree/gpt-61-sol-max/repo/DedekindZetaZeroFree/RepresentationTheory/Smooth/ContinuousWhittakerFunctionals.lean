module

public import Mathlib

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RepresentationsAndFixedLevels

@[expose] public section


noncomputable section

namespace DedekindZetaZeroFree















def CanonicalSmoothModule (V : Type*) [AddCommGroup V] [Module ℂ V] := V
  deriving AddCommGroup, Module ℂ

instance canonicalSmoothModuleTopology (V : Type*) [AddCommGroup V] [Module ℂ V] :
    TopologicalSpace (CanonicalSmoothModule V) := moduleTopology ℂ (CanonicalSmoothModule V)

def canonicalSmoothModuleEquiv (V : Type*) [AddCommGroup V] [Module ℂ V] :
    CanonicalSmoothModule V ≃ₗ[ℂ] V := LinearEquiv.refl ℂ V

instance canonicalSmoothModuleIsModuleTopology (V : Type*) [AddCommGroup V] [Module ℂ V] :
    IsModuleTopology ℂ (CanonicalSmoothModule V) := ⟨rfl⟩







def canonicalSmoothRepresentation {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    Representation ℂ G (CanonicalSmoothModule V) := ρ

def canonicalSmoothModule_linear_continuous {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [TopologicalSpace W] [ContinuousAdd W] [ContinuousSMul ℂ W]
    (f : CanonicalSmoothModule V →ₗ[ℂ] W)  := IsModuleTopology.continuous_of_linearMap f

theorem smoothRepresentation_orbit_isLocallyConstant {G V : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hρ : SmoothRepresentation ρ) (v : V) :
    IsLocallyConstant (fun g : G => ρ g v) := by
  obtain ⟨J, hJ⟩ := hρ v
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨{x : G | g⁻¹ * x ∈ J},
    J.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simpa using J.one_mem
  · intro x hx
    have heq := congrArg (fun w => ρ g w) (hJ (g⁻¹ * x) hx)
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] using heq

def algebraicWhittaker {K G V : Type*} [AddCommGroup K] [Group G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (n : Multiplicative K →* G) (ψ : Multiplicative K →* ℂˣ) :
    Submodule ℂ (V →ₗ[ℂ] ℂ) where
  carrier := {ℓ | ∀ t v, ℓ (ρ (n t) v) = (ψ t : ℂ) * ℓ v}
  zero_mem' := by simp
  add_mem' := by
    intro ℓ m hℓ hm t v
    simp only [LinearMap.add_apply, hℓ t v, hm t v, mul_add]
  smul_mem' := by
    intro c ℓ hℓ t v
    simp only [LinearMap.smul_apply, smul_eq_mul, hℓ t v]
    ring






end DedekindZetaZeroFree

end
