module

public import DedekindZetaZeroFree.Metaplectic.Torus.PrincipalCubicLagrangianPreimage

@[expose] public section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem center_le_rational : Z F ζ hζ ≤ rationalCenterSubgroup F ζ hζ :=
  fun _ => Subgroup.mem_sup_right

theorem rational_extension_continuous (χ : Z F ζ hζ →ₜ* ℂˣ)
    (f : rationalCenterSubgroup F ζ hζ →* ℂˣ)
    (hf : ∀ z, f (Subgroup.inclusion (center_le_rational F ζ hζ) z) = χ z) :
    Continuous f := by
  letI := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  letI := KPGlobalPrincipalCubicLagrangian.principal_discrete F ζ hζ
  let q := coveredTorusDiagonalRatioCubicProjection F ζ hζ
  let qr (g : rationalCenterSubgroup F ζ hζ) : KPGlobalPrincipalCubicLagrangian.A F :=
    ⟨q g, (le_of_eq (rational_subgroup_geometry F ζ hζ).1) g.property⟩
  have hq : Continuous qr :=
    ((pD_continuous F ζ hζ).comp continuous_subtype_val).subtype_mk fun g => (qr g).property
  let i := Subgroup.inclusion (center_le_rational F ζ hζ)
  have he : Set.range i = qr ⁻¹' {1} := by
    ext g
    rw [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]
    change g ∈ Set.range i ↔ q g = 1
    rw [← MonoidHom.mem_ker, ← center_eq_pD_ker]
    constructor
    · rintro ⟨z, rfl⟩
      exact z.property
    · intro hz
      exact ⟨⟨g.val, hz⟩, rfl⟩
  have hmem : Set.range i ∈ nhds (i 1) :=
    (he ▸ (hq.isOpen_preimage _ (isOpen_discrete _))).mem_nhds ⟨1, rfl⟩
  apply continuous_of_continuousAt_one f
  have hc : Continuous (f ∘ i) := (funext hf : f ∘ i = χ) ▸ χ.continuous
  have h := ((Topology.IsEmbedding.inclusion (center_le_rational F ζ hζ)).isInducing.continuousAt_iff'
    hmem).mp (hc.continuousAt (x := 1))
  change ContinuousAt f (i 1) at h
  simpa only [map_one] using h

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension
