module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.LocalPGL.IntegralTriangularization

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ActualFiniteBorel.IwasawaProof
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (q : HeightOneSpectrum (𝓞 F))
local instance : ValuativeRel (q.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F q
local instance : IsNonarchimedeanLocalField (q.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q
local instance : Group (KPPGLLocalCover.LocalPGL2 F (Sum.inr q)) :=
  @QuotientGroup.Quotient.group _ _ (KPPGLLocalCover.scalarSubgroup F (Sum.inr q))
    (KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q))

theorem covered_factor (g : KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)) :
    ∃ b : KPLocalSmoothRepresentation.Borel F ζ hζ q,
      ∃ k : KPRankOneCartanGeometry.coveredK0 F ζ hζ q,
        g = b.val * k.val := by
  let projection₀ := KPPGLLocalCover.projection F ζ hζ (Sum.inr q)
  obtain ⟨G, hG⟩ := QuotientGroup.mk_surjective
    (projection₀ g)
  obtain ⟨r, hr⟩ := triangularize F q G
  obtain ⟨k, hk⟩ := KPPGLLocalCover.projection_surjective F ζ hζ (Sum.inr q)
    (KPPGLLocalCover.baseQuotient F (Sum.inr q) (KPTameCompact.inclusion F q r⁻¹))
  have hkmem : k ∈ KPRankOneCartanGeometry.coveredK0 F ζ hζ q := by
    change projection₀ k ∈ KPRankOneCartanGeometry.K0 F q
    rw [hk]
    exact ⟨r⁻¹, rfl⟩
  have hb : g * k⁻¹ ∈ KPLocalSmoothRepresentation.Borel F ζ hζ q := by
    refine ⟨G * KPTameCompact.inclusion F q r, ?_, hr⟩
    change Matrix.ProjGenLinGroup.mk (G * KPTameCompact.inclusion F q r) =
      KPLocalSmoothRepresentation.ordinaryPGLMap F q
        (projection₀ (g * k⁻¹))
    rw [(projection₀).map_mul,
      (projection₀).map_inv, ← hG, hk,
      map_inv, map_inv, inv_inv]
    rfl
  refine ⟨⟨g * k⁻¹, hb⟩, ⟨k, hkmem⟩, ?_⟩
  simp

theorem covered_intersection (b : KPLocalSmoothRepresentation.Borel F ζ hζ q)
    (hb : b.val ∈ KPRankOneCartanGeometry.coveredK0 F ζ hζ q) :
    KPLocalPrincipalSeries.localAbs (q.adicCompletion F)
      (KPRankOneInduction.borelRatio F q
        ⟨KPLocalSmoothRepresentation.projection F ζ hζ q b.val, b.property⟩) = 1 := by
  obtain ⟨k, hk⟩ := hb
  apply integral_ratio F q _ k
  change Matrix.ProjGenLinGroup.mk (KPTameCompact.inclusion F q k) =
    KPLocalSmoothRepresentation.ordinaryPGLMap F q
      (KPPGLLocalCover.projection F ζ hζ (Sum.inr q) b.val)
  rw [← hk]
  rfl

end
end DedekindZetaZeroFree.ActualFiniteBorel.IwasawaProof
