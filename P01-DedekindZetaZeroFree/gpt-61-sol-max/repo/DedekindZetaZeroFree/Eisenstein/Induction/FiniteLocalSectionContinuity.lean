module

public import DedekindZetaZeroFree.Eisenstein.Induction.CompactOpenLevels

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.FiniteSourceTopology
open KPAdelicCoverRestrictedProduct KPGlobalTorusFiniteStages
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)

 def finiteProjection : RestrictedCover F ζ hζ →* RestrictedCover F ζ hζ :=
  RestrictedProduct.mapAlongMonoidHom
    (KPLocalCover.CubicGL2Raw F ζ hζ) (KPLocalCover.CubicGL2Raw F ζ hζ)
    id Filter.tendsto_id
    (fun v => match v with | Sum.inl _ => 1 | Sum.inr _ => MonoidHom.id _)
    (Filter.Eventually.of_forall (by intro v a ha; cases v <;> simpa using ha))

 theorem finiteProjection_continuous : Continuous (finiteProjection F ζ hζ) := by
  unfold finiteProjection RestrictedProduct.mapAlongMonoidHom
  exact RestrictedProduct.mapAlong_continuous _ _ id Filter.tendsto_id _
    (Filter.Eventually.of_forall (by intro v a ha; cases v <;> simpa using ha))
    (fun v => by cases v <;> first | exact continuous_const | exact continuous_id)

 def finiteQuotient (g : RestrictedCover F ζ hζ) :
    KPGlobalTorusFunctionData.finitePart F ζ hζ :=
  ⟨scalarQuotient F ζ hζ (amalgamation F ζ hζ (finiteProjection F ζ hζ g)), by
    refine Subgroup.mem_map.mpr ⟨finiteProjection F ζ hζ g, ?_, rfl⟩
    simp only [Subgroup.mem_iInf, MonoidHom.mem_ker]
    intro w
    rfl⟩

 theorem finiteQuotient_continuous : Continuous (finiteQuotient F ζ hζ) := by
  exact ((QuotientGroup.continuous_mk.comp QuotientGroup.continuous_mk).comp
    (finiteProjection_continuous F ζ hζ)).subtype_mk _









































end DedekindZetaZeroFree.EisensteinReferenceSections.FiniteSourceTopology

end
