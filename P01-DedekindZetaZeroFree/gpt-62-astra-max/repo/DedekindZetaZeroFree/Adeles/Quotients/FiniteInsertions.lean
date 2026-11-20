module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.FiniteSourceGeometry

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources KPAdelicCoverRestrictedProduct
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)

 def finiteInjection (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) : Group R :=
  scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
    (localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)

 theorem finiteInjection_compact_mem (p : KPFinitePlace F)
    (b : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    (hb : b ∈ compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)) :
    finiteInjection R p b ∈ (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K := by apply @DedekindZetaZeroFree.FiniteWhittakerProjectors.finiteInjection_compact_mem <;> assumption

 theorem finiteInjection_mem_finitePart (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    finiteInjection R q a ∈ KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12 := by
  refine Subgroup.mem_map.mpr ⟨localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a, ?_, rfl⟩
  apply Subgroup.mem_iInf.mpr
  intro w
  simp [localToRestricted]

 def ExteriorFixed (f : Functions R) : Prop :=
  ∀ (p : KPFinitePlace F), p ∉ R.A.Sf →
    ∀ (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)),
    a ∈ compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) →
    ∀ g, f (g * finiteInjection R p a) = f g

end DedekindZetaZeroFree.RootDerivatives

end
