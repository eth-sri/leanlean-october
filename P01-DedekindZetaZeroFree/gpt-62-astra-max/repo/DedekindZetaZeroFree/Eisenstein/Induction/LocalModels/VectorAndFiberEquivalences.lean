module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RestrictedTensors.ExceptionalSetEquivalence
public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSections.ParameterEvaluation
public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarSections.FlatInsertion

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open NumberField MomentSources KPGlobalTorusFiniteStages
open PrincipalOfKP.ResidueCoreBridge.CanonicalBinding
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
    (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
    (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

section

variable (v : KPHilbert.Place F)

def plusEquiv :
    FaithfulSource.RepairedInducing.Plus R N P C v ≃ₗ[ℂ] LiteralSource.Plus R.A P C v := by
  cases v <;> exact LinearEquiv.refl ℂ _

theorem reference_eq :
    plusEquiv R N P C v (FaithfulSource.RepairedInducing.plusReference R N P C v) =
      LiteralSource.plusReference R.A P C v := by
  cases v with
  | inl w => rfl
  | inr q =>
    rfl

theorem localValue_eq
    (g : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 v)
    (x : FaithfulSource.RepairedInducing.Plus R N P C v) :
    FaithfulSource.RepairedInducing.localValue R N P C v g x =
      LiteralSource.localValue R.A P C v g (plusEquiv R N P C v x) := by
  cases v <;> rfl

end

def coreEquiv : FaithfulSource.RepairedInducing.PlusCore R N P C ≃ₗ[ℂ]
    RestrictedTensorSimple.Core (LiteralSource.Plus R.A P C)
      (LiteralSource.plusReference R.A P C) (LiteralSource.bad R.A P C) := by
  exact RestrictedTensorSimple.equalBadEquiv _ _ _ _
    (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.badSet_eq_fullBad
      F R.A.zeta12 R.A.primitive_zeta12 P C)

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end
