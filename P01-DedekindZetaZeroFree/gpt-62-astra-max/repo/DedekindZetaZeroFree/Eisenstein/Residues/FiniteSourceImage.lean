module

public import DedekindZetaZeroFree.Eisenstein.Continuation.LaurentNumeratorCovariance
public import DedekindZetaZeroFree.Eisenstein.Residues.SourceResidueLinearMap

@[expose] public section

noncomputable section
open scoped Classical Topology
namespace DedekindZetaZeroFree.SharedSource
open MomentSources EisensteinSmoothGerms
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
    {C : ScalarContinuation R Q}

def scalarResidualStage (H : ∀ v, ScalarGerm C v) : Submodule ℂ (Functions R) :=
  Submodule.span ℂ (Set.range (fun v => ((H v).cleared 0 : Functions R)))

theorem finiteSourceResidue_range_stage (H : ∀ v, ScalarGerm C v) :
    (finiteSourceResidue H).range = scalarResidualStage H :=
  finiteSourceResidue_range H

end DedekindZetaZeroFree.SharedSource

end
