module

public import DedekindZetaZeroFree.Eisenstein.Residues.SpanAutomorphy
public import DedekindZetaZeroFree.Eisenstein.Induction.Convolution.ProjectedFlatExpansion
public import DedekindZetaZeroFree.Theta.Profiles.IdelicDilation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SharedSource
open MomentSources
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    {R : PrincipalMellin.ActualRecipe S η}

def flatScalarStage (Q : AdmissibleFlatSources R) : Submodule ℂ (Functions R) :=
  Submodule.span ℂ (Set.range (fun v => (Q.flat v).val 0))

end DedekindZetaZeroFree.SharedSource

end
