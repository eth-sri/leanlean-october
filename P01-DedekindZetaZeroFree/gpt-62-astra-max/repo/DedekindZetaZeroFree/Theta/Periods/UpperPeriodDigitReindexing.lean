module

public import DedekindZetaZeroFree.Theta.Digits.SUnitReindexing

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.ThetaExpansion.QuotientDescent
open MomentSources
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)

theorem selected_upper_digit_reindex {N : TraceHaarTransport R} (C : JointMellinGaussianSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (u : R.A.U)
    (b : Bool) (y : R.A.G) (d : Digits R m) :
    upper R C.sources.dq (C.realization.theta v)
      (signedArgument R m b (R.A.diagonal (u.val ^ 6) * y) (digitReindex R m u d)) =
    upper R C.sources.dq (C.realization.theta v) (signedArgument R m b y d) := by
  exact (DedekindZetaZeroFree.DigitMasks.signed_term_reindex R C.realization v m u b y d).2
end DedekindZetaZeroFree.ThetaExpansion.QuotientDescent

end
