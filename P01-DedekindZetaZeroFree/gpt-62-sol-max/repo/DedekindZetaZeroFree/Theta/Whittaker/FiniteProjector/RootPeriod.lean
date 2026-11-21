module

public import DedekindZetaZeroFree.Theta.Profiles.FourierRootCovariance
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.PeriodLinearity
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CompactPeriod.QuotientDescent

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open NumberField MeasureTheory
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem fourier_upper (dq : Measure (KPAdditiveQuotient F)) [dq.IsAddHaarMeasure]
    (f : Functions R)
    (hf : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (x : KPAdeles F) (g : Group R) :
    MomentSources.fourier R dq f
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g) =
      (adelicTraceQuotientCharacter F (QuotientAddGroup.mk x) : ℂ) * MomentSources.fourier R dq f g :=
  MomentSources.fourier_left_root R dq f
    (fun t g => by rw [← KPLiteralExceptionalResidue.rationalLift_unipotent]; exact hf _ _) x g

theorem stage08_fourier_upper {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N)
    (v : R.A.UnitQuotient) (x : KPAdeles F) (g : Group R) :
    MomentSources.fourier R A.sources.dq (A.realization.theta v)
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g) =
      (adelicTraceQuotientCharacter F (QuotientAddGroup.mk x) : ℂ) *
        MomentSources.fourier R A.sources.dq (A.realization.theta v) g := by
  letI := A.sources.quotientHaar
  exact fourier_upper R A.sources.dq (A.realization.theta v)
    (A.realization.automorphic v).2.1 x g

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end
