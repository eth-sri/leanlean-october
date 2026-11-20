module
public import DedekindZetaZeroFree.Theta.Whittaker.LocalFunctionalsFromGlobalPeriods

public import DedekindZetaZeroFree.Theta.Periods.PureTensorDetection

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation
open MomentSources
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    {R : PrincipalMellin.ActualRecipe S η}
    {Q : AdmissibleFlatSources R}

theorem fourier_left_root (μ : Measure (KPAdditiveQuotient F)) [μ.IsAddHaarMeasure]
    (θ : Functions R)
    (hθ : ∀ (t : F) (g : Group R), θ
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (algebraMap F (KPAdeles F) t) * g) = θ g)
    (a : KPAdeles F) (g : Group R)
    (_hi : Integrable (fun q => θ
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (Quotient.out q) * g) * star (adelicTraceQuotientCharacter F q : ℂ)) μ) :
    fourier R μ θ (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 a * g) =
      (adelicTraceQuotientCharacter F (QuotientAddGroup.mk a) : ℂ) * fourier R μ θ g := by apply @DedekindZetaZeroFree.ExteriorWhittakerValues.StoredWhittaker.fourier_left_root <;> assumption

theorem finite_root_injection (q : KPFinitePlace F) (t : q.adicCompletion F) :
    KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12
        (Sum.inr q) (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t)) =
      KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (KPRationalAdelicSplitting.localAdele F (Sum.inr q) t) := by apply @DedekindZetaZeroFree.ExteriorWhittakerValues.StoredWhittaker.finite_root_injection <;> assumption

end DedekindZetaZeroFree.FourierContinuation

end
