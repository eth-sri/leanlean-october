module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.ScalarRealizationClosure

@[expose] public section

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Classical NumberField ENNReal NNReal Topology InnerProductSpace ComplexOrder
namespace DedekindZetaZeroFree.KPGlobalResidualKernel
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev RawAdeles := KPGlobalTorusFunctionData.Adeles F
abbrev RawAdditiveQuotient := RawAdeles F ⧸ NumberField.AdeleRing.principalSubgroup (𝓞 F) F

end DedekindZetaZeroFree.KPGlobalResidualKernel

end

section

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Classical NumberField ENNReal NNReal Topology InnerProductSpace ComplexOrder
namespace DedekindZetaZeroFree.KPGlobalResidualKernel
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def rawRationalBorel : Subgroup (KPRationalAdelicSplitting.RationalPGL2 F) :=
  (KPGlobalTorusFunctionData.borel F ζ hζ).comap
    (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ)
abbrev RawRationalQuotient := Quotient (QuotientGroup.rightRel (rawRationalBorel F ζ hζ))

variable {F ζ hζ}
variable (T : KPMsRationalCompactCrossPairing.ModelData F ζ hζ)
variable (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (A : KPMsRationalCompactCrossPairing.RawCompactComparison F ζ hζ T D R P H)

end DedekindZetaZeroFree.KPGlobalResidualKernel

end
end
