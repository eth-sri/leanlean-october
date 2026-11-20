module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.RationalPeriodizationPairingData

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal Topology
open MeasureTheory
open DedekindZetaZeroFree.KPMsRationalCompactCrossPairing
namespace DedekindZetaZeroFree.KPMsRationalCompactCrossPairingProof
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

alias scalarSmooth_continuous := DedekindZetaZeroFree.KPMsRationalCompactCrossPairing.compact_core_scalar_continuous

theorem sourceCore_le_scalarSmooth (D : Iwasawa F ζ hζ) :
    sourceCore F ζ hζ D ≤ scalarSmooth F ζ hζ (sourcePolarization F ζ hζ 0) := by apply @DedekindZetaZeroFree.KPMsRationalCompactCrossPairing.compact_source_core_smooth <;> assumption

theorem sourceCore_continuous {D : Iwasawa F ζ hζ} (f : Vplus F ζ hζ D) :
    Continuous f.val.val :=
  scalarSmooth_continuous _ _ (sourceCore_le_scalarSmooth D f.property)

variable {C : ModelData F ζ hζ} {D : Iwasawa F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
    (A : RawCompactComparison F ζ hζ C D R P H)

end DedekindZetaZeroFree.KPMsRationalCompactCrossPairingProof

end
