module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.RationalPeriodizationPairingData

@[expose] public section

open scoped Classical NumberField ENNReal NNReal Topology
open MeasureTheory
open DedekindZetaZeroFree.KPMsRationalCompactCrossPairing
namespace DedekindZetaZeroFree.KPMsRationalCompactCrossPairingProof
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem scalarSmooth_continuous
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (f : KPGlobalTorusFunctionData.BorelFunctions F ζ hζ Q)
    (hf : f ∈ scalarSmooth F ζ hζ Q) : Continuous f.val := by apply DedekindZetaZeroFree.KPMsRationalCompactCrossPairing.compact_core_scalar_continuous <;> assumption

theorem sourceCore_le_scalarSmooth (D : Iwasawa F ζ hζ) :
    sourceCore F ζ hζ D ≤ scalarSmooth F ζ hζ (sourcePolarization F ζ hζ 0) := by apply DedekindZetaZeroFree.KPMsRationalCompactCrossPairing.compact_source_core_smooth <;> assumption

theorem sourceCore_continuous {D : Iwasawa F ζ hζ} (f : Vplus F ζ hζ D) :
    Continuous f.val.val :=
  scalarSmooth_continuous _ _ (sourceCore_le_scalarSmooth D f.property)
