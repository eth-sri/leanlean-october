module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.CompactWeakFormDomain

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorTestFriedrichs

open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)

structure Properties : Prop where
  embeddings : KPContActualSectorTestEmbeddings.Properties
    (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H)

  friedrichs : KPContActualSectorFriedrichsSynthesis.Properties
    F ζ hζ U R P H μG hμG hR realization

end DedekindZetaZeroFree.KPContActualSectorTestFriedrichs

namespace DedekindZetaZeroFree

theorem kp_cont_actual_sector_test_friedrichs
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    KPContActualSectorTestFriedrichs.Properties F ζ hζ U R P H μG hμG hR realization :=
  {
    embeddings :=
      kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H realization
    friedrichs :=
      kp_cont_actual_sector_friedrichs_synthesis F ζ hζ μG hμG U R hR P H realization
     }

end DedekindZetaZeroFree

end
