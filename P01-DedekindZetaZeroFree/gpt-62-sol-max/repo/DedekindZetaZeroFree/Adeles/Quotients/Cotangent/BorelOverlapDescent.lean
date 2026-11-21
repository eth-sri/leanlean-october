module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.OverlapNullEquivalence
public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.IntegralDescent

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentBorelOverlapDescent

open KPContActualCotangentCountableShrinking
open KPContCotangentOverlapRationalBranches KPContCotangentOverlapNullEquivalence

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

end DedekindZetaZeroFree.KPContActualCotangentBorelOverlapDescent

namespace DedekindZetaZeroFree

open KPContActualCotangentCountableShrinking
open KPContCotangentFiniteQuotientBorel KPContCotangentChartDescentIntegrals

theorem kp_cont_actual_cotangent_borel_overlap_descent
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (cover : CountableCover F ζ hζ U R P H)
    (S : Type*) [MeasurableSpace S] :
    ∀ a : ShrunkChart F ζ hζ U R P H,
      (∀ n : ℕ, Nonempty (KPContCotangentCorrectedNullEquivalence.NonsingularEnumeration2
        a (cover.chart n))) ∧
      (∀ f : a.domain → S, Measurable f →
        (∀ σ y, f (a.action σ y) = f y) → BorelDescends a.quotientMap f) ∧
      ChartDescentIntegrals a := by
  have realization :
      KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H :=
    actual_levelRealization_of_recipe F ζ hζ U R P H
  intro a
  have ha : a.Properties := every_shrunkChart_properties F ζ hζ U R P H a
  refine ⟨?_, ?_, ?_⟩
  · intro n
    obtain ⟨e⟩ :=
      kp_cont_cotangent_overlap_rational_branches F ζ hζ μG hμG U R hR P H
        realization cover a ha n
    exact ⟨KPContCotangentCorrectedNullEquivalence.withNonsingularity2 e⟩
  · intro f hf hinv
    exact (kp_cont_cotangent_finite_quotient_borel F ζ hζ U R P H S).2 a f hf hinv
  · exact kp_cont_cotangent_chart_descent_integrals F ζ hζ U R P H a

end DedekindZetaZeroFree

end
