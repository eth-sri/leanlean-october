module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.SpectralCoordinateAndPoleOrders
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ComplexStandardIntertwinerGerm
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ContinuedOperatorFamilies

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
open MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ActualLocalProduct
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneShellRepair
open _root_.DedekindZetaZeroFree.KPRankOneTranslatedMeromorphy (actual_coordinate_regular)

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem finite_coordinate_analytic
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (φ : compactPicture S.borel P S.iwasawa .plus)
    (k : S.iwasawa.compact.toOpenSubgroup) (t : actualTorus F ζ hζ q) :
    AnalyticOnNhd ℂ
      (fun s => ((actualCanonicalContinued F q ζ hζ S P μ hμ .plus s φ).val k).val t)
      KPContinuation.spectralDomain := by
  have hd : DifferentiableOn ℂ
      (fun s => ((actualCanonicalContinued F q ζ hζ S P μ hμ .plus s φ).val k).val t)
      KPContinuation.spectralDomain := by
    intro s hs
    refine ((actual_coordinate_regular F ζ hζ q S P μ hμ
      (actualFamilyUniformizer F q) (actualFamilyUniformizer_spec F q) .plus φ k t).2 s (denominator_ne_zero_of_convergence (LocalField F q) .plus s ?_)).differentiableWithinAt
    simpa [convergenceHalfPlane, KPContinuation.spectralDomain, neg_div] using hs
  exact hd.analyticOnNhd KPContinuation.spectralDomain_isOpen

variable (E : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (S : ∀ q : E, CanonicalFiniteInducingData F ζ hζ q.val)
    (P : ∀ q : E, Polarization (S q).heisenberg)
    (μ : ∀ q : E, Measure (LocalField F q.val))
    [hHaar : ∀ q : E, (μ q).IsAddHaarMeasure]
    (hμ : ∀ q : E, μ q ((valuation (LocalField F q.val)).integer : Set (LocalField F q.val)) = 1)
    (φ : ∀ q : E, compactPicture (S q).borel (P q) (S q).iwasawa .plus)
    (k : ∀ q : E, (S q).iwasawa.compact.toOpenSubgroup)
variable (t : ∀ q : E, actualTorus F ζ hζ q.val)
    (β : NumberField.InfinitePlace F → ℂˣ)
    (ψ : NumberField.InfinitePlace F → KPComplexIntertwinerParameterMajorant.CompactPicture)
    (g : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)

end DedekindZetaZeroFree.KPGlobalResidualKernel.ActualLocalProduct

end
