module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CompactCoreLaurentExponents
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactIntegrationOfLaurentFamilies

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField
open NumberField IsDedekindDomain MeasureTheory
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneRootParameter
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)

theorem actual_initial_cutoff_laurent (P : Polarization S.heisenberg)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure] (ε : Sign)
    (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
    (g : ActualCover F ζ hζ q) (h : actualTorus F ζ hζ q)
    (C : Set (LocalField F q)) (hC : IsCompact C) (hmC : MeasurableSet C) :
    ∃ p : ℤ →₀ ℂ, ∀ s : ℂ,
      (∫ x in C,
        ((compactTrivialization S.borel P S.iwasawa (sourceSign ε)
          (sourceParameter ε s) φ).val
          (kernelW (LocalField F q) S.borel ε *
            (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) * g)).val h ∂μ) =
        p.sum (fun n c => (evaluationUnit (LocalField F q) ε s : ℂ) ^ n * c) := by
  classical
  let a := fun x =>
    kernelW (LocalField F q) S.borel ε *
      (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) * g
  let H := fun x s =>
    ((compactTrivialization S.borel P S.iwasawa (sourceSign ε)
      (sourceParameter ε s) φ).val (a x)).val h
  let c := fun x => H x 0
  let e := fun x => initialExponent F ζ hζ q S (a x)
  have hm (x : LocalField F q) (s : ℂ) :
      H x s = c x * (evaluationUnit (LocalField F q) ε s : ℂ) ^ e x := by
    have hz := initialCoordinate_monomial F ζ hζ q S P ε φ (a x) h 0
    have hu : (evaluationUnit (LocalField F q) ε 0 : ℂ) = 1 := by
      cases ε <;> simp [evaluationUnit, rUnit, r]
    rw [hu, one_zpow, mul_one] at hz
    exact (initialCoordinate_monomial F ζ hζ q S P ε φ (a x) h s).trans (congrArg (fun z => z * (evaluationUnit (LocalField F q) ε s : ℂ) ^ e x) hz.symm)
  have hH : IsLocallyConstant H := by
    rw [(funext (fun x => funext (hm x)))]
    exact (standardIntegral_integrand_locallyConstant (LocalField F q) S.borel P S.iwasawa ε 0 φ g h).comp₂ ((initialExponent_locallyConstant F ζ hζ q S).comp_continuous ((continuous_const.mul (continuous_subtype_val.comp
      (S.borel.upperRoot_continuous.comp continuous_ofAdd))).mul continuous_const)) (fun z n => fun s : ℂ => z *
      (evaluationUnit (LocalField F q) ε s : ℂ) ^ n)
  apply KPTameTransposeBaseChartNumerator.compact_set_integral_laurent_family
    μ C hC hmC hC.measure_ne_top (evaluationUnit (LocalField F q) ε) H
    (hH.comp_continuous continuous_subtype_val)
  intro x hx
  refine ⟨Finsupp.single (e x) (c x), ?_⟩
  intro s
  rw [Finsupp.sum_single_index (by simp)]
  exact (hm x s).trans (mul_comm _ _)

end DedekindZetaZeroFree.KPRankOneShellRepair

end
