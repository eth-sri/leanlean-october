module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.CoreShellPartition
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.BoundaryFlux.AngularConormalDescent

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory Filter
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes renaming continuous_core_integrable → continuous_core_integrable
namespace DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.CutoffApproximation
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

 theorem admissible_mono {Y T : ℝ}
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y) (hYT : Y ≤ T) :
    KPMsFixedHaarDisintegration.AdmissibleCutoff A T := by
  refine ⟨lt_of_lt_of_le hY.1 hYT, hY.2.trans ?_⟩
  exact div_le_div_of_nonneg_right (Real.log_le_log hY.1 hYT) (by positivity)

 theorem modulus_gt_of_not_core
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (x : X F ζ hζ) (hx : x ∉ quotientCore A P Y) :
    Y < D.modulus (P.projection U x) := by
  have he : P.projection U x ∈ KPMsFixedHaarDisintegration.cuspEnds A Y := by
    simp only [quotientCore, Set.mem_ofPred_eq, not_forall, not_not] at hx
    obtain ⟨j,hj⟩ := hx
    exact Set.mem_iUnion.mpr ⟨j,hj⟩
  rw [← D.chart_range Y hY] at he
  obtain ⟨⟨c,r⟩,hr⟩ := he
  rw [← hr, D.chart_modulus Y hY c r]
  exact r.property

 theorem cutoff_measurable
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (Y ε : ℝ) : Measurable (coreCutoff A R P D Y ε) := by
  let : BorelSpace (X F ζ hζ) := ⟨rfl⟩
  exact Measurable.ite (FiniteSlabCoreShell.isClosed_quotientCore A P Y).measurableSet
    measurable_const (measurable_const.max (measurable_const.min
      ((measurable_const.sub (D.measurable_modulus.comp (P.continuous U).measurable)).div_const ε)))

 theorem cutoff_bound
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (Y ε : ℝ) (x : X F ζ hζ) : |coreCutoff A R P D Y ε x| ≤ 1 := by
  unfold coreCutoff
  split_ifs with hx
  · norm_num
  · rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le (by norm_num) (min_le_left _ _)

end DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.CutoffApproximation

end
