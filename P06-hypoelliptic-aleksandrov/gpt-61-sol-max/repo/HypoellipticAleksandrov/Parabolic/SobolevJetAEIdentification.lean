module

public import HypoellipticAleksandrov.Parabolic.UniformC2JetLimit
public import HypoellipticAleksandrov.Parabolic.LocalizedHigherJetMollification
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.HigherWeakDerivativeMollification
public import HypoellipticAleksandrov.Measure.TimeVelocity


open private HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily.ordinaryRepresentative_memLp_volume from HypoellipticAleksandrov.Parabolic.HigherWeakDerivativeMollification


/-!
# Almost-everywhere identification of the Sobolev jet
-/

 public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Filter
open scoped ENNReal

section




/-- A uniform coordinate-jet limit agrees almost everywhere with the selected
ambient weak representative. -/
theorem coordinateJet_aeEq_ordinaryRepresentative_of_uniformLimit
    {d : ℕ} {root : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (G : ParabolicWeakDerivativeFamily d (2 * (d + 4)) Set.univ root)
    (rho : ℝ) (hrho : 0 < rho)
    (v : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (huniform : ∀ alpha : TimeVelocityDerivativeIndex d 2,
      TendstoUniformly
        (fun n ↦ TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
          (SpacetimeMollifier.spacetimeMollification (shrinkingRadius rho n)
            (G.ordinaryRepresentative
              (TimeVelocityDerivativeIndex.zero d (d + 4)))))
        (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 v) atTop) :
    ∀ alpha : TimeVelocityDerivativeIndex d 2,
      TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 v =ᵐ[
        (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)]
        G.ordinaryRepresentative
          (TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) alpha) := by
  intro alpha
  let beta  :=
    TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) alpha
  let f  := fun n =>
    SpacetimeMollifier.spacetimeMollification (shrinkingRadius rho n)
      (G.ordinaryRepresentative beta)

  have hLp  := (G.tendsto_eLpNorm_spacetimeMollification_ordinaryRepresentative_sub beta).comp
      (tendsto_shrinkingRadius_nhdsWithin rho hrho)



  obtain ⟨ns, hns, hnae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hLp).exists_seq_tendsto_ae
  filter_upwards [hnae] with z hz



  exact tendsto_nhds_unique (by
      convert (((huniform alpha).tendsto_at z).comp hns.tendsto_atTop) using 1
      funext i
      exact (congrFun ((show ∀ n,
      TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
          (SpacetimeMollifier.spacetimeMollification (shrinkingRadius rho n)
            (G.ordinaryRepresentative
              (TimeVelocityDerivativeIndex.zero d (d + 4)))) = f n by
          intro n
          exact G.coordinateIteratedFDeriv_spacetimeMollification_ordinaryRepresentative
            _ (shrinkingRadius_pos rho hrho n) beta) (ns i)) z).symm) hz

end

end HypoellipticAleksandrov.Parabolic
