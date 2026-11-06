module

public import HypoellipticAleksandrov.Parabolic.UniformC2JetLimit
public import HypoellipticAleksandrov.Parabolic.LocalizedHigherJetMollification
public import HypoellipticAleksandrov.Parabolic.TypeAbbrev

/-!
# Almost-everywhere identification of the Sobolev jet
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

private theorem ordinaryRepresentative_memLp_volume
    {d m : ℕ} {root : TimeVelocity d → ℝ}
    (G : ParabolicWeakDerivativeFamily d (2 * m) Set.univ root)
    (beta : TimeVelocityDerivativeIndex d m) :
    MemLp (G.ordinaryRepresentative beta) (2 : ℝ≥0∞)
      (HypoellipticAleksandrov.Parabolic.TVVolume d) := by
  have h := G.ordinaryRepresentative_memLp beta
  change MemLp (G.ordinaryRepresentative beta) (2 : ℝ≥0∞)
    ((HypoellipticAleksandrov.Parabolic.TVVolume d).restrict Set.univ) at h
  simpa using h

/-- A uniform coordinate-jet limit agrees almost everywhere with the selected
ambient weak representative. -/
theorem coordinateJet_aeEq_ordinaryRepresentative_of_uniformLimit
    {d : ℕ} {root : TimeVelocity d → ℝ}
    (G : ParabolicWeakDerivativeFamily d (2 * (d + 4)) Set.univ root)
    (rho : ℝ) (hrho : 0 < rho)
    (v : TimeVelocity d → ℝ)
    (huniform : ∀ alpha : TimeVelocityDerivativeIndex d 2,
      TendstoUniformly
        (fun n ↦ TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
          (SpacetimeMollifier.spacetimeMollification (shrinkingRadius rho n)
            (G.ordinaryRepresentative
              (TimeVelocityDerivativeIndex.zero d (d + 4)))))
        (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 v) atTop) :
    ∀ alpha : TimeVelocityDerivativeIndex d 2,
      TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 v =ᵐ[
        (HypoellipticAleksandrov.Parabolic.TVVolume d)]
        G.ordinaryRepresentative
          (TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) alpha) := by
  intro alpha
  let beta : TimeVelocityDerivativeIndex d (d + 4) :=
    TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) alpha
  let f : ℕ → TimeVelocity d → ℝ := fun n =>
    SpacetimeMollifier.spacetimeMollification (shrinkingRadius rho n)
      (G.ordinaryRepresentative beta)
  have hf_eq : ∀ n,
      TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
          (SpacetimeMollifier.spacetimeMollification (shrinkingRadius rho n)
            (G.ordinaryRepresentative
              (TimeVelocityDerivativeIndex.zero d (d + 4)))) = f n := by
    intro n
    exact G.coordinateIteratedFDeriv_spacetimeMollification_ordinaryRepresentative
      (shrinkingRadius rho n) (shrinkingRadius_pos rho hrho n) beta
  have hLp : Tendsto (fun n => eLpNorm
      (f n - G.ordinaryRepresentative beta) (2 : ℝ≥0∞)
      (HypoellipticAleksandrov.Parabolic.TVVolume d)) atTop (nhds 0) := by
    exact (G.tendsto_eLpNorm_spacetimeMollification_ordinaryRepresentative_sub beta).comp
      (tendsto_shrinkingRadius_nhdsWithin rho hrho)
  have hbetaMem := ordinaryRepresentative_memLp_volume G beta
  have hfMeas : ∀ n, AEStronglyMeasurable (f n)
      (HypoellipticAleksandrov.Parabolic.TVVolume d) := by
    intro n
    exact (SpacetimeMollifier.contDiff_spacetimeMollification
      (shrinkingRadius_pos rho hrho n) _
      (hbetaMem.locallyIntegrable (by norm_num))).continuous.aestronglyMeasurable
  have hmeasure : TendstoInMeasure (HypoellipticAleksandrov.Parabolic.TVVolume d) f atTop
      (G.ordinaryRepresentative beta) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hLp
  obtain ⟨ns, hns, hnae⟩ := hmeasure.exists_seq_tendsto_ae
  filter_upwards [hnae] with z hz
  have huPoint : Tendsto (fun n =>
      TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (SpacetimeMollifier.spacetimeMollification (shrinkingRadius rho n)
          (G.ordinaryRepresentative
            (TimeVelocityDerivativeIndex.zero d (d + 4)))) z) atTop
      (nhds (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 v z)) :=
    (huniform alpha).tendsto_at z
  have huSub := huPoint.comp hns.tendsto_atTop
  have huSub' : Tendsto (fun i => f (ns i) z) atTop
      (nhds (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 v z)) := by
    convert huSub using 1
    funext i
    exact (congrFun (hf_eq (ns i)) z).symm
  exact tendsto_nhds_unique huSub' hz

end

end HypoellipticAleksandrov.Parabolic
