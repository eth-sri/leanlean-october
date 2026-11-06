module

public import HypoellipticAleksandrov.Parabolic.UniformC2JetLimit
public import HypoellipticAleksandrov.Parabolic.LocalizedHigherJetMollification

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
      (volume : Measure (TimeVelocity d)) := by
  have h := G.ordinaryRepresentative_memLp beta
  change MemLp _ _
    (volume.restrict Set.univ) at h
  simp_all

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
        (volume : Measure (TimeVelocity d))]
        G.ordinaryRepresentative
          (TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) alpha) := by
  intro alpha
  let beta : TimeVelocityDerivativeIndex d _ :=
    TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) alpha
  let f  := fun n =>
    SpacetimeMollifier.spacetimeMollification (shrinkingRadius rho n)
      (G.ordinaryRepresentative beta)
  have hf_eq : ∀ n,
      TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
          (SpacetimeMollifier.spacetimeMollification (shrinkingRadius rho n)
            (G.ordinaryRepresentative
              (TimeVelocityDerivativeIndex.zero d _))) = f n := by
    intro n
    exact G.coordinateIteratedFDeriv_spacetimeMollification_ordinaryRepresentative
      _ (shrinkingRadius_pos rho hrho n) beta
  have hLp : Tendsto (fun n => eLpNorm
      (f n - G.ordinaryRepresentative beta) (2)
      volume) atTop (nhds 0) := (G.tendsto_eLpNorm_spacetimeMollification_ordinaryRepresentative_sub beta).comp
      (tendsto_shrinkingRadius_nhdsWithin rho hrho)
  have hmeasure : TendstoInMeasure _ f atTop
      _ :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hLp
  obtain ⟨ns, hns, hnae⟩ := hmeasure.exists_seq_tendsto_ae
  filter_upwards [hnae] with z hz
  have huPoint  :=
    (huniform alpha).tendsto_at z
  have huSub := huPoint.comp hns.tendsto_atTop
  have huSub' : Tendsto (fun i => f (ns i) z) atTop
      (nhds (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 v z)) := by
    aesop
  exact tendsto_nhds_unique huSub' hz

end

end HypoellipticAleksandrov.Parabolic
