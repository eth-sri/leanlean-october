module

public import HypoellipticAleksandrov.Parabolic.SobolevJetAEIdentification
public import HypoellipticAleksandrov.Parabolic.C2ToScalarC12
import HypoellipticAleksandrov.Parabolic.LocalizedHigherJetMollification
import HypoellipticAleksandrov.Parabolic.UniformC2JetLimit

/-!
# Finite-order Sobolev representatives with scalar parabolic regularity
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped Topology

noncomputable section
open Filter
open scoped ENNReal

/- A finite ordinary weak-derivative family through parabolic weight
`2 * (d + 4)` has one scalar `C^1,2` representative on a positive collar of
every compact subset of its open carrier, with its complete order-two
coordinate jet identified almost everywhere. -/
theorem exists_finiteOrderSobolevC12Representative
    {d U C}
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    {u }
    (D : ParabolicWeakDerivativeFamily d (2 * (d + 4)) U u) :
    ∃ (rho : ℝ) (_ : 0 < rho) (v : TimeVelocity d → ℝ),
      Metric.thickening rho C ⊆ U ∧
      ContDiff ℝ 2 v ∧
      IsScalarC12On v (Metric.thickening rho C) ∧
      v =ᵐ[timeVelocityVolumeOn (Metric.thickening rho C)] u ∧
      ∀ alpha : TimeVelocityDerivativeIndex d 2,
        TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 v =ᵐ[
          timeVelocityVolumeOn (Metric.thickening rho C)]
          D.ordinaryRepresentative
            (TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) alpha) := by
  obtain ⟨rho, hrho, K, hK, hKMeas, hKFinite, b, hbSmooth,
      hbCompact, hbSupport, G, hbOne, hrepEq, hmoll⟩ :=
    exists_localizedHigherJetMollification hU hC hCU D
  have hcollar : Metric.thickening rho C ⊆ U := by
    intro z hz
    apply hbSupport
    apply subset_tsupport b
    change b z ≠ 0
    rw [hbOne (Metric.thickening_subset_cthickening rho C hz)]
    norm_num
  have hsupp : ∀ ε, 0 < ε → ε < rho →
      ∀ beta : TimeVelocityDerivativeIndex d (d + 4),
        tsupport (SpacetimeMollifier.spacetimeMollification ε
          (G.ordinaryRepresentative beta)) ⊆ K := by
    intro ε hε hεrho beta
    exact (hmoll ε hε hεrho beta).2.1
  obtain ⟨v, hv, huniform⟩ :=
    exists_contDiff_two_uniformLimit_coordinateJet_spacetimeMollification_shrinkingRadius
      G rho hrho K hK hsupp
  have hglobal : ∀ alpha : TimeVelocityDerivativeIndex d 2,
      TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 v =ᵐ[
        (volume : Measure (TimeVelocity d))]
        G.ordinaryRepresentative
          (TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) alpha) := by
    intro alpha
    let beta :=
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
        (volume : Measure (TimeVelocity d))) atTop (nhds 0) := by
      exact (G.tendsto_eLpNorm_spacetimeMollification_ordinaryRepresentative_sub beta).comp
        (tendsto_shrinkingRadius_nhdsWithin rho hrho)
    have hbetaMem : MemLp (G.ordinaryRepresentative beta) (2 : ℝ≥0∞)
        (volume : Measure (TimeVelocity d)) := by
        have h := G.ordinaryRepresentative_memLp beta
        change MemLp (G.ordinaryRepresentative beta) (2 : ℝ≥0∞)
          ((volume : Measure (TimeVelocity d)).restrict Set.univ) at h
        simpa only [Measure.restrict_univ] using h

      /- A uniform coordinate-jet limit agrees almost everywhere with the selected
      ambient weak representative. -/
    have hfMeas : ∀ n, AEStronglyMeasurable (f n)
        (volume : Measure (TimeVelocity d)) := by
      intro n
      exact (SpacetimeMollifier.contDiff_spacetimeMollification
        (shrinkingRadius_pos rho hrho n) _
        (hbetaMem.locallyIntegrable (by norm_num))).continuous.aestronglyMeasurable
    have hmeasure :=
      tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hLp
    obtain ⟨ns, hns, hnae⟩ := hmeasure.exists_seq_tendsto_ae
    filter_upwards [hnae] with z hz
    have huPoint :=
      (huniform alpha).tendsto_at z
    have huSub := huPoint.comp hns.tendsto_atTop
    have huSub' : Tendsto (fun i => f (ns i) z) atTop
        (nhds (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 v z)) := by
      convert huSub using 1
      funext i
      exact (congrFun (hf_eq (ns i)) z).symm
    exact tendsto_nhds_unique huSub' hz
  let S := Metric.thickening rho C
  have hSMeas : MeasurableSet S := Metric.isOpen_thickening.measurableSet
  have hjet : ∀ alpha : TimeVelocityDerivativeIndex d 2,
      TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 v =ᵐ[
        timeVelocityVolumeOn S]
        D.ordinaryRepresentative
          (TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) alpha) := by
    intro alpha
    let beta :=
      TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) alpha
    rw [timeVelocityVolumeOn]
    filter_upwards [
      (hglobal alpha).filter_mono (ae_mono Measure.restrict_le_self),
      (ae_restrict_iff' hSMeas).2
        (Filter.Eventually.of_forall fun z hz =>
          hrepEq beta (Metric.thickening_subset_cthickening rho C hz))] with z hz hEqz
    exact hz.trans hEqz
  have hvalue : v =ᵐ[timeVelocityVolumeOn S] u := by
    let zero :=
      TimeVelocityDerivativeIndex.zero d 2
    have hcast : TimeVelocityDerivativeIndex.castLE
        (by omega : 2 ≤ d + 4) zero =
        TimeVelocityDerivativeIndex.zero d (d + 4) := by
      rfl
    have hvzero := hjet zero
    rw [hcast] at hvzero
    change TimeVelocityMultiIndex.coordinateIteratedFDeriv
      (0 : TimeVelocityMultiIndex d) v =ᵐ[timeVelocityVolumeOn S]
        D.ordinaryRepresentative (TimeVelocityDerivativeIndex.zero d (d + 4)) at hvzero
    have hvrep : v =ᵐ[timeVelocityVolumeOn S]
        D.ordinaryRepresentative (TimeVelocityDerivativeIndex.zero d (d + 4)) := by
      filter_upwards [hvzero] with z hz
      simpa only [TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero] using hz
    exact hvrep.trans (D.ordinaryRepresentative_zero_ae.filter_mono (ae_mono (Measure.restrict_mono_set volume hcollar)))
  refine ⟨rho, hrho, v, hcollar, hv, isScalarC12On_of_contDiff_two hv S,
    hvalue, ?_⟩
  exact hjet

end

end HypoellipticAleksandrov.Parabolic
