module

public import HypoellipticAleksandrov.Parabolic.SobolevJetAEIdentification
public import HypoellipticAleksandrov.Parabolic.C2ToScalarC12

/-!
# Finite-order Sobolev representatives with scalar parabolic regularity
-/

 public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory


section

/-- A finite ordinary weak-derivative family through parabolic weight
`2 * (d + 4)` has one scalar `C^1,2` representative on a positive collar of
every compact subset of its open carrier, with its complete order-two
coordinate jet identified almost everywhere. -/
theorem exists_finiteOrderSobolevC12Representative
    {d : ℕ} {U C : HypoellipticAleksandrov.Parabolic.Region d}
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (D : ParabolicWeakDerivativeFamily d (2 * (d + 4)) U u) :
    ∃ (rho : ℝ) (_ : 0 < rho) (v : HypoellipticAleksandrov.Parabolic.ScalarField d),
      Metric.thickening rho C ⊆ U ∧
      ContDiff ℝ 2 v ∧
      IsScalarC12On v (Metric.thickening rho C) ∧
      v =ᵐ[timeVelocityVolumeOn (Metric.thickening rho C)] u ∧
      ∀ alpha : TimeVelocityDerivativeIndex d 2,
        TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 v =ᵐ[
          timeVelocityVolumeOn (Metric.thickening rho C)]
          D.ordinaryRepresentative
            (TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) alpha) := by
  let sharedTerm_87f148fabc := (D.ordinaryRepresentative (TimeVelocityDerivativeIndex.zero d (d + 4)))
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

  obtain ⟨v, hv, huniform⟩ :=
    exists_contDiff_two_uniformLimit_coordinateJet_spacetimeMollification_shrinkingRadius
      G rho hrho K hK (by
          intro ε hε hεrho beta
          exact (hmoll ε hε hεrho beta).2.1)
  have hglobal := coordinateJet_aeEq_ordinaryRepresentative_of_uniformLimit
    G rho hrho v huniform
  let S  := Metric.thickening rho C

  have hjet : ∀ alpha : TimeVelocityDerivativeIndex d 2,
      TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 v =ᵐ[
        timeVelocityVolumeOn S]
        D.ordinaryRepresentative
          (TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) alpha) := by
    intro alpha

    rw [timeVelocityVolumeOn]
    filter_upwards [
      (hglobal alpha).filter_mono (ae_mono Measure.restrict_le_self),
      (ae_restrict_iff' Metric.isOpen_thickening.measurableSet).2
        (Filter.Eventually.of_forall fun z hz =>
          hrepEq (TimeVelocityDerivativeIndex.castLE (by omega : 2 ≤ d + 4) alpha) (Metric.thickening_subset_cthickening rho C hz))] with z hz hEqz
    exact hz.trans hEqz

  refine ⟨rho, hrho, v, hcollar, hv, isScalarC12On_of_contDiff_two hv S,
    (by
        let zero  :=
          TimeVelocityDerivativeIndex.zero d 2
        have hcast : TimeVelocityDerivativeIndex.castLE
            (by omega : 2 ≤ d + 4) zero =
            TimeVelocityDerivativeIndex.zero d (d + 4) := rfl
        have hvzero := hjet zero
        rw [hcast] at hvzero
        change TimeVelocityMultiIndex.coordinateIteratedFDeriv
          (0 : TimeVelocityMultiIndex d) v =ᵐ[timeVelocityVolumeOn S]
            sharedTerm_87f148fabc at hvzero

        have hDzero  :=
          D.ordinaryRepresentative_zero_ae.filter_mono
            (ae_mono (Measure.restrict_mono_set volume hcollar))
        exact (show v =ᵐ[timeVelocityVolumeOn S]
            sharedTerm_87f148fabc by
            filter_upwards [hvzero] with z hz
            simpa using hz).trans hDzero), ?_⟩
  exact hjet

end

end HypoellipticAleksandrov.Parabolic
