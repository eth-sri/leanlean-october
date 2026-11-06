module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionTimeJet
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionJetConvergence

/-! # Recovery of the literal extended time representative -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Filter HypoellipticAleksandrov.Parabolic
open scoped Topology

/- At fixed time the raw time derivative is continuous in the spatial parameter. -/
theorem construction_extendedTimeJet_locallyIntegrable {d alpha}
    (h : CounterProfileStatement d alpha) (r mu R t : ℝ) :
    LocallyIntegrable (constructionExtendedTimeJet h r mu R t) volume := by
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  have _h_inl_8 : Continuous (fun q : XV d =>
      kineticTimeDerivative (timeCutoffProfile (profileFunction h) alpha r mu R)
        ⟨t, q.1, q.2⟩) := by
    simp_rw [timeCutoffProfile_timeDerivative, barrier_timeDerivative]
    exact ((contDiff_timeCutoffTheta.continuous_deriv (by simp)).comp (((continuous_selectedFlatProfile h r).sub (contDiff_nativeBarrier d mu R t).continuous))).neg.mul
      (continuous_const.mul (continuous_const.sub
        ((PDE.contDiff_vecNormSq.continuous.comp continuous_snd).div_const _)))
  exact _h_inl_8.locallyIntegrable.indicator
    (isOpen_lt hH continuous_const).measurableSet

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
