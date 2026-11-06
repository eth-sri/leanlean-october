module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionTimeJet
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionJetConvergence

/-! # Recovery of the literal extended time representative -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory HypoellipticAleksandrov.Parabolic


variable {d : ℕ} {alpha : ℝ} (h : CounterProfileStatement d alpha) (r mu R t : ℝ)

/-- At fixed time the raw time derivative is continuous in the spatial parameter. -/
theorem construction_rawTimeJet_continuous  :
    Continuous (fun q : XV d =>
      kineticTimeDerivative (timeCutoffProfile (profileFunction h) alpha r mu R)
        ⟨t, q.1, q.2⟩) := by
  simp_rw [timeCutoffProfile_timeDerivative, barrier_timeDerivative]
  have hs := ((continuous_selectedFlatProfile h r).sub
    (contDiff_nativeBarrier d mu R t).continuous)
  exact ((contDiff_timeCutoffTheta.continuous_deriv (by simp)).comp hs).neg.mul
    (continuous_const.mul (continuous_const.sub
      ((PDE.contDiff_vecNormSq.continuous.comp continuous_snd).div_const _)))

/-- The time representative of the actual extension is locally integrable. -/
theorem construction_extendedTimeJet_locallyIntegrable  :
    LocallyIntegrable (constructionExtendedTimeJet h r mu R t) volume := (construction_rawTimeJet_continuous h r mu R t).locallyIntegrable.indicator
    (isOpen_lt ((selectedProfile_spec h).2.2.2.2.2.2.1) continuous_const).measurableSet

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
