module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierModulusEstimates
import Batteries.Tactic.Alias
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsFiber



/-! # Position-fiber majorants of the actual homogeneous Bellman jets -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierRegularization
open Set MeasureTheory

/-- The position coordinate gives its own cube-root gauge lower bound. -/
alias barrier_position_gauge_lower := _root_.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.barrier_position_gauge_lower


/-- A negative homogeneous gauge bound has a uniform position-fiber power majorant. -/
alias barrier_position_fiber_bound := _root_.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.barrier_position_fiber_bound


/-- The three jet fibers are integrable on every compact position interval, uniformly in v. -/
theorem barrier_jet_fiber_integrable {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1)
    (v a b : ℝ) :
    IntegrableOn (fun X => bellmanDx phi (X, v)) (Icc a b)  ∧
    IntegrableOn (fun X => bellmanDv phi (X, v)) (Icc a b)  ∧
    IntegrableOn (fun X => bellmanDvv phi (X, v)) (Icc a b)  := by
  have hi (beta : ℝ) (hb : -3 < beta) (hb0 : beta ≤ 0)
      (f : (ℝ × ℝ) → ℝ) (hc : ContinuousOn f bellmanPuncturedSet)
      (C : ℝ) (hC : 0 ≤ C)
      (hbound : ∀ q ∈ bellmanPuncturedSet, |f q| ≤ C * bellmanGauge q ^ beta) :
      IntegrableOn (fun X => f (X, v)) (Icc a b)  := by
    have hm : Measurable (fun X => f (X, v)) :=
      (measurable_of_continuousOn_compl_singleton (0, 0) hc).comp
        (measurable_id.prodMk measurable_const)
    have hmaj := ((bellman_abs_rpow_locallyIntegrable (beta / 3) (by linarith)).smul C)
      |>.integrableOn_isCompact (isCompact_Icc (a := a) (b := b))
    apply hmaj.mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with X hX
    exact barrier_position_fiber_bound beta hb0 f C hC hbound X v hX
  obtain ⟨_, hX, hv, hvv⟩ := h.origin_jet_bounds
  obtain ⟨CX, hCX, hbX⟩ := hX
  obtain ⟨Cv, hCv, hbv⟩ := hv
  obtain ⟨Cvv, hCvv, hbvv⟩ := hvv
  refine ⟨?_, ?_, ?_⟩
  · exact hi (alpha - 3) (by linarith) (by linarith) _ h.dx_continuousOn CX hCX hbX
  · exact hi (alpha - 1) (by linarith) (by linarith) _
      (h.directional_contDiffOn (0, 1)).continuousOn Cv hCv hbv
  · exact hi (alpha - 2) (by linarith) (by linarith) _ h.dvv_continuousOn Cvv hCvv hbvv

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierRegularization
