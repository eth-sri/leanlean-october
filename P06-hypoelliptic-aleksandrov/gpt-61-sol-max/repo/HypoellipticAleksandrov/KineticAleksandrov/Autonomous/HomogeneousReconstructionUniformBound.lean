module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionGap

/-! # Uniform bounds of the actual homogeneous reconstruction on closed future slabs -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory Parabolic


/-- An actual reconstruction satisfying its proved formula and trace continuity remains
uniformly bounded up to every closed future slab. -/
theorem reconstruction_uniform_bound
    (H : Interval) (E : StripEvolution H) {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (lower T : ℝ) (e : StripPole H (T : WithTop ℝ)) (he : lower < e.1.time)
    (phi u : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H lower T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H lower T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M)
    (hformula : ∀ e : StripPole H (T : WithTop ℝ), lower < e.1.time →
      u e.1 = phi e.1 - ∫ p, -forwardScalarOperator A.a phi p ∂stripGreenOfKernel H E.2 T e)
    (hc : ContinuousOn u (reconstructionStrip H lower T ∪ reconstructionExit H lower T)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ reconstructionClosedSlab H e.1.time T, |u p| ≤ B := by
  obtain ⟨g, hg, _⟩ := exists_bounded_reconstruction_source A H lower T phi hphi hb
  obtain ⟨C, hC, hgb⟩ := g.exists_bound
  obtain ⟨M, hM⟩ := hb


  have hLT  := he.trans (WithTop.coe_lt_coe.mp e.2.1)
  let B := M + C * (T - lower)

  refine ⟨B, (add_nonneg ((abs_nonneg _).trans (hM e.1 (⟨he, WithTop.coe_lt_coe.mp e.2.1, e.2.2⟩)).1) (mul_nonneg hC (sub_nonneg.mpr hLT.le))), reconstruction_closed_slab_test_bound H he
    (WithTop.coe_lt_coe.mp e.2.1) u hc B ?_⟩
  intro p hp
  let ep : StripPole H (T : WithTop ℝ) := ⟨p, WithTop.coe_lt_coe.mpr hp.2.1, hp.2.2⟩




  have heq : u p = phi p - stripSourcePotential H E.2 T g p := by
    rw [hformula ep hp.1, stripSourcePotential_eq_green H E.2 T g ep, stripPotentialOfKernel]
    rw [integral_congr_ae (show g =ᵐ[stripGreenOfKernel H E.2 T ep] fun q => -forwardScalarOperator A.a phi q by
        filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T ep,
          reconstruction_green_ae_time_gt H E.2 T ep] with q hq ht
        exact hg q ⟨hp.1.trans ht, hq⟩)]
  rw [heq]
  exact (abs_sub _ _).trans ((add_le_add (hM p hp).1 ((reconstruction_potential_abs_le_time H E.2 T g C hC hgb p).trans (mul_le_mul_of_nonneg_left (max_le (sub_le_sub_left hp.1.le T) (sub_nonneg.mpr hLT.le)) hC))))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
