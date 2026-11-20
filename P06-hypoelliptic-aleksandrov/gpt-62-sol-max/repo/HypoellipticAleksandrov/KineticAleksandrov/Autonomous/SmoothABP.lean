module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothABPFromDensity

/-! # The forward autonomous ABP estimate conditional on improved cylinder density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open scoped MatrixOrder Matrix.Norms.Elementwise

/-- The uniform smooth forward estimate uses no additional analytic hypothesis beyond
the exact improved density statement. -/
theorem forward_autonomous_abp_of_below_four_density
    (hdensity : BelowFourDensityStatement)
    
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (p : ℝ)
    (hp : criticalP ⟨Lam / lam, (le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)⟩ < p) :
    ∃ C : ℝ, 0 < C ∧ SmoothForwardABP lam Lam p C := by
  obtain ⟨alpha, ha, ha1, -, hq, hqa⟩ := exists_autonomous_exponents lam Lam hlam hLam p hp
  obtain ⟨C, hC, hden⟩ := hdensity lam Lam hlam hLam alpha (p / (p - 1))
    ⟨ha, ha1⟩ ⟨hq, hqa⟩
  have hcritical := (criticalP_bounds ⟨Lam / lam, (le_div_iff₀ hlam).2
    (by simpa only [one_mul] using hLam)⟩).1
  have hp1 : 1 < p := by linarith only [hcritical, hp]
  have hid := autonomous_conjugate_identities p hp1
  refine ⟨C, hC, ?_⟩
  intro A Z₀ R hR u g hcont hreg hg0 hLp hsub
  refine forward_autonomous_abp_of_density_bound hlam A Z₀ R hR hp1 (mul_pos hC (Real.rpow_pos_of_pos hR _))
    ?_ u g hcont hreg hg0 hLp hsub
  intro P hP
  obtain ⟨G, hm, hn, he, hG, hb⟩ := hden A Z₀ R hR P hP
  rw [autonomousCylinderGreen, dite_eq_left hP]
  exact ⟨G, ⟨hm, hn, he⟩, hG, hid.2 ▸ hb⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
