module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothABP
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothABPReflection

/-! # Reflection of the conditional smooth autonomous estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic TheoremA

/-- The backward smooth estimate retains the positive-set source and the same constant. -/
theorem autonomous_smooth_localised_of_below_four_density
    (hdensity : BelowFourDensityStatement)
    
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (p : ℝ)
    (hp : criticalP ⟨Lam / lam, (le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)⟩ < p) :
    ∃ C : ℝ, 0 < C ∧ SmoothBackwardABP lam Lam p C := by
  obtain ⟨C, hC, hforward⟩ := forward_autonomous_abp_of_below_four_density hdensity lam Lam hlam hLam p hp
  exact ⟨C, hC, hforward.reflect⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
