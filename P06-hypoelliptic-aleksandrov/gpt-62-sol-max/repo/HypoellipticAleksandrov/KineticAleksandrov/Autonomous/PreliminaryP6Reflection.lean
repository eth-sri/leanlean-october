module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PreliminaryP6ABP
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothABPReflection

/-! # Reflection of the preliminary smooth estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic TheoremA

/-- The backward smooth estimate retains the positive-set source and the same constant. -/
theorem preliminary_backward_abp_of_entrance
    (hentrance : EntranceStatement)
    
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧ SmoothBackwardABP lam Lam 6 C := by
  obtain ⟨C, hC, hforward⟩ := preliminary_forward_abp_of_entrance hentrance lam Lam hlam hLam
  exact ⟨C, hC, hforward.reflect⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
