module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PreliminaryP6Density
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothABPFromDensity
import Mathlib.Tactic

/-! # The preliminary forward autonomous maximum principle -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open scoped MatrixOrder Matrix.Norms.Elementwise

/-- The preliminary forward estimate depends only on entrance counting and classical inputs. -/
theorem preliminary_forward_abp_of_entrance
    (hentrance : EntranceStatement)
    
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧ SmoothForwardABP lam Lam 6 C := by
  obtain ⟨C, hC, hden⟩ := preliminary_cylinder_density_of_entrance hentrance
    lam Lam hlam hLam
  refine ⟨C, hC, ?_⟩
  intro A Z₀ R hR u g hcont hreg hg0 hLp hsub
  refine forward_autonomous_abp_of_density_bound hlam A Z₀ R hR (p := 6) (by norm_num)
    (mul_pos hC (Real.rpow_pos_of_pos hR _)) ?_ u g hcont hreg hg0 hLp hsub
  intro P hP
  rw [autonomousCylinderGreen, dite_eq_left hP]
  norm_num only [show (6 / (6 - 1) : ℝ) = 6 / 5 by norm_num,
    show (2 - 6 / 6 : ℝ) = 1 by norm_num, Real.rpow_one]
  exact hden A Z₀ R hR P hP

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
