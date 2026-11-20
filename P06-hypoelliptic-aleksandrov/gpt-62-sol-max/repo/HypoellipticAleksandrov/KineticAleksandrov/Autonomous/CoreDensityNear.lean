module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDensityArithmetic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GeometricCoreDensityGluing
import Mathlib.Tactic

/-! # Preliminary cylinder density near zero velocity

A countable subcover of the closed cores supplies the same summable positive
power as the continuous logarithmic covering. No return estimate is used.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal

/-- The preliminary sixth-fifths density in cylinders near zero velocity. -/
theorem preliminary_near_density_of_entrance (hentrance : EntranceStatement)
    
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (Z₀ : Point) (R : ℝ) (hR : 0 < R) (P : Point)
      (hP : P ∈ forwardCylinder Z₀ R hR),
      |Z₀.velocity 0| ≤ 8 * R →
      enlargedDensityBound
        ((stripGreen A (capacityCylinderInterval Z₀ R hR)
          (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)).restrict
            (forwardCylinder Z₀ R hR)) (forwardCylinder Z₀ R hR) (6 / 5) (C * R) := by
  obtain ⟨C, hC, hc⟩ := preliminary_core_density_of_entrance hentrance
    lam Lam hlam hLam
  let total := ∑' j, geometricBandPower (1 / 5) j
  have ht : 0 < total := geometricBandPower_tsum_pos _ (by norm_num)
  let B := 7 * C ^ (6 / 5 : ℝ)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨(2 * B * total) ^ (5 / 6 : ℝ), by positivity, ?_⟩
  intro A Z₀ R hR P hP hnear
  have hcover := geometricCoreDensity_of_power_bounds A Z₀ R hR P hP hnear B (1 / 5) (6 / 5)
    hB.le (by norm_num) (by norm_num)
  rw [show (6 / (6 / 5) - 4 : ℝ) = 1 by norm_num,
    show (1 / (6 / 5) : ℝ) = 5 / 6 by norm_num, Real.rpow_one] at hcover
  apply hcover
  intro i c hmeet
  have hr := c.positive
  obtain ⟨f, ⟨hfm, hf0, hfd⟩, hfp, hfn⟩ := hc A c Z₀ R hR P hP hmeet
  refine ⟨f, hfm, hf0, hfd, (preliminary_density_power_le _ f (6 / 5) _ (by norm_num)
    (by positivity) hfp hfn).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have h := preliminary_core_power_le C R c.r hC hR hr (geometricCoreClock_radius R hR i.2 i.1)
  rw [show c.r / R = _ from geometricCoreClock_radius_ratio R hR i.2 i.1] at h
  simpa only [B, geometricBandPower, show (6 - 4 * (6 / 5) : ℝ) = 6 / 5 by norm_num] using h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
