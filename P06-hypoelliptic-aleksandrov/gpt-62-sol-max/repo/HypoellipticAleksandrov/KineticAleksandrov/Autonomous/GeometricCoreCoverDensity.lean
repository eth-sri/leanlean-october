module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GeometricCoreDensityGluing
import Mathlib.Tactic

/-! # Improved density in cylinders whose velocities meet the region near zero -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal

/-- The source geometric-cover density theorem from the band estimate and zero capacity. -/
theorem below_four_near_velocity_density (hband : BelowFourBandStatement)
    
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha q : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam) ((le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)) - 2 < alpha ∧ alpha < 1)
    (hq : 1 < q ∧ q < (4 - (1 - alpha)) / (3 - (1 - alpha))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (Z₀ : Point) (R : ℝ) (hR : 0 < R) (P : Point)
      (hP : P ∈ forwardCylinder Z₀ R hR),
      |Z₀.velocity 0| ≤ 8 * R →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        (stripGreen A (capacityCylinderInterval Z₀ R hR)
          (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)).restrict
            (forwardCylinder Z₀ R hR) =
          (volume.restrict (forwardCylinder Z₀ R hR)).withDensity
            (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) (volume.restrict (forwardCylinder Z₀ R hR)) ∧
        (eLpNorm G (ENNReal.ofReal q)
          (volume.restrict (forwardCylinder Z₀ R hR))).toReal ≤ C * R ^ (6 / q - 4) := by
  have hx := belowFour_exponent_range lam Lam hlam hLam alpha q ha hq
  let delta := 4 - 3 * q + (1 - alpha) * (q - 1)
  have hd : 0 < delta := hx.2.2
  have hq0 : 0 < q := zero_lt_one.trans hq.1
  obtain ⟨C, hC, hc⟩ := hband lam Lam hlam hLam alpha q ha ⟨hq.1, hx.2.1⟩
  let total := ∑' j, geometricBandPower delta j
  have ht : 0 < total := geometricBandPower_tsum_pos delta hd
  refine ⟨(2 * C * total) ^ (1 / q), by positivity, ?_⟩
  intro A Z₀ R hR P hP hnear
  have h := geometricCoreDensity_of_power_bounds A Z₀ R hR P hP hnear C delta q hC.le hd hq0 ?_
  · obtain ⟨G, ⟨hm, h0, he⟩, hp, hn⟩ := h
    exact ⟨G, hm, h0, he, hp, hn⟩
  · intro i c _
    obtain ⟨f, hfm, hf0, hfd, hfp, hfn⟩ := hc A c Z₀ R hR P hP
      (geometricCoreClock_center R hR i.2 i.1) (geometricCoreClock_radius R hR i.2 i.1)
    rw [show c.r / R = _ from geometricCoreClock_radius_ratio R hR i.2 i.1] at hfn
    exact ⟨f, hfm, hf0, hfd, density_power_integral_le _ f q _ hq0
      (by unfold geometricBandPower; positivity) hfp hfn⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
