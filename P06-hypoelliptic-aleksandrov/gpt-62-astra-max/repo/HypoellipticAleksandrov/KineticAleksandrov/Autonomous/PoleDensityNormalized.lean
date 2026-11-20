module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityExtension
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateDensity

/-! # The actual normalized physical Green has a uniform real Lebesgue density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution Green
open scoped ENNReal NNReal

/-- The actual normalized physical Green has a uniformly bounded measurable real density.
Only ellipticity and the exponent enter the constant; the three classical inputs are explicit. -/
theorem clockGreen_real_density
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q) (hq2 : q < (3 : ℝ) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
      (he : e.velocity 0 ∈ c.active), ∃ F : Point → ℝ,
      Measurable F ∧ (∀ p, 0 ≤ F p) ∧
      clockGreen hlam hLam A c e he = volume.withDensity (fun p => ENNReal.ofReal (F p)) ∧
      eLpNorm F (ENNReal.ofReal q) volume ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hc⟩ := clockNativeGreen_density hlam hLam q hq hq2
  refine ⟨C, hC, ?_⟩
  intro A c e he
  obtain ⟨G, hm, hd, hn, -⟩ := hc A c e he
  obtain ⟨F, hFm, hFn, hFd, hFN, hFLp⟩ := real_density_of_eLpNorm_bound volume
    (clockGreen hlam hLam A c e he) (poleDensityExtend G)
    (poleDensityExtend_measurable hm) ((congrArg (fun μ : Measure (GreenCarrier 1) => μ.map (elapsedPhysicalPoint 0)) hd).trans (poleDensityExtend_map_withDensity hm)) q C (by linarith) hC.le ((poleDensityExtend_eLpNorm hm _).le.trans hn)
  refine ⟨F, hFm, hFn, hFd, ?_⟩
  exact (ENNReal.ofReal_toReal hFLp.eLpNorm_ne_top).symm.le.trans
    (ENNReal.ofReal_le_ofReal hFN)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
