module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.MixtureDensityMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstractHolder
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral

/-! # Uniform conjugate-test bounds for the actual Green mixture

Source: companion paper, Corollary 8.4. The one-pole estimate is integrated against the actual Borel
family. No joint measurability of arbitrarily chosen pole densities is asserted.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory
open SectionTwo


/-- The one-pole density estimate bounds every positive bounded conjugate test uniformly. -/
theorem mixture_density_conjugate_tests
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q p : ℝ) (hpq : q.HolderConjugate p) (hq2 : q < (3 : ℝ) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (nu : Measure Point) [IsFiniteMeasure nu] (f : BoundedBorel Point),
      MemLp f (ENNReal.ofReal p)  → (∀ z, 0 ≤ f z) →
      (∫ z, f z ∂enlargedActiveGreen hH hLE hlam hLam A c nu) ≤
        C * c.r ^ (6 / q - 4) * (eLpNorm f (ENNReal.ofReal p) ).toReal *
          (nu univ).toReal := by
  obtain ⟨C, hC, hc⟩ := one_sign_pole_density hH hLE hlam hLam q hpq.lt hq2
  refine ⟨C, hC, ?_⟩
  intro A c nu _ f hfp hfn
  classical
  let K := enlargedActiveGreenKernel hH hLE hlam hLam A c
  let L := C * c.r ^ (6 / q - 4) * (eLpNorm f (ENNReal.ofReal p) ).toReal
  have hL : 0 ≤ L := mul_nonneg
    (mul_nonneg hC.le (Real.rpow_nonneg c.positive.le _)) ENNReal.toReal_nonneg
  have  := mixtureActiveGreenKernel_isFiniteKernel hH hLE hlam hLam A c

  have hfi : Integrable f (K ∘ₘ nu) := boundedBorel_integrable f _

  have hm := integral_mono (by
      rw [Measure.comp_eq_comp_const_apply] at hfi
      simpa only [Kernel.const_apply] using hfi.integral_comp) (integrable_const  L) (by
      intro e
      by_cases he : e.velocity 0 ∈ c.active
      · obtain ⟨g, hgm, hgn, hgd, hgb, _⟩ := hc A c e he

        have hgr  :=
          (ENNReal.toReal_mono ENNReal.ofReal_ne_top hgb).trans_eq
            (ENNReal.toReal_ofReal (mul_nonneg hC.le (Real.rpow_nonneg c.positive.le _)))
        have htest := abp_potential_holder volume _ g f hpq hgm hgn
          (Filter.Eventually.of_forall hfn) hgd (hgb.trans_lt ENNReal.ofReal_lt_top) hfp hgr
        change (∫ z, f z ∂(if hv : e.velocity 0 ∈ c.active then
          stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e hv)
            else 0)) ≤ L
        rw [dite_eq_left he]
        exact htest
      · change (∫ z, f z ∂(if hv : e.velocity 0 ∈ c.active then
          stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e hv)
            else 0)) ≤ L
        rw [dite_eq_right he, integral_zero_measure]
        exact hL)

  change (∫ z, f z ∂K ∘ₘ nu) ≤ L * (nu univ).toReal
  rw [(nested_integral_bind nu K K.measurable f hfi)]
  simpa only [integral_const, smul_eq_mul, Measure.real, mul_comm] using hm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
