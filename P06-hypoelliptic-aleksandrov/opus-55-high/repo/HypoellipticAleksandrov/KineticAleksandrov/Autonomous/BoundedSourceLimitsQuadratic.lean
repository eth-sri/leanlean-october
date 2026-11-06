module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassInfinite

/-! # Quadratic bounds and velocity-face limits for bounded Borel source potentials -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open scoped Topology ENNReal

/-- The actual finite-horizon source potential obeys the exact quadratic interval estimate. -/
theorem stripPotentialOfRealization_abs_le_quadratic
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (g : BoundedBorel Point) (C : ℝ) (hC : 0 ≤ C) (hg : ∀ p, |g p| ≤ C) :
    |stripPotentialOfKernel H E.2 T g e| ≤
      C * ((e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)) := by
  let q := (e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)
  have hq : 0 ≤ q :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr e.2.2.1.le) (sub_nonneg.mpr e.2.2.2.le))
      (by positivity)
  have hm : (stripGreenOfKernel H E.2 T e).real univ ≤ q := by
    have hmass := stripGreenOfRealization_quadratic_mass hH hlam hLam A H E hE T e
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass).trans_eq
      (ENNReal.toReal_ofReal hq)
  have hb : |stripPotentialOfKernel H E.2 T g e| ≤
      C * (stripGreenOfKernel H E.2 T e).real univ := by
    simpa only [stripPotentialOfKernel, Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const (f := g) (C := C)
        (μ := stripGreenOfKernel H E.2 T e)
        (Eventually.of_forall fun p => by simp_all)
  exact hb.trans (mul_le_mul_of_nonneg_left hm hC)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
