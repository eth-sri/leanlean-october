module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CapacityPrimitive
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
public import PDEFoundation.Calculus.RegularityOrder


/-! # The convex velocity test for strip capacity -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- A smooth convex test with second derivative twice a compact interval majorant. -/
theorem exists_capacity_test (E : Interval) :
    ∃ chi Phi : ℝ → ℝ, ContDiff ℝ PDE.smoothOrder chi ∧ HasCompactSupport chi ∧
      (∀ v, 0 ≤ chi v ∧ chi v ≤ 1) ∧ (∀ v ∈ Icc E.lo E.hi, chi v = 1) ∧
      (∫ v, chi v) ≤ 2 * (E.hi - E.lo) ∧ ContDiff ℝ PDE.smoothOrder Phi ∧
      (∀ v, deriv (deriv Phi) v = 2 * chi v) ∧
      (∀ v, |deriv Phi v| ≤ 2 * (E.hi - E.lo)) := by
  obtain ⟨chi, hs, hc, hsup, hn, h1, hm⟩ := exists_capacity_cutoff E
  let a := E.lo - (E.hi - E.lo) / 2
  let F  := fun v => 2 * (∫ x in a..v, chi x) - ∫ x, chi x

  have hF : ContDiff ℝ PDE.smoothOrder F :=
    (contDiff_const.mul (capacity_primitive_smooth hs a)).sub contDiff_const
  have hdF (v : ℝ) : HasDerivAt F (2 * chi v) v := by
    have hd := intervalIntegral.integral_hasDerivAt_right
      (hs.continuous.intervalIntegrable a v)
      hs.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hs.continuous.continuousAt
    exact (hd.const_mul 2).sub_const _
  have hdPhi (v : ℝ)  :=
    intervalIntegral.integral_hasDerivAt_right (hF.continuous.intervalIntegrable 0 v)
      hF.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuous.continuousAt
  have he  := funext fun v => (hdPhi v).deriv
  refine ⟨chi, (fun v => ∫ x in 0..v, F x), hs, hc, hn, h1, hm, capacity_primitive_smooth hF 0, ?_, ?_⟩
  · intro v
    rw [he]
    exact (hdF v).deriv
  · intro v
    rw [he]


    obtain ⟨hlo, hhi⟩ := capacity_cumulative_bounds (hs.continuous.integrable_of_hasCompactSupport hc) (fun x => (hn x).1) (fun x hx => (hsup hx).1) v

    dsimp only [F]
    apply abs_le.mpr
    constructor <;> linarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
