module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapHolder
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped ENNReal

/-- Weighted positive sums satisfy the q-power form of Holder's inequality. -/
theorem position_weighted_tsum_rpow_le {ι : Type*} [Countable ι]
    (w a : ι → ℝ≥0∞) (q : ℝ) (hq : 1 < q) :
    (∑' i, w i * a i) ^ q ≤ (∑' i, w i) ^ (q - 1) * ∑' i, w i * a i ^ q := by
  let : MeasurableSpace ι := ⊤
  have hm (f : ι → ℝ≥0∞) : Measurable f := measurable_from_top
  have h := position_integral_rpow_le (Measure.count.withDensity w) a (hm a) q hq
  have hw : (Measure.count.withDensity w) univ = ∑' i, w i := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count]
  rw [hw, lintegral_withDensity_eq_lintegral_mul _ (hm w) (hm a),
    lintegral_withDensity_eq_lintegral_mul _ (hm w) ((hm a).pow_const q),
    lintegral_count, lintegral_count] at h
  exact h

/-- Translation-invariant positive convolution is bounded on the q-power counting norm. -/
theorem position_two_index_young {ι : Type*} [AddCommGroup ι] [Countable ι]
    (w a : ι → ℝ≥0∞) (q : ℝ) (hq : 1 < q) :
    (∑' g, (∑' h, w h * a (g - h)) ^ q) ≤
      (∑' h, w h) ^ q * ∑' g, a g ^ q := by
  calc
    _ ≤ ∑' g, (∑' h, w h) ^ (q - 1) * ∑' h, w h * a (g - h) ^ q :=
      ENNReal.tsum_le_tsum (fun g => position_weighted_tsum_rpow_le w
        (fun h => a (g - h)) q hq)
    _ = (∑' h, w h) ^ (q - 1) * ∑' h, w h * ∑' g, a (g - h) ^ q := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]
      congr 1
      apply tsum_congr
      intro h
      exact ENNReal.tsum_mul_left
    _ = (∑' h, w h) ^ (q - 1) * ((∑' h, w h) * ∑' g, a g ^ q) := by
      have hshift (h : ι) : (∑' g, a (g - h) ^ q) = ∑' g, a g ^ q := by
        exact (Equiv.subRight h).tsum_eq (fun g => a g ^ q)
      simp_rw [hshift]
      rw [ENNReal.tsum_mul_right]
    _ = (∑' h, w h) ^ q * ∑' g, a g ^ q := by
      rw [← mul_assoc, position_rpow_sub_one_mul _ q hq.le]



/-- A product exponential majorant on the literal two-index lattice. -/
def positionYoungKernel (d : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-d * |(z.1 : ℝ)|) * Real.exp (-d * |(z.2 : ℝ)|)

/-- Finite-speed overlap is majorized by a separable exponential kernel. -/
theorem position_overlap_majorant (c h k : ℝ) (hc : 0 < c) (hh : 0 ≤ h)
    (hk : |k| ≤ 5 * (h + 1)) :
    Real.exp (-c * max (h - 1) 0) ≤
      Real.exp (2 * c) * (Real.exp (-(c / 12) * |h|) * Real.exp (-(c / 12) * |k|)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [abs_of_nonneg hh]
  nlinarith only [hc, hh, hk, (le_max_left (h - 1) 0), (le_max_right (h - 1) 0)]

/-- Exponential absolute-value tails on the integer grid are summable. -/
theorem position_exp_abs_summable (d : ℝ) (hd : 0 < d) :
    Summable (fun k : ℤ => Real.exp (-d * |(k : ℝ)|)) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · have h := (Real.summable_exp_nat_mul_iff).mpr (show -d < 0 by linarith)
    simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), mul_comm]
      using h
  · have h := (Real.summable_exp_nat_mul_iff).mpr (show -d < 0 by linarith)
    simpa only [Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), mul_comm] using h

/-- The two-index majorant has finite real l1 mass. -/
theorem positionYoungKernel_summable (d : ℝ) (hd : 0 < d) :
    Summable (positionYoungKernel d) := by
  exact (position_exp_abs_summable d hd).mul_of_nonneg
    (position_exp_abs_summable d hd) (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

