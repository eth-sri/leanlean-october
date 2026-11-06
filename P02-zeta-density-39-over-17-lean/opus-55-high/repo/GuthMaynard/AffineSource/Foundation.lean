module
/- Isolated from Scott McColm, smccolm/Lean pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1. MIT-0. See notes/guth-maynard-affine-reuse-audit.md. -/
public import Mathlib
public import MathCollab.Density.DivisorGrowth
public import GuthMaynard.NativeSource.GuthMaynard.VanDerCorput
public import GuthMaynard.NativeSource.GuthMaynard.ZeroDetector
import WeylPort.Analytic.RealLaplace

@[expose] public section
open Complex Finset Filter FourierTransform MeasureTheory Real
open scoped ContDiff FourierTransform Topology
namespace RiemannZeta.GuthMaynard

noncomputable def dfiUnitRedundantBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

noncomputable def gmIntDecayProfile (q : ℕ) (m : ℤ) : ℝ :=
  if m = 0 then 0 else 1 / |(m : ℝ)| ^ q

theorem summable_gmIntDecayProfile {q : ℕ} (hq : 2 ≤ q) :
    Summable (gmIntDecayProfile q) := by
  have hs : Summable (fun m : ℤ => |1 / (m : ℝ) ^ q|) := by
    rw [summable_abs_iff]
    exact Real.summable_one_div_int_pow.mpr (lt_of_lt_of_le (by norm_num) hq)
  apply Summable.of_nonneg_of_le (fun m => by
    simp only [gmIntDecayProfile]
    split_ifs
    grind
    · positivity) (fun m => ?_) hs
  pm_1452 hm m gmIntDecayProfile
  · simp only [gmIntDecayProfile, ite_false, hm, abs_div, abs_one, abs_pow]
    exact le_rfl

noncomputable def gmCubicLocalBump (x : ℝ) : ℝ :=
  dfiUnitRedundantBump (x / 2)

theorem gmCubicLocalBump_nonneg (x : ℝ) : 0 ≤ gmCubicLocalBump x :=
  dfiUnitRedundantBump.nonneg

theorem gmCubicLocalBump_one {x : ℝ} (hx : |x| ≤ 1) :
    gmCubicLocalBump x = 1 := by
  unfold gmCubicLocalBump
  apply dfiUnitRedundantBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  rw [sub_zero, show dfiUnitRedundantBump.rIn = (1 / 2 : ℝ) by rfl]
  rw [abs_div]
  norm_num
  linarith

theorem gmCubicLocalBump_le_one (x : ℝ) : gmCubicLocalBump x ≤ 1 :=
  dfiUnitRedundantBump.le_one

theorem gmCubicLocalBump_eq_zero_of_two_le_abs
    {x : ℝ} (hx : 2 ≤ |x|) : gmCubicLocalBump x = 0 := by
  by_contra hne
  have hsupp : x / 2 ∈ Function.support dfiUnitRedundantBump := by
    exact hne
  pm_823
  have habs : |x / 2| = |x| / 2 := by
    grind
  rw [habs] at hsupp
  linarith

export GuthMaynard.NativeMoment (norm_sum_sq_le_card_mul_sum_norm_sq DivisorCountBoundProp)

theorem divisorCountBound_native : DivisorCountBoundProp := by
  intro ε hε
  obtain ⟨C,hC,h⟩ := MathCollab.Density.divisor_card_subpower hε
  exact ⟨C,by linarith,h⟩

end RiemannZeta.GuthMaynard
