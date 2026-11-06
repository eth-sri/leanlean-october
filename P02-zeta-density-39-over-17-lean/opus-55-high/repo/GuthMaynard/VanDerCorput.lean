module
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.InnerProductSpace.Basic
public import GuthMaynard.NativeSource.GuthMaynard.VanDerCorput

@[expose] public section

open Complex Finset Set
open scoped InnerProductSpace

namespace RiemannZeta.GuthMaynard

/-!
# The logarithmic exponential sums used in the classical density argument

This file develops the two concrete van der Corput estimates needed by the
project.  Angles in `unitaryPhase` are measured in radians; this avoids a
pervasive factor `2 * pi` when the phase is `-t * log x`.
-/

export GuthMaynard.NativeMoment (finite_weyl_differencing kusminLandau_one_period kusminLandau_interval interval_weyl_differencing norm_sum_le_resolvent_variation finite_resolvent_telescoping phaseResolvent_eq norm_phaseResolvent_sub_eq sum_norm_sq_paddedShift_eq unitaryPhase_resolvent_step phaseResolvent_variation sin_half_lower abs_cot_half_le_norm_phaseResolvent norm_phaseResolvent_le sum_paddedShift_eq norm_sum_sq_le_card_mul_sum_norm_sq hasDerivAt_real_cot strictAntiOn_real_cot unitaryPhase_logarithmicPhase_eq_cpow hasDerivAt_logarithmicPhase norm_phaseSum_le_card unitaryPhase_sub paddedShift norm_logarithmicSum_le_length unitaryPhase_sub_int_mul_two_pi unitaryPhase_int_mul_two_pi unitaryPhase_add phaseSum norm_unitaryPhase logarithmicSum phaseResolvent unitaryPhase logarithmicPhase)

/-! ## Kusmin--Landau cancellation -/

/-- Decreasing-increment form of one-period Kusmin--Landau cancellation. -/
theorem kusminLandau_one_period_decreasing (f : ℕ → ℝ) (N : ℕ) (δ : ℝ)
    (hδ : 0 < δ)
    (hlow : ∀ n ≤ N, δ ≤ f (n + 1) - f n)
    (hhigh : ∀ n ≤ N, f (n + 1) - f n ≤ 2 * Real.pi - δ)
    (hmono : ∀ n < N, f (n + 2) - f (n + 1) ≤ f (n + 1) - f n) :
    ‖∑ n ∈ Finset.range (N + 1), unitaryPhase (f n)‖ ≤
      2 * Real.pi / δ := by
  let g : ℕ → ℝ := fun n => -f n + (n : ℝ) * (2 * Real.pi)
  have hdiff (n : ℕ) :
      g (n + 1) - g n = 2 * Real.pi - (f (n + 1) - f n) := by
    dsimp only [g]
    push_cast
    ring_nf
  have hphase (n : ℕ) :
      unitaryPhase (g n) = starRingEnd ℂ (unitaryPhase (f n)) := by
    rw [show g n = (n : ℝ) * (2 * Real.pi) - f n by dsimp only [g]; ring_nf]
    rw [unitaryPhase_sub]
    rw [show unitaryPhase ((n : ℝ) * (2 * Real.pi)) = 1 by
      simpa only [Int.cast_natCast] using unitaryPhase_int_mul_two_pi (n : ℤ)]
    simp
  have hKL := kusminLandau_one_period g N δ hδ
    (fun n hn => by rw [hdiff]; linarith [hhigh n hn])
    (fun n hn => by rw [hdiff]; linarith [hlow n hn])
    (fun n hn => by rw [hdiff, hdiff]; linarith [hmono n hn])
  have hsum :
      (∑ n ∈ Finset.range (N + 1), unitaryPhase (g n)) =
        starRingEnd ℂ (∑ n ∈ Finset.range (N + 1), unitaryPhase (f n)) := by
    simp_rw [hphase]
    exact (map_sum (starRingEnd ℂ) _ _).symm
  rw [hsum] at hKL
  change ‖star (∑ n ∈ Finset.range (N + 1), unitaryPhase (f n))‖ ≤ _ at hKL
  rw [norm_star] at hKL
  exact hKL

/-! ## Finite Weyl differencing -/

end RiemannZeta.GuthMaynard
