/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! # The signed Pareto coefficient in the inner cluster

The maximum density contributes `a` times this convergent integral. This reuses the planar beta
integral (`beta_negative_power_integral`) at exponent `a + 1`, rather than a new endpoint-series
calculation.
-/

public section

open MeasureTheory Set

namespace DOZZ.Proofs

/-- The full signed integral from the independent exponential maximum. -/
theorem reflected_pareto_integral (p a : ℝ) (hp : 0 < p) (ha : 0 < a)
    (ha₁ : a < 1) :
    IntegrableOn (fun w : ℝ => ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)) (Ioi 0) ∧
      (∫ w : ℝ in Ioi 0, ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)) =
        Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p := by
  have h := beta_negative_power_integral p (a + 1) hp (by linarith)
    (by linarith)
  grind

/-- The omitted small Pareto values have a first-order bound, valid on the entire half-line. -/
theorem reflected_negative_power_increment (p v : ℝ) (hp : 0 < p) (hv : 0 ≤ v) :
    |(1 + v) ^ (-p) - 1| ≤ p * v := by
  have hd : ∀ x ∈ Ici 0,
      HasDerivAt (fun y => (1 + y) ^ (-p))
        ((-p) * (1 + x) ^ (-p - 1)) x := by
    intro x hx
    have hx0 : 0 ≤ x := hx
    have hh := (Real.hasDerivAt_rpow_const (x := 1 + x) (p := -p)
      (Or.inl (by positivity))).comp x ((hasDerivAt_id x).const_add 1)
    aesop
  have hb : ∀ x ∈ Ici 0, ‖deriv (fun y : ℝ => (1 + y) ^ (-p)) x‖ ≤ p := by
    intro x hx
    have hx0 : 0 ≤ x := hx
    rw [(hd x hx).deriv, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hp,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact mul_le_of_le_one_right hp.le
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
        (by linarith))
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hd x hx).differentiableAt) hb (convex_Ici 0)
    (show 0 ∈ Ici 0 from le_rfl) (show v ∈ Ici 0 from hv)
  simpa only [add_zero, Real.one_rpow, sub_zero, Real.norm_eq_abs, abs_of_nonneg hv]
    using hm
section
variable (p a ε : ℝ)
section
variable (hp : 0 < p) (ha : 0 < a) (ha₁ : a < 1) (hε : 0 ≤ ε)
include hp ha ha₁ hε

/-- The lower-cutoff Pareto error is bounded by its explicit integrable power primitive. -/
theorem reflected_pareto_lower_cut_bound :
    |∫ w : ℝ in Ioc 0 ε, ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)| ≤
      p * ε ^ (1 - a) / (1 - a) := by
  have hf := (reflected_pareto_integral p a hp ha ha₁).1.mono_set
    (show Ioc 0 ε ⊆ Ioi 0 from fun _ hw => hw.1)
  have hi : IntegrableOn (fun w : ℝ => w ^ (-a)) (Ioc 0 ε) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ε)
      (by linarith)).1
  have hb : ∀ᵐ w ∂(volume.restrict (Ioc 0 ε)),
      ‖((1 + w) ^ (-p) - 1) * w ^ (-a - 1)‖ ≤ p * w ^ (-a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
    have hwpos := hw.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hwpos _)]
    calc
      |(1 + w) ^ (-p) - 1| * w ^ (-a - 1) ≤ (p * w) * w ^ (-a - 1) :=
        mul_le_mul_of_nonneg_right (reflected_negative_power_increment p w hp hwpos.le)
          (Real.rpow_nonneg hwpos.le _)
      _ = p * w ^ (-a) := by
        have he : w * w ^ (-a - 1) = w ^ (-a) := by
          calc
            w * w ^ (-a - 1) = w ^ 1 * w ^ (-a - 1) := by simp
            _ = w ^ (1 + (-a - 1)) := (Real.rpow_add hwpos ..).symm
            _ = w ^ (-a) := by simp
        nlinarith
  have hint : (∫ w : ℝ in Ioc 0 ε, p * w ^ (-a)) = p * ε ^ (1 - a) / (1 - a) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hε,
      integral_rpow (Or.inl (by linarith))]
    rw [show -a + 1 = 1 - a by ring, Real.zero_rpow (by positivity), sub_zero]
    ring
  calc
    _ = ‖∫ w : ℝ in Ioc 0 ε, ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ∫ w : ℝ in Ioc 0 ε, ‖((1 + w) ^ (-p) - 1) * w ^ (-a - 1)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ w : ℝ in Ioc 0 ε, p * w ^ (-a) := integral_mono_ae hf.norm (hi.const_mul p) hb
    _ = _ := hint

/-- Truncating the Pareto integral at ε changes its full coefficient by an explicit small error. -/
theorem reflected_pareto_tail_coefficient_bound :
    |(∫ w : ℝ in Ioi ε, ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)) -
      Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p| ≤
        p * ε ^ (1 - a) / (1 - a) := by
  obtain ⟨hf, hfull⟩ := reflected_pareto_integral p a hp ha ha₁
  have hid := intervalIntegral.integral_Ioi_sub_Ioi hf hε
  rw [intervalIntegral.integral_of_le hε] at hid
  have he : (∫ w : ℝ in Ioi ε, ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)) -
      Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p =
      -(∫ w : ℝ in Ioc 0 ε, ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)) := by
    linarith
  rw [he, abs_neg]
  exact reflected_pareto_lower_cut_bound p a ε hp ha ha₁ hε

end

end

/-- The Pareto expansion has an explicit first-order error after restoring the mass scale. -/
theorem reflected_pareto_scaled_error (p a A x : ℝ) (hp : 0 < p) (ha : 0 < a)
    (ha₁ : a < 1) (hA : 0 < A) (hx : 0 < x) :
    |a * A ^ (-p) * x ^ a *
        (∫ w : ℝ in Ioi x, ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)) -
      (a * Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p) * A ^ (-p) * x ^ a| ≤
        (a * p / (1 - a)) * A ^ (-p) * x := by
  have hcoef : 0 ≤ a * A ^ (-p) * x ^ a :=
    by positivity
  have he : a * A ^ (-p) * x ^ a *
        (∫ w : ℝ in Ioi x, ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)) -
      (a * Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p) * A ^ (-p) * x ^ a =
      (a * A ^ (-p) * x ^ a) *
        ((∫ w : ℝ in Ioi x, ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)) -
          Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p) := by ring
  rw [he, abs_mul, abs_of_nonneg hcoef]
  calc
    _ ≤ (a * A ^ (-p) * x ^ a) * (p * x ^ (1 - a) / (1 - a)) :=
      mul_le_mul_of_nonneg_left (reflected_pareto_tail_coefficient_bound p a x hp ha ha₁ hx.le)
        hcoef
    _ = (a * p / (1 - a)) * A ^ (-p) * x := by
      have hpow : x ^ a * x ^ (1 - a) = x := by
        rw [← Real.rpow_add hx, add_sub_cancel, Real.rpow_one]
      grind

end DOZZ.Proofs
