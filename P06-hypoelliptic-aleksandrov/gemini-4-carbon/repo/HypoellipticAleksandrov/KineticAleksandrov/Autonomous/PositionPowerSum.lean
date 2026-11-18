module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitsStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.DegreeGap

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open scoped BigOperators

/-- The admissible barrier degree gives the source range `1 < gamma < 2`. -/
theorem enlargedAdmissibleAlpha_gamma_range {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha : ℝ)
    (ha : enlargedAdmissibleAlpha lam Lam hlam hLam alpha) :
    1 < 2 - alpha ∧ 2 - alpha < 2 := by
  have hb := bellmanAdjointExponent_two_le (Lam / lam) ((le_div_iff₀ hlam).2
    (by simpa using hLam))
  obtain ⟨hal, hau⟩ := ha
  constructor <;> linarith

/-- The combined decay exponent is summable up to the source horizon power. -/
theorem position_decay_power_sum_horizon_le (g q : ℝ)
    (hg : 1 < g ∧ g < 2) (hq : 1 < q ∧ q < 3 / 2)
    (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r) (N : ℕ)
    (hN : (N : ℝ) ≤ 2 + (R / r) ^ 2) :
    (∑ j ∈ Finset.range (N + 1),
      (1 + (j : ℝ)) ^ (-(1 + g * (q - 1)) / 2)) ≤
      ((1 + 1 / (1 - (1 + g * (q - 1)) / 2)) *
        (3 : ℝ) ^ (1 - (1 + g * (q - 1)) / 2)) *
          (1 + R / r) ^ (1 - g * (q - 1))  := by
  have time_decay_power_sum_horizon_le (q : ℝ) (hq : 1 < q) (hq2 : q < 2) :
      (∑ i ∈ Finset.range (N + 1), (1 + (i : ℝ)) ^ (-q / 2)) ≤
      ((1 + 1 / (1 - q / 2)) * 3 ^ (1 - q / 2)) *
        (1 + R / r) ^ (2 - q) := open Set MeasureTheory in by
    have time_decay_power_sum_le :
        (∑ i ∈ Finset.range (N + 1), (1 + (i : ℝ)) ^ (-q / 2)) ≤
        (1 + 1 / (1 - q / 2)) * ((N : ℝ) + 1) ^ (1 - q / 2) := by
      let f := fun x : ℝ => x ^ (-q / 2)
      have hb : 0 < 1 - q / 2 := by linarith
      have he : -1 < -q / 2 := by linarith
      have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      have hf : AntitoneOn f (Icc 1 (1 + (N : ℝ))) := by
        intro x hx y hy hxy
        exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
      have hs := hf.sum_le_integral (x₀ := 1)
      have hi : (∫ x in (1 : ℝ)..1 + (N : ℝ), f x) =
          (((1 + (N : ℝ)) ^ (1 - q / 2) - 1) / (1 - q / 2)) := by
        rw [integral_rpow (Or.inl he), Real.one_rpow]
        rw [show -q / 2 + 1 = 1 - q / 2 by ring]
      rw [hi] at hs
      have hsum : (∑ i ∈ Finset.range (N + 1), (1 + (i : ℝ)) ^ (-q / 2)) =
          1 + ∑ i ∈ Finset.range N, f (1 + ((i + 1 : ℕ) : ℝ)) := by
        rw [Finset.sum_range_succ']
        simp
        ring
      rw [hsum]
      have hp : 1 ≤ ((N : ℝ) + 1) ^ (1 - q / 2) :=
        Real.one_le_rpow (by linarith) hb.le
      have ha : 1 + (N : ℝ) = (N : ℝ) + 1 := add_comm _ _
      rw [ha] at hs
      have hs' := add_le_add_right hs 1
      apply hs'.trans
      have hle : (((N : ℝ) + 1) ^ (1 - q / 2) - 1) / (1 - q / 2) ≤
          ((N : ℝ) + 1) ^ (1 - q / 2) / (1 - q / 2) :=
        div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) hb.le
      calc
        _ ≤ 1 + ((N : ℝ) + 1) ^ (1 - q / 2) / (1 - q / 2) := add_le_add_right hle 1
        _ ≤ ((N : ℝ) + 1) ^ (1 - q / 2) +
            ((N : ℝ) + 1) ^ (1 - q / 2) / (1 - q / 2) := add_le_add_left hp _
        _ = _ := by ring
    have hb : 0 < 1 - q / 2 := by linarith
    have hx := div_nonneg hR hr.le
    have hs : (N : ℝ) + 1 ≤ 3 * (1 + R / r) ^ 2 := by nlinarith
    have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (N : ℝ) + 1) hs hb.le
    have he : (3 * (1 + R / r) ^ 2) ^ (1 - q / 2) =
        3 ^ (1 - q / 2) * (1 + R / r) ^ (2 - q) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (sq_nonneg _),
        ← Real.rpow_natCast_mul (by linarith : 0 ≤ 1 + R / r)]
      norm_num only [Nat.cast_ofNat]
      rw [show 2 * (1 - q / 2) = 2 - q by ring]
    rw [he] at hp
    apply (time_decay_power_sum_le).trans
    have hC : 0 ≤ 1 + 1 / (1 - q / 2) := by positivity
    exact (mul_le_mul_of_nonneg_left hp hC).trans_eq (mul_assoc _ _ _).symm
  have hprod : 0 < g * (q - 1) := mul_pos (by linarith [hg.1]) (by linarith [hq.1])
  have hprod1 : g * (q - 1) < 1 := by
    have h := mul_lt_mul_of_pos_right hg.2 (by linarith [hq.1] : 0 < q - 1)
    linarith [hq.2]
  simpa only [show 2 - (1 + g * (q - 1)) = 1 - g * (q - 1) by ring] using (time_decay_power_sum_horizon_le (1 + g * (q - 1)) (by linarith) (by linarith))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

