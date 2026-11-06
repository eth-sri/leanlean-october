module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BelowFourBandStatement
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Lean.Elab.Tactic.Grind



/-! # The literal signed geometric core cover used below exponent four -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set

variable (R : ℝ)

/-- The source geometric centre magnitudes, 8R(7/8)^j. -/
def geometricCoreScale  (j : ℕ) : ℝ := 8 * R * (7 / 8 : ℝ) ^ j

section
variable (hR : 0 < R) (j : ℕ)

include hR in
/-- Every source centre magnitude is positive. -/
theorem geometricCoreScale_pos   :
    0 < geometricCoreScale R j := by unfold geometricCoreScale; positivity

/-- The source positive and negative clock data have radius half the centre magnitude. -/
def geometricCoreClock   (positive : Bool) : Clock where
  vbar := if positive then geometricCoreScale R j else -geometricCoreScale R j
  r := geometricCoreScale R j / 2
  nonzero := by split <;> have h := geometricCoreScale_pos R hR j <;> linarith
  positive := by have h := geometricCoreScale_pos R hR j; positivity
  radius := by
    grind

variable (s : Bool)

/-- The source signed geometric clocks satisfy the band-centre relation. -/
theorem geometricCoreClock_center    :
    |(geometricCoreClock R hR j s).vbar| = 2 * (geometricCoreClock R hR j s).r := by

  cases s <;> simp only [geometricCoreClock, Bool.false_eq_true, ↓reduceIte,
    abs_neg, abs_of_pos (geometricCoreScale_pos R hR j)] <;> ring

/-- Every geometric band radius is at most 4R, hence within the allowed 6R. -/
theorem geometricCoreClock_radius    :
    (geometricCoreClock R hR j s).r ≤ 6 * R := by
  have hj : (7 / 8 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  change 8 * R * (7 / 8 : ℝ) ^ j / 2 ≤ 6 * R
  nlinarith
end


section
variable (R v : ℝ) (hR : 0 < R)

include hR in
/-- Geometric annuli cover every positive magnitude up to 9R, including endpoints. -/
theorem geometricCoreScale_covers  (hv : 0 < v)
    (hupper : v ≤ 9 * R) :
    ∃ j : ℕ, geometricCoreScale R j * (7 / 8) ≤ v ∧
      v ≤ geometricCoreScale R j * (9 / 8) := by
  have hex : ∃ j : ℕ, geometricCoreScale R j * (7 / 8) ≤ v := by
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show 0 < v / (8 * R) by positivity)
      (show (7 / 8 : ℝ) < 1 by norm_num)
    refine ⟨j, ?_⟩
    have hj' : 8 * R * (7 / 8 : ℝ) ^ j < v :=
      by
      simpa only [mul_comm] using
        (lt_div_iff₀ (by positivity : 0 < 8 * R)).mp hj

    unfold geometricCoreScale
    nlinarith
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  cases hn : Nat.find hex with
  | zero => simp only [geometricCoreScale, pow_zero, mul_one]; linarith
  | succ j =>
    have hj : ¬geometricCoreScale R j * (7 / 8) ≤ v :=
      Nat.find_min hex (by omega)

    have he : geometricCoreScale R (j + 1) = geometricCoreScale R j * (7 / 8) := by
      simp only [geometricCoreScale, pow_succ]; ring
    rw [he]
    linarith

/-- The actual closed cores cover both signs of every nonzero velocity up to 9R. -/
theorem geometricCoreClock_covers  (hv : v ≠ 0)
    (hupper : |v| ≤ 9 * R) :
    ∃ j : ℕ, ∃ s : Bool, v ∈ (geometricCoreClock R hR j s).core := by
  obtain ⟨j, hl, hu⟩ := geometricCoreScale_covers R |v| hR (abs_pos.mpr hv) hupper
  refine ⟨j, ?_⟩
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · refine ⟨false, ?_⟩
    rw [abs_of_neg hneg] at hl hu
    change -geometricCoreScale R j - (geometricCoreScale R j / 2) / 4 ≤ v ∧
      v ≤ -geometricCoreScale R j + (geometricCoreScale R j / 2) / 4
    constructor <;> linarith
  · refine ⟨true, ?_⟩
    rw [abs_of_pos hpos] at hl hu
    change geometricCoreScale R j - (geometricCoreScale R j / 2) / 4 ≤ v ∧
      v ≤ geometricCoreScale R j + (geometricCoreScale R j / 2) / 4
    constructor <;> linarith
end


/-- The characterized Bellman degree forces exactly the positive geometric exponent. -/
theorem belowFour_exponent_range (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (alpha q : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam) ((le_div_iff₀ hlam).2
      (by simpa)) - 2 < alpha ∧ alpha < 1)
    (hq : 1 < q ∧ q < (4 - (1 - alpha)) / (3 - (1 - alpha))) :
    0 < alpha ∧ q < 3 / 2 ∧ 0 < 4 - 3 * q + (1 - alpha) * (q - 1) := by
  have hb := bellmanAdjointExponent_range (Lam / lam) ((le_div_iff₀ hlam).2
    (by simpa))


  have hq' := (lt_div_iff₀ (by linarith)).mp hq.2
  refine ⟨(by linarith [hb.1, ha.1]), ?_, ?_⟩ <;> nlinarith [ha.2]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
