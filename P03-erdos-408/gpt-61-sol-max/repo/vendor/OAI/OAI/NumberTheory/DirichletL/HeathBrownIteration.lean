module
public import Mathlib.Tactic

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace OAI

namespace SevenEighths.HeathBrownIteration

noncomputable section

def step (x : ℝ)  := (6 * x - 4) / (3 * x - 1)

theorem step_sub  x  (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 = 2 * (x - 4 / 3) / (3 * x - 1) := by
  grind [step]

section
variable {x : ℝ} (hx : (4 / 3 : ℝ) < x)


include hx in
theorem step_gt     :
    (4 / 3 : ℝ) < step x := by
  have h := step_sub x hx.le
  have hp : 0 < 2 * (x - 4 / 3) / (3 * x - 1) :=
    div_pos (mul_pos (by norm_num) (sub_pos.mpr hx)) (by linarith)
  linarith

theorem step_error_le   (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 ≤ (2 / 3 : ℝ) * (x - 4 / 3) := by
  rw [step_sub x hx]
  apply (div_le_iff₀ (by linarith : 0 < 3 * x - 1)).mpr
  nlinarith [sq_nonneg (x - 4 / 3)]

include hx in
theorem step_lt     : step x < x := by
  have h := step_error_le hx.le
  linarith

end

def exponent : ℕ → ℝ
  | 0 => 2
  | n + 1 => step (exponent n)

section
variable (n : ℕ) {P : ℝ → Prop} (hstart : P 2) (himprove : ∀ x : ℝ, (4 / 3 : ℝ) < x → x ≤ 2 → P x → P (step x)) {ε : ℝ} (hε : 0 < ε)


theorem exponent_bounds   :
    (4 / 3 : ℝ) < exponent n ∧ exponent n ≤ 2 := by
  induction n with
  | zero => norm_num [exponent]
  | succ n ih =>
    exact ⟨step_gt ih.1, (step_lt ih.1).le.trans ih.2⟩

theorem exponent_error_le   :
    exponent n - 4 / 3 ≤ (2 / 3 : ℝ) ^ (n + 1) := by
  induction n with
  | zero => norm_num [exponent]
  | succ n ih =>
    calc
      exponent (n + 1) - 4 / 3 ≤ (2 / 3 : ℝ) * (exponent n - 4 / 3) :=
        step_error_le (exponent_bounds n).1.le
      _ ≤ (2 / 3 : ℝ) * (2 / 3 : ℝ) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (2 / 3 : ℝ) ^ (n + 1 + 1) := by rw [pow_succ]; ring

include hε in
theorem exists_exponent_lt     :
    ∃ n : ℕ, exponent n < 4 / 3 + ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 / 3 : ℝ) < 1)
  refine ⟨n, ?_⟩
  have hp : (2 / 3 : ℝ) ^ (n + 1) ≤ (2 / 3 : ℝ) ^ n := by
    bound
  have he := exponent_error_le n
  linarith

include hstart himprove hε in
theorem finite_improvement    
     
        :
    ∃ x : ℝ, (4 / 3 : ℝ) < x ∧ x ≤ 2 ∧ x < 4 / 3 + ε ∧ P x := by
  have hp (n : ℕ) : P (exponent n) := by
    induction n with
    | zero => exact hstart
    | succ n ih => exact himprove _ (exponent_bounds n).1 (exponent_bounds n).2 ih
  grind [exists_exponent_lt, exponent, exponent_bounds]

end

end

end SevenEighths.HeathBrownIteration

end OAI
