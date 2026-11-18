module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public section

@[expose] section

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

namespace MatrixMultiplication.Foundation

open Filter
open scoped Topology

noncomputable def factorialLogRemainder (n : ℕ) : ℝ :=
  Real.log (Nat.factorial n : ℝ) - ((n : ℝ) * Real.log n - n)

@[simp] theorem factorialLogRemainder_zero : factorialLogRemainder 0 = 0 := by
  simp [factorialLogRemainder]

theorem factorialLogRemainder_stirling (n : ℕ) :
    factorialLogRemainder n =
      Real.log (Stirling.stirlingSeq n) + (1 / 2 : ℝ) * Real.log (2 * n) := by
  cases n with
  | zero => simp
  | succ n =>
    have h := Stirling.log_stirlingSeq_formula (n + 1)
    rw [Real.log_div (by positivity) (Real.exp_ne_zero _), Real.log_exp] at h
    unfold factorialLogRemainder
    linarith

theorem tendsto_factorialLogRemainder_div :
    Tendsto (fun n : ℕ => factorialLogRemainder n / (n : ℝ)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hstirling :
      Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ))
        atTop (𝓝 0) :=
    (Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).div_atTop hnat
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hconstant : Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnat
  have hsum : Tendsto
      (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
        (1 / 2 : ℝ) * (Real.log 2 / (n : ℝ) + Real.log (n : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa using hstirling.add ((hconstant.add hlog).const_mul (1 / 2 : ℝ))
  apply hsum.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  rw [factorialLogRemainder_stirling,
    Real.log_mul (by norm_num) (Nat.cast_ne_zero.mpr hn)]
  ring

theorem tendsto_factorialLogRemainder_mul_div (c : ℕ) :
    Tendsto (fun t : ℕ => factorialLogRemainder (t * c) / (t : ℝ))
      atTop (𝓝 0) := by
  by_cases hc : c = 0
  · subst c
    simp
  have hmul : Tendsto (fun t : ℕ => t * c) atTop atTop :=
    tendsto_id.atTop_mul_const' (Nat.pos_of_ne_zero hc)
  have hscaled : Tendsto
      (fun t : ℕ => factorialLogRemainder (t * c) / (t * c : ℕ) * (c : ℝ))
      atTop (𝓝 0) := by
    simpa using (tendsto_factorialLogRemainder_div.comp hmul).mul_const (c : ℝ)
  apply hscaled.congr
  intro t
  by_cases ht : t = 0
  · simp [ht]
  rw [Nat.cast_mul]
  field_simp [Nat.cast_ne_zero.mpr hc, Nat.cast_ne_zero.mpr ht]

end MatrixMultiplication.Foundation

end OAI
