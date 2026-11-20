module

public import HK.Basic

/-!
# Five SBI agents with a constant digraph and oscillatory convergence

The averaging map on the three moving agents' offsets has a complex conjugate pair of modes; the
initial offset cancels its real mode. Three consecutive instances of the second-order recurrence give
both signs in every five consecutive times, with no trigonometry and no density argument.
-/

public section

namespace HK

local notation "poly" u:arg => 60 * u ^ 3 - 47 * u ^ 2 + 9 * u - 1

theorem sbi5_root_exists : ∃ ρ : ℝ, 57 / 100 < ρ ∧ ρ < 29 / 50 ∧ poly ρ = 0 := by
  simp_rw [← and_assoc, ← Set.mem_Ioo]
  exact intermediate_value_Ioo (f := fun u : ℝ => poly u) (by norm_num) (by fun_prop)
    (by norm_num [Set.mem_Ioo])

local notation3 "InWindow " k " from " t ", " p => ∃ k, t ≤ k ∧ k ≤ t + 4 ∧ p

/-- On a window of one sign the recurrence gives three linear inequalities, using
`a ≤ 2/9` and `b ≥ 1/40`. Together they force the first two entries to vanish,
which is impossible since the recurrence is reversible. -/
private theorem window {f : ℕ → ℝ} {a b : ℝ} (rec : ∀ t, f (t + 2) = a * f (t + 1) - b * f t)
    (init : ¬ (f 0 = 0 ∧ f 1 = 0)) (ha : a ≤ 2 / 9) (hb : 1 / 40 ≤ b)
    (t : ℕ) : (InWindow k from t, f k < 0) ∧ (InWindow k from t, 0 < f k) := by
  have nz : ¬ (f t = 0 ∧ f (t + 1) = 0) := by
    induction t with
    | zero => exact init
    | succ t ih => grind [rec t, mul_eq_zero]
  have rel (j : Fin 3) := rec (t + j)
  constructor <;> by_contra! H <;>
    have sign (j : Fin 5) := H (t + j.val) (by omega) (by omega) <;>
    norm_num [hk_data, Nat.add_assoc] at sign rel <;>
    apply nz <;> constructor <;>
    nlinarith

section
variable (ρ : ℝ) (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
local notation "Z" => sbi5Offset ρ
local notation "X" => traj Model.sbi sbi5_r (sbi5_x0 ρ)

private theorem offset_succ (t : ℕ) : Z (t + 1) = sbi5LinearStep (Z t) :=
  Function.iterate_succ_apply' ..

corollary offset_zero := sbi5Offset.eq_def ρ 0
attribute [local hk_data] offset_zero offset_succ pi_norm_le_iff_of_nonempty

include hlo hhi
private theorem shrink (t : ℕ) : ‖sbi5Lift (Z t)‖ ≤ (2 / 3 : ℝ) ^ t / 3 := by
  induction t <;> norm_num [pow_succ, hk_data] at * <;> grind

theorem complexOrbit : Orbit .sbi sbi5_r (sbi5_x0 ρ) (fun t => sbi5_lim + sbi5Lift (Z t))
    (fun _ => rows![{0}, {0, 1, 3}, 0⋯4, {0, 2, 3, 4}, {4}]) where
  init := rfl
  rows t := by
    have h := shrink ρ hlo hhi t
    simp [hk_data] at h
    have : (2 / 3 : ℝ) ^ t ≤ 1 := by bound
    finite_check
  next t := by finite_check

local notation "orbit5" => complexOrbit ρ hlo hhi

corollary sbi5_trajectory := Orbit.form orbit5

corollary sbi5_neighbors := Orbit.table orbit5

corollary sbi5_digraph_constant := Orbit.constant orbit5

theorem sbi5_tendsto : Converges X sbi5_lim := by
  have hp := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    (by norm_num : |(2 / 3 : ℝ)| < 1)).div_const 3
  rw [funext (Orbit.form orbit5)]
  simpa using (squeeze_zero_norm (shrink ρ hlo hhi) (by simpa using hp)).const_add sbi5_lim

variable (hp : poly ρ = 0)
include hp

omit hlo hhi in
private theorem recurrence (t : ℕ) : Z (t + 2) = fun i =>
    (47 / 60 - ρ) * Z (t + 1) i - (ρ ^ 2 - 47 / 60 * ρ + 3 / 20) * Z t i := by
  induction t with
  | zero => finite_check
  | succ t ih =>
    conv_lhs => rw [offset_succ, ih]
    finite_check

theorem sbi5_oscillates_every_five (t : ℕ) (i : Fin 5) (hi : i ∈ (1⋯3 : Finset _)) :
    (InWindow k from t, X k i < sbi5_lim i) ∧ (InWindow k from t, sbi5_lim i < X k i) := by
  have hs (j : Fin 3) := window (f := fun k => Z k j) (fun k => congrFun (recurrence ρ hp k) j)
    (by fin_cases j <;> finite_check)
    (by linarith) (by nlinarith) t
  fin_cases i <;> simp [sbi5_trajectory ρ hlo hhi, sbi5Lift] at hi ⊢ <;> apply hs

theorem unstable5 : Unstable X := by
  apply crossing (sbi5_tendsto ρ hlo hhi) 1
  intro t
  grind [sbi5_oscillates_every_five ρ hlo hhi hp t 1 (by simp)]

corollary sbi5_not_fixedFrom := (unstable5 ρ hlo hhi hp).1

corollary sbi5_not_pseudoStableAfter := (unstable5 ρ hlo hhi hp).2

end

corollary complexRefutes := sbi5_root_exists.elim fun ρ ⟨a, b, h⟩ =>
  refutes_of_unstable (unstable5 ρ a b h) (by finite_check) (sbi5_digraph_constant ρ a b)

corollary not_conjecture23_sbi_five := complexRefutes.1
corollary not_theorem64iv_sbi_five := complexRefutes.2

end HK
