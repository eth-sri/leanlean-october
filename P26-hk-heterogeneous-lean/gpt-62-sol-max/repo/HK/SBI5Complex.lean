module

public import HK.Basic

/-!
# Five SBI agents with a constant digraph and a pair of complex modes

A second-order recurrence for the moving offsets implies that they take both signs in every
five-step window. The decay bound comes directly from the three rows of the averaging map.
-/

@[expose] public section

namespace HK

open Filter Topology

local notation "cubic" r:max => (60 * r ^ 3 - 47 * r ^ 2 + 9 * r - 1)

theorem sbi5_root_exists : ∃ ρ : ℝ, 57 / 100 < ρ ∧ ρ < 29 / 50 ∧
    cubic ρ = 0 := by
  obtain ⟨ρ, h, hp⟩ := intermediate_value_Ioo (f := fun ρ => cubic ρ)
    (by norm_num : (57 / 100 : ℝ) ≤ 29 / 50) (by fun_prop) (by norm_num :
      0 ∈ Set.Ioo (cubic (57 / 100 : ℝ)) (cubic (29 / 50)))
  exact ⟨ρ, h.1, h.2, hp⟩

section

variable (ρ : ℝ) (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)

local notation "X" => traj Model.sbi sbi5_r (sbi5_x0 ρ)
local notation "z" => sbi5Offset ρ
local notation "N" => ![{0}, {0, 1, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4}, {4}]
local notation "Y[" t "]" => sbi5_lim + sbi5Lift (z t)
local notation "p" => (2 / 3 : ℝ)

private theorem offset_succ (t : ℕ) : z (t + 1) = sbi5LinearStep (z t) :=
  Function.iterate_succ_apply' ..

include hlo hhi

private theorem offset_bound (t : ℕ) (i : Fin 3) : |z t i| ≤ p ^ t / 3 := by
  induction t generalizing i with
  | zero =>
    fin_cases i <;> norm_num [sbi5Offset, abs_le]
    grind
  | succ t ih =>
    have h (j : Fin 3) := abs_le.mp (ih j)
    rw [offset_succ, pow_succ]
    fin_cases i <;> norm_num [sbi5LinearStep, abs_le] <;> grind

private theorem table (t : ℕ) : neighbors .sbi sbi5_r Y[t] = N := by
  have h : p ^ t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hl (i : Fin 3) :=
    abs_le.mp (show |z t i| ≤ 1 / 3 by linarith [offset_bound ρ hlo hhi t i])
  check_neighbors [sbi5_r, sbi5_lim, sbi5Lift]

theorem sbi5_trajectory (t : ℕ) : X t = Y[t] :=
  traj_of_average (table ρ hlo hhi) (fun t => by
    rw [offset_succ ρ t]
    check_rows [sbi5_lim, sbi5Lift, sbi5LinearStep]) rfl t

theorem sbi5_neighbors (t : ℕ) : neighbors .sbi sbi5_r (X t) = N := by
  rw [sbi5_trajectory ρ hlo hhi, table ρ hlo hhi]

theorem sbi5_digraph_constant (t : ℕ) :
    proximityDigraph .sbi sbi5_r (X t) = proximityDigraph .sbi sbi5_r (sbi5_x0 ρ) :=
  digraph_constant (sbi5_neighbors ρ hlo hhi) t

theorem sbi5_tendsto : Tendsto X atTop (𝓝 sbi5_lim) := by
  have h (i : Fin 3) : Tendsto (fun t => z t i) atTop (𝓝 0) :=
    squeeze_zero_norm (fun t => by simpa [Real.norm_eq_abs] using offset_bound ρ hlo hhi t i)
      (by simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |p| < 1)).div_const 3)
  rw [tendsto_pi_nhds]
  intro i
  fin_cases i <;> simp [sbi5_trajectory ρ hlo hhi, sbi5_lim, sbi5Lift] <;>
    simpa using (h _).const_add _

local notation "α" => (47 / 60 - ρ)
local notation "β" => (ρ ^ 2 - 47 / 60 * ρ + 3 / 20)

private theorem coefficients : 0 < α ∧ 0 < β ∧ β < α ^ 2 ∧ α ^ 2 < 2 * β := by
  and_intros <;> nlinarith

omit hlo hhi

private theorem map_sub_smul (a b : ℝ) (u v : Fin 3 → ℝ) :
    sbi5LinearStep (a • u - b • v) = a • sbi5LinearStep u - b • sbi5LinearStep v := by
  check_rows [sbi5LinearStep]

variable (hp : cubic ρ = 0)

include hp in
private theorem recurrence (t : ℕ) (i : Fin 3) : z (t + 2) i = α * z (t + 1) i - β * z t i := by
  have hz (t : ℕ) : z (t + 2) = α • z (t + 1) - β • z t := by
    induction t with
    | zero =>
      check_rows [sbi5Offset, sbi5LinearStep, Function.iterate_succ_apply']
      nlinarith only [hp]
    | succ t ih => simpa only [map_sub_smul, ← offset_succ] using congrArg sbi5LinearStep ih
  exact congrFun (hz t) i

include hlo hhi hp

private theorem pair_nonzero (t : ℕ) (i : Fin 3) : ¬ (z t i = 0 ∧ z (t + 1) i = 0) := by
  have hb := (coefficients ρ hlo hhi).2.1.ne'
  induction t with
  | zero =>
    fin_cases i <;> norm_num [sbi5Offset, sbi5LinearStep, Function.iterate_succ_apply']
    linarith
  | succ t ih =>
    have he := recurrence ρ hp t i
    change ¬ (z (t + 1) i = 0 ∧ z (t + 2) i = 0)
    grind

/-- The fourth iterate is a strictly negative combination of the two starting offsets. -/
private theorem five_window (t : ℕ) (i : Fin 3) :
    (∃ k, t ≤ k ∧ k ≤ t + 4 ∧ z k i < 0) ∧ (∃ k, t ≤ k ∧ k ≤ t + 4 ∧ 0 < z k i) := by
  set a := α * (α ^ 2 - 2 * β)
  set b := β * (β - α ^ 2)
  obtain ⟨ha, hb, h₁, h₂⟩ := coefficients ρ hlo hhi
  have hna : a < 0 := mul_neg_of_pos_of_neg ha (sub_neg.mpr h₂)
  have hnb : b < 0 := mul_neg_of_pos_of_neg hb (sub_neg.mpr h₁)
  have hrec : z (t + 4) i = a * z (t + 1) i + b * z t i := by
    rw [recurrence ρ hp (t + 2) i, recurrence ρ hp (t + 1) i, recurrence ρ hp t i]
    dsimp [a, b]
    ring
  constructor <;> by_contra! h
  all_goals
    have h₀ := h t le_rfl (by omega)
    have h₁ := h (t + 1) (by omega) (by omega)
    have h₄ := h (t + 4) (by omega) le_rfl
    exact pair_nonzero ρ hlo hhi hp t i (by constructor <;> nlinarith only [hna, hnb, hrec, h₀, h₁, h₄])

theorem sbi5_oscillates_every_five (t : ℕ) (i : Fin 5) (hi : i ∈ ({1, 2, 3} : Finset (Fin 5))) :
    (∃ k, t ≤ k ∧ k ≤ t + 4 ∧ X k i < sbi5_lim i) ∧
    (∃ k, t ≤ k ∧ k ≤ t + 4 ∧ sbi5_lim i < X k i) := by
  fin_cases hi <;> simpa [sbi5_trajectory ρ hlo hhi, sbi5Lift] using five_window ρ hlo hhi hp t _

private theorem unstable : NeverStable X :=
  neverStable_of_crossing (sbi5_tendsto ρ hlo hhi) (i := 1) fun τ => by
    have := sbi5_oscillates_every_five ρ hlo hhi hp τ 1 (by decide)
    grind

theorem sbi5_not_fixedFrom (τ : ℕ) : ¬ FixedFrom X τ := (unstable ρ hlo hhi hp).1 τ

theorem sbi5_not_pseudoStableAfter (xinf : Fin 5 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter X xinf τ := (unstable ρ hlo hhi hp).2 xinf τ

end

private theorem r_pos : ∀ i, 0 < sbi5_r i := by norm_num [Fin.forall_fin_succ, sbi5_r]

private theorem refutations : ¬ Conjecture23ForAgents .sbi 5 ∧ ¬ Theorem64ivForAgents .sbi 5 := by
  obtain ⟨ρ, hlo, hhi, hp⟩ := sbi5_root_exists
  have h := unstable ρ hlo hhi hp
  exact ⟨refute23 r_pos h, refute64 r_pos (sbi5_digraph_constant ρ hlo hhi) h⟩

theorem not_conjecture23_sbi_five : ¬ Conjecture23ForAgents .sbi 5 := refutations.1

theorem not_theorem64iv_sbi_five : ¬ Theorem64ivForAgents .sbi 5 := refutations.2

end HK
