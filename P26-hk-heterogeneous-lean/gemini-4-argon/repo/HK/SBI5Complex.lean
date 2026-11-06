module

public import HK.Basic

/-!
# Five SBI agents with a constant digraph and oscillatory convergence

The averaging map on the three moving agents' offsets has a complex conjugate pair of modes; the
initial offset cancels its real mode. A four-step consequence of the second-order recurrence gives
both signs in every five consecutive times, with no trigonometry and no density argument.
-/

@[expose] public section

namespace HK

open Filter Topology

set_option hygiene false

local notation "sbi5_N" =>
  ![{0}, {0, 1, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4}, {4}]
local notation "P(" ρ ")" => 60 * ρ ^ 3 - 47 * ρ ^ 2 + 9 * ρ - 1
local notation "α" => 47 / 60 - ρ
local notation "β" => ρ ^ 2 - 47 / 60 * ρ + 3 / 20
local notation "tr5i" => traj .sbi sbi5_r (sbi5_x0 ρ)
local notation "z" => sbi5Offset ρ

theorem sbi5Offset_succ ρ t : z (t + 1) = sbi5LinearStep (z t) :=
  Function.iterate_succ_apply' _ _ _

theorem sbi5_root_exists : ∃ ρ : ℝ, 57 / 100 < ρ ∧ ρ < 29 / 50 ∧ P(ρ) = 0 := by
  obtain ⟨ρ, ⟨h1, h2⟩, hp⟩ : ∃ ρ ∈ Set.Icc (%57 / 100) (29 / 50), P(ρ) = 0 :=
    intermediate_value_Icc (by norm_num) (by fun_prop) ⟨by norm_num, by norm_num⟩
  exact ⟨ρ, h1.lt_of_ne (by rintro rfl; norm_num at hp),
    h2.lt_of_ne (by rintro rfl; norm_num at hp), hp⟩

variable (ρ : ℝ) (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50) (hp : P(ρ) = 0)
include hlo hhi

theorem sbi5_offset_bound t : ∀ i, |z t i| ≤ (%2 / 3) ^ t / 3 := by
  induction t with
  | zero => intro i; fin_cases i <;> simp [sbi5Offset, abs_le] <;> (try constructor) <;> linarith
  | succ t ih =>
    simp only [abs_le] at ih
    intro i; rw [sbi5Offset_succ, pow_succ]
    fin_cases i <;> simp [abs_le] <;> constructor <;> linarith [ih 0, ih 1, ih 2]

theorem sbi5_table t : nbi sbi5_r (sbi5_lim + sbi5Lift (z t)) = sbi5_N := by
  have := (unit_pow (2 / 3) t).2
  have hz i := abs_le.1 (sbi5_offset_bound ρ hlo hhi t i)
  have := hz 0; have := hz 1; have := hz 2
  hk_table

theorem sbi5_trajectory t : tr5i t = sbi5_lim + sbi5Lift (z t) := by
  hk_traj rfl =>
    rw [sbi5_table ρ hlo hhi, sbi5Offset_succ]; hk_avg

theorem sbi5_neighbors t : nbi sbi5_r (tr5i t) = sbi5_N := by
  rw [sbi5_trajectory ρ hlo hhi, sbi5_table ρ hlo hhi]

theorem sbi5_tendsto : Tendsto tr5i atTop (𝓝 sbi5_lim) :=
  tendsto_pi_nhds.mpr fun i => by
    have hz c j : Tendsto (fun t => c + z t j) atTop (𝓝 c) := by
      simpa using (squeeze_zero_norm (sbi5_offset_bound ρ hlo hhi · j)
        (by simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
          (by norm_num)).div_const 3)).const_add c
    simp only [sbi5_trajectory ρ hlo hhi]; fin_cases i <;> simp [hz]

theorem sbi5_digraph_constant t :
    pdi sbi5_r (tr5i t) = pdi sbi5_r (sbi5_x0 ρ) :=
  digraph_const_of_neighbors (sbi5_neighbors ρ hlo hhi) t

include hp

theorem sbi5_oscillates_every_five t i (hi : i ∈ ~{1, 2, 3}) :
    (∃ k, t ≤ k ∧ k ≤ t + 4 ∧ tr5i k i < sbi5_lim i) ∧
    (∃ k, t ≤ k ∧ k ≤ t + 4 ∧ sbi5_lim i < tr5i k i) := by
  have ⟨j, hj⟩ : ∃ j, ∀ k, sbi5Lift (z k) i = z k j := by
    fin_cases i <;> simp_all <;> exact ⟨_, fun _ => rfl⟩
  simp only [sbi5_trajectory ρ hlo hhi, Pi.add_apply, hj]
  have h2 s : ∀ k, z (s + 2) k = α * z (s + 1) k - β * z s k := by
    induction s with
    | zero => intro k; fin_cases k <;> simp [sbi5Offset] <;> nlinarith [hp]
    | succ s ih =>
      intro k; conv_lhs => rw [sbi5Offset_succ _ (s + 2), funext ih]
      fin_cases k <;> simp [sbi5Offset_succ] <;> ring
  let c := α * (α ^ 2 - 2 * β)
  let d := β * (β - α ^ 2)
  have : c < 0 ∧ d < 0 := ⟨mul_neg_of_pos_of_neg (by linarith) (by nlinarith),
    mul_neg_of_pos_of_neg (by nlinarith) (by nlinarith)⟩
  have hrec : z (t + 4) j = c * z (t + 1) j + d * z t j := by
    linear_combination h2 (t + 2) j + α * h2 (t + 1) j + (α ^ 2 - β) * h2 t j
  have hnz s : ¬ (z s j = 0 ∧ z (s + 1) j = 0) := by
    induction s with
    | zero => fin_cases j <;> simp [sbi5Offset]; linarith
    | succ s ih => rintro ⟨h1, _⟩; exact ih ⟨by nlinarith [h2 s j], h1⟩
  constructor <;>
    (by_contra! hn
     refine hnz t ⟨?_, ?_⟩ <;>
       nlinarith [hn t le_rfl (by omega), hn (t + 1) (by omega) (by omega), hn (t + 4) (by omega) le_rfl])

local notation "osc" => sbi5_oscillates_every_five ρ hlo hhi hp τ 1 (by simp)

theorem sbi5_not_fixedFrom τ : ¬ FixedFrom tr5i τ := fun hf => by
  obtain ⟨⟨k, hk0, -, hk⟩, ⟨l, hl0, -, hl⟩⟩ := osc
  linarith [congrFun (hf k hk0) 1, congrFun (hf l hl0) 1]

theorem sbi5_not_pseudoStableAfter xinf τ : ¬ PseudoStableAfter tr5i xinf τ := by
  rintro ⟨hlim, F, C, -, -, -, hFC, h⟩
  obtain rfl := tendsto_nhds_unique hlim (sbi5_tendsto ρ hlo hhi)
  obtain ⟨⟨k, hk0, -, hk⟩, ⟨l, hl0, -, hl⟩⟩ := osc
  rcases Finset.mem_union.mp (hFC ▸ Finset.mem_univ 1) with h1 | h1
  · linarith [(h k hk0).1 1 h1]
  · have hc t (ht : τ ≤ t) : tr5i t 1 < sbi5_lim 1 ↔ tr5i τ 1 < sbi5_lim 1 := by
      induction t, ht using Nat.le_induction with
      | base => rfl
      | succ t ht ih =>
        rw [← ih]
        rcases (h t ht).2 1 h1 with ⟨_, _⟩ | ⟨_, _⟩ <;> constructor <;> intro <;> linarith
    rw [hc k hk0, ← hc l hl0] at hk; linarith

omit hlo hhi hp

def sbi5_refute :=
  let ⟨ρ, hlo, hhi, hp⟩ := sbi5_root_exists
  refute_both (sbi5_digraph_constant ρ hlo hhi) (sbi5_not_fixedFrom ρ hlo hhi hp)
    (sbi5_not_pseudoStableAfter ρ hlo hhi hp)

theorem not_conjecture23_sbi_five : ¬ Conjecture23ForAgents .sbi 5 := sbi5_refute.1

theorem not_theorem64iv_sbi_five : ¬ Theorem64ivForAgents .sbi 5 := sbi5_refute.2

end HK
