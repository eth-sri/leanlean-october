module

public import PaperStatements

@[expose] public section

namespace ImprovedExponents

open Finset ThreeSumApsp

def prefCount (k m : ℕ) : ℕ := ∑ j ∈ range (m + 1), k.choose j * 9 ^ (k - j)

theorem nine_mul_prefCount_le (k m : ℕ) : 9 * prefCount k m ≤ prefCount (k + 1) m := by
  unfold prefCount; rw [mul_sum]
  refine sum_le_sum fun j _ => ?_
  rcases Nat.lt_or_ge k j with hj | hj
  · simp [Nat.choose_eq_zero_of_lt hj]
  · rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ]
    nlinarith [Nat.mul_le_mul_right (9 ^ (k - j)) (Nat.choose_le_succ k j)]

theorem pow_mul_prefCount_le (k d m : ℕ) : 9 ^ d * prefCount k m ≤ prefCount (k + d) m := by
  induction d with
  | zero => simp
  | succ d ih =>
    exact (by ring : 9 ^ (d + 1) * prefCount k m = 9 * (9 ^ d * prefCount k m)).trans_le
      ((Nat.mul_le_mul_left 9 ih).trans (nine_mul_prefCount_le _ _))

theorem prefCount_le_M_div {L m : ℕ} (h : 10 * m ≤ L) :
    (prefCount L m : ℝ) ≤ (M L m : ℝ) / (1 - rho L m) := by
  have haux : ∀ j ≤ m, (L - m + 1 - 9 * m) * prefCount L j ≤ (L - m + 1) * (L.choose j * 9 ^ (L - j)) := by
    intro j; induction j with
    | zero => intro _; simp [prefCount]
    | succ j ih =>
      intro hj
      have hrat : (L - j) * (L.choose j * 9 ^ (L - j))
          = 9 * (j + 1) * (L.choose (j + 1) * 9 ^ (L - (j + 1))) := by
        have h1 : L - j = (L - (j + 1)) + 1 := by omega
        rw [h1, pow_succ, ← h1]
        linear_combination 9 * 9 ^ (L - (j + 1)) * (Nat.choose_succ_right_eq L j).symm
      have hstep : (L - m + 1) * (L.choose j * 9 ^ (L - j))
          ≤ 9 * m * (L.choose (j + 1) * 9 ^ (L - (j + 1))) :=
        (Nat.mul_le_mul_right _ (by omega : L - m + 1 ≤ L - j)).trans
          (hrat.trans_le (Nat.mul_le_mul_right _ (by omega)))
      unfold prefCount at ih ⊢
      rw [sum_range_succ, mul_add]
      exact (Nat.add_le_add_right ((ih (by omega)).trans hstep) _).trans_eq
        (by rw [← add_mul, Nat.add_sub_cancel' (by omega)])
  have hM : M L m = L.choose m * 9 ^ (L - m) := by
    unfold M K N0; rw [← pow_mul, mul_comm (L - m) 2, pow_mul]; norm_num
  have hnat : (L - m + 1 - 9 * m) * prefCount L m ≤ (L - m + 1) * M L m := hM ▸ haux m le_rfl
  have h' : (10 : ℝ) * m ≤ L := by exact_mod_cast h
  have hcast : ((L : ℝ) - m + 1 - 9 * m) * prefCount L m ≤ ((L : ℝ) - m + 1) * M L m := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    rwa [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_add,
      Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at this
  have : (0 : ℝ) < (L : ℝ) - m + 1 := by linarith
  rw [show 1 - rho L m = ((L : ℝ) - m + 1 - 9 * m) / ((L : ℝ) - m + 1) by unfold rho; field_simp,
    div_div_eq_mul_div, le_div_iff₀ (by linarith)]
  linarith

def encWorkP (L m : ℕ) : ℕ := ∑ k ∈ range (L + 1), prefCount k m * 7 ^ (L - k)

theorem encWorkP_le_M_div {L m : ℕ} (h : 10 * m ≤ L) :
    (encWorkP L m : ℝ) ≤ 9 / 2 * (M L m : ℝ) / (1 - rho L m) := by
  have hgeom (n : ℕ) : ∑ d ∈ range n, ((7 : ℝ) / 9) ^ d = 9 / 2 * (1 - (7 / 9) ^ n) := by
    induction n with | zero => simp | succ n ih => rw [sum_range_succ, ih]; ring
  have hterm (k : ℕ) (hk : k ∈ range (L + 1)) :
      ((prefCount k m * 7 ^ (L - k) : ℕ) : ℝ) ≤ prefCount L m * ((7 : ℝ) / 9) ^ (L - k) := by
    have hk' := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have h' : (9 : ℝ) ^ (L - k) * prefCount k m ≤ prefCount L m := by
      have hp := pow_mul_prefCount_le k (L - k) m
      rw [Nat.add_sub_cancel' hk'] at hp; exact_mod_cast hp
    have : (0 : ℝ) < 7 ^ (L - k) := by positivity
    push_cast; rw [div_pow, ← mul_div_assoc, le_div_iff₀ (by positivity)]; nlinarith
  have hsum : ∑ k ∈ range (L + 1), ((7 : ℝ) / 9) ^ (L - k) ≤ 9 / 2 := by
    have hr : ∑ k ∈ range (L + 1), ((7 : ℝ) / 9) ^ (L - k) = ∑ d ∈ range (L + 1), ((7 : ℝ) / 9) ^ d := by
      rw [← sum_range_reflect (fun d => ((7 : ℝ) / 9) ^ d) (L + 1)]
      exact sum_congr rfl fun k _ => by simp 
    rw [hr, hgeom]; linarith [show (0 : ℝ) ≤ (7 / 9) ^ (L + 1) by positivity]
  have h1 : (encWorkP L m : ℝ) ≤ 9 / 2 * prefCount L m :=
    calc (encWorkP L m : ℝ) = ∑ k ∈ range (L + 1), ((prefCount k m * 7 ^ (L - k) : ℕ) : ℝ) := by
          unfold encWorkP; push_cast; rfl
      _ ≤ ∑ k ∈ range (L + 1), (prefCount L m : ℝ) * ((7 : ℝ) / 9) ^ (L - k) := sum_le_sum hterm
      _ = prefCount L m * ∑ k ∈ range (L + 1), ((7 : ℝ) / 9) ^ (L - k) := by rw [mul_sum]
      _ ≤ 9 / 2 * prefCount L m := by linarith [mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (prefCount L m))]
  rw [mul_div_assoc]; linarith [prefCount_le_M_div h]

theorem pow_seven_le_encWorkP (L m : ℕ) : 7 ^ L ≤ encWorkP L m := by
  exact (by simp [prefCount, sum_range_succ'] :
    7 ^ L = prefCount 0 m * 7 ^ (L - 0)).trans_le
    (single_le_sum (f := fun k => prefCount k m * 7 ^ (L - k)) (fun _ _ => Nat.zero_le _)
      (mem_range.mpr (Nat.succ_pos L)))

end ImprovedExponents
