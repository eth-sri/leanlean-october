module

public import PaperStatements

@[expose] public section

namespace ImprovedExponents

open Finset ThreeSumApsp

def prefCount (k m : ℕ) : ℕ := ∑ j ∈ range (m + 1), k.choose j * 9 ^ (k - j)

theorem pow_mul_prefCount_le (k d m : ℕ) : 9 ^ d * prefCount k m ≤ prefCount (k + d) m := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hstep : 9 * prefCount (k + d) m ≤ prefCount (k + d + 1) m := by
      unfold prefCount
      rw [mul_sum]
      refine sum_le_sum fun j _ => ?_
      rcases Nat.lt_or_ge (k + d) j with hj | hj
      · simp [Nat.choose_eq_zero_of_lt hj]
      · rw [show k + d + 1 - j = (k + d - j) + 1 by omega, pow_succ]
        nlinarith [Nat.choose_le_succ (k + d) j, Nat.zero_le (9 ^ (k + d - j)),
          Nat.mul_le_mul_right (9 ^ (k + d - j)) (Nat.choose_le_succ (k + d) j)]
    calc 9 ^ (d + 1) * prefCount k m = 9 * (9 ^ d * prefCount k m) := by ring
      _ ≤ 9 * prefCount (k + d) m := by gcongr
      _ ≤ prefCount (k + d + 1) m := hstep

theorem prefCount_term_ratio (L j : ℕ) :
    (L - j) * (L.choose j * 9 ^ (L - j))
      = 9 * (j + 1) * (L.choose (j + 1) * 9 ^ (L - (j + 1))) := by
  rcases Nat.lt_or_ge j L with hj | hj
  · have h1 : L - j = (L - (j + 1)) + 1 := by omega
    have h2 := Nat.choose_succ_right_eq L j
    rw [h1, pow_succ, ← h1]
    calc (L - j) * (L.choose j * (9 ^ (L - (j + 1)) * 9))
        = 9 * (L.choose j * (L - j)) * 9 ^ (L - (j + 1)) := by ring
      _ = 9 * (L.choose (j + 1) * (j + 1)) * 9 ^ (L - (j + 1)) := by rw [h2]
      _ = 9 * (j + 1) * (L.choose (j + 1) * 9 ^ (L - (j + 1))) := by ring
  · rw [Nat.sub_eq_zero_of_le hj, Nat.choose_eq_zero_of_lt (by omega : L < j + 1)]
    simp

theorem sub_mul_prefCount_le {L m : ℕ} (h : 10 * m ≤ L) :
    (L - m + 1 - 9 * m) * prefCount L m ≤ (L - m + 1) * M L m := by
  have hM : M L m = L.choose m * 9 ^ (L - m) := by
    unfold M K N0
    rw [← pow_mul, mul_comm (L - m) 2, pow_mul]
    norm_num
  rw [hM]
  have haux : ∀ j ≤ m,
      (L - m + 1 - 9 * m) * prefCount L j ≤ (L - m + 1) * (L.choose j * 9 ^ (L - j)) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [prefCount, zero_add, range_one, sum_singleton]
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    | succ j ih =>
      intro hj
      have hstep : (L - m + 1) * (L.choose j * 9 ^ (L - j))
          ≤ 9 * m * (L.choose (j + 1) * 9 ^ (L - (j + 1))) := calc
        (L - m + 1) * (L.choose j * 9 ^ (L - j)) ≤ (L - j) * (L.choose j * 9 ^ (L - j)) :=
          Nat.mul_le_mul_right _ (by omega)
        _ = 9 * (j + 1) * (L.choose (j + 1) * 9 ^ (L - (j + 1))) := prefCount_term_ratio L j
        _ ≤ 9 * m * (L.choose (j + 1) * 9 ^ (L - (j + 1))) :=
          Nat.mul_le_mul_right _ (by omega)
      have hsplit : prefCount L (j + 1) = prefCount L j + L.choose (j + 1) * 9 ^ (L - (j + 1)) := by
        unfold prefCount; rw [sum_range_succ]
      rw [hsplit, mul_add]
      exact (Nat.add_le_add_right ((ih (by omega)).trans hstep) _).trans_eq
        (by rw [← add_mul, Nat.add_sub_cancel' (by omega)])
  exact haux m le_rfl

def encWorkP (L m : ℕ) : ℕ := ∑ k ∈ range (L + 1), prefCount k m * 7 ^ (L - k)

theorem encWorkP_le_M_div {L m : ℕ} (h : 10 * m ≤ L) :
    (encWorkP L m : ℝ) ≤ 9 / 2 * (M L m : ℝ) / (1 - rho L m) := by
  have hgeom : ∀ n : ℕ, ∑ d ∈ range n, ((7 : ℝ) / 9) ^ d = 9 / 2 * (1 - (7 / 9) ^ n) := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; ring
  have hterm : ∀ k ∈ range (L + 1),
      ((prefCount k m * 7 ^ (L - k) : ℕ) : ℝ) ≤ prefCount L m * ((7 : ℝ) / 9) ^ (L - k) := by
    intro k hk
    have hk' : k ≤ L := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hp := pow_mul_prefCount_le k (L - k) m
    rw [Nat.add_sub_cancel' hk'] at hp
    have hp' : (9 : ℝ) ^ (L - k) * prefCount k m ≤ prefCount L m := by exact_mod_cast hp
    have h7 : (0 : ℝ) < 7 ^ (L - k) := by positivity
    have h9 : (0 : ℝ) < 9 ^ (L - k) := by positivity
    push_cast
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ h9]
    nlinarith
  have hsum : ∑ k ∈ range (L + 1), ((7 : ℝ) / 9) ^ (L - k) ≤ 9 / 2 := by
    have hrefl : ∑ k ∈ range (L + 1), ((7 : ℝ) / 9) ^ (L - k)
        = ∑ d ∈ range (L + 1), ((7 : ℝ) / 9) ^ d := by
      rw [← sum_range_reflect (fun d => ((7 : ℝ) / 9) ^ d) (L + 1)]
      rfl
    rw [hrefl, hgeom]
    have : (0 : ℝ) ≤ (7 / 9) ^ (L + 1) := by positivity
    linarith
  have h1 : (encWorkP L m : ℝ) ≤ 9 / 2 * prefCount L m :=
    calc (encWorkP L m : ℝ) = ∑ k ∈ range (L + 1), ((prefCount k m * 7 ^ (L - k) : ℕ) : ℝ) := by
          unfold encWorkP; push_cast; rfl
      _ ≤ ∑ k ∈ range (L + 1), (prefCount L m : ℝ) * ((7 : ℝ) / 9) ^ (L - k) := sum_le_sum hterm
      _ = prefCount L m * ∑ k ∈ range (L + 1), ((7 : ℝ) / 9) ^ (L - k) := by rw [mul_sum]
      _ ≤ prefCount L m * (9 / 2) := by gcongr
      _ = 9 / 2 * prefCount L m := by ring
  have h' : (10 : ℝ) * m ≤ L := by exact_mod_cast h
  have hcast : ((L : ℝ) - m + 1 - 9 * m) * prefCount L m ≤ ((L : ℝ) - m + 1) * M L m := by
    have := (Nat.cast_le (α := ℝ)).mpr (sub_mul_prefCount_le h)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_sub (by omega)]
      at this
    simpa using this
  have : (0 : ℝ) < (L : ℝ) - m + 1 := by linarith
  have hrho : 1 - rho L m = ((L : ℝ) - m + 1 - 9 * m) / ((L : ℝ) - m + 1) := by
    unfold rho; field_simp
  have : (prefCount L m : ℝ) ≤ (M L m : ℝ) / (1 - rho L m) := by
    rw [hrho, div_div_eq_mul_div, le_div_iff₀ (by linarith)]
    linarith
  rw [mul_div_assoc]
  linarith

theorem pow_seven_le_encWorkP (L m : ℕ) : 7 ^ L ≤ encWorkP L m := by
  unfold encWorkP
  calc 7 ^ L = prefCount 0 m * 7 ^ (L - 0) := by
        simp [prefCount, sum_range_succ', Nat.choose_zero_succ]
    _ ≤ ∑ k ∈ range (L + 1), prefCount k m * 7 ^ (L - k) :=
      single_le_sum (f := fun k => prefCount k m * 7 ^ (L - k)) (fun _ _ => Nat.zero_le _)
        (mem_range.mpr (Nat.succ_pos L))

end ImprovedExponents
