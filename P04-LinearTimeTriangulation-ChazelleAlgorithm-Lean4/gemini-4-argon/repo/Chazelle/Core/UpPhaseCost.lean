module

public import Chazelle.Core.UpPhase20
public import Chazelle.Cost.UpPhase

/-!
# WP-J up phase: the cost of one chain

Every part of the cost of one chain of grade `g` is at most a constant times
`Y g = 2^g 2^(-g/76)`: Lemma 4.1 (`lemma41Nat_le`, via `slack76_cubic`), the coarsening
(`FB`, via Lemma 2.3 and `slack76_linear`), the preprocessing (`NB`), brute force (`g < 7`).
Hence `stepB g + 19 ≤ K₁ · Y g` (`stepB_le`).
-/

namespace Chazelle.Core.Up

open Chazelle.Cost

@[expose] public section

/-- The per-chain scale `2^g 2^(-g/76)`. -/
noncomputable def Yg (g : ℕ) : ℝ := (2 : ℝ) ^ g * (2 : ℝ) ^ (-(g : ℝ) / 76)

/-- **The per-chain constant.** -/
noncomputable def K1 (κB κL : ℕ) (κG : ℕ → ℕ) (κO : ℕ) : ℝ :=
  κB * 129 ^ 3 + κL * (2 * 34200 ^ 3 + 2) +
    κG 4 * (18 * l23c 4 * (Nat.clog 2 (l23c 4) + 17) + 1) + κO * (130 * l23c 4 + 1) + 2000

section proofs

theorem Yg_pos (g : ℕ) : 0 < Yg g := by unfold Yg; have := two_rpow_pos (-(g : ℝ) / 76); positivity

theorem one_le_Yg (g : ℕ) : 1 ≤ Yg g := by
  unfold Yg
  rw [← Real.rpow_natCast, two_rpow_mul_two_rpow]
  apply Real.one_le_rpow (by norm_num)
  have : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  linarith

theorem Yg_le (g : ℕ) : Yg g ≤ (2 : ℝ) ^ g := by
  unfold Yg
  have h1 : (2 : ℝ) ^ (-(g : ℝ) / 76) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have : (0 : ℝ) ≤ g := Nat.cast_nonneg g
    linarith
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ g := by positivity
  nlinarith

/-- `2^(-g/5) ≤ 2^(-g/76)`, times `2^g`. -/
theorem pow_mul_div5_le (g : ℕ) : (2 : ℝ) ^ g * (2 : ℝ) ^ (-(g : ℝ) / 5) ≤ Yg g := by
  unfold Yg
  exact mul_le_mul_of_nonneg_left (two_rpow_neg_div5_le g) (by positivity)

/-- `2^g · g 2^(-g/5) ≤ 12 Y g`. -/
theorem pow_mul_lin_le (g : ℕ) :
    (2 : ℝ) ^ g * ((g : ℝ) * (2 : ℝ) ^ (-(g : ℝ) / 5)) ≤ 12 * Yg g := by
  unfold Yg
  have := mul_le_mul_of_nonneg_left (slack76_linear g) (show (0 : ℝ) ≤ (2 : ℝ) ^ g by positivity)
  linarith

/-- **Lemma 4.1's bound** is at most a constant times `Y g`. -/
theorem lemma41Nat_le (g : ℕ) : (lemma41Nat g : ℝ) ≤ (2 * 34200 ^ 3 + 1) * Yg g := by
  unfold lemma41Nat
  set x : ℝ := (g : ℝ) ^ 2 * ((Nat.clog 2 g : ℝ) + 1) * (2 : ℝ) ^ ((74 : ℝ) / 75 * g) with hx
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have hcl : (Nat.clog 2 g : ℝ) ≤ g := by exact_mod_cast clog_two_le_self g
  have hcl0 : (0 : ℝ) ≤ Nat.clog 2 g := Nat.cast_nonneg _
  have hp : (0 : ℝ) < (2 : ℝ) ^ ((74 : ℝ) / 75 * g) := two_rpow_pos _
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hsq : (g : ℝ) ^ 2 * ((Nat.clog 2 g : ℝ) + 1) ≤ 2 * (g : ℝ) ^ 3 := by
    rcases Nat.eq_zero_or_pos g with h | h
    · subst h; simp
    · have : (1 : ℝ) ≤ g := by exact_mod_cast h
      nlinarith
  have hsplit : (2 : ℝ) ^ ((74 : ℝ) / 75 * g) = (2 : ℝ) ^ g * (2 : ℝ) ^ (-(g : ℝ) / 75) := by
    rw [← Real.rpow_natCast, two_rpow_mul_two_rpow]; congr 1; ring
  have hc := slack76_cubic g
  have hq : 0 ≤ (2 : ℝ) ^ (-(g : ℝ) / 75) := (two_rpow_pos _).le
  have h2g : (0 : ℝ) < (2 : ℝ) ^ g := by positivity
  have hxle : x ≤ 2 * 34200 ^ 3 * Yg g := by
    unfold Yg
    calc x ≤ 2 * (g : ℝ) ^ 3 * (2 : ℝ) ^ ((74 : ℝ) / 75 * g) := by
          rw [hx]; exact mul_le_mul_of_nonneg_right hsq hp.le
      _ = 2 * (2 : ℝ) ^ g * ((g : ℝ) ^ 3 * (2 : ℝ) ^ (-(g : ℝ) / 75)) := by rw [hsplit]; ring
      _ ≤ 2 * (2 : ℝ) ^ g * (34200 ^ 3 * (2 : ℝ) ^ (-(g : ℝ) / 76)) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 2 * 34200 ^ 3 * ((2 : ℝ) ^ g * (2 : ℝ) ^ (-(g : ℝ) / 76)) := by ring
  have hce := Nat.ceil_lt_add_one hx0
  have := one_le_Yg g
  linarith

/-- `1 / (γ'_g + 1) ≤ 2^(-g/5)`. -/
theorem inv_gradeGran_le (g : ℕ) : 1 / ((gradeGran g : ℝ) + 1) ≤ (2 : ℝ) ^ (-(g : ℝ) / 5) := by
  refine le_trans ?_ (inv_two_pow_ceilBeta_le g)
  have h1 : (2 : ℝ) ^ ceilBeta g ≤ (gradeGran g : ℝ) + 1 := by
    have : 2 ^ ceilBeta g ≤ gradeGran g := by unfold gradeGran; omega
    have : ((2 ^ ceilBeta g : ℕ) : ℝ) ≤ gradeGran g := by exact_mod_cast this
    push_cast at this; linarith
  exact one_div_le_one_div_of_le (by positivity) h1

/-- **The chord bound of a normal form of grade `g`** is `O(2^g 2^(-g/5))`. -/
theorem NB_le (g : ℕ) : (NB g : ℝ) ≤ 10 * l23c 4 * ((2 : ℝ) ^ g * (2 : ℝ) ^ (-(g : ℝ) / 5)) := by
  unfold NB
  refine le_trans Nat.cast_div_le ?_
  have hi := inv_gradeGran_le g
  have hl : (0 : ℝ) ≤ l23c 4 := Nat.cast_nonneg _
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ g := one_le_pow₀ (by norm_num)
  push_cast
  rw [div_eq_mul_one_div]
  calc (l23c 4 : ℝ) * ((2 : ℝ) ^ (g + 1) + 8) * (1 / ((gradeGran g : ℝ) + 1))
      ≤ (l23c 4 : ℝ) * ((2 : ℝ) ^ (g + 1) + 8) * (2 : ℝ) ^ (-(g : ℝ) / 5) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ (l23c 4 : ℝ) * (10 * (2 : ℝ) ^ g) * (2 : ℝ) ^ (-(g : ℝ) / 5) := by
        rw [pow_succ]
        apply mul_le_mul_of_nonneg_right _ (two_rpow_pos _).le
        apply mul_le_mul_of_nonneg_left _ hl
        linarith
    _ = 10 * l23c 4 * ((2 : ℝ) ^ g * (2 : ℝ) ^ (-(g : ℝ) / 5)) := by ring

/-- **The preprocessing term.** -/
theorem NB_term_le (g : ℕ) :
    ((NB g * (g + 1) + 1 : ℕ) : ℝ) ≤ (130 * l23c 4 + 1) * Yg g := by
  have h := NB_le g
  have hl : (0 : ℝ) ≤ l23c 4 := Nat.cast_nonneg _
  have hY := one_le_Yg g
  have hA := pow_mul_div5_le g
  have hB := pow_mul_lin_le g
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have hNB0 : (0 : ℝ) ≤ NB g := Nat.cast_nonneg _
  push_cast
  have e1 : (NB g : ℝ) * ((g : ℝ) + 1) ≤
      10 * l23c 4 * ((2 : ℝ) ^ g * (2 : ℝ) ^ (-(g : ℝ) / 5)) * ((g : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right h (by linarith)
  have e2 : 10 * (l23c 4 : ℝ) * ((2 : ℝ) ^ g * (2 : ℝ) ^ (-(g : ℝ) / 5)) * ((g : ℝ) + 1) =
      10 * l23c 4 * ((2 : ℝ) ^ g * ((g : ℝ) * (2 : ℝ) ^ (-(g : ℝ) / 5)) +
        (2 : ℝ) ^ g * (2 : ℝ) ^ (-(g : ℝ) / 5)) := by ring
  have e3 : (2 : ℝ) ^ g * ((g : ℝ) * (2 : ℝ) ^ (-(g : ℝ) / 5)) +
      (2 : ℝ) ^ g * (2 : ℝ) ^ (-(g : ℝ) / 5) ≤ 13 * Yg g := by linarith
  have e4 := mul_le_mul_of_nonneg_left e3 (show (0 : ℝ) ≤ 10 * l23c 4 by positivity)
  nlinarith

/-- **The chord bound of the coarsened child** is `O(2^g 2^(-g/5))`. -/
theorem FB_le (g : ℕ) : (FB g : ℝ) ≤ 18 * l23c 4 * ((2 : ℝ) ^ g * (2 : ℝ) ^ (-(g : ℝ) / 5)) := by
  unfold FB
  refine le_trans Nat.cast_div_le ?_
  have hi := inv_gradeGran_le (g - 1)
  have hl : (0 : ℝ) ≤ l23c 4 := Nat.cast_nonneg _
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ g := one_le_pow₀ (by norm_num)
  have hg1 : (g : ℝ) ≤ ((g - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : g ≤ g - 1 + 1)
  have hsh : (2 : ℝ) ^ (-((g - 1 : ℕ) : ℝ) / 5) ≤ 2 * (2 : ℝ) ^ (-(g : ℝ) / 5) := by
    have : (2 : ℝ) ^ (-((g - 1 : ℕ) : ℝ) / 5) ≤ (2 : ℝ) ^ (1 + -(g : ℝ) / 5) :=
      two_rpow_le_two_rpow (by linarith)
    rwa [← two_rpow_mul_two_rpow, Real.rpow_one] at this
  push_cast
  rw [div_eq_mul_one_div]
  calc (l23c 4 : ℝ) * ((2 : ℝ) ^ g + 8) * (1 / ((gradeGran (g - 1) : ℝ) + 1))
      ≤ (l23c 4 : ℝ) * ((2 : ℝ) ^ g + 8) * (2 * (2 : ℝ) ^ (-(g : ℝ) / 5)) :=
        mul_le_mul_of_nonneg_left (hi.trans hsh) (by positivity)
    _ ≤ (l23c 4 : ℝ) * (9 * (2 : ℝ) ^ g) * (2 * (2 : ℝ) ^ (-(g : ℝ) / 5)) := by
        apply mul_le_mul_of_nonneg_right _ (by have := two_rpow_pos (-(g : ℝ) / 5); positivity)
        apply mul_le_mul_of_nonneg_left _ hl
        linarith
    _ = 18 * l23c 4 * ((2 : ℝ) ^ g * (2 : ℝ) ^ (-(g : ℝ) / 5)) := by ring

theorem FB_clog (g : ℕ) : Nat.clog 2 (FB g) ≤ Nat.clog 2 (l23c 4) + g + 4 := by
  have h1 : FB g ≤ l23c 4 * (2 ^ g + 8) := Nat.div_le_self _ _
  have h2 := Nat.clog_mono_right 2 h1
  have h3 := MergeAsm.clog_mul_le (l23c 4) (2 ^ g + 8)
  have h4 : Nat.clog 2 (2 ^ g + 8) ≤ g + 4 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add]; have := Nat.one_le_two_pow (n := g); omega
  omega

/-- **The coarsening term.** -/
theorem FB_term_le (g : ℕ) : ((FB g * (Nat.clog 2 (FB g) + 1) + 1 : ℕ) : ℝ) ≤
    (18 * l23c 4 * (Nat.clog 2 (l23c 4) + 17) + 1) * Yg g := by
  have h := FB_le g
  have hc := FB_clog g
  have hl : (0 : ℝ) ≤ l23c 4 := Nat.cast_nonneg _
  have hY := one_le_Yg g
  have hA := pow_mul_div5_le g
  have hB := pow_mul_lin_le g
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have hF0 : (0 : ℝ) ≤ FB g := Nat.cast_nonneg _
  set a : ℝ := (Nat.clog 2 (l23c 4) : ℝ) with ha
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  have hc' : ((Nat.clog 2 (FB g) : ℕ) : ℝ) + 1 ≤ a + g + 5 := by
    have : ((Nat.clog 2 (FB g) : ℕ) : ℝ) ≤ ((Nat.clog 2 (l23c 4) + g + 4 : ℕ) : ℝ) := by
      exact_mod_cast hc
    push_cast at this; linarith
  push_cast
  have e1 : (FB g : ℝ) * ((Nat.clog 2 (FB g) : ℝ) + 1) ≤ (FB g : ℝ) * (a + g + 5) :=
    mul_le_mul_of_nonneg_left hc' hF0
  have e2 : (FB g : ℝ) * (a + g + 5) ≤
      18 * l23c 4 * ((2 : ℝ) ^ g * (2 : ℝ) ^ (-(g : ℝ) / 5)) * (a + g + 5) :=
    mul_le_mul_of_nonneg_right h (by linarith)
  have e3 : 18 * (l23c 4 : ℝ) * ((2 : ℝ) ^ g * (2 : ℝ) ^ (-(g : ℝ) / 5)) * (a + g + 5) =
      18 * l23c 4 * ((2 : ℝ) ^ g * ((g : ℝ) * (2 : ℝ) ^ (-(g : ℝ) / 5)) +
        (a + 5) * ((2 : ℝ) ^ g * (2 : ℝ) ^ (-(g : ℝ) / 5))) := by ring
  have e4 : (2 : ℝ) ^ g * ((g : ℝ) * (2 : ℝ) ^ (-(g : ℝ) / 5)) +
      (a + 5) * ((2 : ℝ) ^ g * (2 : ℝ) ^ (-(g : ℝ) / 5)) ≤ (a + 17) * Yg g := by
    have := mul_le_mul_of_nonneg_left hA (show (0 : ℝ) ≤ a + 5 by linarith)
    linarith
  have e5 := mul_le_mul_of_nonneg_left e4 (show (0 : ℝ) ≤ 18 * l23c 4 by positivity)
  nlinarith

/-- The cost of one chain, in natural numbers. -/
theorem stepB_le_nat (κB κL : ℕ) (κG : ℕ → ℕ) (κO g : ℕ) :
    stepB κB κL κG κO g + 19 ≤ κB * 129 ^ 3 + κL * (lemma41Nat g + 1) +
      κG 4 * (FB g * (Nat.clog 2 (FB g) + 1) + 1) + κO * (NB g * (g + 1) + 1) + 1993 := by
  unfold stepB nfB
  split_ifs with h
  · have h1 : 2 ^ g ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (2 ^ g + 1) ^ 3 ≤ 129 ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h3 := Nat.mul_le_mul_left κB h2
    omega
  · omega

/-- **The cost of one chain of grade `g` is at most `K₁ · 2^g 2^(-g/76)`.** -/
theorem stepB_le (κB κL : ℕ) (κG : ℕ → ℕ) (κO g : ℕ) :
    ((stepB κB κL κG κO g + 19 : ℕ) : ℝ) ≤ K1 κB κL κG κO * Yg g := by
  have h := stepB_le_nat κB κL κG κO g
  have h' : ((stepB κB κL κG κO g + 19 : ℕ) : ℝ) ≤ ((κB * 129 ^ 3 + κL * (lemma41Nat g + 1) +
      κG 4 * (FB g * (Nat.clog 2 (FB g) + 1) + 1) + κO * (NB g * (g + 1) + 1) + 1993 : ℕ) : ℝ) := by
    exact_mod_cast h
  have hY := one_le_Yg g
  have hL := lemma41Nat_le g
  have hF := FB_term_le g
  have hN := NB_term_le g
  have hB0 : (0 : ℝ) ≤ κB := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ κL := Nat.cast_nonneg _
  have hG0 : (0 : ℝ) ≤ κG 4 := Nat.cast_nonneg _
  have hO0 : (0 : ℝ) ≤ κO := Nat.cast_nonneg _
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, (34200 : ℝ) ^ 3 = Cc := ⟨_, rfl⟩
  rw [hCc] at hL
  have i1 : (κB : ℝ) * 129 ^ 3 ≤ κB * 129 ^ 3 * Yg g :=
    le_mul_of_one_le_right (by positivity) hY
  have i2 : (κL : ℝ) * ((lemma41Nat g : ℝ) + 1) ≤ κL * (2 * Cc + 2) * Yg g := by
    have : (lemma41Nat g : ℝ) + 1 ≤ (2 * Cc + 2) * Yg g := by linarith
    exact (mul_le_mul_of_nonneg_left this hL0).trans_eq (by ring)
  have i3 : (κG 4 : ℝ) * ((FB g * (Nat.clog 2 (FB g) + 1) + 1 : ℕ) : ℝ) ≤
      κG 4 * (18 * l23c 4 * (Nat.clog 2 (l23c 4) + 17) + 1) * Yg g := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hF hG0
  have i4 : (κO : ℝ) * ((NB g * (g + 1) + 1 : ℕ) : ℝ) ≤ κO * (130 * l23c 4 + 1) * Yg g := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hN hO0
  have i5 : (1993 : ℝ) ≤ 2000 * Yg g := by linarith
  have hK : K1 κB κL κG κO * Yg g = κB * 129 ^ 3 * Yg g + κL * (2 * Cc + 2) * Yg g +
      κG 4 * (18 * l23c 4 * (Nat.clog 2 (l23c 4) + 17) + 1) * Yg g +
      κO * (130 * l23c 4 + 1) * Yg g + 2000 * Yg g := by unfold K1; rw [hCc]; ring
  rw [hK]
  push_cast at h' i3 i4 ⊢
  linarith

end proofs

end

end Chazelle.Core.Up
