module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Log

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

public section

@[expose] section

namespace OAI.MatrixMultiplication.AuxiliarySeparation

open Filter
open scoped Topology NNReal

/-- An affine polynomial prefactor cannot increase an exponential growth rate. -/
theorem le_of_pow_le_polynomial_mul_pow {a b C : ℝ} {d k : ℕ} (ha : 0 ≤ a)
    (h : ∀ n : ℕ, b^n ≤ C * ((k : ℝ)*n+1)^d * a^n) : b ≤ a := by
  by_contra! hab
  have hb := ha.trans_lt hab
  have hC : 0 ≤ C := zero_le_one.trans (by simpa using h 0)
  let D := C * ((k : ℝ)+1)^d
  have H := (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt d
    (show ‖a‖ < b by simpa [Real.norm_eq_abs, abs_of_nonneg ha] using hab)).const_mul_left D
  refine (Asymptotics.IsBigO.of_norm_eventuallyLE ?_).not_isLittleO
    (Eventually.of_forall fun n => (pow_pos hb n).ne').frequently H
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [Real.norm_of_nonneg (pow_nonneg hb.le _)]
  refine (h n).trans ?_
  simp only [D, mul_assoc]
  rw [← mul_assoc (((k : ℝ)+1)^d), ← mul_pow]
  gcongr
  exact_mod_cast (by rw [Nat.add_mul]; omega : k*n+1 ≤ (k+1)*n)

theorem le_of_pow_le_const_mul_pow {a b C : ℝ} (ha : 0 ≤ a)
    (h : ∀ n : ℕ, b^n ≤ C * a^n) : b ≤ a :=
  le_of_pow_le_polynomial_mul_pow (d := 0) (k := 0) ha (by simpa using h)

/-- A uniform bound on all positive natural inputs forces the exponent on
the left to be no larger than the exponent on the right. -/
theorem rpow_exponent_le_of_nat_bound {a b C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ a ≤ C * (n : ℝ) ^ b) :
    a ≤ b := by
  apply (Real.rpow_le_rpow_left_iff (by norm_num : 1 < (2 : ℝ))).mp
  refine le_of_pow_le_const_mul_pow (C := C) (by positivity) (fun j => ?_)
  simpa [Nat.cast_pow, ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)] using
    hbound (2 ^ j) (Nat.one_le_pow _ _ (by omega))

/-- A constant additive error disappears under unbounded positive scaling. -/
theorem le_of_scaled_le {a b C : ℝ} (h : ∀ n : ℕ, n.succ*a ≤ n.succ*b+C) : a ≤ b := by
  by_contra! he
  obtain ⟨n, hn⟩ := exists_lt_nsmul (sub_pos.mpr he) C
  grind

/-- Monotone multiplicative functions agreeing at two agree on positive inputs. -/
private theorem le_of_two_eq {f g : ℕ →* ℝ≥0} (hf : Monotone f) (hg : Monotone g)
    (h : f 2 = g 2) {n : ℕ} (hn : 0 < n) : f n ≤ g n := by
  refine NNReal.coe_le_coe.mp (le_of_pow_le_const_mul_pow (C := f 2) (by positivity) ?_)
  norm_cast
  intro j
  let k := Nat.log 2 (n^j)
  rw [← map_pow, ← map_pow]
  calc
    _ ≤ f (2 ^ (k+1)) := hf (Nat.lt_pow_succ_log_self (by decide) _).le
    _ = f 2 * g (2^k) := by grind
    _ ≤ _ := mul_le_mul_of_nonneg_left (hg (Nat.pow_log_le_self _ (by positivity))) zero_le

/-- A monotone multiplicative function on positive natural numbers is a real power. -/
theorem monotoneMonoidHom_eq_rpow (f : ℕ →* ℝ≥0) (hf : Monotone f) {n : ℕ} (hn : 0 < n) :
    f n = (n : ℝ≥0) ^ Real.logb 2 (f 2) := by
  let t := Real.logb 2 (f 2)
  have h2 : 1 ≤ f 2 := by simpa using hf (show 1 ≤ 2 by decide)
  let g := (NNReal.rpowMonoidHom t).comp (Nat.castRingHom ℝ≥0).toMonoidHom
  have hg : Monotone g := fun a b h => NNReal.rpow_le_rpow (Nat.cast_le.mpr h)
    (Real.logb_nonneg (by norm_num) (by exact_mod_cast h2))
  have h : g 2 = f 2 := NNReal.eq (Real.rpow_logb (by norm_num) (by norm_num) (by positivity))
  exact le_antisymm (le_of_two_eq hf hg h.symm hn) (le_of_two_eq hg hf h hn)

/-- The scalar profile hypotheses used in Section 6. Only positive indices
carry mathematical content; the values on either coordinate axis are unused. -/
structure ScalarProfile (t : ℝ) where
  value : ℕ → ℕ → ℝ
  nonneg : ∀ a b, 0 ≤ value a b
  symmetric : ∀ a b, value a b = value b a
  unit : value 1 1 = 1
  concave : ∀ a h : ℕ, 1 ≤ a →
    value a h + value a (h + 2) ≤ 2 * value a (h + 1)
  tripling : ∀ a h : ℕ, 3 * value a h ≤ value a (3 * h + a - 1)
  rank_bound : ∀ n : ℕ, value n n ≤ (2 * (n : ℝ)) ^ (3 / t)

namespace ScalarProfile

private noncomputable def scale (a h : ℕ) : ℝ := h + ((a : ℝ) - 1) / 2

private theorem scale_pos {a h : ℕ} (ha : 1 ≤ a) (hh : 1 ≤ h) : 0 < scale a h := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  unfold scale
  positivity

/-- Subtract the affine function with the chosen tangent slope and the
tripling shift. The gap is nonincreasing on the tail, while tripling forces
it to grow by a factor of at least three. -/
private theorem le_tangent_slope {t : ℝ} (P : ScalarProfile t)
    {a b h : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hh : b ≤ h) :
    P.value a h / scale a h ≤ P.value a (b + 1) - P.value a b := by
  apply (div_le_iff₀ (scale_pos ha (hb.trans hh))).mpr
  let Δ (n : ℕ) := P.value a (n+1) - P.value a n
  let q (n : ℕ) := P.value a n - scale a n * Δ b
  have hΔ : Antitone Δ := antitone_nat_of_succ_le fun n => by
    dsimp [Δ]
    linarith [P.concave a n ha]
  have hq : AntitoneOn q (Set.Ici b) := antitoneOn_nat_Ici_of_succ_le fun n hn => by
    have hd := hΔ hn
    dsimp [q, scale]
    push_cast
    linarith
  have H := hq hh (show b ≤ 3*h+a-1 by omega) (show h ≤ 3*h+a-1 by omega)
  dsimp [q, scale] at H ⊢
  push_cast [Nat.cast_sub (by omega : 1 ≤ 3*h+a)] at H
  linarith [P.tripling a h]

/-- Cubing the recurrence between adjacent diagonal values gives the lower bound. -/
private theorem diagonal_fourth_power_lower {t : ℝ} (P : ScalarProfile t)
    (n : ℕ) (hn : 1 ≤ n) : (n : ℝ)^4 ≤ P.value n n ^ 3 := by
  let u (j : ℕ) := P.value j j / scale j j
  have he (j : ℕ) (hj : 1 ≤ j) : P.value j j = u j * scale j j :=
    (div_mul_cancel₀ _ (scale_pos hj hj).ne').symm
  have hs (j : ℕ) (hj : 1 ≤ j) : (3*(j : ℝ)+1) * u j ≤ 3*(j : ℝ) * u (j+1) := by
    have H := add_le_add (P.le_tangent_slope hj hj le_rfl)
      (P.le_tangent_slope (by omega : 1 ≤ j+1) hj (Nat.le_succ j))
    change u j + u (j+1) ≤ _ at H
    rw [P.symmetric (j+1) j, he j hj, he (j+1) (by omega)] at H
    dsimp [scale] at H
    push_cast at H
    linarith
  have hc (j : ℕ) (hj : 1 ≤ j) : (j : ℝ) ≤ u j ^ 3 := by
    induction j, hj using Nat.le_induction with
    | base => norm_num [u, scale, P.unit]
    | succ j hj ih =>
      rw [Nat.cast_succ, ← mul_le_mul_iff_right₀ (pow_pos (by positivity : 0 < 3*(j : ℝ)) 3)]
      have h₀ : 0 ≤ u j := div_nonneg (P.nonneg ..) (scale_pos hj hj).le
      have H := pow_le_pow_left₀ (mul_nonneg (by positivity) h₀) (hs j hj) 3
      rw [mul_pow, mul_pow] at H
      nlinarith [mul_le_mul_of_nonneg_left ih (show 0 ≤ (3*(j : ℝ)+1)^3 by positivity)]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnr : (n : ℝ) ≤ scale n n := by unfold scale; linarith
  rw [he n hn, mul_pow, pow_succ']
  have H := hc n hn
  have h0 := (Nat.cast_nonneg (α := ℝ) n).trans H
  gcongr

/-- The dimension upper bound cannot grow more slowly than the diagonal lower bound. -/
theorem exponent_le_nine_quarters {t : ℝ} (P : ScalarProfile t) (ht : 0 < t) :
    t ≤ 9 / 4 := by
  have H : (4 : ℝ) ≤ (3/t)*3 := rpow_exponent_le_of_nat_bound (C := 2 ^ ((3/t)*3)) fun n hn => by
    have H := (P.diagonal_fourth_power_lower n hn).trans
      (pow_le_pow_left₀ (P.nonneg ..) (P.rank_bound n) 3)
    rw [← Real.rpow_mul_natCast (by positivity), Real.mul_rpow (by norm_num) (by positivity)] at H
    simpa using H
  have := mul_le_mul_of_nonneg_right H ht.le
  grind

end ScalarProfile

end OAI.MatrixMultiplication.AuxiliarySeparation
