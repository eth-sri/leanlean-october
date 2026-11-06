module

public import Chazelle.Core.DownPhaseDrvPMath
public import Chazelle.RewriteTactics
public import Chazelle.MiscTactics

/-!
# Down-phase pieces (D4), part 8: arithmetic of the cost

* `lemma41Nat_mono`: Lemma 4.1's bound is monotone in the grade;
* `le_lemma41Nat`: `g ≤ lemma41Nat g`;
* `kcost_le`: a normal form of a grade-`g` leaf (`K · 2^⌈βg⌉ ≤ 2520 · 2^g`, from Lemma 2.3)
  has `K (⌈log₂ K⌉ + 1) ≤ 35280 · lemma41Nat g` (the build and the granularity enforcement on it
  stay within Lemma 4.1's bound);
* `kcost_mono`: `K (⌈log₂ K⌉ + 1)` is monotone.
-/

namespace Chazelle.Core

namespace DrvP

@[expose] public section

theorem lemma41Nat_mono {g g' : ℕ} (h : g ≤ g') : lemma41Nat g ≤ lemma41Nat g' := by
  unfold lemma41Nat
  apply Nat.ceil_mono
  have h1 : (g : ℝ) ≤ g' := by exact_mod_cast h
  have h2 : ((Nat.clog 2 g : ℕ) : ℝ) ≤ (Nat.clog 2 g' : ℕ) := by
    exact_mod_cast Nat.clog_mono_right 2 h
  have h3 : (2 : ℝ) ^ ((74 : ℝ) / 75 * g) ≤ (2 : ℝ) ^ ((74 : ℝ) / 75 * g') :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have h0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have hc : (0 : ℝ) ≤ (Nat.clog 2 g : ℕ) := Nat.cast_nonneg _
  have hp : (0 : ℝ) < (2 : ℝ) ^ ((74 : ℝ) / 75 * g) := Real.rpow_pos_of_pos (by norm_num) _
  have hg2 : (g : ℝ) ^ 2 ≤ (g' : ℝ) ^ 2 := by nlinarith
  calc (g : ℝ) ^ 2 * ((Nat.clog 2 g : ℝ) + 1) * (2 : ℝ) ^ ((74 : ℝ) / 75 * g)
      ≤ (g' : ℝ) ^ 2 * ((Nat.clog 2 g' : ℝ) + 1) * (2 : ℝ) ^ ((74 : ℝ) / 75 * g) := by
        apply mul_le_mul_of_nonneg_right _ hp.le
        exact mul_le_mul hg2 (by linarith) (by linarith) (by positivity)
    _ ≤ (g' : ℝ) ^ 2 * ((Nat.clog 2 g' : ℝ) + 1) * (2 : ℝ) ^ ((74 : ℝ) / 75 * g') :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

/-- The real bound below `lemma41Nat`. -/
theorem real_le_lemma41Nat (g : ℕ) :
    (g : ℝ) ^ 2 * ((Nat.clog 2 g : ℝ) + 1) * (2 : ℝ) ^ ((74 : ℝ) / 75 * g) ≤ lemma41Nat g :=
  Nat.le_ceil _

theorem le_lemma41Nat (g : ℕ) : g ≤ lemma41Nat g := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · exact Nat.zero_le _
  have h := real_le_lemma41Nat g
  have h1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ ((74 : ℝ) / 75 * g) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have h3 : (0 : ℝ) ≤ (Nat.clog 2 g : ℕ) := Nat.cast_nonneg _
  have : (g : ℝ) ≤ (lemma41Nat g : ℝ) := by
    calc (g : ℝ) ≤ (g : ℝ) ^ 2 * ((Nat.clog 2 g : ℝ) + 1) * 1 := by nlinarith
      _ ≤ _ := by
        apply le_trans _ h
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
  exact_mod_cast this

theorem kcost_mono {K K' : ℕ} (h : K ≤ K') :
    K * (Nat.clog 2 K + 1) ≤ K' * (Nat.clog 2 K' + 1) :=
  Nat.mul_le_mul h (Nat.add_le_add_right (Nat.clog_mono_right 2 h) 1)

/-- **The size of a grade-`g` normal form against Lemma 4.1's bound.** -/
theorem kcost_le {g K : ℕ} (hg : 1 ≤ g) (hK : K * 2 ^ Cost.ceilBeta g ≤ 2520 * 2 ^ g) :
    K * (Nat.clog 2 K + 1) ≤ 35280 * lemma41Nat g := by
  set cb := Cost.ceilBeta g with hcb
  have hcbg  := Cost.ceilBeta_le g
  set e := g - cb with he
  have hpow : 2 ^ g = 2 ^ e * 2 ^ cb := by rw [← pow_add]; congr 1; omega
  have hKe : K ≤ 2520 * 2 ^ e := by
    rw [hpow, ← Nat.mul_assoc] at hK
    exact Nat.le_of_mul_le_mul_right hK (Nat.two_pow_pos _)
  have hlog : Nat.clog 2 K ≤ 12 + e := by
    apply Nat.clog_le_of_le_pow
    calc K ≤ 2520 * 2 ^ e := hKe
      _ ≤ 2 ^ 12 * 2 ^ e := Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ (12 + e) := by rw [pow_add]
  have h1 : K * (Nat.clog 2 K + 1) ≤ 2520 * 2 ^ e * (13 + e) :=
    Nat.mul_le_mul hKe (by omega)
  -- the real comparison
  have hcbr : (g : ℝ) / 5 ≤ (cb : ℝ) := by
    have := Nat.le_ceil (Cost.beta * (g : ℝ))
    rw [Cost.beta_eq] at this
    rw [hcb]; unfold Cost.ceilBeta; rwli [Cost.beta_eq]
  have her : (e : ℝ) ≤ (74 : ℝ) / 75 * g := by
    rw [he, Nat.cast_sub hcbg]
    have : (0 : ℝ) ≤ g := Nat.cast_nonneg g
    linarith
  have h2e : ((2 ^ e : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((74 : ℝ) / 75 * g) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) her
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hge : (e : ℝ) ≤ g := by have := her; nlinarith
  have h13 : ((13 + e : ℕ) : ℝ) ≤ 14 * (g : ℝ) ^ 2 * ((Nat.clog 2 g : ℝ) + 1) := by
    push_cast
    have hc : (0 : ℝ) ≤ (Nat.clog 2 g : ℕ) := Nat.cast_nonneg _
    nlinarith
  have hreal := real_le_lemma41Nat g
  have hp : (0 : ℝ) ≤ ((2 ^ e : ℕ) : ℝ) := Nat.cast_nonneg _
  have key : ((2520 * 2 ^ e * (13 + e) : ℕ) : ℝ) ≤ ((35280 * lemma41Nat g : ℕ) : ℝ) := by
    push_cast
    have hc : (0 : ℝ) ≤ (Nat.clog 2 g : ℕ) := Nat.cast_nonneg _
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ ((74 : ℝ) / 75 * g) := by positivity
    calc (2520 : ℝ) * 2 ^ e * (13 + e)
        = 2520 * ((2 ^ e : ℕ) : ℝ) * ((13 + e : ℕ) : ℝ) := by pcr
      _ ≤ 2520 * (2 : ℝ) ^ ((74 : ℝ) / 75 * g) *
          (14 * (g : ℝ) ^ 2 * ((Nat.clog 2 g : ℝ) + 1)) := by
        apply mul_le_mul (by linarith) h13 (by positivity) (by positivity)
      _ = 35280 * ((g : ℝ) ^ 2 * ((Nat.clog 2 g : ℝ) + 1) *
          (2 : ℝ) ^ ((74 : ℝ) / 75 * g)) := by ring
      _ ≤ 35280 * (lemma41Nat g : ℝ) := by linarith
  have := (Nat.cast_le (α := ℝ)).1 key
  omega

end

end DrvP

end Chazelle.Core
