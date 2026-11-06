module
public import RationalUniformShortRange

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem rpow_log_quotient {T x : ℝ} (hT : 1 < T) (hx : 0 < x) :
    T ^ (Real.log x / Real.log T) = x := by
  rw [Real.rpow_def_of_pos (by linarith : 0 < T)]
  rw [mul_div_cancel₀ _ (Real.log_pos hT).ne', Real.exp_log hx]

theorem coprime_pair_den {q : ℕ × ℕ} (hq : 0 < q.2)
    (hc : Nat.Coprime q.1 q.2) : (pairRatio q).den = q.2 := by
  have hh := Rat.den_div_eq_of_coprime (a := (q.1 : ℤ)) (b := (q.2 : ℤ))
    (by exact_mod_cast hq) (by simpa using hc)
  have he : ((pairRatio q).den : ℤ) = q.2 := by simpa only [pairRatio, Int.cast_natCast] using hh
  exact_mod_cast he

theorem dyadic_pair_log {M : ℝ} {q : ℕ × ℕ}
    (hq1 : 0 < q.1) (hq2 : 0 < q.2)
    (hlo1 : M < q.1) (hhi1 : (q.1 : ℝ) ≤ 2*M)
    (hlo2 : M < q.2) (hhi2 : (q.2 : ℝ) ≤ 2*M) :
    |Real.log (pairRatio q : ℝ)| ≤ 1 := by
  have h1 : (0 : ℝ) < q.1 := by exact_mod_cast hq1
  have h2 : (0 : ℝ) < q.2 := by exact_mod_cast hq2
  have h12 : (q.1 : ℝ)/q.2 ≤ 2 := (div_le_iff₀ h2).mpr (by linarith)
  have h21 : (q.2 : ℝ)/q.1 ≤ 2 := (div_le_iff₀ h1).mpr (by linarith)
  have hl2 : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) using 1
    norm_num
  simp only [pairRatio, Rat.cast_div, Rat.cast_natCast]
  apply abs_le.mpr
  refine ⟨?_, (Real.log_le_log (div_pos h1 h2) h12).trans hl2⟩
  have hh := (Real.log_le_log (div_pos h2 h1) h21).trans hl2
  rw [Real.log_div h2.ne' h1.ne'] at hh
  rw [Real.log_div h1.ne' h2.ne']
  linarith

