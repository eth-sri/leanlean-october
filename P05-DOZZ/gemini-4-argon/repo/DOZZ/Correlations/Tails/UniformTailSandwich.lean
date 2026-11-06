/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.PolynomialShiftParameters

/-! Uniform tail errors from the two localization comparisons and their moment bounds. -/

@[expose] public section
open Set

namespace DOZZ.Proofs

theorem uniform_tail_sandwich_bound
    (T L : ℝ → ℝ) (p P η a r R c cmax E K₁ K₂ : ℝ)
    (hp : 0 ≤ p) (hpP : p ≤ P) (hη : 0 < η) (ha : η ≤ a)
    (hrR : r ≤ R) (hslack : p+η ≤ (1-a)*r)
    (hc : 0 ≤ c) (hcc : c ≤ cmax) (hE : 0 ≤ E) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hT : ∀ x : ℝ, 1 ≤ x → 0 ≤ T x ∧ T x ≤ 1)
    (hL : ∀ x : ℝ, 1 ≤ x → |L x-c*x^(-p)| ≤ E*x^(-p-η))
    (hSand : ∀ x : ℝ, 2 ≤ x →
      let h := x^(1-a)/4
      L (x+h)-K₂*h^(-r) ≤ T x ∧ T x ≤ L (x-2*h)+(K₁+K₂)*h^(-r))
    x (hx : 1 ≤ x) :
    |T x-c*x^(-p)| ≤
      ((1+cmax)*2^(P+η)+E*2^(P+η)+cmax*P*2^(P+1)+(K₁+K₂)*4^R)*x^(-p-η) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have := hp.trans hpP
  have hcm := hc.trans hcc
  let Csmall := (1+cmax)*2^(P+η)
  let Cshift := E*2^(P+η)+cmax*P*2^(P+1)
  let Cerr := (K₁+K₂)*4^R
  suffices H : |T x-c*x^(-p)| ≤ (Csmall+Cshift+Cerr)*x^(-p-η) by
    simpa only [Csmall,Cshift,Cerr,add_assoc] using H
  by_cases hx2 : 2 ≤ x
  · let h := x^(1-a)/4
    have hs := hSand x hx2
    have hrate := polynomial_shift_moment_rate x a r R p η hx hrR hslack
    have hshift s (hs : |s| ≤ 2) :
        |L (x+s*h)-c*x^(-p)| ≤ Cshift*x^(-p-η) := by
      let y := (x+s*h)/x
      have hy := polynomial_shift_relative x a s hx (hη.le.trans ha) hs
      have hb := uniform_power_tail_shift L x y p P η a c cmax E hx hy.1
        hp hpP hη ha hc hcc hE hy.2 (hL (x*y) (by nlinarith only [(mul_le_mul_of_nonneg_left hy.1.1 hx0.le),hx2]))
      rw [(show x*y = x+s*h by dsimp [y]; field_simp)] at hb
      exact hb
    have hupper := (abs_le.mp (hshift (-2) (by norm_num))).2
    have hlower := (abs_le.mp (hshift 1 (by norm_num))).1
    rw [one_mul] at hlower
    have herr₁ : K₂*h^(-r) ≤ Cerr*x^(-p-η) := by
      calc _ ≤ (K₁+K₂)*h^(-r) := mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_left hK₁) (Real.rpow_nonneg (by dsimp [h]; positivity) _)
        _ ≤ (K₁+K₂)*(4^R*x^(-p-η)) := mul_le_mul_of_nonneg_left hrate (add_nonneg hK₁ hK₂)
        _ = _ := by dsimp [Cerr]; ring
    apply abs_le.mpr
    constructor <;> rw [add_mul,add_mul] <;> dsimp only at hs <;> linarith only [hs.1,hs.2,hlower,(show L (x-2*h)-c*x^(-p) ≤ Cshift*x^(-p-η) by simpa only [neg_mul,sub_eq_add_neg] using hupper),herr₁,(show (K₁+K₂)*h^(-r) ≤ Cerr*x^(-p-η) by simpa only [Cerr,mul_assoc] using mul_le_mul_of_nonneg_left hrate (add_nonneg hK₁ hK₂)),(mul_nonneg (by dsimp [Csmall]; positivity) (Real.rpow_nonneg hx0.le _) : 0 ≤ Csmall*x^(-p-η))]
  · have hx2' : x ≤ 2 := le_of_not_ge hx2
    have hrough : |T x-c*x^(-p)| ≤ 1+cmax := by
      apply abs_le.mpr
      obtain ⟨ht0,ht1⟩ := hT x hx
      constructor <;> linarith only [ht0,ht1,((mul_le_of_le_one_right hc (Real.rpow_le_one_of_one_le_of_nonpos hx (neg_nonpos.mpr hp))).trans hcc),(mul_nonneg hc (Real.rpow_nonneg hx0.le _) : 0 ≤ c*x^(-p)),hcm]
    have hpow : (2 : ℝ)^(-(P+η)) ≤ x^(-p-η) := by
      calc (2 : ℝ)^(-(P+η)) ≤ 2^(-p-η) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hpP])
        _ ≤ x^(-p-η) := Real.rpow_le_rpow_of_nonpos hx0 hx2' (by linarith only [hp,hη])
    have hmain : 1+cmax ≤ Csmall*x^(-p-η) := by
      have h := mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (show 0 ≤ 1+cmax by linarith only [hcm]) (Real.rpow_nonneg zero_le_two (P+η)))
      rw [mul_assoc,(show (2 : ℝ)^(P+η)*2^(-(P+η)) = 1 by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),add_neg_cancel,Real.rpow_zero]),mul_one] at h
      exact h
    exact hrough.trans (hmain.trans (mul_le_mul_of_nonneg_right
      (by linarith only [(show 0 ≤ Cshift by dsimp [Cshift]; positivity),(show 0 ≤ Cerr by dsimp [Cerr]; positivity)] : Csmall ≤ Csmall+Cshift+Cerr) (Real.rpow_nonneg hx0.le _)))


end DOZZ.Proofs
