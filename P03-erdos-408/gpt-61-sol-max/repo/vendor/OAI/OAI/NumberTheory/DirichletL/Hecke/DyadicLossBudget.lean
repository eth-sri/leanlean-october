module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Hecke.DyadicCentralBudget

@[expose] public section

namespace OAI


namespace SevenEighths.HeckeDyadic

theorem central_squared_exponents (R a e κ η ε r m : ℝ)
    (hR : 0≤R) (he : 0≤e) (hκ : 0≤κ) (_hη : 0≤η)
    (hr : r≤R) (hm : 0≤m)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε) :
    2*((a-1/2+6*e)*r+2*κ+η)≤(2*a-1)*r+ε ∧
    2*((a-1/2)*(1-m)+6*e*(2-m)+4*κ+η)≤(2*a-1)*(1-m)+ε := by
  have hEr : e*r≤e*R := mul_le_mul_of_nonneg_left hr he
  have hEm : 0≤e*m := mul_nonneg he hm
  have hER : 0≤e*R := mul_nonneg he hR
  constructor <;> nlinarith

theorem indexed_height_bound  i I  (hi : i≤I)  T  (hT : 0≤T) :
    (3+(3*i+2 : ℕ)*T)^4≤(3*(I : ℝ)+5)^4*(1+T)^4 := by
  have hi' : (i : ℝ)≤I := by exact_mod_cast hi
  have hlin : 3+(3*i+2 : ℕ)*T≤(3*(I : ℝ)+5)*(1+T) := by
    push_cast
    nlinarith
  calc
    _ ≤ ((3*(I : ℝ)+5)*(1+T))^4 := pow_le_pow_left₀ (by positivity) hlin 4
    _ = _ := mul_pow _ _ _

theorem min_plain_bound (X C U δ m ε : ℝ)
    (h₁ : X≤C*U^(δ*m+ε)) (h₂ : X≤C*U^(δ*(1-m)+ε)) :
    X≤C*U^(δ*min m (1-m)+ε) := by
  grind

theorem squared_bound_of_central_and_error (z : ℂ) (U C E p b ε : ℝ)
    (hU : 1≤U) (hC : 0≤C) (hE : 0≤E) (hε : 0≤ε)
    (hb : 2*b≤ε)
    (hz : ‖z‖≤C*U^(p+b)+E*U^p) :
    ‖z‖^2≤(C+E)^2*U^(2*p+ε) := by
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hp₁ : U^(p+b)≤U^(p+ε/2) :=
    Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hp₂ : U^p≤U^(p+ε/2) :=
    Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hn : ‖z‖≤(C+E)*U^(p+ε/2) := by
    calc
      _ ≤ C*U^(p+b)+E*U^p := hz
      _ ≤ C*U^(p+ε/2)+E*U^(p+ε/2) := add_le_add
        (mul_le_mul_of_nonneg_left hp₁ hC) (mul_le_mul_of_nonneg_left hp₂ hE)
      _ = _ := by ring
  calc
    _ ≤ ((C+E)*U^(p+ε/2))^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = _ := by
      have hp : (U^(p+ε/2))^2=U^(2*p+ε) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le]
        congr 1
        norm_num
        ring
      rw [mul_pow,hp]

end SevenEighths.HeckeDyadic



end OAI
