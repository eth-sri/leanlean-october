/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Statements.Defs.ExtendedSeiberg3
public import DOZZ.Upsilon.ZeroStructure
/-! # The extended charge domain and the finite DOZZ denominator -/
@[expose] public section
namespace DOZZ.Proofs
section
variable {γ a b c : ℝ}
section
variable (hγ : 0 < γ) (h : ExtendedSeiberg3 γ a b c)
include hγ h
/-- The extended moment bounds imply the three strict triangle inequalities. -/
theorem roots_extended_triangle : a < b + c ∧ b < a + c ∧ c < a + b := by
  have h1 := lt_of_lt_of_le h.2.2.2 ((min_le_right ..).trans (min_le_left ..))
  have h2 := lt_of_lt_of_le h.2.2.2 ((min_le_right ..).trans ((min_le_right ..).trans (min_le_left ..)))
  have h3 := lt_of_lt_of_le h.2.2.2 ((min_le_right ..).trans ((min_le_right ..).trans (min_le_right ..)))
  have he : -sExp γ a b c = (2 * Q γ - (a + b + c)) / γ := by unfold sExp; ring
  rw [he] at h1 h2 h3
  have e (x : ℝ) : 2 / γ * (Q γ - x) = (2 * (Q γ - x)) / γ := by ring
  rw [e] at h1 h2 h3
  have h1' := (div_lt_div_iff_of_pos_right hγ).mp h1
  have h2' := (div_lt_div_iff_of_pos_right hγ).mp h2
  have h3' := (div_lt_div_iff_of_pos_right hγ).mp h3
  grind
/-- All three charges in the extended three-point domain are positive. -/
theorem roots_extended_positive : 0 < a ∧ 0 < b ∧ 0 < c := by
  obtain ⟨h1, h2, h3⟩ := roots_extended_triangle hγ h
  grind

end
/-- The zero-mode Upsilon factor is nonzero at every pole-free extended triple. -/
theorem roots_upsilon_zeroMode_ne_zero (hγ : 0 < γ) (hγ2 : γ < 2)
    {U : ℂ → ℂ} (hU : IsUpsilon γ U) (h : ExtendedSeiberg3 γ a b c)
    (hs : ∀ n : ℕ, sExp γ a b c ≠ -(n : ℝ)) :
    U (((a + b + c - 2 * Q γ) / 2 : ℝ) : ℂ) ≠ 0 := by
  let w := (a + b + c - 2 * Q γ) / 2
  have hwlo : -(2 / γ) < w := by
    have hb := lt_of_lt_of_le h.2.2.2 (min_le_left ..)
    have he : -sExp γ a b c = (2 * Q γ - (a + b + c)) / γ := by unfold sExp; ring
    rw [he] at hb
    have hb' := (div_lt_iff₀ hγ).mp hb
    have he' : (4 / γ ^ 2) * γ = 4 / γ := by field_simp
    grind
  have hwQ : w < Q γ := by
    have hQ : 0 < Q γ := by unfold Q; positivity
    dsimp only [w]
    linarith only [h.1, h.2.1, h.2.2.1, hQ]
  intro hz
  obtain ⟨m, n, hn | hn⟩ := (IsUpsilon.eq_zero_iff hγ hγ2 hU w).mp hz
  · have he : w = -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ)) :=
      Complex.ofReal_inj.mp (by simp_all)
    have hn0 : n = 0 := by
      by_contra hne
      have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
      have hm0 : 0 ≤ (m : ℝ) * (γ / 2) := mul_nonneg (Nat.cast_nonneg _) (by positivity)
      have hmul := mul_le_mul_of_nonneg_right hn1 (show 0 ≤ 2 / γ by positivity)
      linarith only [hwlo, he, hm0, hmul]
    subst n
    apply hs m
    apply (div_eq_iff hγ.ne').mpr
    grind
  · have he := Complex.ofReal_inj.mp hn
    have hm0 : 0 ≤ m * (γ / 2) := by positivity
    have hn0 : 0 ≤ n * (2 / γ) := by positivity
    linarith

end
end DOZZ.Proofs
