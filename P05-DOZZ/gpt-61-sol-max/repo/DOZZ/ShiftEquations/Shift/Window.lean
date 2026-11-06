/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.TwoPoleWindow

/-!
# Admissible two-pole windows exist for every small `η`

At the two-pole charges `α₂ = 2/γ + η`, `α₃ = 2/γ - η` the reflection exponents are
`1 ∓ 2η/γ`, the one-insertion error ceilings are positive (the first uniformly in `η`), and the
two-insertion tail ceiling exceeds `1 + 2η/γ` by a margin of order one. Hence for every
`0 < η < η₀` some `δ > 0` makes `TwoPoleWindow γ η δ` hold.
-/

public section

namespace DOZZ.Proofs

variable {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)

include γ hγ hγ2 in
theorem four_div_sq_gt_one  : 1 < 4 / γ ^ 2 := by
  rw [one_lt_div (by positivity)]
  nlinarith

/-- The one-insertion error ceiling is positive below the moment ceiling. -/
theorem oneInsertionErrorCeiling_pos {γ α : ℝ} (hγ : 0 < γ)
    (hp0 : 0 ≤ reflectionExponent γ α) (hp : reflectionExponent γ α < 4 / γ ^ 2) :
    0 < oneInsertionErrorCeiling γ α := by
  unfold oneInsertionErrorCeiling oneInsertionMomentCeiling
  have h2γ : 0 < 2 / γ ^ 2 := by positivity
  have h1 : reflectionExponent γ α < min (reflectionExponent γ α + 2 / γ ^ 2) (4 / γ ^ 2) :=
    lt_min (by linarith) hp
  have h2 : 0 < 1 + min (reflectionExponent γ α + 2 / γ ^ 2) (4 / γ ^ 2) := by
    bound
  exact div_pos (by linarith) h2

/-- The one-insertion error ceiling is bounded below uniformly for exponents in `[0, 1]`. -/
theorem oneInsertionErrorCeiling_ge {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hp0 : 0 ≤ reflectionExponent γ α) (hp : reflectionExponent γ α ≤ 1) :
    min (2 / γ ^ 2) (4 / γ ^ 2 - 1) / (1 + 4 / γ ^ 2) ≤ oneInsertionErrorCeiling γ α := by
  have h4 := four_div_sq_gt_one hγ hγ2
  have h2 : 0 < 2 / γ ^ 2 := by positivity
  unfold oneInsertionErrorCeiling oneInsertionMomentCeiling
  set p := reflectionExponent γ α
  have hM : min (p + 2 / γ ^ 2) (4 / γ ^ 2) - p = min (2 / γ ^ 2) (4 / γ ^ 2 - p) := by
    rw [← min_sub_sub_right, add_sub_cancel_left]
  have hk : min (2 / γ ^ 2) (4 / γ ^ 2 - 1) ≤ min (p + 2 / γ ^ 2) (4 / γ ^ 2) - p := by
    rw [hM]
    exact min_le_min le_rfl (by linarith)
  have hk0 : 0 ≤ min (2 / γ ^ 2) (4 / γ ^ 2 - 1) := le_min h2.le (by linarith)
  have hMpos : 0 < min (p + 2 / γ ^ 2) (4 / γ ^ 2) := lt_min (by linarith) (by linarith)
  exact div_le_div₀ (hk0.trans hk) hk (by linarith)
    (by simp_all)

include γ hγ hγ2 in
/-- **Admissible two-pole windows exist for every small `η`.** -/
theorem exists_twoPoleWindow  :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ → ∃ δ : ℝ, TwoPoleWindow γ η δ := by
  have h4 := four_div_sq_gt_one hγ hγ2
  have hγh : γ / 2 < 2 / γ := by
    gcongr
  have hsq : (2 / γ - γ / 2) * (2 / γ) = 4 / γ ^ 2 - 1 := by
    field_simp
    ring
  set e₀ := min (2 / γ ^ 2) (4 / γ ^ 2 - 1) / (1 + 4 / γ ^ 2) with he₀

  have hmin0 : 0 < min (2 / γ - γ / 2) (min (γ / 4) (1 / (2 * γ))) :=
    lt_min (by linarith) (lt_min (by positivity) (by positivity))
  refine ⟨min (min (2 / γ - γ / 2) (min (γ / 4) (1 / (2 * γ)))) (γ * min e₀ (1 / 2) / 8),
    lt_min hmin0 (by positivity), ?_⟩
  intro η hη hη₀
  have hη1  :=
    lt_of_lt_of_le hη₀ (min_le_left _ _)
  have hη2  := lt_of_lt_of_le hη₀ (min_le_right _ _)
  have hηa  := lt_of_lt_of_le hη1 (min_le_left _ _)
  have hηb  :=
    lt_of_lt_of_le hη1 ((min_le_right _ _).trans (min_le_left _ _))
  have hηγ  := div_pos hη hγ
  have hp₂ : reflectionExponent γ (2 / γ + η) = 1 - 2 * η / γ := by
    unfold reflectionExponent Q
    field_simp
    ring
  have hp₃ : reflectionExponent γ (Q γ - η - γ / 2) = 1 + 2 * η / γ := by
    unfold reflectionExponent Q
    field_simp
    ring
  have hq₂ : (Q γ - (2 / γ + η)) / γ = 1 / 2 - η / γ := by
    unfold Q
    field_simp
    ring
  have hq₃ : (Q γ - (Q γ - η - γ / 2)) / γ = 1 / 2 + η / γ := by
    field_simp
    ring
  have h2ηγ : 2 * η / γ < 4 / γ ^ 2 - 1 := by
    rw [← hsq, show 2 * η / γ = η * (2 / γ) by ring]
    gcongr
  have h2ηγ' : 2 * η / γ < 1 / 2 := by
    rw [div_lt_iff₀ hγ]
    linarith
  have h2ηγ0 : 0 < 2 * η / γ := by positivity
  have hE₂ : e₀ ≤ oneInsertionErrorCeiling γ (2 / γ + η) :=
    oneInsertionErrorCeiling_ge hγ hγ2 (by rw [hp₂]; linarith) (by rw [hp₂]; linarith)
  have hE₃  :=
    oneInsertionErrorCeiling_pos hγ (by rw [hp₃]; positivity) (by rw [hp₃]; linarith)
  set E₂ := oneInsertionErrorCeiling γ (2 / γ + η) with hE₂def
  set E₃ := oneInsertionErrorCeiling γ (Q γ - η - γ / 2) with hE₃def
  have hmE : min e₀ (1 / 2) ≤ min E₂ (1 / 2) := min_le_min hE₂ le_rfl
  set sa := 4 / γ - γ - 2 * η with hsa
  set sb := γ - 4 * η with hsb
  set sc := γ * min E₂ (1 / 2) - 4 * η with hsc
  set sd := γ * min E₃ (1 / 2 - η / γ) with hsd
  have h4γ : 4 / γ = 2 * (2 / γ) := by ring
  have hsa0 : 0 < sa := by rw [hsa]; linarith
  have hsb0 : 0 < sb := by rw [hsb]; linarith
  have hsc0 : 0 < sc := by
    rw [hsc]
    have  := mul_le_mul_of_nonneg_left hmE hγ.le
    linarith
  have hhalf : 0 < 1 / 2 - η / γ := by
    rw [sub_pos, div_lt_iff₀ hγ]
    linarith
  have hsd0  := mul_pos hγ (lt_min hE₃ hhalf)
  set δ := min (min sa sb) (min sc sd) / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδa : δ < sa := by
    grind
  have hδb : δ < sb := by
    grind
  have hδc : δ < sc := by
    grind
  have hδd : δ < sd := by
    grind
  refine ⟨δ, hη, hη1, hδ0, by rw [hsa] at hδa; linarith, by rw [hsb] at hδb; linarith, ?_⟩
  unfold twoInsertionTailCeiling twoInsertionPointLoss
  rw [hp₂, hp₃, hq₂, hq₃, ← hE₂def, ← hE₃def]
  -- the first term
  have hX : (4 * η + δ) / γ < min E₂ (1 / 2) := by
    rw [div_lt_iff₀ hγ, mul_comm]
    rw [hsc] at hδc
    linarith
  have hY : δ / γ < min E₃ (1 / 2 - η / γ) := by
    rw [div_lt_iff₀ hγ, mul_comm]
    rw [hsd] at hδd
    linarith


  refine lt_min ?_ ?_
  all_goals grind

end DOZZ.Proofs

end
