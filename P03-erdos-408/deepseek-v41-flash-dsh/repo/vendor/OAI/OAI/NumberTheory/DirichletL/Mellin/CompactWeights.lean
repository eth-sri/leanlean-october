module

public import OAI.NumberTheory.DirichletL.Mellin.CompactScale

@[expose] public section

namespace OAI

noncomputable section












































namespace CompactScaleBridge

section



end



end CompactScaleBridge




namespace ConcreteCompactWeight

noncomputable def bumpData : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

noncomputable def bump (y : ℝ) : ℝ := bumpData y

noncomputable def positiveExtension (y : ℝ) : ℝ :=
  1 + (y - 1) * Real.smoothTransition (2 * y - 1)

theorem positiveExtension_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) positiveExtension := by
  unfold positiveExtension
  have ht : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => 2 * y - 1) := by fun_prop
  exact contDiff_const.add
    ((contDiff_id.sub contDiff_const).mul
      ((Real.smoothTransition.contDiff (n := ⊤)).comp ht))

theorem positiveExtension_pos (y : ℝ) : 0 < positiveExtension y := by
  unfold positiveExtension
  by_cases hhalf : y ≤ 1 / 2
  · have ht : 2 * y - 1 ≤ 0 := by linarith
    rw [Real.smoothTransition.zero_of_nonpos ht]
    norm_num
  · by_cases hone : 1 ≤ y
    · have ht : 1 ≤ 2 * y - 1 := by linarith
      rw [Real.smoothTransition.one_of_one_le ht]
      linarith
    · have hle := Real.smoothTransition.le_one (2 * y - 1)
      have hnonneg := Real.smoothTransition.nonneg (2 * y - 1)
      have hprod : (1 - y) * Real.smoothTransition (2 * y - 1) ≤ 1 - y := by
        exact (mul_le_mul_of_nonneg_left hle (by linarith)).trans_eq (mul_one _)
      nlinarith

theorem positiveExtension_eq (y : ℝ) (hy : 1 ≤ y) :
    positiveExtension y = y := by
  unfold positiveExtension
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * y - 1)]
  ring

noncomputable def weight (ρ : ℂ) (y : ℝ) : ℂ :=
  (bump y : ℂ) * Complex.exp ((Real.log (positiveExtension y) : ℂ) * (-ρ))

end ConcreteCompactWeight

namespace CompactScaleBridge

section



end

end CompactScaleBridge

namespace ActualEisensteinCubic



end ActualEisensteinCubic

namespace TwoPassProfiles

end TwoPassProfiles

end

end OAI
