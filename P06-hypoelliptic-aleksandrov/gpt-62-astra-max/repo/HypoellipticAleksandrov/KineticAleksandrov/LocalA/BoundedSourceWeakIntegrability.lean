module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeakWeights

/-! # Integrability of compact weak-test weights -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal
variable {d : ℕ}

/-- A measurable function bounded on a compact test's support is integrable with that weight. -/
theorem integrable_compact_weight_bounded
    (Λ : ℝ × EvolutionAmbientState d → ℝ) (hΛ : Continuous Λ)
    (hc : HasCompactSupport Λ) (f : ℝ × EvolutionAmbientState d → ℝ)
    (hf : Measurable f) (C : ℝ) (_hC : 0 ≤ C)
    (hb : ∀ q, Λ q ≠ 0 → |f q| ≤ C) : Integrable (fun q => Λ q * f q) := by
  have hi : Integrable (fun q => C * ‖Λ q‖) :=
    (hΛ.integrable_of_hasCompactSupport hc).norm.const_mul C
  apply hi.mono' (hΛ.measurable.mul hf).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro q
  change ‖Λ q * f q‖ ≤ C * ‖Λ q‖
  rw [norm_mul, Real.norm_eq_abs (f q)]
  by_cases hq : Λ q = 0
  · simp only [hq, norm_zero, zero_mul, mul_zero, le_refl]
  · exact (mul_le_mul_of_nonneg_left (hb q hq) (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- Positive-part weights remain continuous with compact support. -/
theorem positive_weight_compact (Λ : ℝ × EvolutionAmbientState d → ℝ)
    (hΛ : Continuous Λ) (hc : HasCompactSupport Λ) :
    Continuous (fun q => max (Λ q) 0) ∧ HasCompactSupport (fun q => max (Λ q) 0) :=
  ⟨hΛ.max continuous_const, hc.comp_left (g := fun r : ℝ => max r 0) (max_self 0)⟩

/-- Positive and negative compact weights recover the signed weighted integral. -/
theorem integral_positive_negative_weight_sub
    (Λ : ℝ × EvolutionAmbientState d → ℝ) (hΛ : Continuous Λ)
    (hc : HasCompactSupport Λ) (f : ℝ × EvolutionAmbientState d → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ q, Λ q ≠ 0 → |f q| ≤ C) :
    (∫ q, max (Λ q) 0 * f q) - (∫ q, max (-Λ q) 0 * f q) = ∫ q, Λ q * f q := by
  obtain ⟨hpcont, hpcomp⟩ := positive_weight_compact Λ hΛ hc
  obtain ⟨hncont, hncomp⟩ := positive_weight_compact (fun q => -Λ q) hΛ.neg hc.neg
  have hp : Integrable (fun q => max (Λ q) 0 * f q) :=
    integrable_compact_weight_bounded _ hpcont hpcomp f hf C hC (fun q hq => by
      apply hb q
      intro hz
      exact hq (by simp only [hz, max_self]))
  have hn : Integrable (fun q => max (-Λ q) 0 * f q) :=
    integrable_compact_weight_bounded _ hncont hncomp f hf C hC (fun q hq => by
      apply hb q
      intro hz
      exact hq (by simp only [hz, neg_zero, max_self]))
  rw [← integral_sub hp hn]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  change max (Λ q) 0 * f q - max (-Λ q) 0 * f q = Λ q * f q
  rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
