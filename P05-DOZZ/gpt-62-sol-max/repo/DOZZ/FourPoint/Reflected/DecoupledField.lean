/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.GluedFieldGaussian

/-! # The actual independent-copy field on the two fusion regions -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal NNReal

namespace DOZZ.Proofs

section
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω) (Φ : Ω → S → ℝ)
  (hΦ : IsCenteredGaussianField P Φ) (A : Set S)
include Ω S hΦ

/-- The independent-copy Wick mass is the sum of the two independent regional masses. -/
theorem independent_piece_field_mass (hA : MeasurableSet A)
    (ν : Measure S) (h : S → ℝ≥0) (γ : ℝ) (ω : Ω × Ω) :
    fieldChaosMass (P.prod P) (independent_piece_field Φ A) ν h γ ω =
      fieldChaosMass P Φ (ν.restrict A) h γ ω.1 +
        fieldChaosMass P Φ (ν.restrict Aᶜ) h γ ω.2 := by
  unfold fieldChaosMass
  refine (lintegral_add_compl _ hA).symm.trans ?_
  congr 1
  · apply setLIntegral_congr_fun hA
    intro x hx
    dsimp only
    rw [independent_piece_field_variance P Φ hΦ A, independent_piece_field, Set.indicator_of_mem hx,
      Set.indicator_of_notMem (show x ∉ Aᶜ from fun hn => hn hx), add_zero]
  · apply setLIntegral_congr_fun hA.compl
    intro x hx
    dsimp only
    rw [independent_piece_field_variance P Φ hΦ A, independent_piece_field, Set.indicator_of_notMem (show x ∉ A from hx),
      Set.indicator_of_mem hx, zero_add]

end

end DOZZ.Proofs
