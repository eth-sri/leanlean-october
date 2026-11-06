/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.LocalScale
public import Mathlib.Data.Finset.Max

/-!
# Fixed-shape covers for GMC annuli

An outer annulus of scale epsilon can be covered by finitely many balls of that same
scale. A fixed cover is chosen once on the radius-two reference disk. Moving the centers
through a compact set and a bounded radius interval preserves compactness. Positive
moments use a finite-sum estimate, without independence of the covered masses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- Every nonnegative power of a finite sum is bounded by the sum of the corresponding
powers times a finite cardinality factor. No probabilistic independence enters this estimate. -/
theorem ennreal_finset_sum_rpow_le_card_rpow_sum
    {ι : Type*} (S : Finset ι) (hne : S.Nonempty) (f : ι → ℝ≥0∞)
    (p : ℝ) (hp : 0 ≤ p) :
    (∑ i ∈ S, f i) ^ p ≤ (S.card : ℝ≥0∞) ^ p * ∑ i ∈ S, (f i) ^ p := by
  obtain ⟨i₀, hi₀, hmax⟩ := S.exists_max_image f hne
  have hsum : (∑ i ∈ S, f i) ≤ S.card * f i₀ := by
    calc
      _ ≤ ∑ _i ∈ S, f i₀ := Finset.sum_le_sum (fun i hi => hmax i hi)
      _ = _ := by simp
  have h := ENNReal.rpow_le_rpow hsum hp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp] at h
  exact h.trans (mul_le_mul' le_rfl (Finset.single_le_sum (f := fun i => (f i) ^ p) (fun _ _ => zero_le) hi₀))

end DOZZ.Proofs
