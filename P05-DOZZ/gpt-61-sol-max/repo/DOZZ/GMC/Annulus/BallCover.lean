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

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- Every nonnegative power of a finite sum is bounded by the sum of the corresponding
powers times a finite cardinality factor. No probabilistic independence enters this estimate. -/
theorem ennreal_finset_sum_rpow_le_card_rpow_sum
    {ι : Type*} (S : Finset ι) (hne : S.Nonempty) (f : ι → ℝ≥0∞)
    (p : ℝ) (hp : 0 ≤ p) :
    (∑ i ∈ S, f i) ^ p ≤ (S.card : ℝ≥0∞) ^ p * ∑ i ∈ S, (f i) ^ p := by
  classical
  obtain ⟨i₀, hi₀, hmax⟩ := S.exists_max_image f hne
  have hsum : (∑ i ∈ S, f i) ≤ (S.card : ℝ≥0∞) * f i₀ := by
    calc
      _ ≤ ∑ _i ∈ S, f i₀ := Finset.sum_le_sum (fun i hi => hmax i hi)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have h := ENNReal.rpow_le_rpow hsum hp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp] at h
  exact h.trans (mul_le_mul' le_rfl (Finset.single_le_sum (f := fun i => (f i) ^ p) (fun _ _ => zero_le) hi₀))

/-- The random full measure supplied by any `DOZZ.IsGMCOf` version is AE measurable. -/
theorem gmc_measure_aemeasurable_of_isGMCOf
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    AEMeasurable M P := by
  obtain ⟨N, hN, _, he⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  exact hN.aemeasurable.congr (he.mono (fun _ h => h.symm))

end DOZZ.Proofs
