module

public import NearlyMinimax.SpatialSubsetIntegral
public import Mathlib.Data.Finset.Powerset


@[expose] public section

/-! Actual square-integrability and finite subset-sum energy bounds on Q^k. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

theorem finite_pi_reindex_integrable {I J E : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace E] {μ : Measure E} [SigmaFinite μ] (e : I ≃ J) {f : (J → E) → ℝ}
    (hf : Integrable f (Measure.pi (fun _ => μ))) :
    Integrable (fun U => f (fun j => U (e.symm j))) (Measure.pi (fun _ => μ)) := by
  have hp := measurePreserving_piCongrLeft (fun _ => μ) e
  have he (U : I → E) : (Equiv.piCongrLeft (fun _ => E) e) U =
      fun j => U (e.symm j) := by
    funext j
    simp [Equiv.piCongrLeft_apply_eq_cast, cast_eq]
  have h := hp.integrable_comp_of_integrable hf
  simpa only [Function.comp_def, MeasurableEquiv.coe_piCongrLeft, he] using h

theorem spatial_subset_square_integrable_enumerated {d k : ℕ} {s : Finset (Fin k)}
    {f : (Fin s.card → Covariate d) → ℝ}
    (hf : Integrable (fun V => f V ^ 2) (fullSpatialPatchDesign d s.card)) :
    Integrable (fun U => f (spatialSubsetConfiguration s U) ^ 2)
      (fullSpatialPatchDesign d k) := by
  let e  := (Fintype.equivFin s).trans (finCongr (Fintype.card_coe s))
  have hi := finite_pi_reindex_integrable e hf
  have h := finite_pi_subset_integrable hi
  exact h

/-- Finite sums preserve L², expressed here using the squared real integrands. -/
 theorem finite_sum_square_integrable {I X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset I) (f : I → X → ℝ)
    (hm : ∀ i ∈ s, Measurable (f i)) (hi : ∀ i ∈ s, Integrable (fun x => f i x ^ 2) μ) :
    Integrable (fun x => (∑ i ∈ s, f i x)^2) μ :=
  (memLp_finsetSum s (fun i h => (memLp_two_iff_integrable_sq (hm i h).aestronglyMeasurable).2 (hi i h))).integrable_sq

theorem finite_sum_square_integral_le {I X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset I) (f : I → X → ℝ) (K : ℝ)
    (hm : ∀ i ∈ s, Measurable (f i))
    (hi : ∀ i ∈ s, Integrable (fun x => f i x ^ 2) μ)
    (hK : ∀ i ∈ s, (∫ x, f i x ^ 2 ∂μ) ≤ K) :
    (∫ x, (∑ i ∈ s, f i x) ^ 2 ∂μ) ≤ s.card ^ 2 * K := by
  classical
  have hb (x : X) : (∑ i ∈ s, f i x) ^ 2 ≤ s.card * ∑ i ∈ s, f i x ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => 1) (fun i => f i x)
  have hu : Integrable (fun x => s.card * ∑ i ∈ s, f i x ^ 2) μ :=
    (integrable_finsetSum s hi).const_mul _
  have h := integral_mono (finite_sum_square_integrable μ s f hm hi) hu hb
  rw [integral_const_mul, integral_finsetSum _ hi] at h
  apply h.trans
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hK) (Nat.cast_nonneg s.card)
  simpa only [Finset.sum_const, nsmul_eq_mul, sq, ← mul_assoc] using hh

/-- This is the exact binomial and unused-coordinate factor in the paper's
subset lift; each selected kernel is integrated over its genuine Q^r law. -/
theorem spatial_subset_sum_square_integral_le {d k r : ℕ}
    {f : (s : Finset (Fin k)) → (Fin s.card → Covariate d) → ℝ} (K : ℝ)
    (hm : ∀ s ∈ Finset.univ.powersetCard r, Measurable (f s))
    (hi : ∀ s ∈ Finset.univ.powersetCard r,
      Integrable (fun V => f s V ^ 2) (fullSpatialPatchDesign d s.card))
    (hK : ∀ s ∈ Finset.univ.powersetCard r,
      (∫ V, f s V ^ 2 ∂fullSpatialPatchDesign d s.card) ≤ K) :
    (∫ U, (∑ s ∈ Finset.univ.powersetCard r,
      f s (spatialSubsetConfiguration s U)) ^ 2 ∂fullSpatialPatchDesign d k) ≤
      (k.choose r) ^ 2 * 2 ^ (d * (k - r)) * K := by
  classical
  have h := finite_sum_square_integral_le (fullSpatialPatchDesign d k)
    (Finset.univ.powersetCard r)
    (fun s U => f s (spatialSubsetConfiguration s U)) (2 ^ (d * (k - r)) * K)
    (fun s hs => (hm s hs).comp (spatialSubsetConfiguration_measurable s))
    (fun s hs => spatial_subset_square_integrable_enumerated (hi s hs))
    (fun s hs => by
      rw [spatial_subset_square_integral_enumerated]
      have hc := (Finset.mem_powersetCard.mp hs).2
      bound)
  simpa only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, ← mul_assoc] using h

end NearlyMinimax
