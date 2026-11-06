module

public import OAI.NumberTheory.DirichletL.Moments.Smooth

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.CenteredMomentTail
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCommonSupport CenteredMomentCorrelation
open CenteredMomentSupportedCorrelation

theorem fullModulusCorrelation_norm_le (u v : ActualEisensteinCubic.O) (_hu : u ≠ 0) (_hv : v ≠ 0)
    [Fintype (Residue u)] [Fintype (Residue v)]
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ) (j : ActualEisensteinCubic.O) :
    ‖fullModulusCorrelation u v χu χv j‖ ≤
      (Ideal.absNorm (Ideal.span {u}) : ℝ) * (Ideal.absNorm (Ideal.span {v}) : ℝ) := by
  unfold fullModulusCorrelation fullCorrelation
  calc
    _ ≤ ∑ x : Residue u, ‖∑ y : Residue v,
      if scaledResidue u v (u * v) rfl x - scaledResidue v u (u * v) (by ring) y =
        Ideal.Quotient.mk _ j then χu x * star (χv y) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue u, ∑ _y : Residue v, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro y hy
      split_ifs
      · rw [norm_mul, norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg _)
          (QuadraticInitialBound.norm_finite_character_le_one χu x)).trans
          (QuadraticInitialBound.norm_finite_character_le_one χv y)
      simp
    _ = _ := by
      simp [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem actualCorrelation_norm_le (u v : ActualEisensteinCubic.O)
    (hu : CanonicalQuadraticSieve.Supported (Ideal.span {u}))
    (hv : CanonicalQuadraticSieve.Supported (Ideal.span {v})) (j : ActualEisensteinCubic.O) :
    ‖actualCorrelation u v hu hv j‖ ≤
      (Ideal.absNorm (Ideal.span {u}) : ℝ) * (Ideal.absNorm (Ideal.span {v}) : ℝ) := by
  let := finite_quotient_span (supported_element_ne_zero u hu)
  let := finite_quotient_span (supported_element_ne_zero v hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  unfold actualCorrelation
  exact fullModulusCorrelation_norm_le u v (supported_element_ne_zero u hu)
    (supported_element_ne_zero v hv) _ _ j

theorem weighted_set_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (D : Set ActualEisensteinCubic.O) (K T B : ℝ), 0 < K → 0 ≤ T → 0 ≤ B →
      (∀ h ∈ D, T ≤ K * ‖eisEmbedding h‖ ^ 2) →
      ∀ c δ : ActualEisensteinCubic.O → ℂ, (∀ h ∈ D, ‖c h‖ ≤ B) → (∀ h ∈ D, ‖δ h‖ ≤ 1) →
      ‖∑' h : D, δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        B * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W D K T B hK hT hB hD c δ hc hδ
  let L := {h : ActualEisensteinCubic.O | T ≤ K * ‖eisEmbedding h‖ ^ 2}
  let f : D → L := fun h => ⟨h.val, hD h.val h.property⟩
  have hfi : Function.Injective f := by
    intro x y h
    exact by grind
  have hs := paperRadialFourier_lattice_summable_norm W K hK
  have hp (h : D) : ‖δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
      B * ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_of_le_one_left (norm_nonneg _) (by grind)).trans (by grind))
      (norm_nonneg _)
  have hsum : Summable (fun h : D =>
      ‖δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (by grind) hp ((hs.subtype D).mul_left B)
  calc
    _ ≤ ∑' h : D, ‖δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
      norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' h : D, B * ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
      hsum.tsum_le_tsum hp ((hs.subtype D).mul_left B)
    _ = B * ∑' h : D, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ := tsum_mul_left
    _ ≤ B * ∑' h : L, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
      mul_le_mul_of_nonneg_left ((hs.subtype D).tsum_le_tsum_of_inj f hfi
        (by simp) (by grind) (hs.subtype L)) hB
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left (ht W K T hK hT) hB using 1
      · rfl
      ring

theorem uniform_sector_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (D : Set ActualEisensteinCubic.O) (K₀ T B : ℝ), 0 < K₀ → 0 ≤ T → 0 ≤ B →
      (∀ h ∈ D, T ≤ K₀ * ‖eisEmbedding h‖ ^ 2) →
      ∀ K : ℝ, K₀ ≤ K →
      ∀ c δ : ActualEisensteinCubic.O → ℂ, (∀ h ∈ D, ‖c h‖ ≤ B) → (∀ h ∈ D, ‖δ h‖ ≤ 1) →
      ‖∑' h : D, δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        B * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K₀) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := weighted_set_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W D K₀ T B hK₀ hT hB hD K hK c δ hc hδ
  have hD' (h : ActualEisensteinCubic.O) (hh : h ∈ D) : T ≤ K * ‖eisEmbedding h‖ ^ 2 :=
    (hD h hh).trans (mul_le_mul_of_nonneg_right hK (sq_nonneg _))
  apply (ht W D K T B (by linarith) hT hB hD' c δ hc hδ).trans
  apply div_le_div_of_nonneg_left (by positivity)
    (by positivity)
  gcongr

end SevenEighths.CenteredMomentTail
end

end OAI
