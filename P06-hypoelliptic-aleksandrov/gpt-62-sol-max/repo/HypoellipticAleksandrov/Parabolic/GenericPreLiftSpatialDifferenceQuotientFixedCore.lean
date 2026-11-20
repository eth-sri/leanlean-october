module

public import HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientFixedDirection

/-!
# Fixed-cylinder generic spatial difference-quotient estimate

This module aggregates the one-direction estimate over all spatial directions.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped Convex ENNReal MatrixOrder

/-- Fixed-cylinder spatial difference-quotient control for the gradient in a
tested divergence-form equation. -/
theorem exists_gradient_spatialDifferenceQuotient_estimate_of_testedEquation
    (d : ℕ) (s₀ t₁ t₂ s₁ : ℝ)
    (hs₀t₁ : s₀ < t₁) (ht₁t₂ : t₁ < t₂) (ht₂s₁ : t₂ < s₁)
    (O₀ O₁ : Set (PDE.Vec d))
    (hO₀ : IsOpen O₀) (hO₁ : IsOpen O₁)
    (hO₁compact : IsCompact (closure O₁))
    (hO₁O₀ : closure O₁ ⊆ O₀)
    (lam Lam Ma : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hMa : 0 ≤ Ma) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ (A : TimeVelocity d → PDE.Mat d) (q : TimeVelocity d → ℝ)
        (G : Fin d → TimeVelocity d → ℝ) (R : TimeVelocity d → ℝ),
        DivergenceFormL2Data (Ioo s₀ s₁ ×ˢ O₀) lam Lam Ma A q G R →
        ∀ h : ℝ, 0 < h → h < δ →
          (∀ j k, ParabolicMemLpOn (Set.Ioo t₁ t₂ ×ˢ O₁) 2
            (spatialDifferenceQuotient k h (G j))) ∧
          (∑ j, ∑ k, (ENNReal.toReal (eLpNorm
            (spatialDifferenceQuotient k h (G j)) 2
            (timeVelocityVolumeOn (Set.Ioo t₁ t₂ ×ˢ O₁)))) ^ 2) ≤
            C * ((ENNReal.toReal (eLpNorm q 2
              (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O₀)))) ^ 2 +
              (∑ j, (ENNReal.toReal (eLpNorm (G j) 2
                (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O₀)))) ^ 2) +
              (ENNReal.toReal (eLpNorm R 2
                (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O₀)))) ^ 2) := by
  classical
  obtain ⟨C, δ, hC, hδ, hfixed⟩ :=
    exists_fixedDirection_gradient_spatialDifferenceQuotient_estimate_of_testedEquation
      d s₀ t₁ t₂ s₁ hs₀t₁ ht₁t₂ ht₂s₁ O₀ O₁ hO₀ hO₁
      hO₁compact hO₁O₀ lam Lam Ma hlam hlamLam hMa
  refine ⟨(d : ℝ) * C, δ, mul_nonneg (Nat.cast_nonneg d) hC, hδ, ?_⟩
  intro A q G R hdata h hh hhd
  have hk (k : Fin d) := hfixed A q G R hdata k h hh hhd
  constructor
  · exact fun j k ↦ (hk k).1 j
  · have hsum := Finset.sum_le_sum fun k (_hk : k ∈ Finset.univ) ↦ (hk k).2
    rw [Finset.sum_comm]
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_id, mul_assoc] using hsum

end HypoellipticAleksandrov.Parabolic
