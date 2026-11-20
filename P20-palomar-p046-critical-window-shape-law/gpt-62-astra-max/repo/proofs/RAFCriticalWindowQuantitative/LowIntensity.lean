module

public import proofs.RAFCriticalWindowQuantitative.SmallOpenness
public import proofs.RAFReactionQuotient.Resolution

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient unitInterval

theorem criticalOpenness_pos_le (lam : ℝ) (hlam : 0 < lam) :
    0 < (criticalOpenness lam hlam : ℝ) ∧ (criticalOpenness lam hlam : ℝ) ≤ lam := by
  change 0 < 1-Real.exp (-lam) ∧ 1-Real.exp (-lam) ≤ lam
  constructor
  · have h := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hlam)
    linarith
  · linarith [Real.add_one_le_exp (-lam)]

theorem power_bound_intensity_flatness (S : I → ℝ) (C : ℕ → ℕ)
    (hbound : ∀ a r, S a ≤ (C r : ℝ)*(a : ℝ)^r) (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ →
      S (criticalOpenness lam hlam) < ε*lam^d := by
  obtain ⟨δ,hδ,h⟩ := power_bound_implies_flatness S C hbound d ε hε
  refine ⟨δ,hδ,?_⟩
  intro lam hlam hlamδ
  have ha := criticalOpenness_pos_le lam hlam
  exact (h _ ha.1 (ha.2.trans_lt hlamδ)).trans_le
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.1.le ha.2 d) hε.le)

theorem split_low_intensity_flatness (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ →
      (staticSurvival (criticalOpenness lam hlam)).toReal < ε*lam^d :=
  power_bound_intensity_flatness _ splitSparseCoefficient split_sparse_real d ε hε

theorem quotient_low_intensity_flatness (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ →
      quotientTransitionLimit lam hlam < ε*lam^d :=
  power_bound_intensity_flatness _ quotientSparseCoefficient quotient_sparse_real d ε hε

end RAFCriticalWindowQuantitative
