module

public import Erdos408.Extraction.TypeII.BoxSum

/-!
# Freezing the cutoff on a box

On a box `m ∈ (λ, λ(1+δ)]`, `n ∈ (μ, μ(1+δ)]` replace `Φ((mn - 1)/x)` by the constant
`Φ(λμ/x)`. The difference is at most `D₁ (3δ(κx + 1) + 1)/x` by the mean value theorem, and
vanishes unless `λμ ≤ κx + 1`, in which case `mn ≤ 4(κx + 1)`.
-/

@[expose] public section

namespace Erdos408.TypeII

/-- A cutoff in the class is Lipschitz with constant `M₁ T^{C_Φ}`. -/
theorem abs_sub_le_of_isCutoff {κ CΦ x : ℝ} {M : ℕ → ℝ} {Φ : ℝ → ℝ}
    (hΦ : IsCutoff κ CΦ M x Φ) (a b : ℝ) :
    |Φ a - Φ b| ≤ M 1 * logLog x ^ (CΦ * 1) * |a - b| := by
  obtain ⟨hsmooth, -, -, hder⟩ := hΦ
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun y _ => (hsmooth.differentiable (by simp)) y) (fun y _ => by
      simpa using hder 1 y) convex_univ
    (Set.mem_univ b) (Set.mem_univ a)
  simpa using h

/-- The derivative bound of a cutoff is nonnegative. -/
theorem cutoff_deriv_bound_nonneg {κ CΦ x : ℝ} {M : ℕ → ℝ} {Φ : ℝ → ℝ}
    (hΦ : IsCutoff κ CΦ M x Φ) (r : ℕ) : 0 ≤ M r * logLog x ^ (CΦ * r) :=
  (abs_nonneg _).trans (hΦ.2.2.2 r 0)

/-- The frozen cutoff on a box. -/
theorem abs_cutoff_freeze_le {κ CΦ x : ℝ} {M : ℕ → ℝ} {Φ : ℝ → ℝ} (hΦ : IsCutoff κ CΦ M x Φ)
    (hx : 0 < x) (hκ : 1 < κ) {lam mu δ : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) {m n : ℕ} (hm1 : lam < m) (hm2 : m ≤ lam * (1 + δ)) (hn1 : mu < n)
    (hn2 : n ≤ mu * (1 + δ)) :
    |Φ (((m * n : ℕ) - 1) / x) - Φ (lam * mu / x)| ≤
      (if (m * n) ≤ 4 * (κ * x + 1) then
        M 1 * logLog x ^ (CΦ * 1) * ((3 * δ * (κ * x + 1) + 1) / x) else 0) := by
  have hsupp := hΦ.2.2.1
  have hmn1 := mul_lt_mul'' hm1 hn1 hlam hmu
  have hmn2 : (m : ℝ) * n ≤ lam * mu * (1 + δ) ^ 2 := by
    nlinarith
  by_cases hz : Φ (((m * n : ℕ) - 1) / x) = 0 ∧ Φ (lam * mu / x) = 0
  · rw [hz.1, hz.2, sub_zero, abs_zero]
    have h1 := cutoff_deriv_bound_nonneg hΦ 1
    push_cast at h1
    split_ifs
    · positivity
    · exact le_rfl
  · -- `λμ ≤ κx + 1`
    have hlm : lam * mu ≤ κ * x + 1 := by
      rcases not_and_or.1 hz with h | h
      all_goals
        have := (hsupp _ h).2
        rw [div_le_iff₀ hx] at this
      · push_cast at this
        linarith
      · linarith
    have hX : m * n ≤ 4 * (κ * x + 1) := by
      have : (1 + δ) ^ 2 ≤ 4 := by nlinarith
      calc _ ≤ lam * mu * (1 + δ) ^ 2 := hmn2
        _ ≤ (κ * x + 1) * 4 := by gcongr
        _ = _ := by ring
    simp only [hX, ↓reduceIte]
    refine (abs_sub_le_of_isCutoff hΦ _ _).trans ?_
    have h1 := cutoff_deriv_bound_nonneg hΦ 1
    push_cast at h1
    refine mul_le_mul_of_nonneg_left ?_ h1
    rw [← sub_div, abs_div, abs_of_pos hx]
    refine div_le_div_of_nonneg_right ?_ hx.le
    push_cast
    rw [abs_le]
    have h3 : (m : ℝ) * n - lam * mu ≤ 3 * δ * (lam * mu) := by
      have : lam * mu * (1 + δ) ^ 2 - lam * mu ≤ 3 * δ * (lam * mu) := by
        have : 0 ≤ lam * mu := by positivity
        nlinarith
      linarith
    have h4 : 3 * δ * (lam * mu) ≤ 3 * δ * (κ * x + 1) :=
      by gcongr
    constructor <;> linarith

end Erdos408.TypeII
