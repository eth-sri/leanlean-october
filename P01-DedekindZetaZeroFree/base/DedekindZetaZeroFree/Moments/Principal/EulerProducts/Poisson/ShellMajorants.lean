module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.Domain

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.EulerShellMargin

noncomputable section

open DedekindZetaZeroFree.Quantitative.EulerDomain

def shellExponent (x y v : ℝ) (e₀ k ℓ m : ℕ) : ℝ :=
  (1 / 2 - x) * e₀ + (2 - 3 * x) * ℓ + (1 / 2 - y) * k - 6 * v * m

private theorem shellExponent_le_margin_aux (δ x y v : ℝ) (hδ : 0 < δ) (e₀ k ℓ m : ℕ)
    (he₀ : e₀ ≤ 1) (hk : k ≤ 1) (hpos : 0 < e₀ + 3 * ℓ)
    (hx : 1 / 2 + δ ≤ x) (hA : 2 + δ ≤ 3 * x) (hB : 5 / 2 + δ ≤ 3 * x + y)
    (hC : 1 + δ ≤ x + y) (hv : δ ≤ v) :
    shellExponent x y v e₀ k ℓ m ≤ -(δ / 2) - (δ / 2) * (ℓ : ℝ) - (δ / 2) * (m : ℝ) := by
  unfold shellExponent
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm6 : δ * m ≤ 6 * v * m := by nlinarith
  rcases Nat.eq_zero_or_pos ℓ with h | h
  · subst h
    have he : e₀ = 1 := by omega
    subst he
    interval_cases k <;> norm_num <;> nlinarith
  · have hl1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast h
    have hl : (0 : ℝ) ≤ ℓ := by linarith
    interval_cases e₀ <;> interval_cases k <;> push_cast <;>
      nlinarith [mul_nonneg (sub_nonneg.mpr hl1) (by linarith : (0 : ℝ) ≤ 3 * x - 2 - δ)]

theorem shellExponent_le_margin (δ : ℝ) (hδ : 0 < δ) :
    ∃ δ₀ δ' : ℝ, 0 < δ₀ ∧ 0 < δ' ∧ ∀ p ∈ OmegaStarMargin δ,
      ∀ e₀ k ℓ m : ℕ, e₀ ≤ 1 → k ≤ 1 → 0 < e₀ + 3 * ℓ →
        shellExponent p.1.re p.2.1.re p.2.2.re e₀ k ℓ m ≤
          -δ₀ - δ' * ℓ - δ' * m := by
  refine ⟨δ / 2, δ / 2, by linarith, by linarith, ?_⟩
  intro p hp e₀ k ℓ m he₀ hk hpos
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hp
  exact shellExponent_le_margin_aux δ _ _ _ hδ e₀ k ℓ m he₀ hk hpos (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

end

end DedekindZetaZeroFree.Quantitative.EulerShellMargin
