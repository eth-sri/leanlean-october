module
public import Mathlib.Tactic

public import Erdos821.P3Edge.PowRho
public import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

/-- Ordered-retrieval counts against input damping, uniformly for `a ≤ Amax`.
This is `eq:promotion-count`: `(Z')_a ρ^{Z'-a}` is majorized by all maps
`Z'^a` times the same damping, and the supremum over all `Z'` is finite
independently of `J`. -/
lemma promo_allmaps_bound  rho  (hrho0 : 0 < rho) (hrho1 : rho < 1)  Amax  :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z' a : ℕ), a ≤ Amax →
      (Z' : ℝ) ^ a * rho ^ (Z' - a) ≤ C := by
  classical
  obtain ⟨C₀, hC₀pos, hC₀⟩ := pow_mul_rho_bound rho hrho0 hrho1 Amax
  refine ⟨max (C₀ / rho ^ Amax) (((Amax : ℕ) : ℝ) ^ Amax), ?_, fun Z' a ha => ?_⟩
  · simp_all
  · by_cases hZa : a ≤ Z'
    · have hZX : a + (Z' - a) = Z' := Nat.add_sub_cancel' hZa
      have h1 : (Z' : ℝ) ^ a * rho ^ Z' ≤ C₀ := hC₀ a ha Z'
      have h2 : rho ^ Amax ≤ rho ^ a :=
        pow_le_pow_of_le_one hrho0.le hrho1.le ha
      have h3 : ((Z' : ℝ) ^ a * rho ^ Z') / rho ^ a ≤ C₀ / rho ^ Amax := by
        bound
      have hN : (Z' : ℝ) ^ a * rho ^ (Z' - a)
          = ((Z' : ℝ) ^ a * rho ^ Z') / rho ^ a := by
        have hpow : rho ^ Z' = rho ^ a * rho ^ (Z' - a) := by
          conv_lhs => rw [← hZX]
          rw [pow_add]
        rw [eq_div_iff (pow_ne_zero _ (ne_of_gt hrho0)), hpow]
        ring
      rw [hN]
      exact le_trans h3 (le_max_left _ _)
    · push Not at hZa
      have hle : Z' ≤ Amax := le_trans (le_of_lt hZa) ha
      have hsub : Z' - a = 0 := Nat.sub_eq_zero_of_le (le_of_lt hZa)
      rw [hsub, pow_zero, mul_one]
      have h1 : (Z' : ℝ) ^ a ≤ ((Amax : ℕ) : ℝ) ^ a :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hle) _
      have h2 : ((Amax : ℕ) : ℝ) ^ a ≤ ((Amax : ℕ) : ℝ) ^ Amax := by
        by_cases hA : Amax = 0
        · simp_all
        · exact pow_le_pow_right₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hA) ha
      exact le_trans (le_trans h1 h2) (le_max_right _ _)

end Erdos821.P3Edge
