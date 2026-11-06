module

public import Erdos821.Blueprint.Graph
public import Erdos821.Blueprint.Analytic

@[expose] public section


namespace Erdos821.Blueprint.Graph

/-- §2 tilted reciprocal-prime law is uniformly close to the original. -/
theorem tilted_density_bound (p e : ℝ) (hp : 0 < p) (he : 0 ≤ e) (he' : 2 * e ≤ p) :
    0 < 1 - e / p ∧ 1 ≤ (1 - e / p)⁻¹ ∧ (1 - e / p)⁻¹ ≤ 1 + 2 * e / p := by
  have hep_nonneg : 0 ≤ e / p := by positivity
  have hep_le : e / p ≤ 1 / 2 := by
    rw [div_le_iff₀ hp]
    linarith
  have h1 : 0 < 1 - e / p := by linarith
  refine ⟨h1, ?_, ?_⟩
  · rw [one_le_inv_iff₀]
    simp_all
  · rw [inv_le_iff_one_le_mul₀ h1]
    have hexpand : (1 + 2 * e / p) * (1 - e / p) = 1 + (e / p) * (1 - 2 * (e / p)) := by
      ring
    nlinarith

/-- §2 compatibility of a prime active at both endpoints. -/
theorem active_both_divides_step (p : ℕ) (n k D : ℤ) (hp : Nat.Prime p)
    (hn : (p : ℤ) ∣ n) (hn' : (p : ℤ) ∣ n + k * D) (hk : ¬ (p : ℤ) ∣ k) :
    (p : ℤ) ∣ D := by
  have hprime := Nat.prime_iff_prime_int.mp hp
  have hsub : (p : ℤ) ∣ (n + k * D) - n := dvd_sub hn' hn
  have heq : (n + k * D) - n = k * D := by ring
  rw [heq] at hsub
  rw [Prime.dvd_mul hprime] at hsub
  simp_all

end Erdos821.Blueprint.Graph
