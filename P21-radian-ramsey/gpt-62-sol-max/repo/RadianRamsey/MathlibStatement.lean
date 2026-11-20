module

public import RadianRamsey.Radian

@[expose] public section

namespace RadianRamsey

open OAI.EuclideanRamsey (Ramsey Space)
open OAI.EuclideanRamsey.Radian

-- These notations expand to Mathlib terms, so no Ramsey-specific constants appear in the statements.
set_option quotPrecheck false in
local notation "Ramseyₘ(" a ")" => (∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
    ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b, Congruent a b ∧ ∃ k, ∀ i, χ (b i) = k)
local notation "ninePoints" θ => (fun k : Fin 9 => (WithLp.toLp 2
    ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)] : EuclideanSpace ℝ (Fin 2)))

private theorem ramsey_bridge {s d : ℕ} (a : Fin s → Space d) : Ramsey a ↔ Ramseyₘ(a) := by
  have h {D : ℕ} (b : Fin s → Space D) : OAI.EuclideanRamsey.Congruent a b ↔ Congruent a b := by
    rw [congruent_iff_dist_eq]
    exact forall₂_congr fun _ _ => eq_comm
  simp only [Ramsey,h]

/-- **Theorem D, ⇒, Mathlib vocabulary.** -/
theorem radian_configuration_mathlib (θ : ℝ) (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    let a : Fin 9 → EuclideanSpace ℝ (Fin 2) := ninePoints θ
    Function.Injective a ∧ (∀ k, a k ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
      ¬ Ramseyₘ(a) := by
  simpa only [Metric.mem_sphere, ← ramsey_bridge] using! radian_configuration θ ht

/-- **Theorem D, Mathlib vocabulary.** -/
theorem radian_ramsey_iff_mathlib (θ : ℝ) :
    let a : Fin 9 → EuclideanSpace ℝ (Fin 2) := ninePoints θ
    Function.Injective a → (Ramseyₘ(a) ↔
      IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ)) := by
  simpa only [← ramsey_bridge] using! radian_ramsey_iff θ

/-- **Theorem D, half-angle form, Mathlib vocabulary.** -/
theorem radian_ramsey_iff_tan_mathlib (θ : ℝ) :
    let a : Fin 9 → EuclideanSpace ℝ (Fin 2) := ninePoints θ
    Function.Injective a → (Ramseyₘ(a) ↔ IsAlgebraic ℚ (Real.tan (θ / 2))) := by
  simpa only [← ramsey_bridge] using! radian_ramsey_iff_tan θ

end RadianRamsey
