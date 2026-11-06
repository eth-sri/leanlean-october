module

public import RadianRamsey.Radian

@[expose] public section

namespace RadianRamsey
open OAI.EuclideanRamsey.Radian

/-- **Theorem D, ⇒, Mathlib vocabulary.** -/
theorem radian_configuration_mathlib (θ : ℝ) (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    let a : Fin 9 → EuclideanSpace ℝ (Fin 2) := fun k =>
      WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]
    Function.Injective a ∧ (∀ k, a k ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
      ¬ (∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
        ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin 9 → EuclideanSpace ℝ (Fin D),
          Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k) := by
  intro a
  simp only [Metric.mem_sphere, congruent_iff_dist_eq, eq_comm (a := dist (a _) (a _))]
  exact radian_configuration θ ht

/-- **Theorem D, Mathlib vocabulary.** -/
theorem radian_ramsey_iff_mathlib (θ : ℝ) :
    let a : Fin 9 → EuclideanSpace ℝ (Fin 2) := fun k =>
      WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]
    Function.Injective a →
      ((∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
          ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin 9 → EuclideanSpace ℝ (Fin D),
            Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k) ↔
        IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ)) := by
  intro a hinj
  simp only [congruent_iff_dist_eq, eq_comm (a := dist (a _) _)]
  exact radian_ramsey_iff θ hinj

/-- **Theorem D, Mathlib vocabulary, half-angle form.** -/
theorem radian_ramsey_iff_tan_mathlib (θ : ℝ) :
    let a : Fin 9 → EuclideanSpace ℝ (Fin 2) := fun k =>
      WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]
    Function.Injective a →
      ((∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
          ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin 9 → EuclideanSpace ℝ (Fin D),
            Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k) ↔
        IsAlgebraic ℚ (Real.tan (θ / 2))) := by
  intro a hinj
  simp only [congruent_iff_dist_eq, eq_comm (a := dist (a _) _)]
  exact radian_ramsey_iff_tan θ hinj

end RadianRamsey

