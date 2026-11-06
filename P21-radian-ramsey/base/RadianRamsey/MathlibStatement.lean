module

public import RadianRamsey.Radian
public import RadianRamsey.MathlibBridge

@[expose] public section

/-!
# Theorem D in Mathlib vocabulary

The radian nine-gon `k ↦ (cos kθ, sin kθ)`, `k = 0, …, 8`, written out in
`EuclideanSpace ℝ (Fin 2)`; "on the unit circle" is `Metric.sphere`, and OpenAI's `Ramsey` is
unfolded by `oai_ramsey_iff` into Mathlib's `Congruent`. These are
`OAI.EuclideanRamsey.Radian.radian_configuration`, `radian_ramsey_iff` and
`radian_ramsey_iff_tan` with OpenAI's definitions removed.
-/

namespace RadianRamsey

open OAI.EuclideanRamsey.Radian in
/-- **Theorem D, ⇒, Mathlib vocabulary.** If `tan (θ/2)` is transcendental, the nine points
`(cos kθ, sin kθ)`, `k = 0, …, 8`, are distinct, lie on the unit circle, and are not Euclidean
Ramsey: for some number `r ≥ 2` of colours, every dimension `D ≥ 1` has an `r`-colouring of
`EuclideanSpace ℝ (Fin D)` with no monochromatic congruent copy. -/
theorem radian_configuration_mathlib (θ : ℝ) (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    let a : Fin 9 → EuclideanSpace ℝ (Fin 2) := fun k =>
      WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]
    Function.Injective a ∧ (∀ k, a k ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
      ¬ (∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
        ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin 9 → EuclideanSpace ℝ (Fin D),
          Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k) := by
  intro a
  obtain ⟨h1, h2, h3⟩ := radian_configuration θ ht
  refine ⟨h1, fun k => Metric.mem_sphere.mpr (h2 k), fun h => h3 ((oai_ramsey_iff a).2 h)⟩

open OAI.EuclideanRamsey.Radian in
/-- **Theorem D, Mathlib vocabulary.** For distinct radian points: Euclidean Ramsey iff `cos θ` and
`sin θ` are algebraic (that is, iff `e^{iθ}` is algebraic). -/
theorem radian_ramsey_iff_mathlib (θ : ℝ) :
    let a : Fin 9 → EuclideanSpace ℝ (Fin 2) := fun k =>
      WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]
    Function.Injective a →
      ((∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
          ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin 9 → EuclideanSpace ℝ (Fin D),
            Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k) ↔
        IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ)) := by
  intro a hinj
  rw [← oai_ramsey_iff a]
  exact radian_ramsey_iff θ hinj

open OAI.EuclideanRamsey.Radian in
/-- **Theorem D, Mathlib vocabulary, half-angle form.** For distinct radian points: Euclidean
Ramsey iff `tan (θ/2)` is algebraic (Mathlib's `tan` has the junk value `0` at `θ/2 ≡ π/2`). -/
theorem radian_ramsey_iff_tan_mathlib (θ : ℝ) :
    let a : Fin 9 → EuclideanSpace ℝ (Fin 2) := fun k =>
      WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]
    Function.Injective a →
      ((∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
          ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin 9 → EuclideanSpace ℝ (Fin D),
            Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k) ↔
        IsAlgebraic ℚ (Real.tan (θ / 2))) := by
  intro a hinj
  rw [← oai_ramsey_iff a]
  exact radian_ramsey_iff_tan θ hinj

end RadianRamsey
