module

public import RadianRamsey.Radian

public section

/-!
# Theorem D in Mathlib vocabulary

The radian nine-gon `k ↦ (cos kθ, sin kθ)`, `k = 0, …, 8`, written out in
`EuclideanSpace ℝ (Fin 2)`; "on the unit circle" is `Metric.sphere`, and OpenAI's `Ramsey` is
unfolded by grind
`OAI.EuclideanRamsey.Radian.radian_configuration`, `radian_ramsey_iff` and
`radian_ramsey_iff_tan` with OpenAI's definitions removed.
-/

set_option autoImplicit true
namespace RadianRamsey
open OAI.EuclideanRamsey.Radian

theorem oai_congruent_iff (a : Fin s → OAI.EuclideanRamsey.Space d)
    (b : Fin s → OAI.EuclideanRamsey.Space D) : OAI.EuclideanRamsey.Congruent a b ↔ Congruent a b := by grind [congruent_iff_dist_eq, OAI.EuclideanRamsey.Congruent]

set_option hygiene false
notation "𝔯" => ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧ ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin 9 → EuclideanSpace ℝ (Fin D), Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k
notation "𝔩" t => let a : Fin 9 → EuclideanSpace ℝ (Fin 2) := fun k => WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]; t

/-- **Theorem D, ⇒, Mathlib vocabulary.** If `tan (θ/2)` is transcendental, the nine points
`(cos kθ, sin kθ)`, `k = 0, …, 8`, are distinct, lie on the unit circle, and are not Euclidean
Ramsey: for some number `r ≥ 2` of colours, every dimension `D ≥ 1` has an `r`-colouring of
`EuclideanSpace ℝ (Fin D)` with no monochromatic congruent copy. -/
theorem radian_configuration_mathlib (θ : ℝ) (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    𝔩 Function.Injective a ∧ (∀ k, a k ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
      ¬ 𝔯 := by
  simp only [← oai_congruent_iff]
  exact radian_configuration θ ht

/-- **Theorem D, Mathlib vocabulary.** For distinct radian points: Euclidean Ramsey iff `cos θ` and
`sin θ` are algebraic (that is, iff `e^{iθ}` is algebraic). -/
theorem radian_ramsey_iff_mathlib (θ : ℝ) :
    𝔩 Function.Injective a →
      (𝔯 ↔
        IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ)) := by
  simp only [← oai_congruent_iff]
  exact radian_ramsey_iff θ

/-- **Theorem D, Mathlib vocabulary, half-angle form.** For distinct radian points: Euclidean
Ramsey iff `tan (θ/2)` is algebraic (Mathlib's `tan` has the junk value `0` at `θ/2 ≡ π/2`). -/
theorem radian_ramsey_iff_tan_mathlib (θ : ℝ) :
    𝔩 Function.Injective a →
      (𝔯 ↔
        IsAlgebraic ℚ (Real.tan (θ / 2))) := by
  simp only [← oai_congruent_iff]
  exact radian_ramsey_iff_tan θ
