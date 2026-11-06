module

public import Mathlib

@[expose] public section

/-!
# Advertised statements: the radian nine-gon (Theorem D)

Mathlib-only. The trusted surface is the four definitions below and the seven theorem statements.

* `Space`, `Congruent`, `Ramsey` are restated verbatim from OpenAI's
  `OAI/Combinatorics/EuclideanRamsey/Model.lean` (openai/math fd4aeeb2, Apache-2.0), which is also
  the text of OpenAI's own Comparator challenge for result 172. A finite configuration
  `a : Fin s → ℝ^d` is *Ramsey* if for every number of colours `r ≥ 2` there is a dimension `D`
  such that every `r`-colouring of `ℝ^D` contains a monochromatic congruent copy of `a`.
* `radianConfig θ` is the nine points `(cos kθ, sin kθ)`, `k = 0, …, 8`, on the unit circle,
  verbatim from `RadianRamsey/Radian.lean`.
* The last three theorems restate the first three with no definitions beyond Mathlib: the nine
  points written out, "on the unit circle" as `Metric.sphere`, and OpenAI's `Ramsey` unfolded,
  with Mathlib's `Congruent`.

**Fidelity.** Mathlib's `Real.tan` is `sin / cos` with `x / 0 = 0`, so `tan (θ/2) = 0` (algebraic)
at `θ ≡ π (mod 2π)`; there the transcendence hypothesis fails and the points are not distinct
anyway. No explicit `θ` with `tan (θ/2)` transcendental is exhibited in Lean (see `README.md`).
-/

namespace OAI

noncomputable section
open scoped TensorProduct
namespace EuclideanRamsey

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def Congruent {s d D : ℕ} (a : Fin s → Space d) (b : Fin s → Space D) : Prop :=
  ∀ i j, dist (b i) (b j) = dist (a i) (a j)

def Ramsey {s d : ℕ} (a : Fin s → Space d) : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
    ∀ c : Space D → Fin r, ∃ b : Fin s → Space D,
      Congruent a b ∧ ∃ k : Fin r, ∀ i, c (b i) = k

namespace Radian

/-- The nine points at angles `0, θ, 2θ, …, 8θ` on the unit circle. -/
def radianConfig (θ : ℝ) (k : Fin 9) : Space 2 :=
  WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]

/-- **Theorem D, ⇒.** If `tan (θ/2)` is transcendental, the nine points at angles
`0, θ, …, 8θ` are distinct, lie on the unit circle, and are not Euclidean Ramsey. -/
theorem radian_configuration (θ : ℝ) (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    Function.Injective (radianConfig θ) ∧ (∀ k, dist (radianConfig θ k) 0 = 1) ∧
      ¬ Ramsey (radianConfig θ) := by
  sorry

/-- The third conjunct of `radian_configuration` alone. -/
theorem radian_not_ramsey (θ : ℝ) (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    ¬ Ramsey (radianConfig θ) := by
  sorry

/-- **Theorem D.** For distinct radian points: Ramsey iff `cos θ` and `sin θ` are algebraic. -/
theorem radian_ramsey_iff (θ : ℝ) (hinj : Function.Injective (radianConfig θ)) :
    Ramsey (radianConfig θ) ↔ IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ) := by
  sorry

/-- **Theorem D, half-angle form.** For distinct radian points: Ramsey iff `tan (θ/2)` is
algebraic. -/
theorem radian_ramsey_iff_tan (θ : ℝ) (hinj : Function.Injective (radianConfig θ)) :
    Ramsey (radianConfig θ) ↔ IsAlgebraic ℚ (Real.tan (θ / 2)) := by
  sorry

end Radian

end EuclideanRamsey

end

end OAI

namespace RadianRamsey

/-- **Theorem D, ⇒, Mathlib vocabulary.** -/
theorem radian_configuration_mathlib (θ : ℝ) (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    let a : Fin 9 → EuclideanSpace ℝ (Fin 2) := fun k =>
      WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]
    Function.Injective a ∧ (∀ k, a k ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
      ¬ (∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
        ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin 9 → EuclideanSpace ℝ (Fin D),
          Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k) := by
  sorry

/-- **Theorem D, Mathlib vocabulary.** -/
theorem radian_ramsey_iff_mathlib (θ : ℝ) :
    let a : Fin 9 → EuclideanSpace ℝ (Fin 2) := fun k =>
      WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]
    Function.Injective a →
      ((∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
          ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin 9 → EuclideanSpace ℝ (Fin D),
            Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k) ↔
        IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ)) := by
  sorry

/-- **Theorem D, half-angle form, Mathlib vocabulary.** -/
theorem radian_ramsey_iff_tan_mathlib (θ : ℝ) :
    let a : Fin 9 → EuclideanSpace ℝ (Fin 2) := fun k =>
      WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]
    Function.Injective a →
      ((∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
          ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin 9 → EuclideanSpace ℝ (Fin D),
            Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k) ↔
        IsAlgebraic ℚ (Real.tan (θ / 2))) := by
  sorry

end RadianRamsey
