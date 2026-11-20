module

public import RadianRamsey.Radian

@[expose] public section

/-!
# Theorem D in Mathlib vocabulary

The radian nine-gon `k ↦ (cos kθ, sin kθ)`, `k = 0, …, 8`, written out in
`EuclideanSpace ℝ (Fin 2)`; "on the unit circle" is `Metric.sphere`, and OpenAI's `Ramsey` is
unfolded by `bridge` into Mathlib's `Congruent`. These are
`OAI.EuclideanRamsey.Radian.radian_configuration`, `radian_ramsey_iff` and
`radian_ramsey_iff_tan` with OpenAI's definitions removed.
-/

namespace RadianRamsey
open OAI.EuclideanRamsey.Radian

-- Local notation expands in the theorem types: the public statements mention
-- only Mathlib's spaces, sphere and congruence.
local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "points(" θ ")" => fun k : Fin 9 =>
  WithLp.toLp 2 ![Real.cos ((k : ℕ)*θ), Real.sin ((k : ℕ)*θ)]
set_option quotPrecheck false in
local notation "RamseyIn(" a ")" => ∀ r, 2 ≤ r → ∃ D, 1 ≤ D ∧
  ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b, Congruent a b ∧ ∃ k, ∀ i, χ (b i) = k

private lemma bridge (a : Fin 9 → Plane) :
    OAI.EuclideanRamsey.Ramsey a ↔ RamseyIn(a) := by
  simp [OAI.EuclideanRamsey.Ramsey,OAI.EuclideanRamsey.Congruent,congruent_iff_dist_eq,eq_comm]

/-- **Theorem D, ⇒, Mathlib vocabulary.** If `tan (θ/2)` is transcendental, the nine points
`(cos kθ, sin kθ)`, `k = 0, …, 8`, are distinct, lie on the unit circle, and are not Euclidean
Ramsey: for some number `r ≥ 2` of colours, every dimension `D ≥ 1` has an `r`-colouring of
`EuclideanSpace ℝ (Fin D)` with no monochromatic congruent copy. -/
theorem radian_configuration_mathlib (θ : ℝ) (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    let a : Fin 9 → Plane := points(θ)
    Function.Injective a ∧ (∀ k, a k ∈ Metric.sphere (0 : Plane) 1) ∧
      ¬ RamseyIn(a) := by
  intro a
  rw [← bridge a]; exact radian_configuration θ ht

/-- **Theorem D, Mathlib vocabulary.** For distinct radian points: Euclidean Ramsey iff `cos θ` and
`sin θ` are algebraic (that is, iff `e^{iθ}` is algebraic). -/
theorem radian_ramsey_iff_mathlib (θ : ℝ) :
    let a : Fin 9 → Plane := points(θ)
    Function.Injective a →
      (RamseyIn(a) ↔
        IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ)) := by
  intro a hinj
  rw [← bridge a]
  exact radian_ramsey_iff θ hinj

/-- **Theorem D, Mathlib vocabulary, half-angle form.** For distinct radian points: Euclidean
Ramsey iff `tan (θ/2)` is algebraic (Mathlib's `tan` has the junk value `0` at `θ/2 ≡ π/2`). -/
theorem radian_ramsey_iff_tan_mathlib (θ : ℝ) :
    let a : Fin 9 → Plane := points(θ)
    Function.Injective a →
      (RamseyIn(a) ↔
        IsAlgebraic ℚ (Real.tan (θ / 2))) := by
  intro a hinj
  rw [← bridge a]
  exact radian_ramsey_iff_tan θ hinj

end RadianRamsey
