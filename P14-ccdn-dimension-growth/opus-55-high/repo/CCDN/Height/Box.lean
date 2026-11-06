/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Int.Interval

/-!
# Integral points in real-radius boxes

Coordinates are integers; membership in the locus is tested after casting to rational numbers.
The definition works for real radii, including the boundary `B = 1` in CCDN Theorem 3.
`InBox x B` states that every coordinate of `x` has absolute value at most `B`; for points of
`ℤⁿ` it is membership in the finite box `integerBox n B` (`mem_integerBox`). The counted sets
are typically zero loci `zeroLocus f` of rational polynomials.
-/

namespace CCDN

section
variable (n : ℕ)

/-- Integer points of affine `n`-space, as vectors `Fin n → ℤ`. -/
abbrev IntPoint := Fin n → ℤ
/-- Rational points of affine `n`-space, as vectors `Fin n → ℚ`. -/
abbrev RatPoint := Fin n → ℚ

end

/-- The integer point `x`, regarded as a rational point by casting each coordinate. -/
def rationalPoint {n : ℕ} (x : IntPoint n) : RatPoint n := fun i => x i

/-- Every coordinate of the integer vector `x` has absolute value at most `B`. -/
abbrev InBox {ι : Type*} (x : ι → ℤ) (B : ℝ) : Prop :=
  ∀ i, |(x i : ℝ)| ≤ B

/-- The finite box of integer points of `ℤⁿ` all of whose coordinates have absolute value at
most the real radius `B`. -/
noncomputable def integerBox (n : ℕ) (B : ℝ) : Finset (IntPoint n) :=
  Fintype.piFinset fun _ => Finset.Icc (-⌊B⌋) ⌊B⌋

/-- An integer point lies in `integerBox n B` exactly when all its coordinates have absolute value
at most `B`. -/
theorem mem_integerBox {n : ℕ} {B : ℝ} {x : IntPoint n} :
    x ∈ integerBox n B ↔ InBox x B := by
  simp [integerBox, Fintype.mem_piFinset, Finset.mem_Icc]
  apply forall_congr'
  intro i
  rw [abs_le]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hneg : -(x i) ≤ ⌊B⌋ := by omega
    have hn := Int.le_floor.mp hneg
    have hp := Int.le_floor.mp hhi
    grind
  · rintro ⟨hlo, hhi⟩
    have hn : (-(x i) : ℝ) ≤ B := by linarith
    have hneg : -(x i) ≤ ⌊B⌋ := Int.le_floor.mpr (by grind)
    exact ⟨by omega, Int.le_floor.mpr hhi⟩

section
variable {n : ℕ} (X : Set (RatPoint n)) (B : ℝ)

/-- The integer points of absolute value at most `B` whose rational image lies in the set `X`. -/
noncomputable def integralPoints :
    Finset (IntPoint n) := by
  classical
  exact (integerBox n B).filter fun x => rationalPoint x ∈ X

/-- The number of integer points with all coordinates of absolute value at most `B` whose rational
image lies in the set `X`. -/
noncomputable def count : ℕ :=
  (integralPoints X B).card

end

variable {n : ℕ}

/-- An integer point belongs to `integralPoints X B` exactly when it lies in the box of radius `B`
and its rational image lies in `X`. -/
theorem mem_integralPoints {X : Set (RatPoint n)} {B : ℝ} {x : IntPoint n} :
    x ∈ integralPoints X B ↔ InBox x B ∧ rationalPoint x ∈ X := by
  simp [integralPoints, mem_integerBox]

/-- The integral point count is monotone in both the locus and the box radius. -/
theorem count_mono {X Y : Set (RatPoint n)} {B C : ℝ}
    (hXY : X ⊆ Y) (hBC : B ≤ C) : count X B ≤ count Y C := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hb, hx⟩ := mem_integralPoints.mp hx
  exact mem_integralPoints.mpr ⟨fun i => (hb i).trans hBC, hXY hx⟩

/-- The integral point count of a union is at most the sum of the counts. -/
theorem count_union_le (X Y : Set (RatPoint n)) (B : ℝ) :
    count (X ∪ Y) B ≤ count X B + count Y B := by
  have h : integralPoints (X ∪ Y) B = integralPoints X B ∪ integralPoints Y B := by
    ext x
    simp [mem_integralPoints, Finset.mem_union, Set.mem_union]
    tauto
  unfold count
  rw [h]
  exact Finset.card_union_le _ _

/-- The rational zeros of a polynomial with rational coefficients. -/
def zeroLocus (f : MvPolynomial (Fin n) ℚ) : Set (RatPoint n) :=
  {x | MvPolynomial.eval x f = 0}

