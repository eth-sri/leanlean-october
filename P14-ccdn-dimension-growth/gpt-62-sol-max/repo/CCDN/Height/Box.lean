/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Int.Interval

/-!
# Integral points in real-radius boxes

Coordinates are integers; membership in the locus is tested after casting to rational numbers.
The definition works for real radii, including the boundary `B = 1` in CCDN Theorem 3.
`InBox x B` states that every coordinate of `x` has absolute value at most `B`; for points of
`ℤⁿ` it is membership in the finite box `integerBox n B` (`mem_integerBox`). The counted sets
are typically zero loci `zeroLocus f` of rational polynomials.
-/

@[expose] public section

namespace CCDN

/-- Integer points of affine `n`-space, as vectors `Fin n → ℤ`. -/
abbrev IntPoint (n : ℕ) := Fin n → ℤ
/-- Rational points of affine `n`-space, as vectors `Fin n → ℚ`. -/
abbrev RatPoint (n : ℕ) := Fin n → ℚ

/-- The integer point `x`, regarded as a rational point by casting each coordinate. -/
def rationalPoint {n : ℕ} (x : IntPoint n) : RatPoint n := fun i => x i

@[simp] lemma rationalPoint_zero (n : ℕ) : rationalPoint (0 : IntPoint n) = 0 :=
  funext fun _ => Int.cast_zero

/-- The inclusion of integer points into rational points is injective. -/
lemma rationalPoint_injective (n : ℕ) : Function.Injective (@rationalPoint n) := by
  intro z w he
  funext j
  exact Int.cast_injective (congrFun he j)

/-- Evaluating an integral equation commutes with passage to rational points. -/
lemma eval_rationalPoint_map_eq_zero {n : ℕ} (x : IntPoint n)
    (f : MvPolynomial (Fin n) ℤ) :
    MvPolynomial.eval (rationalPoint x) (MvPolynomial.map (Int.castRingHom ℚ) f) = 0 ↔
      MvPolynomial.eval x f = 0 := by
  change MvPolynomial.eval (Int.castRingHom ℚ ∘ x) (MvPolynomial.map (Int.castRingHom ℚ) f) = 0 ↔ _
  rw [← MvPolynomial.map_eval]
  exact Int.cast_eq_zero

/-- Every coordinate of the integer vector `x` has absolute value at most `B`. -/
abbrev InBox {ι : Type*} (x : ι → ℤ) (B : ℝ) : Prop :=
  ∀ i, |(x i : ℝ)| ≤ B

/-- The integers in the interval of radius `B`. -/
noncomputable def integerInterval (B : ℝ) : Finset ℤ := Finset.Icc (-⌊B⌋) ⌊B⌋

@[simp] lemma mem_integerInterval {z : ℤ} {B : ℝ} :
    z ∈ integerInterval B ↔ |(z : ℝ)| ≤ B := by
  rw [integerInterval, Finset.mem_Icc, neg_le, abs_le']
  simp only [Int.le_floor, Int.cast_neg, and_comm]

lemma integerInterval_card_cast {B : ℝ} (hB : 0 ≤ B) :
    ((integerInterval B).card : ℝ) = 2 * (⌊B⌋ : ℝ) + 1 := by
  have := Int.floor_nonneg.mpr hB
  rw [integerInterval, Int.card_Icc]
  exact_mod_cast (show ((⌊B⌋ + 1 - -⌊B⌋).toNat : ℤ) = 2 * ⌊B⌋ + 1 by omega)

lemma integerInterval_card_le {B : ℝ} (hB : 0 ≤ B) :
    ((integerInterval B).card : ℝ) ≤ 2 * B + 1 := by
  rw [integerInterval_card_cast hB]
  linarith [Int.floor_le B]

/-- The finite box of integer points of `ℤⁿ` all of whose coordinates have absolute value at
most the real radius `B`. -/
noncomputable def integerBox (n : ℕ) (B : ℝ) : Finset (IntPoint n) :=
  Fintype.piFinset fun _ => integerInterval B

/-- An integer point lies in `integerBox n B` exactly when all its coordinates have absolute value
at most `B`. -/
theorem mem_integerBox {n : ℕ} {B : ℝ} {x : IntPoint n} :
    x ∈ integerBox n B ↔ InBox x B := by
  simp [integerBox]

/-- The integer points of absolute value at most `B` whose rational image lies in the set `X`. -/
noncomputable def integralPoints {n : ℕ} (X : Set (RatPoint n)) (B : ℝ) :
    Finset (IntPoint n) := by
  classical
  exact {x ∈ integerBox n B | rationalPoint x ∈ X}

/-- The number of integer points with all coordinates of absolute value at most `B` whose rational
image lies in the set `X`. -/
noncomputable def count {n : ℕ} (X : Set (RatPoint n)) (B : ℝ) : ℕ :=
  (integralPoints X B).card

/-- An integer point belongs to `integralPoints X B` exactly when it lies in the box of radius `B`
and its rational image lies in `X`. -/
theorem mem_integralPoints {n : ℕ} {X : Set (RatPoint n)} {B : ℝ} {x : IntPoint n} :
    x ∈ integralPoints X B ↔ InBox x B ∧ rationalPoint x ∈ X := by
  grind [integralPoints, mem_integerBox]

lemma count_le_of_integral_mem {n : ℕ} {X Y : Set (RatPoint n)} {B : ℝ}
    (h : ∀ x : IntPoint n, InBox x B → rationalPoint x ∈ X → rationalPoint x ∈ Y) :
    count X B ≤ count Y B := by
  apply Finset.card_le_card
  simp only [Finset.subset_iff, mem_integralPoints]
  exact fun x hx => ⟨hx.1, h x hx.1 hx.2⟩

/-- The integral point count of a union is at most the sum of the counts. -/
theorem count_union_le {n : ℕ} (X Y : Set (RatPoint n)) (B : ℝ) :
    count (X ∪ Y) B ≤ count X B + count Y B := by
  classical
  have h : integralPoints (X ∪ Y) B = integralPoints X B ∪ integralPoints Y B := by
    grind [mem_integralPoints]
  unfold count
  grind

/-- The rational zeros of a polynomial with rational coefficients. -/
def zeroLocus {n : ℕ} (f : MvPolynomial (Fin n) ℚ) : Set (RatPoint n) :=
  {x | MvPolynomial.eval x f = 0}

end CCDN
