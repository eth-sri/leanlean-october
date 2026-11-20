/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
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

section

variable (n : ℕ)

/-- Integer points of affine `n`-space, as vectors `Fin n → ℤ`. -/
abbrev IntPoint := Fin n → ℤ
/-- Rational points of affine `n`-space, as vectors `Fin n → ℚ`. -/
abbrev RatPoint := Fin n → ℚ

/-- The integer point `x`, regarded as a rational point by casting each coordinate. -/
def rationalPoint {n : ℕ} (x : IntPoint n) : RatPoint n := fun i => x i

/-- The inclusion of integer points into rational points is injective. -/
lemma rationalPoint_injective : Function.Injective (@rationalPoint n) :=
  fun _ _ h => funext fun i => Int.cast_injective (congrFun h i)

end

open MvPolynomial in
lemma eval_rationalPoint_map {n} (z : IntPoint n) (f : IntegerPolynomial n) :
    eval (rationalPoint z) (rationalEquation f) = (eval z f : ℚ) :=
  (map_eval (Int.castRingHom ℚ) z f).symm

/-- Every coordinate of the integer vector `x` has absolute value at most `B`. -/
abbrev InBox {ι : Type*} (x : ι → ℤ) (B : ℝ) : Prop :=
  ∀ i, |(x i : ℝ)| ≤ B

noncomputable abbrev boxInterval (B : ℝ) := Finset.Icc (-⌊B⌋) ⌊B⌋

@[simp] lemma mem_boxInterval {k : ℤ} {B : ℝ} : k ∈ boxInterval B ↔ |(k:ℝ)| ≤ B := by
  rw [Finset.mem_Icc,abs_le,Int.le_floor]; constructor <;> rintro ⟨h,l⟩ <;> refine ⟨?_,l⟩
  · have := Int.le_floor.mp (show -k ≤ ⌊B⌋ by omega); push_cast at this; linarith
  · have := Int.le_floor.mpr (show ((-k:ℤ):ℝ) ≤ B by push_cast; linarith); omega

lemma boxInterval_card {B : ℝ} (hB : 0 ≤ B) : ((boxInterval B).card:ℝ) ≤ 2*B+1 := by
  have := Int.floor_nonneg.mpr hB
  rw [boxInterval,Int.card_Icc,← Int.cast_natCast,Int.toNat_of_nonneg (by omega)]; push_cast; linarith [Int.floor_le B]

/-- The finite box of integer points of `ℤⁿ` all of whose coordinates have absolute value at
most the real radius `B`. -/
noncomputable def integerBox (n : ℕ) (B : ℝ) : Finset (IntPoint n) :=
  Fintype.piFinset fun _ => Finset.Icc (-⌊B⌋) ⌊B⌋

variable {n : ℕ} (X : Set (RatPoint n)) (B : ℝ)

/-- An integer point lies in `integerBox n B` exactly when all its coordinates have absolute value
at most `B`. -/
theorem mem_integerBox {B : ℝ} {x : IntPoint n} :
    x ∈ integerBox n B ↔ InBox x B := by
  simp only [integerBox,Fintype.mem_piFinset]
  exact forall_congr' fun _ => mem_boxInterval

/-- The integer points of absolute value at most `B` whose rational image lies in the set `X`. -/
noncomputable def integralPoints :
    Finset (IntPoint n) := by
  classical
  exact (integerBox n B).filter fun x => rationalPoint x ∈ X

/-- The number of integer points with all coordinates of absolute value at most `B` whose rational
image lies in the set `X`. -/
noncomputable def count : ℕ :=
  (integralPoints X B).card

/-- An integer point belongs to `integralPoints X B` exactly when it lies in the box of radius `B`
and its rational image lies in `X`. -/
theorem mem_integralPoints {X : Set (RatPoint n)} {B : ℝ} {x : IntPoint n} :
    x ∈ integralPoints X B ↔ InBox x B ∧ rationalPoint x ∈ X := by
  simp [integralPoints, mem_integerBox]

/-- The integral point count is monotone in both the locus and the box radius. -/
theorem count_mono {X Y : Set (RatPoint n)} {B C : ℝ}
    (hXY : X ⊆ Y) (hBC : B ≤ C) : count X B ≤ count Y C := by
  apply Finset.card_le_card
  grind [mem_integralPoints.mp, mem_integralPoints.mpr]

/-- The integral point count of a union is at most the sum of the counts. -/
theorem count_union_le (Y : Set (RatPoint n)) (B : ℝ) :
    count (X ∪ Y) B ≤ count X B + count Y B := by
  classical
  have h : integralPoints (X ∪ Y) B = integralPoints X B ∪ integralPoints Y B := by
    ext x
    simp only [mem_integralPoints, Finset.mem_union, Set.mem_union]
    tauto
  unfold count
  grind

/-- The rational zeros of a polynomial with rational coefficients. -/
def zeroLocus (f : CoordinatePolynomial n) : Set (RatPoint n) :=
  {x | MvPolynomial.eval x f = 0}


open MvPolynomial Finset

lemma mem_integer_zeroLocus {n : ℕ} {x : IntPoint n} {f : IntegerPolynomial n} : rationalPoint x ∈ zeroLocus (rationalEquation f) ↔ eval x f = 0 := by
  change eval _ _ = _ ↔ _; rw [eval_rationalPoint_map,Int.cast_eq_zero]

lemma count_le_of_box_imp {n : ℕ} {X Y : Set (RatPoint n)} {B : ℝ}
    (h : ∀ x : IntPoint n, InBox x B → rationalPoint x ∈ X → rationalPoint x ∈ Y) : count X B ≤ count Y B :=
  card_le_card fun x hx => by obtain ⟨hB,hx⟩ := mem_integralPoints.mp hx; exact mem_integralPoints.mpr ⟨hB,h x hB hx⟩

/-- The number of integral points of height at most `B` on a finite union of sets is at most
the sum of the numbers of such points on the individual sets. -/
theorem count_biUnion_finset_le {n : ℕ} {ι : Type*}
    (s : Finset ι) (X : ι → Set (RatPoint n)) (B : ℝ) :
    count (⋃ i ∈ s, X i) B ≤ ∑ i ∈ s, count (X i) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [count, integralPoints]
  | @insert i s hi ih =>
    simpa [*] using (count_union_le (X i) (⋃ j ∈ s, X j) B).trans (Nat.add_le_add_left ih _)

lemma count_iUnion_bound {n : ℕ} {α : Type*} [Finite α] (X : α → Set (RatPoint n)) (B : ℝ) {M : ℝ}
    (bound : ∀ i, (count (X i) B : ℝ) ≤ M) : (count (⋃ i, X i) B : ℝ) ≤ Nat.card α * M := by
  classical
  let := Fintype.ofFinite α
  have h := count_biUnion_finset_le univ X B
  simp at h
  calc _ ≤ ∑ i, (count (X i) B:ℝ) := by exact_mod_cast h
       _ ≤ ∑ _i : α, M := sum_le_sum fun i _ => bound i
       _ = _ := by simp [Nat.card_eq_fintype_card]

end CCDN
