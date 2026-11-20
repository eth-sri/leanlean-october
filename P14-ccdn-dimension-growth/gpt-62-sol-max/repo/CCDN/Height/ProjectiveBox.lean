/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.Box
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization

/-! Rational projective points with the multiplicative height used by CCDN.
Bounded-height sets are finite, and primitive integral coordinates recover
the paper's maximum-coordinate height. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- Rational points of projective `n`-space, as lines in `ℚ^(n+1)`. -/
abbrev ProjectivePoint (n : ℕ) := Projectivization ℚ (Fin (n + 1) → ℚ)

/-- A nonzero integer point remains nonzero as a rational point. -/
lemma rationalPoint_ne_zero {n : ℕ} {x : IntPoint n} (hx : x ≠ 0) :
    rationalPoint x ≠ 0 := fun h => hx (rationalPoint_injective n (h.trans (rationalPoint_zero n).symm))

/-- The chosen projective height is exactly CCDN's height on primitive coordinates. -/
private theorem projective_height_primitive {n : ℕ} (x : IntPoint (n + 1)) (hx : x ≠ 0)
    (hprimitive : Finset.univ.gcd x = 1) :
    (Projectivization.mk ℚ (rationalPoint x) (rationalPoint_ne_zero hx)).mulHeight =
      ((⨆ i, |x i| : ℤ) : ℝ) := by
  rw [Projectivization.mulHeight_mk]
  exact Rat.mulHeight_eq_max_abs_of_gcd_eq_one hprimitive


/-- Clear denominators and divide out the gcd to obtain primitive coordinates. -/
theorem exists_primitive_projective_rep {n : ℕ} (x : ProjectivePoint n) :
    ∃ (z : IntPoint (n + 1)) (hz : z ≠ 0), Finset.univ.gcd z = 1 ∧
      Projectivization.mk ℚ (rationalPoint z) (rationalPoint_ne_zero hz) = x := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) x.rep
  choose u hu using hb
  obtain ⟨z, hz, hprim⟩ := Finset.extract_gcd u Finset.univ_nonempty
  
  have he : x.rep = (((Finset.univ.gcd u : ℤ) : ℚ) / (b : ℤ)) • rationalPoint z := by
    funext i
    have hi : (u i : ℚ) = (b : ℤ) * x.rep i := hu i
    rw [hz i (Finset.mem_univ i), Int.cast_mul] at hi
    change x.rep i = _ * (z i : ℚ)
    field_simp
    linear_combination -hi
  have hz0 : z ≠ 0 := by
    intro h
    exact x.rep_nonzero (by simpa [h] using he)
  refine ⟨z, hz0, hprim, ?_⟩
  rw [eq_comm, ← x.mk_rep, Projectivization.mk_eq_mk_iff']
  exact ⟨_, he.symm⟩

/-- A chosen primitive integer representative of the projective point `x`: a nonzero integer
vector with coprime coordinates spanning `x`. -/
def primitiveProjectiveRep {n : ℕ} (x : ProjectivePoint n) : IntPoint (n + 1) :=
  (exists_primitive_projective_rep x).choose

section

variable {n : ℕ}
include n

/-- The primitive integer representative of a projective point is nonzero. -/
lemma primitiveProjectiveRep_ne_zero (x : ProjectivePoint n) :
    primitiveProjectiveRep x ≠ 0 :=
  (exists_primitive_projective_rep x).choose_spec.choose

/-- The coordinates of the primitive integer representative of a projective point have gcd `1`. -/
lemma primitiveProjectiveRep_gcd (x : ProjectivePoint n) :
    Finset.univ.gcd (primitiveProjectiveRep x) = 1 :=
  (exists_primitive_projective_rep x).choose_spec.choose_spec.1

/-- The primitive integer representative of `x` spans `x`. -/
lemma primitiveProjectiveRep_mk (x : ProjectivePoint n) :
    Projectivization.mk ℚ (rationalPoint (primitiveProjectiveRep x))
      (rationalPoint_ne_zero (primitiveProjectiveRep_ne_zero x)) = x :=
  (exists_primitive_projective_rep x).choose_spec.choose_spec.2

/-- Distinct projective points have distinct primitive integer representatives. -/
theorem primitiveProjectiveRep_injective :
    Function.Injective (primitiveProjectiveRep (n := n)) := by
  intro x y h
  have hm := Projectivization.mk_eq_mk_iff' ℚ (rationalPoint (primitiveProjectiveRep x))
    (rationalPoint (primitiveProjectiveRep y)) (rationalPoint_ne_zero (primitiveProjectiveRep_ne_zero x))
    (rationalPoint_ne_zero (primitiveProjectiveRep_ne_zero y))
  simpa only [primitiveProjectiveRep_mk] using hm.mpr ⟨1, by simp [h]⟩

private lemma primitiveProjectiveRep_height (x : ProjectivePoint n) :
    x.mulHeight = ((⨆ j, |primitiveProjectiveRep x j| : ℤ) : ℝ) := by
  simpa only [primitiveProjectiveRep_mk] using
    projective_height_primitive _ (primitiveProjectiveRep_ne_zero x) (primitiveProjectiveRep_gcd x)

/-- Some coordinate of the primitive representative attains the projective height. -/
lemma primitiveProjectiveRep_height_eq (x : ProjectivePoint n) :
    ∃ j, |(primitiveProjectiveRep x j : ℝ)| = x.mulHeight := by
  rw [primitiveProjectiveRep_height]
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i => |primitiveProjectiveRep x i|)
  exact ⟨j, by exact_mod_cast hj⟩

/-- Every coordinate of the primitive representative is bounded by the projective height. -/
theorem primitiveProjectiveRep_bound (x : ProjectivePoint n) (i : Fin (n + 1)) :
    |(primitiveProjectiveRep x i : ℝ)| ≤ x.mulHeight := by
  rw [primitiveProjectiveRep_height]
  exact_mod_cast Finite.le_ciSup (fun j => |primitiveProjectiveRep x j|) i

end

/-- Finiteness follows by embedding into the box of bounded primitive representatives. -/
theorem projective_height_finite (n : ℕ) (B : ℝ) :
    {x : ProjectivePoint n | x.mulHeight ≤ B}.Finite :=
  ((integerBox (n + 1) B).finite_toSet.preimage primitiveProjectiveRep_injective.injOn).subset
    fun x hx => mem_integerBox.mpr fun j => (primitiveProjectiveRep_bound x j).trans hx

/-- Projective points, counted once per rational line. -/
def projectivePoints {n : ℕ} (X : Set (ProjectivePoint n)) (B : ℝ) :
    Finset (ProjectivePoint n) := by
  classical
  exact (projective_height_finite n B).toFinset.filter fun x => x ∈ X

/-- The number of points of `X` of multiplicative height at most `B`. -/
def projectiveCount {n : ℕ} (X : Set (ProjectivePoint n)) (B : ℝ) : ℕ :=
  (projectivePoints X B).card

/-- A projective point belongs to `projectivePoints X B` exactly when it lies in `X` and has
height at most `B`. -/
lemma mem_projectivePoints {n : ℕ} {X : Set (ProjectivePoint n)} {B : ℝ}
    {x : ProjectivePoint n} :
    x ∈ projectivePoints X B ↔ x.mulHeight ≤ B ∧ x ∈ X := by
  simp [projectivePoints]

/-- The projective point count is monotone in both the set and the height bound. -/
theorem projectiveCount_mono {n : ℕ} {X Y : Set (ProjectivePoint n)} {B C : ℝ}
    (hXY : X ⊆ Y) (hBC : B ≤ C) : projectiveCount X B ≤ projectiveCount Y C := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hB, hX⟩ := mem_projectivePoints.mp hx
  exact mem_projectivePoints.mpr ⟨hB.trans hBC, hXY hX⟩

/-- By Bézout, an integral vector that is a rational multiple of a primitive
vector is an integer multiple of it. -/
lemma integral_scalar_of_primitive {n : ℕ} {v w : IntPoint n}
    (hv : Finset.univ.gcd v = 1) {c : ℚ} (hw : rationalPoint w = c • rationalPoint v) :
    ∃ k : ℤ, (k : ℚ) = c := by
  obtain ⟨a, ha⟩ := Finset.gcd_eq_sum_mul Finset.univ v
  rw [hv] at ha
  have hq : (∑ j, (v j : ℚ) * a j) = 1 := by exact_mod_cast ha.symm
  have he (j) : (w j : ℚ) = c * v j := congrFun hw j
  refine ⟨∑ j, w j * a j, ?_⟩
  push_cast
  simp_rw [he, mul_assoc, ← Finset.mul_sum, hq, mul_one]

end
end CCDN
