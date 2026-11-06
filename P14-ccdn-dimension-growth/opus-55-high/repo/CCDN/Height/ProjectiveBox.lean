/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Height.Box
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization

/-! Rational projective points with the multiplicative height used by CCDN.
Bounded-height sets are finite, and primitive integral coordinates recover
the paper's maximum-coordinate height. -/

namespace CCDN
noncomputable section

/-- Rational points of projective `n`-space, as lines in `ℚ^(n+1)`. -/
abbrev ProjectivePoint (n : ℕ) := Projectivization ℚ (Fin (n + 1) → ℚ)

section
variable {n : ℕ} (x : ProjectivePoint n)

/-- The multiplicative height of the chosen representative of a projective point equals the
height of the point. -/
lemma projective_rep_height :
    Height.mulHeight x.rep = x.mulHeight := by
  rw [← Projectivization.mulHeight_mk x.rep_nonzero, x.mk_rep]

/-- Every coordinate ratio has height bounded by the projective height. -/
lemma projective_coordinate_ratio_height
    (i j : Fin (n + 1)) :
    Height.mulHeight₁ (x.rep j / x.rep i) ≤ x.mulHeight := by
  rw [Height.mulHeight₁_div_eq_mulHeight]
  have h := Height.mulHeight_comp_le (![j, i] : Fin 2 → Fin (n + 1)) x.rep
  have he : x.rep ∘ ![j, i] = ![x.rep j, x.rep i] := by
    funext k
    fin_cases k <;> rfl
  rwa [he, projective_rep_height] at h

end

section
/-- Northcott finiteness in rational projective space, proved using affine charts. -/
theorem projective_height_finite (n : ℕ) (B : ℝ) :
    {x : ProjectivePoint n | x.mulHeight ≤ B}.Finite := by
  have hv : {v : Fin (n + 1) → ℚ | ∀ j, Height.mulHeight₁ (v j) ≤ B}.Finite :=
    Set.Finite.pi' fun _ => Northcott.finite_le B
  have hs : {v : {v : Fin (n + 1) → ℚ // v ≠ 0} |
      ∀ j, Height.mulHeight₁ (v.val j) ≤ B}.Finite :=
    hv.preimage Subtype.val_injective.injOn
  apply (hs.image (Projectivization.mk' ℚ)).subset
  intro x hx
  obtain ⟨i, hi⟩ := Function.ne_iff.mp x.rep_nonzero
  change x.rep i ≠ 0 at hi
  let v : Fin (n + 1) → ℚ := fun j => x.rep j / x.rep i
  have hv0 : v ≠ 0 := by
    intro h
    have := congrFun h i
    simp [v, hi] at this
  refine ⟨⟨v, hv0⟩, fun j => (projective_coordinate_ratio_height x i j).trans hx, ?_⟩
  rw [Projectivization.mk'_eq_mk, ← x.mk_rep, Projectivization.mk_eq_mk_iff']
  refine ⟨(x.rep i)⁻¹, ?_⟩
  funext j
  simp [v, div_eq_mul_inv, mul_comm]

variable {n : ℕ} (X : Set (ProjectivePoint n)) (B : ℝ)

/-- Projective points, counted once per rational line. -/
def projectivePoints :
    Finset (ProjectivePoint n) := by
  classical
  exact (projective_height_finite n B).toFinset.filter fun x => x ∈ X

/-- The number of points of `X` of multiplicative height at most `B`. -/
def projectiveCount : ℕ :=
  (projectivePoints X B).card

end

variable {n : ℕ}

/-- A projective point belongs to `projectivePoints X B` exactly when it lies in `X` and has
height at most `B`. -/
lemma mem_projectivePoints {X : Set (ProjectivePoint n)} {B : ℝ}
    {x : ProjectivePoint n} :
    x ∈ projectivePoints X B ↔ x.mulHeight ≤ B ∧ x ∈ X := by
  classical
  simp [projectivePoints]

/-- The projective point count is monotone in both the set and the height bound. -/
theorem projectiveCount_mono {X Y : Set (ProjectivePoint n)} {B C : ℝ}
    (hXY : X ⊆ Y) (hBC : B ≤ C) : projectiveCount X B ≤ projectiveCount Y C := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hB, hX⟩ := mem_projectivePoints.mp hx
  exact mem_projectivePoints.mpr ⟨hB.trans hBC, hXY hX⟩

/-- A nonzero integer point remains nonzero as a rational point. -/
lemma rationalPoint_ne_zero {x : IntPoint n} (hx : x ≠ 0) :
    rationalPoint x ≠ 0 := by
  intro h
  apply hx
  funext i
  have hi := congrFun h i
  change (x i : ℚ) = 0 at hi
  exact_mod_cast hi

/-- The chosen projective height is exactly CCDN's height on primitive coordinates. -/
theorem projective_height_primitive (x : IntPoint (n + 1)) (hx : x ≠ 0)
    (hprimitive : Finset.univ.gcd x = 1) :
    (Projectivization.mk ℚ (rationalPoint x) (rationalPoint_ne_zero hx)).mulHeight =
      ((⨆ i, |x i| : ℤ) : ℝ) := by
  rw [Projectivization.mulHeight_mk]
  exact Rat.mulHeight_eq_max_abs_of_gcd_eq_one hprimitive

