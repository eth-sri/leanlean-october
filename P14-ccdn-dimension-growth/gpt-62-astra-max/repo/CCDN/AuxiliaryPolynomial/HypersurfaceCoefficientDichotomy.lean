/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.AuxiliaryPolynomial.Nonmultiple
public import CCDN.Height.IntegerCoefficientHeight
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CCDN.Determinant.HomogeneousDeterminantComparison

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A quantitative coefficient-height dichotomy on the complete bounded
projective zero set. The height branch has log(H)<=N log(N)+d N log(B). -/
theorem projective_coefficient_height_dichotomy {n d : ℕ}
    (f : IntegerPolynomial (n + 1)) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    {B : ℝ} (hB : 1 ≤ B) :
    Real.log (integerCoefficientHeight f : ℝ) ≤
      ((n + d).choose d : ℝ) * Real.log ((n + d).choose d) +
        ((n + d).choose d : ℝ) * d * Real.log B ∨
    ∃ g, IsProjectiveAuxiliary f g d B := by
  classical
  let e := (Fintype.equivFin (projectivePoints (projectiveZeroLocus (rationalEquation f)) B)).symm
  let z := fun i => primitiveProjectiveRep (e i).val
  have hz (i)  :=
    (mem_integer_projectiveZeroLocus hf _).mp (mem_projectivePoints.mp (e i).property).2
  have hbox (i j)  :=
    (primitiveProjectiveRep_bound _ j).trans (mem_projectivePoints.mp (e i).property).1
  by_cases hrel : ∀ g : IntegerPolynomial _, g.IsHomogeneous d →
      (∀ i, eval (z i) g = 0) → f ∣ g
  exact Or.inl (by apply homogeneous_no_auxiliary_coefficient_height <;> assumption)
  · right
    push Not at hrel
    obtain ⟨g, hgh, hgz, hgnd⟩ := hrel
    refine ⟨g, fun h => hgnd (by simp [h]), hgh, ?_, hgnd⟩
    intro x hxB hxf
    obtain ⟨i, hi⟩ := e.surjective ⟨x, mem_projectivePoints.mpr ⟨hxB, hxf⟩⟩
    have hh := hgz i
    dsimp only [z] at hh
    rw [hi] at hh
    exact (mem_integer_projectiveZeroLocus hgh x).mpr hh

end
end CCDN
