/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IntegerLinearForms
import CCDN.Algebra.ProjectiveSection
import CCDN.Height.ProjectiveBox
import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Hilbert.LinearProjectionFiltration
import CCDN.Algebra.ProjectiveFiniteFibers
import CCDN.Projection.BoundedDegreeNormalizationFiber
import CCDN.Projection.BoundedIntegerNormalization

/-! The zero-dimensional case of projective dimension growth. A
one-parameter normalization sends every projective point to the unique
point of projective zero-space; its affine fiber bound controls
the whole source, independently of height. -/

namespace CCDN
section
open MvPolynomial Matrix

theorem exists_integer_linear_normalization_of_le (m n : ℕ) (hmn : m + 1 ≤ n)
    (I : Ideal (MvPolynomial (Fin n) ℚ)) [I.IsPrime] (d : ℕ)
    (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ a : Fin (m + 1) → Fin n → ℤ,
      (projectionCoordinateMap I (fun i => integerLinearForm (a i))).IsIntegral ∧
      Function.Injective (projectionCoordinateMap I (fun i => integerLinearForm (a i))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨a, _, hint, hi⟩ := exists_bounded_integer_normalization m k I d hdimdeg
  exact ⟨a, hint, hi⟩

