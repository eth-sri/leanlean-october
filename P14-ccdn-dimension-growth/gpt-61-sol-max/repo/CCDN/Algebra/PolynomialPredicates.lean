/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Predicates on polynomials and ideals

Named forms of hypotheses that recur throughout the library: homogeneity of an ideal of a
polynomial ring, absolute irreducibility of a polynomial (irreducibility over `ℚ̄`), and
absolute irreducibility of its top-degree homogeneous part (the hypothesis of CCDN Theorem 4).
All are abbreviations, so proofs may use them as their unfolded statements.
-/

public section

namespace CCDN

open MvPolynomial

variable {σ K : Type*} [CommSemiring K]

/-- An ideal of a polynomial ring is homogeneous when it contains every homogeneous
component of each of its elements. -/
abbrev IsHomogeneousIdeal (I : Ideal (MvPolynomial σ K))  :=
  ∀ f ∈ I, ∀ N, homogeneousComponent N f ∈ I

/-- An integer polynomial is absolutely irreducible when it is irreducible over `ℚ̄`. -/
abbrev AbsolutelyIrreducible (f : MvPolynomial σ ℤ)  :=
  Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f)

/-- A rational polynomial is absolutely irreducible when it is irreducible over `ℚ̄`. -/
abbrev AbsolutelyIrreducibleRat (f : MvPolynomial σ ℚ)  :=
  Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) f)

/-- An integer polynomial is absolutely irreducible exactly when its image over `ℚ` is. -/
theorem absolutelyIrreducibleRat_map_iff (f : MvPolynomial σ ℤ) :
    AbsolutelyIrreducibleRat (CCDN.rationalPolynomial f) ↔ AbsolutelyIrreducible f := by
  rw [AbsolutelyIrreducibleRat, map_map, RingHom.ext_int ((algebraMap ℚ _).comp _)]

/-- The top-degree homogeneous part of an integer polynomial is irreducible over `ℚ̄`. -/
abbrev HasAbsIrreducibleTopForm (f : MvPolynomial σ ℤ)  :=
  AbsolutelyIrreducible (homogeneousComponent f.totalDegree f)

/-- The top-degree homogeneous part of a rational polynomial is irreducible over `ℚ̄`. -/
abbrev HasAbsIrreducibleTopFormRat (f : MvPolynomial σ ℚ)  :=
  AbsolutelyIrreducibleRat (homogeneousComponent f.totalDegree f)

end CCDN
