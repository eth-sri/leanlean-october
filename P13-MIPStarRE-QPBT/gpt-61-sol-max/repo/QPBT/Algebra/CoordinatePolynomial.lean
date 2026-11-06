module

public import Mathlib.Algebra.MvPolynomial.Basic

/-! Multivariate polynomials with a finite coordinate index. -/

@[expose] public section

abbrev MIPStarRE.QPBT.CoordinatePolynomial (n : ℕ) (R : Type*) [CommSemiring R] := MvPolynomial (Fin n) R
