/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.HomogeneousMonomials
import CCDN.ForMathlib.MvPolynomial
import CCDN.Noether.EulerClosedFormRank

/-! Canonical monomial coordinates for the d^2-1 Euler parameters and the
coefficient matrix of their closed-form operator. -/

namespace CCDN
noncomputable section
open MvPolynomial Module

section
variable (k : ℕ)

/-- Index set of the bivariate monomials of total degree at most `k`, encoded as multisets of size
`k` in `Option (Fin 2)` (the entry `none` pads the degree up to `k`). -/
abbrev EulerLowIndex := Sym (Option (Fin 2)) k
/-- Index set of the bivariate monomials of total degree exactly `k`, encoded as multisets of size
`k` in `Fin 2`. -/
abbrev EulerTopIndex := Sym (Fin 2) k
/-- Index set of the basis `eulerPairBasis` of `EulerPairSpace R k`: two blocks of monomials of
degree at most `k` and one block of monomials of degree exactly `k`. These index the columns of
the Euler closed-form coefficient matrix. -/
abbrev EulerColumns := EulerLowIndex k ⊕ (EulerLowIndex k ⊕ EulerTopIndex k)

end

section
variable (R : Type*) [CommRing R] (k : ℕ)

/-- The usual monomial basis of the total-degree-at-most space. -/
def eulerLowBasis :
    Basis (EulerLowIndex k) R (restrictTotalDegree (Fin 2) R k) := by
  exact (basisRestrictSupport R {p : Fin 2 →₀ ℕ | p.degree ≤ k}).reindex
    (Finsupp.degreeLeEquivSym (Fin 2) k)

/-- The usual monomial basis of the homogeneous space. -/
def eulerTopBasis :
    Basis (EulerTopIndex k) R (homogeneousSubmodule (Fin 2) R k) := by
  let e : restrictSupport R {p : Fin 2 →₀ ℕ | p.degree = k} ≃ₗ[R]
      homogeneousSubmodule (Fin 2) R k :=
    LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported (Fin 2) R k).symm
  exact ((basisRestrictSupport R {p : Fin 2 →₀ ℕ | p.degree = k}).reindex
    (degreeEqEquivSym (Fin 2) k)).map e

/-- The monomial basis of `EulerPairSpace R k`. Under `eulerPairCoordinates`, every basis vector
is either a single low monomial or one radial syzygy pair (yQ,-xQ); no coefficient-dependent
basis is chosen. -/
def eulerPairBasis :
    Basis (EulerColumns k) R (EulerPairSpace R k) :=
  (eulerLowBasis R k).prod ((eulerLowBasis R k).prod (eulerTopBasis R k))

end

variable (k : ℕ)

/-- There are exactly `(k + 2) ^ 2 - 1` Euler columns. -/
theorem card_eulerColumns : Fintype.card (EulerColumns k) = (k + 2) ^ 2 - 1 := by
  rw [← Module.finrank_eq_card_basis (eulerPairBasis ℚ k), finrank_eulerPairSpace]

/-- The matrix of the Euler closed-form operator of `f` in the basis `eulerPairBasis`. The
equation's coefficients enter the matrix linearly. The column set has cardinality d^2-1, and
rows are ordinary coefficient positions. -/
def eulerClosedFormCoefficientMatrix {R : Type*} [CommRing R]
    (f : Polynomial (Polynomial R)) : Matrix (ℕ × ℕ) (EulerColumns k) R :=
  fun i j => ((eulerClosedFormOperator k f (eulerPairBasis R k j)).coeff i.1).coeff i.2

