/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

import Mathlib

public import ArithmeticHeights.RowSpace
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# The Cauchy–Binet identity

The product of a matrix with the transpose of another is a determinant that the maximal minors
compute: `det (A Bᵀ) = ∑ₛ det Aₛ · det Bₛ`, the sum over the sets `s` of `m` columns. Taking
`B = A` turns the sum of squares of the maximal minors into the **Gram determinant** `det (A Aᵀ)`
of the rows, and taking `B = conj A` turns the sum of their squared absolute values into
`det (A Aᴴ)`. Those two are the archimedean local factors of the Arakelov height of the tuple of
minors — of the row space, by Layer 3.3 — and they are where the `√|det (A Aᵀ)|` of the
Bombieri–Vaaler bound comes from.

Everything here is proved once, over an arbitrary commutative ring, for the Plücker coordinates of
Layer 3.1; the matrix statements are that identity read through Layer 3.3's dictionary.

## Main results

* `exteriorPower.sum_plucker_mul_plucker`: the identity itself, for two families of vectors —
  `∑ₛ plucker k v s * plucker k w s` is the determinant of the matrix of dot products `v i ⬝ᵥ w j`.
* `Matrix.det_mul_eq_sum_plucker` and `Matrix.det_mul_transpose_eq_sum_plucker`, with
  `Matrix.det_mul_eq_sum_det_submatrix` and `Matrix.det_mul_transpose_eq_sum_det_submatrix`
  spelling the same statements with `Matrix.submatrix` and `Finset.orderEmbOfFin`.
* `Matrix.det_mul_transpose_self_eq_sum_sq`: the **real** specialization, `det (A Aᵀ)` is the sum of
  the squares of the maximal minors, over any commutative ring.
* `Matrix.det_mul_conjTranspose_self_eq_sum`: the **complex** specialization, over a commutative
  star ring, with `Matrix.det_mul_conjTranspose_self_eq_sum_sq_norm` its `RCLike` form
  `det (A Aᴴ) = ∑ₛ ‖det Aₛ‖²` and
  `NumberField.InfinitePlace.det_map_embedding_mul_conjTranspose_self` its form at an infinite
  place of a number field, which is the local factor named above.
* `Matrix.det_mul_transpose_self_eq_zero_iff` and
  `Matrix.linearIndependent_row_iff_det_mul_transpose_self_ne_zero`: over an ordered field the Gram
  determinant of the rows detects full row rank, the Gram criterion.
* `exteriorPower.plucker_map`: the Plücker coordinates commute with a ring homomorphism, which is
  what carries the identity to a completion or an embedding.

## Implementation notes

The proof is Mathlib's pairing `exteriorPower.pairingDual` between `⋀ⁿ (Dual R M)` and `⋀ⁿ M`,
evaluated on the image of a wedge under `exteriorPower.map n (Pi.basisFun R ι).toDual`. Read on the
induced basis of the exterior power that composite is the diagonal bilinear form
`∑ₛ xₛ yₛ`, because `Basis.toDual` sends the standard basis to the dual basis and
`exteriorPower.ιMultiDual` — the coordinate functional of Layer 3.1's basis — is *by definition*
the pairing against the wedge of dual basis vectors; read on wedges it is a determinant of
dot products, by `exteriorPower.pairingDual_ιMulti_ιMulti`. So the identity is the statement that
one bilinear form has two descriptions, and no expansion of a determinant over permutations is
carried out anywhere.

Mathlib's `LinearMap.BilinForm.exteriorPower` is that same composite and would be the natural name
for it. What is missing is its defining equation: `LinearMap.BilinForm.bilinForm_ιMulti_ιMulti`,
which evaluates the form on two wedges as a determinant, carries no `public` in a module that has
no `public section`, so it is invisible outside its own file and every user has to re-prove it.
That proof is exactly the content of the identity below, so the composite is written out here.

`Pi.basisFun_toDual_apply`, that `Basis.toDual` of the standard basis is the dot product, is
stated here because Mathlib has `Basis.toDual_apply_left` only for a basis vector in the second
argument.

## References

A. L. Cauchy (1812) and J. P. M. Binet (1812); the identity is Proposition 2.8.8 of
E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
and §2 Lemma 1 of W. M. Schmidt, "On heights of algebraic subspaces and diophantine
approximations", *Annals of Mathematics* **85** (1967), 430–472. It enters the Siegel-lemma
literature as equation (2.4)(iv) of E. Bombieri and J. Vaaler, "On Siegel's lemma",
*Inventiones Mathematicae* **73** (1983), 11–32, whose bound is stated in terms of
`√|det (A Aᵀ)|`.

This is Layer 3.4 of the `ArithmeticHeights` roadmap.
-/

public section

namespace exteriorPower

open Matrix Module

/-!
### The identity in Plücker coordinates
-/

section Dual

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The dual map of the standard basis is the dot product.** Mathlib's `Basis.toDual_apply_left`
evaluates `b.toDual x` on a basis vector; for the standard basis of `ι → R` the value on an
arbitrary vector is the dot product. -/
theorem _root_.Pi.basisFun_toDual_apply (x y : ι → R) :
    (Pi.basisFun R ι).toDual x y = x ⬝ᵥ y := by
  conv_lhs => rw [← (Pi.basisFun R ι).sum_repr y]
  rw [map_sum]
  simp only [map_smul, Basis.toDual_apply_left, Pi.basisFun_repr, smul_eq_mul, dotProduct]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

end Dual

section Basis

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] [LinearOrder ι]

/-- The pairing against the image of a basis vector of `⋀^k (ι → R)` reads off a coordinate: this
is `exteriorPower.ιMultiDual` unfolded, since that functional is *defined* as the pairing against
the wedge of the dual basis vectors indexed by `s`. -/
private lemma pairingDual_map_toDual_basis (k : ℕ) (s : Set.powersetCard ι k)
    (y : ⋀[R]^k (ι → R)) :
    pairingDual R (ι → R) k
        (map k (Pi.basisFun R ι).toDual ((Pi.basisFun R ι).exteriorPower k s)) y
      = ((Pi.basisFun R ι).exteriorPower k).repr y s := by
  rw [basis_apply, map_apply_ιMulti_family,
    show (Pi.basisFun R ι).toDual ∘ (Pi.basisFun R ι) = (Pi.basisFun R ι).coord from
      funext fun i ↦ Basis.coe_toDual_self _ i, basis_repr_apply]
  rfl

end Basis

section CauchyBinet

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}

/-- On the basis of `⋀^k (ι → R)` induced by the standard basis, the bilinear form obtained by
pairing along `Basis.toDual` is the diagonal one. -/
private lemma pairingDual_map_toDual (k : ℕ) (x y : ⋀[R]^k (ι → R)) :
    pairingDual R (ι → R) k (map k (Pi.basisFun R ι).toDual x) y
      = ∑ s : Set.powersetCard ι k, ((Pi.basisFun R ι).exteriorPower k).repr x s *
          ((Pi.basisFun R ι).exteriorPower k).repr y s := by
  conv_lhs => rw [← ((Pi.basisFun R ι).exteriorPower k).sum_repr x]
  rw [map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [map_smul, map_smul, LinearMap.smul_apply, pairingDual_map_toDual_basis, smul_eq_mul]

/-- **The Cauchy–Binet identity.** The sum over the `k`-element sets of columns of the product of
the two Plücker coordinates is the determinant of the `k × k` matrix of dot products. Over any
commutative ring, and with no hypothesis on either family. -/
theorem sum_plucker_mul_plucker (k : ℕ) (v w : Fin k → (ι → R)) :
    ∑ s : Set.powersetCard ι k, plucker k v s * plucker k w s
      = (Matrix.of fun i j ↦ v i ⬝ᵥ w j).det := by
  have h := pairingDual_map_toDual k (ιMulti R k v) (ιMulti R k w)
  rw [map_apply_ιMulti, pairingDual_ιMulti_ιMulti] at h
  simp only [plucker, Basis.equivFun_apply]
  rw [← h]
  simp only [Function.comp_apply, Pi.basisFun_toDual_apply]
  rw [← Matrix.det_transpose (Matrix.of fun i j ↦ v i ⬝ᵥ w j)]
  rfl

/-- **The Plücker coordinates commute with a ring homomorphism**, each being a determinant. This is
what carries the identity along an embedding of a number field into `ℂ`. -/
theorem plucker_map {S : Type*} [CommRing S] (f : R →+* S) (k : ℕ) (v : Fin k → (ι → R))
    (s : Set.powersetCard ι k) : plucker k (fun i ↦ f ∘ v i) s = f (plucker k v s) := by
  rw [plucker_apply, plucker_apply, RingHom.map_det]
  rfl

end CauchyBinet

end exteriorPower

namespace Matrix

open _root_.Module exteriorPower

/-!
### The identity for matrices
-/

section CauchyBinet

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

/-- The Plücker coordinates of the rows commute with a ring homomorphism applied entrywise. -/
theorem plucker_row_map {S : Type*} [CommRing S] (f : R →+* S) (A : Matrix (Fin m) ι R)
    (s : Set.powersetCard ι m) : plucker m (A.map f).row s = f (plucker m A.row s) :=
  plucker_map f m A.row s

/-- **The Cauchy–Binet identity**, for `A Bᵀ`: the determinant of the matrix of dot products of the
rows of `A` with the rows of `B` is the sum over the sets of `m` columns of the products of
corresponding maximal minors. -/
theorem det_mul_transpose_eq_sum_plucker (A B : Matrix (Fin m) ι R) :
    (A * Bᵀ).det = ∑ s : Set.powersetCard ι m, plucker m A.row s * plucker m B.row s :=
  (sum_plucker_mul_plucker m A.row B.row).symm

variable (A : Matrix (Fin m) ι R) (B : Matrix ι (Fin m) R)

/-- **The Cauchy–Binet identity**, for a product `A B` of an `m × ι` by an `ι × m` matrix: the
determinant is the sum over the sets of `m` indices of the product of the maximal minor of `A` on
those columns with the maximal minor of `B` on those rows. -/
theorem det_mul_eq_sum_plucker  :
    (A * B).det = ∑ s : Set.powersetCard ι m, plucker m A.row s * plucker m B.col s := by
  conv_lhs => rw [← Matrix.transpose_transpose B]
  exact (sum_plucker_mul_plucker m A.row Bᵀ.row).symm

/-- The Cauchy–Binet identity for `A B` in the `submatrix` spelling: the maximal minors of `A` on
the columns of `s` against those of `B` on the rows of `s`. -/
theorem det_mul_eq_sum_det_submatrix  :
    (A * B).det = ∑ s : Set.powersetCard ι m,
      (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det *
        (B.submatrix ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s)) id).det := by
  rw [det_mul_eq_sum_plucker]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [plucker_row_eq_det_submatrix, show B.col = Bᵀ.row from rfl, plucker_row_eq_det_submatrix,
    ← Matrix.det_transpose (B.submatrix _ id), Matrix.transpose_submatrix]

end CauchyBinet

/-!
### The Gram determinant of the rows
-/

section Gram

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

/-- **The archimedean specialization at a real place.** The Gram determinant of the rows is the sum
of the squares of the maximal minors. This is the `√|det (A Aᵀ)|` of the Bombieri–Vaaler bound:
its square is the ℓ² local factor of the tuple of minors. -/
theorem det_mul_transpose_self_eq_sum_sq (A : Matrix (Fin m) ι R) :
    (A * Aᵀ).det = ∑ s : Set.powersetCard ι m, plucker m A.row s ^ 2 := by
  grind [det_mul_transpose_eq_sum_plucker]



end Gram

/-!
### The Gram determinant at a complex place
-/





end Matrix

namespace NumberField.InfinitePlace

open Matrix exteriorPower


end NumberField.InfinitePlace

section Examples

open Matrix exteriorPower

end Examples

end
