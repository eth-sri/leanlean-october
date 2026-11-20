/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousChart
public import CCDN.Algebra.HomogeneousTranslation
public import CCDN.Algebra.OriginShift

/-! The affine translations underlying the homogeneous coordinate changes
preserve degree and irreducibility, over every coefficient field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The translation `X j ↦ X j + a j` of polynomials in `Fin n` variables, as an algebra
automorphism over `R`. -/
def affineTranslation (R : Type*) [CommRing R] {n : ℕ} (a : Fin n → R) :
    MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R :=
  originShiftEquiv a

/-- An affine translation of variables preserves and reflects irreducibility. -/
lemma affineTranslation_irreducible_iff {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    Irreducible (affineTranslation R a f) ↔ Irreducible f :=
  MulEquiv.irreducible_iff (f := affineTranslation R a)

section

variable {R : Type*} [CommRing R] {n : ℕ}
  (a : Fin n → R) (f : MvPolynomial (Fin n) R)
include R n a f

/-- An affine translation of variables does not increase the total degree. -/
lemma affineTranslation_totalDegree_le :
    (affineTranslation R a f).totalDegree ≤ f.totalDegree :=
  originShift_totalDegree_le a f

/-- An affine translation of variables preserves the total degree over a nontrivial ring. -/
lemma affineTranslation_totalDegree :
    (affineTranslation R a f).totalDegree = f.totalDegree := by
  apply le_antisymm (affineTranslation_totalDegree_le a f)
  have hh := affineTranslation_totalDegree_le (-a) (affineTranslation R a f)
  have he : affineTranslation R (-a) (affineTranslation R a f) = f :=
    (affineTranslation R a).symm_apply_apply f
  simp_all

end

/-- Affine translation preserves the top-degree form. -/
theorem affineTranslation_leading_homogeneousComponent {R : Type*}
    [CommRing R] [IsDomain R] {n : ℕ} (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    homogeneousComponent (affineTranslation R a f).totalDegree (affineTranslation R a f) =
      homogeneousComponent f.totalDegree f := by
  rw [affineTranslation_totalDegree]
  exact homogeneousComponent_originShift_of_le a f _ le_rfl

/-- Affine translation commutes with mapping coefficients along a ring homomorphism `φ`, the
translation vector being mapped by `φ` as well. -/
lemma affineTranslation_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    MvPolynomial.map φ (affineTranslation R a f) =
      affineTranslation S (φ ∘ a) (MvPolynomial.map φ f) :=
  originShift_map φ a f

end
end CCDN
