/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.AffineTranslation
public import CCDN.Algebra.HomogeneousSlice
import CCDN.AuxiliaryPolynomial.AffineTranslationCount
import CCDN.Height.MultivariateGridHeight

/-! Translation preserves the leading homogeneous equation exactly. Bounded
integer translations make the constant coefficient nonzero in every dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}

private lemma scaledHomogenize_one_affineTranslation [Nontrivial R]
    {n d : ℕ} (a : Fin n → R) (f : MvPolynomial (Fin n) R) (hd : f.totalDegree ≤ d) :
    scaledHomogenize d 1 (affineTranslation R a f) =
      homogeneousTranslation R a (scaledHomogenize d 1 f) := by
  have ht : (affineTranslation R a f).totalDegree ≤ d := by
    rwa [affineTranslation_totalDegree]
  apply affineChart_injective_on_homogeneous
    (scaledHomogenize_homogeneous _ _ ht)
    (homogeneousTranslation_homogeneous _ (scaledHomogenize_homogeneous _ _ hd))
  rw [affineChart_scaledHomogenize_one, affineChart_homogeneousTranslation,
    affineChart_scaledHomogenize_one]

private lemma homogeneousSlice_zero_translation
    (a : Fin n → R) (f : MvPolynomial (Fin (n + 1)) R) :
    homogeneousSlice n 0 (homogeneousTranslation R a f) = homogeneousSlice n 0 f := by
  have he : (homogeneousSlice n (0 : R)).comp (homogeneousTranslation R a).toRingHom =
      homogeneousSlice n 0 := by
    apply MvPolynomial.ringHom_ext
    · simp [homogeneousSlice, homogeneousTranslation, homogeneousTranslationHom]
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j <;>
        simp [homogeneousSlice, homogeneousTranslation, homogeneousTranslationHom]
  exact RingHom.congr_fun he f

private lemma homogeneousSlice_zero_scaledHomogenize_one {d : ℕ} (f : MvPolynomial (Fin n) R) (hd : f.totalDegree ≤ d) :
    homogeneousSlice n 0 (scaledHomogenize d 1 f) = homogeneousComponent d f := by
  classical
  rw [scaledHomogenize, map_sum]
  conv_rhs => rw [f.as_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [homogeneousSlice_monomial, chartExponent_homogenizedExponent]
  by_cases he : m.sum (fun _ e => e) = d
  simp [homogeneousComponent_eq_self (isHomogeneous_monomial _ he), homogenizedExponent, he]
  · have hlt := lt_of_le_of_ne ((le_totalDegree hm).trans hd) he
    simp [homogeneousComponent_eq_zero d _ ((totalDegree_monomial_le m _).trans_lt hlt), homogenizedExponent, Nat.sub_ne_zero_of_lt hlt]

/-- Affine translation of the variables does not change the leading form: the top-degree
homogeneous component of `affineTranslation R a f` equals that of `f`. -/
theorem affineTranslation_leading_homogeneousComponent [Nontrivial R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    homogeneousComponent (affineTranslation R a f).totalDegree (affineTranslation R a f) =
      homogeneousComponent f.totalDegree f := by
  simp [affineTranslation_totalDegree, ← homogeneousSlice_zero_scaledHomogenize_one _ (affineTranslation_totalDegree_le a f), scaledHomogenize_one_affineTranslation a f le_rfl, homogeneousSlice_zero_translation, homogeneousSlice_zero_scaledHomogenize_one f le_rfl]

end
end CCDN
