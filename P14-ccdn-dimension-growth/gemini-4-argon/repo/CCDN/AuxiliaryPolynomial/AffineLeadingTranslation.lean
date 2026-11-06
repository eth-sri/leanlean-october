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

/-- Affine translation of the variables does not change the leading form: the top-degree
homogeneous component of `affineTranslation R a f` equals that of `f`. -/
theorem affineTranslation_leading_homogeneousComponent {R : Type*}
    [CommRing R] [Nontrivial R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    homogeneousComponent (affineTranslation R a f).totalDegree (affineTranslation R a f) =
      homogeneousComponent f.totalDegree f := by
  classical
  let d := f.totalDegree
  have hslice (g : MvPolynomial (Fin n) R) (hd : g.totalDegree ≤ d) :
      homogeneousSlice n 0 (scaledHomogenize d 1 g) = homogeneousComponent d g := by
    rw [scaledHomogenize, map_sum]
    conv_rhs => rw [g.as_sum, map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [homogeneousSlice_monomial, chartExponent_homogenizedExponent]
    have hmd : m.sum (fun _ e => e) ≤ d := (le_totalDegree hm).trans hd
    by_cases he : m.sum (fun _ e => e) = d
    · rw [homogeneousComponent_eq_self (isHomogeneous_monomial (g.coeff m) he)]
      simp [homogenizedExponent, he]
    · have hlt : m.sum (fun _ e => e) < d := lt_of_le_of_ne hmd he
      rw [homogeneousComponent_eq_zero d _ ((totalDegree_monomial_le m (g.coeff m)).trans_lt hlt)]
      simp [homogenizedExponent, Nat.sub_ne_zero_of_lt hlt]
  have htr : scaledHomogenize d 1 (affineTranslation R a f) =
      homogeneousTranslation R a (scaledHomogenize d 1 f) := by
    apply affineChart_injective_on_homogeneous
      (scaledHomogenize_homogeneous _ _ (affineTranslation_totalDegree_le a f))
      (homogeneousTranslation_homogeneous _ (scaledHomogenize_homogeneous _ _ le_rfl))
    rw [affineChart_scaledHomogenize_one, affineChart_homogeneousTranslation,
      affineChart_scaledHomogenize_one]
  have hsl_tr : homogeneousSlice n 0 (homogeneousTranslation R a (scaledHomogenize d 1 f)) =
      homogeneousSlice n 0 (scaledHomogenize d 1 f) := by
    have he : (homogeneousSlice n (0 : R)).comp (homogeneousTranslation R a).toRingHom =
        homogeneousSlice n 0 := by
      apply MvPolynomial.ringHom_ext
      · intro c; simp [homogeneousSlice, homogeneousTranslation, homogeneousTranslationHom]
      · intro j; refine Fin.cases ?_ (fun k => ?_) j <;>
          simp [homogeneousSlice, homogeneousTranslation, homogeneousTranslationHom]
    exact RingHom.congr_fun he _
  rw [affineTranslation_totalDegree, ← hslice _ (affineTranslation_totalDegree_le a f),
    htr, hsl_tr, hslice f le_rfl]

/-- A nonzero integral polynomial `f` in `n` variables has an integral translate with nonzero
constant coefficient by a vector whose entries lie in `[0, deg f]`. -/
theorem exists_bounded_affine_translation_nonzero_constant {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) :
    ∃ a : Fin n → ℤ, (∀ j, 0 ≤ a j ∧ a j ≤ f.totalDegree) ∧
      (affineTranslation ℤ a f).coeff 0 ≠ 0 := by
  obtain ⟨a, ha, he, _⟩ := exists_integer_multivariate_grid_height_witness f hf le_rfl
  exact ⟨a, ha, by rwa [affineTranslation_constantCoeff]⟩

end
end CCDN
