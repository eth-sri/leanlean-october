/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.CoefficientwiseHomogeneous
import CCDN.Hypersurface.GraphHyperplaneRestriction
import CCDN.Height.ProjectiveZeroLocus
import CCDN.Hypersurface.CoefficientwiseSubstitution

/-! A homogeneous universal hyperplane restriction without denominators.
The normal A cuts out A₀x₀+ΣAᵢxᵢ=0; the chart A₀≠0 is represented by
x₀=−ΣAᵢxᵢ and xᵢ=A₀xᵢ before evaluating a degree-d equation. -/

namespace CCDN
noncomputable section
open MvPolynomial

/-- The universal restriction of an integer polynomial to the hyperplane
`A none * x_none + ∑ A (some j) * x j = 0`, whose normal coefficients `A` are indeterminates,
without denominators: it substitutes `x_none ↦ -∑ A (some j) * x j` and `x j ↦ A none * x j`. -/
def universalHyperplaneRestriction {σ : Type*} [Fintype σ] :
    MvPolynomial (Option σ) ℤ →ₐ[ℤ]
      MvPolynomial σ (MvPolynomial (Option σ) ℤ) :=
  aeval (fun i => Option.elim i
    (-(∑ j, C (X (some j)) * X j)) (fun j => C (X none) * X j))

section
variable {K σ : Type*} [CommRing K] [Fintype σ] (A : Option σ → K)

/-- The restriction of a polynomial to the hyperplane `A none * x_none + ∑ A (some j) * x j = 0`
without denominators, obtained by substituting `x_none ↦ -∑ A (some j) * x j` and
`x j ↦ A none * x j`. -/
def scaledHyperplaneRestriction
    : MvPolynomial (Option σ) K →ₐ[K] MvPolynomial σ K :=
  aeval (fun i => Option.elim i
    (-(∑ j, C (A (some j)) * X j)) (fun j => C (A none) * X j))

/-- Specializing the coefficient indeterminates of the universal hyperplane restriction at a
normal vector `A` gives the scaled hyperplane restriction for `A`. -/
lemma universalHyperplaneRestriction_specialize
    (f : MvPolynomial (Option σ) ℤ) :
    map (eval₂Hom (Int.castRingHom K) A) (universalHyperplaneRestriction f) =
      scaledHyperplaneRestriction A (map (Int.castRingHom K) f) := by
  have he : (map (eval₂Hom (Int.castRingHom K) A)).comp
      (universalHyperplaneRestriction).toRingHom =
      (scaledHyperplaneRestriction A).toRingHom.comp (map (Int.castRingHom K)) := by
    apply MvPolynomial.ringHom_ext
    · simp_all
    · intro i
      cases i <;> simp [universalHyperplaneRestriction, scaledHyperplaneRestriction]
  exact RingHom.congr_fun he f

end

/-- The universal hyperplane restriction of a homogeneous polynomial of degree `d` has
coefficients that are homogeneous of degree `d` in the normal coefficients. -/
lemma universalHyperplaneRestriction_coefficientwiseHomogeneous
    {σ : Type*} [Fintype σ] {d : ℕ} {f : MvPolynomial (Option σ) ℤ}
    (hf : f.IsHomogeneous d) :
    CoefficientwiseHomogeneous (universalHyperplaneRestriction f) d := by
  have hx (i : Option σ) (j : σ) : CoefficientwiseHomogeneous
      (C (X i) * X j : MvPolynomial σ (MvPolynomial (Option σ) ℤ)) 1 := by
    have hh := (CoefficientwiseHomogeneous.C_of_isHomogeneous (isHomogeneous_X ℤ i)).mul
      (CoefficientwiseHomogeneous.map_C (X j : MvPolynomial σ ℤ))
    simpa using hh
  have hg (i : Option σ) : CoefficientwiseHomogeneous
      (Option.elim i (-(∑ j, C (X (some j)) * X j))
        (fun j => C (X none) * X j) :
          MvPolynomial σ (MvPolynomial (Option σ) ℤ)) 1 := by
    cases i with
    | none => exact (CoefficientwiseHomogeneous.sum _ _ _ (fun j _ => hx (some j) j)).neg
    | some j => exact hx none j
  have hc (z : ℤ) : CoefficientwiseHomogeneous
      (C (C z) : MvPolynomial σ (MvPolynomial (Option σ) ℤ)) 0 :=
    CoefficientwiseHomogeneous.C_of_isHomogeneous (isHomogeneous_C _ z)
  have he : algebraMap ℤ (MvPolynomial σ (MvPolynomial (Option σ) ℤ)) = C.comp C := by aesop
  simpa [universalHyperplaneRestriction, aeval_def, coe_eval₂Hom, he, one_mul] using
    CoefficientwiseHomogeneous.eval₂ hf (C.comp C) _ hc hg

variable {K σ : Type*} [Fintype σ]

/-- The scaled hyperplane restriction preserves homogeneity of degree `d`. -/
lemma scaledHyperplaneRestriction_homogeneous
    [CommRing K] (A : Option σ → K)
    {d : ℕ} {f : MvPolynomial (Option σ) K} (hf : f.IsHomogeneous d) :
    (scaledHyperplaneRestriction A f).IsHomogeneous d := by
  have hg (i : Option σ) :
      (Option.elim i (-(∑ j, C (A (some j)) * X j))
        (fun j => C (A none) * X j) : MvPolynomial σ K).IsHomogeneous 1 := by
    cases i with
    | none =>
      exact (IsHomogeneous.sum _ _ _ (fun j _ =>
        (isHomogeneous_X _ j).C_mul (A (some j)))).neg
    | some j => exact (isHomogeneous_X _ j).C_mul (A none)
  simpa [scaledHyperplaneRestriction, one_mul] using hf.aeval _ hg

/-- The scaled hyperplane restriction for the normal vector `(1, -a)` is the restriction to the
graph hyperplane `x_none = ∑ a i * x i`. -/
lemma scaledHyperplaneRestriction_normalized
    [CommRing K] (a : σ → K) (f : MvPolynomial (Option σ) K) :
    scaledHyperplaneRestriction (fun i => Option.elim i 1 (fun j => -a j)) f =
      graphHyperplaneRestriction a f := by
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> simp [scaledHyperplaneRestriction, graphHyperplaneRestriction,
    ← Finset.sum_neg_distrib]

