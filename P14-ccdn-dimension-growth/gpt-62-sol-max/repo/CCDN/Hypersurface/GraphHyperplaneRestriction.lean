/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Plane.SectionBounds
import CCDN.Determinant.PlaneMultiplicity
import CCDN.Plane.FullDegreeSectionIrreducibility
import Mathlib.Algebra.MvPolynomial.Funext

/-! A hyperplane written as x₀ = ∑ aᵢxᵢ. A full-degree
irreducible plane contained in that hyperplane certifies irreducibility
of the entire hyperplane restriction. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The restriction of a polynomial in the coordinates `x_none` and `x i` to the hyperplane
`x_none = ∑ a i * x i`, as a polynomial in the remaining coordinates `x i`. -/
def graphHyperplaneRestriction {K σ : Type*} [CommRing K] [Fintype σ]
    (a : σ → K) : MvPolynomial (Option σ) K →ₐ[K] MvPolynomial σ K :=
  aeval (fun i => Option.elim i (∑ j, C (a j) * X j) X)

section

variable {K σ : Type*}
  [CommRing K]
include K σ

private lemma graphHyperplaneRestriction_X_homogeneous [Fintype σ] (a : σ → K) (i : Option σ) :
    (Option.elim i (∑ j, C (a j) * X j) X).IsHomogeneous 1 := by
  cases i
  · exact IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X K j).C_mul (a j)
  · exact isHomogeneous_X K _

/-- Restriction to a graph hyperplane does not increase the total degree. -/
lemma graphHyperplaneRestriction_totalDegree_le [Fintype σ] (a : σ → K) (f : MvPolynomial (Option σ) K) :
    (graphHyperplaneRestriction a f).totalDegree ≤ f.totalDegree :=
  linear_eval₂_totalDegree_le (.id K) _ (fun i => (graphHyperplaneRestriction_X_homogeneous a i).totalDegree_le) f

/-- Evaluating the restriction of `f` to the hyperplane `x_none = ∑ a j * x j` at `x` is
evaluating `f` at the point of the hyperplane lying over `x`. -/
lemma graphHyperplaneRestriction_eval [Fintype σ]
    (a x : σ → K) (f : MvPolynomial (Option σ) K) :
    eval x (graphHyperplaneRestriction a f) =
      eval (fun i => Option.elim i (∑ j, a j * x j) x) f := by
  change eval x (eval₂ C _ f) = _
  rw [← eval_assoc]
  congr 2
  funext i
  cases i <;> simp

end

/-- Restriction to the graph hyperplane commutes with applying a ring homomorphism `φ` to the
coefficients, the hyperplane coefficients `a` being mapped by `φ` as well. -/
lemma graphHyperplaneRestriction_map {K L σ : Type*}
    [CommRing K] [CommRing L] [Fintype σ]
    (φ : K →+* L) (a : σ → K) (f : MvPolynomial (Option σ) K) :
    map φ (graphHyperplaneRestriction a f) =
      graphHyperplaneRestriction (φ ∘ a) (map φ f) := by
  change map φ (eval₂ C _ f) = eval₂ C _ (map φ f)
  rw [map_eval₂]
  congr 1
  funext i
  cases i <;> simp

section

variable {K σ : Type*}
include K σ

/-- Restriction to a graph hyperplane commutes with taking the homogeneous component of
degree `d`. -/
lemma graphHyperplaneRestriction_homogeneousComponent
    [CommRing K] [Fintype σ] (a : σ → K)
    (f : MvPolynomial (Option σ) K) (d : ℕ) :
    graphHyperplaneRestriction a (homogeneousComponent d f) =
      homogeneousComponent d (graphHyperplaneRestriction a f) := by
  exact (homogeneousComponent_aeval_linear _ (graphHyperplaneRestriction_X_homogeneous a) d f).symm

private lemma planeSectionPolynomial_eval [CommRing K]
    (f : MvPolynomial σ K) (v : PlaneParameters σ → K) (t : Fin 2 → K) :
    eval t (planeSectionPolynomial f v) =
      eval (fun i => v (i, 0) + v (i, 1) * t 0 + v (i, 2) * t 1) f := by
  rw [← bivariateEval_equiv, planeSectionPolynomial, AlgEquiv.apply_symm_apply]
  exact universalPlaneSection_eval f v (t 0) (t 1)

private lemma graphHyperplaneRestriction_planeSection
    [Field K] [Infinite K] [Fintype σ]
    (a : σ → K) (v : PlaneParameters (Option σ) → K)
    (hv : ∀ j : Fin 3, v (none, j) = ∑ i, a i * v (some i, j))
    (f : MvPolynomial (Option σ) K) :
    planeSectionPolynomial (graphHyperplaneRestriction a f) (fun p => v (some p.1, p.2)) =
      planeSectionPolynomial f v := by
  apply MvPolynomial.funext
  intro t
  rw [planeSectionPolynomial_eval, graphHyperplaneRestriction_eval, planeSectionPolynomial_eval]
  apply congrArg (fun z : Option σ → K => eval z f)
  funext i
  cases i with
  | none => simp [hv, mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
  | some i => rfl

/-- Full degree and irreducibility of a concrete contained plane force both
properties for the containing hyperplane. -/
theorem graphHyperplaneRestriction_irreducible_of_plane [Field K] [Infinite K] [Fintype σ]
    (f : MvPolynomial (Option σ) K) (a : σ → K)
    (v : PlaneParameters (Option σ) → K)
    (hv : ∀ j : Fin 3, v (none, j) = ∑ i, a i * v (some i, j))
    (hir : Irreducible (universalPlaneSection f v))
    (hdegree : bivariateTotalDegree (universalPlaneSection f v) = f.totalDegree) :
    (graphHyperplaneRestriction a f).totalDegree = f.totalDegree ∧
      Irreducible (graphHyperplaneRestriction a f) := by
  let w : PlaneParameters σ → K := fun p => v (some p.1, p.2)
  have he := graphHyperplaneRestriction_planeSection a v hv f
  have hfull : (graphHyperplaneRestriction a f).totalDegree = f.totalDegree := by
    apply le_antisymm (graphHyperplaneRestriction_totalDegree_le a f)
    have hh := planeSectionPolynomial_totalDegree (graphHyperplaneRestriction a f) w
    rw [show w = (fun p => v (some p.1, p.2)) from rfl, he] at hh
    exact hdegree ▸ hh
  refine ⟨hfull, ?_⟩
  apply irreducible_of_full_degree_map (planeSectionPolynomialHom w)
    (fun g => planeSectionPolynomial_totalDegree g w)
  · change Irreducible (planeSectionPolynomial (graphHyperplaneRestriction a f) w)
    rw [show w = (fun p => v (some p.1, p.2)) from rfl, he]
    exact (MulEquiv.irreducible_iff (bivariatePolynomialEquiv K).symm).mpr hir
  · change (planeSectionPolynomial (graphHyperplaneRestriction a f) w).totalDegree =
      (graphHyperplaneRestriction a f).totalDegree
    aesop

end

end
end CCDN
