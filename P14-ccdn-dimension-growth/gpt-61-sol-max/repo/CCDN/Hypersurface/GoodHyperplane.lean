/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Hypersurface.GraphHyperplaneRestriction
import CCDN.Algebra.IntegerPolynomialAvoidance
import CCDN.Hypersurface.EffectiveHyperplaneAvoidance
import CCDN.Hypersurface.GoodHyperplaneReindex

/-! A good integer hyperplane normal of height at most d³, obtained from
the universal Noether detector and integer-grid avoidance. -/

public section
namespace CCDN
open MvPolynomial

private lemma exists_good_hyperplane_double_option {n : ℕ}
    (f : MvPolynomial (Option (Option (Fin (2 + n)))) ℤ)
    (d : ℕ) (hd : 2 ≤ d) (hf : f.IsHomogeneous d)
    (hir : AbsolutelyIrreducible f) :
    ∃ (D : ℤ) (a : Option (Fin (2 + n)) → ℤ),
      D ≠ 0 ∧ |D| ≤ (d ^ 3) ∧ (∀ i, |a i| ≤ (d ^ 3)) ∧
      AbsolutelyIrreducibleRat (graphHyperplaneRestriction (fun i => (a i : ℚ) / D)
        (CCDN.rationalPolynomial f)) := by
  obtain ⟨G, hG, hhom, hbad⟩ := exists_effective_hyperplane_avoidance f d hd hf hir
  have hd2 : 1 ≤ d ^ 2 := by nlinarith
  have hdeg : G.totalDegree ≤ d ^ 3 := by
    rw [hhom.totalDegree hG]
    have he : d * (d ^ 2 - 1) + d = d ^ 3 := by
      grind [Nat.sub_add_cancel]
    omega
  obtain ⟨v, hv, hvalue⟩ := exists_integer_grid_eval_ne_zero G hG (d ^ 3) hdeg
  let A : Option (Option (Fin (2 + n))) → ℚ := fun i => v i
  have hvalueQ : eval₂ (Int.castRingHom ℚ) A G ≠ 0 := by
    have he : eval₂ (Int.castRingHom ℚ) A G = (eval v G : ℚ) := by
      rw [eval₂_eq_eval_map]
      exact (map_eval (Int.castRingHom ℚ) v G).symm
    rw [he]
    exact_mod_cast hvalue
  have hD : v none ≠ 0 := by
    intro hz
    apply hvalueQ
    exact hbad ℚ A (fun h => (h (by simp [A, hz])).elim)
  have hirA : AbsolutelyIrreducibleRat (graphHyperplaneRestriction
      (fun i => -A (some i) / A none) (CCDN.rationalPolynomial f)) := by
    by_contra hn
    exact hvalueQ (hbad ℚ A (fun _ => hn))
  let a := fun i => -v (some i)
  have hα : (fun i => (a i : ℚ) / (v none : ℚ)) =
      (fun i => -A (some i) / A none) := by
    funext i
    simp [a, A]
  refine ⟨v none, a, hD, ?_, ?_, ?_⟩
  · grind
  · grind
  · rwa [hα]

/-- Full-degree geometrically integral hyperplane restriction, with a cubic
integer normal bound independent of the coefficients and ambient dimension. -/
theorem exists_geometrically_good_hyperplane {n : ℕ}
    (f : MvPolynomial (Option (Fin (3 + n))) ℤ)
    (d : ℕ) (hd : 2 ≤ d) (hf : f.IsHomogeneous d)
    (hir : AbsolutelyIrreducible f) :
    ∃ (D : ℤ) (a : CCDN.IntPoint (3 + n)),
      D ≠ 0 ∧ |D| ≤ (d ^ 3) ∧ (∀ i, |a i| ≤ (d ^ 3)) ∧
      AbsolutelyIrreducibleRat (graphHyperplaneRestriction (fun i => (a i : ℚ) / D)
        (CCDN.rationalPolynomial f)) := by
  let e : Fin (3 + n) ≃ Option (Fin (2 + n)) :=
    (finCongr (by omega)).trans (_root_.finSuccEquiv (2 + n))
  let F := rename (Equiv.optionCongr e) f
  have hFir : AbsolutelyIrreducible F := by
    rw [AbsolutelyIrreducible, map_rename]
    exact (MulEquiv.irreducible_iff (renameEquiv (AlgebraicClosure ℚ) e.optionCongr).toMulEquiv).mpr hir
  obtain ⟨D, a, hD, hDb, hab, hirA⟩ :=
    exists_good_hyperplane_double_option F d hd hf.rename_isHomogeneous hFir
  have hgood : AbsolutelyIrreducibleRat (graphHyperplaneRestriction
      (fun i => ((a ∘ e) i : ℚ) / D) (CCDN.rationalPolynomial f)) := by
    have he := congrArg (map (algebraMap ℚ (AlgebraicClosure ℚ)))
      (graphHyperplaneRestriction_rename e (fun i => (a i : ℚ) / D)
        (CCDN.rationalPolynomial f))
    rw [map_rename] at he
    apply (MulEquiv.irreducible_iff
      (f := (renameEquiv (AlgebraicClosure ℚ) e).toMulEquiv)).mp
    change Irreducible (rename e (map (algebraMap ℚ (AlgebraicClosure ℚ))
      (graphHyperplaneRestriction ((fun i => (a i : ℚ) / D) ∘ e)
        (CCDN.rationalPolynomial f))))
    rw [he]
    simpa only [AbsolutelyIrreducibleRat, F, map_rename] using hirA
  exact ⟨D, a ∘ e, hD, hDb, fun i => hab (e i), hgood⟩

end CCDN
