/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hypersurface.GraphHyperplaneRestriction
import CCDN.Algebra.IntegerPolynomialAvoidance
import CCDN.Hypersurface.EffectiveHyperplaneAvoidance
import CCDN.Hypersurface.GoodHyperplaneReindex

/-! A good integer hyperplane normal of height at most d³, obtained from
the universal Noether detector and integer-grid avoidance. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Full-degree geometrically integral hyperplane restriction, with a cubic
integer normal bound independent of the coefficients and ambient dimension. -/
theorem exists_geometrically_good_hyperplane {n : ℕ}
    (f : MvPolynomial (Option (Fin (3 + n))) ℤ)
    (d : ℕ) (hd : 2 ≤ d) (hf : f.IsHomogeneous d)
    (hir : AbsolutelyIrreducible f) :
    ∃ (D : ℤ) (a : Fin (3 + n) → ℤ),
      D ≠ 0 ∧ |D| ≤ (d ^ 3 : ℕ) ∧ (∀ i, |a i| ≤ (d ^ 3 : ℕ)) ∧
      (graphHyperplaneRestriction (fun i => (a i : ℚ) / D)
        (map (Int.castRingHom ℚ) f)).totalDegree = d ∧
      AbsolutelyIrreducibleRat (graphHyperplaneRestriction (fun i => (a i : ℚ) / D)
        (map (Int.castRingHom ℚ) f)) := by
  let e : Fin (3 + n) ≃ Option (Fin (2 + n)) :=
    (finCongr (by omega)).trans (_root_.finSuccEquiv (2 + n))
  let F := rename (Equiv.optionCongr e) f
  have hFir : AbsolutelyIrreducible F := by
    rw [AbsolutelyIrreducible, map_rename]
    exact (MulEquiv.irreducible_iff
      (f := (renameEquiv (AlgebraicClosure ℚ) (Equiv.optionCongr e)).toMulEquiv)).mpr hir
  obtain ⟨G, hG, hhom, _, hbad⟩ :=
    exists_effective_hyperplane_avoidance F d hd hf.rename_isHomogeneous hFir
  have hd2 : 1 ≤ d ^ 2 := by nlinarith
  have hdeg : G.totalDegree ≤ d ^ 3 := by
    rw [hhom.totalDegree hG]
    have he : d * (d ^ 2 - 1) + d = d ^ 3 := by
      calc d * (d ^ 2 - 1) + d = d * ((d ^ 2 - 1) + 1) := by ring
        _ = d * d ^ 2 := by rw [Nat.sub_add_cancel hd2]
        _ = _ := by ring
    omega
  obtain ⟨v, hv, hvalue⟩ := exists_integer_grid_eval_ne_zero G hG (d ^ 3) hdeg
  let A : Option (Option (Fin (2 + n))) → ℚ := fun i => v i
  have hvalueQ : eval₂ (Int.castRingHom ℚ) A G ≠ 0 := by
    rw [eval₂_eq_eval_map, show eval A (map (Int.castRingHom ℚ) G) = (eval v G : ℚ) from
      (map_eval (Int.castRingHom ℚ) v G).symm]
    exact_mod_cast hvalue
  have hD : v none ≠ 0 := fun hz => hvalueQ (hbad ℚ A fun h => (h (by simp [A, hz])).elim)
  let a := fun i => -v (some i)
  have hα : (fun i => (a i : ℚ) / (v none : ℚ)) = (fun i => -A (some i) / A none) := by
    funext i; simp [a, A]
  have hirA : AbsolutelyIrreducibleRat (graphHyperplaneRestriction
      (fun i => (a i : ℚ) / v none) (map (Int.castRingHom ℚ) F)) := by
    rw [hα]; by_contra hn; exact hvalueQ (hbad ℚ A fun _ => hn)
  have hgood : AbsolutelyIrreducibleRat (graphHyperplaneRestriction
      (fun i => ((a ∘ e) i : ℚ) / v none) (map (Int.castRingHom ℚ) f)) := by
    have he := congrArg (map (algebraMap ℚ (AlgebraicClosure ℚ)))
      (graphHyperplaneRestriction_rename e (fun i => (a i : ℚ) / v none)
        (map (Int.castRingHom ℚ) f))
    rw [map_rename] at he
    apply (MulEquiv.irreducible_iff
      (f := (renameEquiv (AlgebraicClosure ℚ) e).toMulEquiv)).mp
    change Irreducible (rename e (map (algebraMap ℚ (AlgebraicClosure ℚ))
      (graphHyperplaneRestriction ((fun i => (a i : ℚ) / v none) ∘ e)
        (map (Int.castRingHom ℚ) f))))
    rw [he]
    simpa only [AbsolutelyIrreducibleRat, F, map_rename] using hirA
  refine ⟨v none, a ∘ e, hD, by rw [abs_of_nonneg (hv none).1]; exact (hv none).2,
    fun i => by simpa only [a, Function.comp_apply, abs_neg, abs_of_nonneg (hv _).1] using (hv _).2,
    (graphHyperplaneRestriction_homogeneous _ (hf.map (Int.castRingHom ℚ))).totalDegree
      fun hz => hgood.ne_zero (by rw [hz, map_zero]), hgood⟩

end
end CCDN
