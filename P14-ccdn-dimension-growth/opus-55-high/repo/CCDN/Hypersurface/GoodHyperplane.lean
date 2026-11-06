/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hypersurface.GraphHyperplaneRestriction
import CCDN.Algebra.IntegerPolynomialAvoidance
import CCDN.Hypersurface.EffectiveHyperplaneAvoidance
import CCDN.Hypersurface.GoodHyperplaneReindex

/-! A good integer hyperplane normal of height at most d³, obtained from
the universal Noether detector and integer-grid avoidance. -/

namespace CCDN
section
open MvPolynomial

variable {n : ℕ}

/-- Full-degree geometrically integral hyperplane restriction, with a cubic
integer normal bound independent of the coefficients and ambient dimension. -/
theorem exists_geometrically_good_hyperplane
    (f : MvPolynomial (Option (Fin (3 + n))) ℤ)
    (d : ℕ) (hd : 2 ≤ d) (hf : f.IsHomogeneous d)
    (hir : AbsolutelyIrreducible f) :
    ∃ (D : ℤ) (a : Fin (3 + n) → ℤ),
      D ≠ 0 ∧ |D| ≤ (d ^ 3 : ℕ) ∧ (∀ i, |a i| ≤ (d ^ 3 : ℕ)) ∧
      AbsolutelyIrreducibleRat (graphHyperplaneRestriction (fun i => (a i : ℚ) / D)
        (map (Int.castRingHom ℚ) f)) := by
  let e : Fin (3 + n) ≃ Option (Fin (2 + n)) :=
    (finCongr (by omega)).trans (_root_.finSuccEquiv (2 + n))
  let F := rename (Equiv.optionCongr e) f
  obtain ⟨G, hG, hhom, hbad⟩ := exists_effective_hyperplane_avoidance F d hd hf.rename_isHomogeneous (by
    rw [AbsolutelyIrreducible, map_rename]
    exact (MulEquiv.irreducible_iff
      (f := (renameEquiv (AlgebraicClosure ℚ) (Equiv.optionCongr e)).toMulEquiv)).mpr hir)
  have hd2 : 1 ≤ d ^ 2 := by nlinarith
  obtain ⟨v, hv, hvalue⟩ := exists_integer_grid_eval_ne_zero G hG (d ^ 3) (by
    rw [hhom.totalDegree hG]
    have he : d * (d ^ 2 - 1) + d = d ^ 3 := by
      calc
        _ = d * ((d ^ 2 - 1) + 1) := by ring
        _ = d * d ^ 2 := by grind
        _ = _ := by ring
    omega)
  let A : Option (Option (Fin (2 + n))) → ℚ := fun i => v i
  have hvalueQ : eval₂ (Int.castRingHom ℚ) A G ≠ 0 := by
    have he : eval₂ (Int.castRingHom ℚ) A G = (eval v G : ℚ) := by
      rw [eval₂_eq_eval_map]
      exact (map_eval (Int.castRingHom ℚ) v G).symm
    simp_all
  have hirA : AbsolutelyIrreducibleRat (graphHyperplaneRestriction
      (fun i => -A (some i) / A none) (map (Int.castRingHom ℚ) F)) := by
    by_contra hn
    exact hvalueQ (hbad ℚ A (fun _ => hn))
  let a := fun i => -v (some i)
  have hα : (fun i => (a i : ℚ) / (v none : ℚ)) =
      (fun i => -A (some i) / A none) := by
    funext i
    simp [a, A]
  rw [← hα] at hirA
  have hgood : AbsolutelyIrreducibleRat (graphHyperplaneRestriction
      (fun i => ((a ∘ e) i : ℚ) / (v none : ℚ)) (map (Int.castRingHom ℚ) f)) := by
    have he := congrArg (map (algebraMap ℚ (AlgebraicClosure ℚ)))
      (graphHyperplaneRestriction_rename e (fun i => (a i : ℚ) / (v none : ℚ))
        (map (Int.castRingHom ℚ) f))
    rw [map_rename] at he
    apply (MulEquiv.irreducible_iff
      (f := (renameEquiv (AlgebraicClosure ℚ) e).toMulEquiv)).mp
    change Irreducible (rename e (map (algebraMap ℚ (AlgebraicClosure ℚ))
      (graphHyperplaneRestriction ((fun i => (a i : ℚ) / (v none : ℚ)) ∘ e)
        (map (Int.castRingHom ℚ) f))))
    rw [he]
    simpa [AbsolutelyIrreducibleRat, F, map_rename] using hirA
  exact ⟨v none, a ∘ e, (by
    intro hz
    apply hvalueQ
    exact hbad ℚ A (fun h => (h (by aesop)).elim)), by grind, fun i => by grind, hgood⟩

