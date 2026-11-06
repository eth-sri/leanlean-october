/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.SingularTangent
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity.Finset

/-!
Finite-precision generation of hypersurface local quotients.
Generator counts equal the layer dimensions; for plane curves each
weight needs at most μ generators.

Homogeneous generators lifted from the origin-adic layers of a
plane equation, with the number at every weight bounded by its multiplicity.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Module

/-- In every ambient dimension, the numbers of homogeneous generators are
exactly the dimensions of the origin-adic layers. -/
theorem exists_origin_truncation_generators {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) :
    ∃ (r : ℕ → ℕ) (g : (k : ℕ) → Fin (r k) → MvPolynomial (Fin (n + 1)) K),
      (∀ k, r k = Module.finrank K (originLayer f k)) ∧
      (∀ k j, (g k j).IsHomogeneous k) ∧
      ∀ N u, ∃ c : (k : Fin N) → Fin (r k.val) → K,
        u - ∑ k : Fin N, ∑ j, c k j • g k.val j ∈
          Ideal.span {f} ⊔ idealOfVars (Fin (n + 1)) K ^ N := by
  classical
  have hlayer (k : ℕ) : ∃ (rk : ℕ) (gk : Fin rk → MvPolynomial (Fin (n + 1)) K),
      rk = Module.finrank K (originLayer f k) ∧ (∀ j, (gk j).IsHomogeneous k) ∧
      ∀ u ∈ idealOfVars (Fin (n + 1)) K ^ k, ∃ c : Fin rk → K,
        u - ∑ j, c j • gk j ∈ originTruncationIdeal f k := by
    let b := Module.finBasis K (originLayer f k)
    let φ := (Ideal.Quotient.mkₐ K (originTruncationIdeal f k)).toLinearMap
    choose gk hg he using show ∀ j, ∃ g : MvPolynomial (Fin (n + 1)) K,
        g.IsHomogeneous k ∧ φ g = (b j).val from fun j =>
      Submodule.mem_map.mp ((originLayer_eq_homogeneousCoordinateSpace f k).le (b j).property)
    refine ⟨Module.finrank K (originLayer f k), gk, rfl, hg, fun u hu => ?_⟩
    let ubar : originLayer f k := ⟨φ u, Submodule.mem_map.mpr ⟨u, hu, rfl⟩⟩
    refine ⟨fun j => b.repr ubar j, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    change φ (u - ∑ j, b.repr ubar j • gk j) = 0
    rw [map_sub, map_sum]; simp only [map_smul, he]
    exact sub_eq_zero.mpr (by
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using
        (congrArg Subtype.val (b.sum_repr ubar)).symm)
  choose r g hr hg hs using hlayer
  refine ⟨r, g, hr, hg, fun N u => ?_⟩
  induction N with
  | zero => exact ⟨fun k => Fin.elim0 k, by simp⟩
  | succ N ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨p, hp, q, hq, he⟩ := Submodule.mem_sup.mp hc
    obtain ⟨b, hb⟩ := hs N q hq
    refine ⟨Fin.lastCases b c, ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, Fin.val_last]
    convert (Ideal.span {f} ⊔ idealOfVars (Fin (n + 1)) K ^ (N + 1)).add_mem
      (Submodule.mem_sup_left hp) hb using 1
    linear_combination -he

/- Finite-precision weighted generators for any plane equation of
multiplicity μ. -/

end
end CCDN
