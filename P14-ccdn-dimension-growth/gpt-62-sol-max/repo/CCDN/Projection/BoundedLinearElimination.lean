/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IntegerLinearForms
public import CCDN.Projection.FilteredGenerators
import CCDN.Algebra.HomogeneousChart
import CCDN.Algebra.IntegerPolynomialAvoidance
import CCDN.AuxiliaryPolynomial.HypersurfacePositioning
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! Bounded linear elimination by a monic equation along an integral direction
whose first coordinate is one. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A nonzero ideal equation gives a bounded integral projection dropping one variable. -/
theorem exists_integer_elimination_of_mem {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) (f : MvPolynomial (Fin (n + 1)) ℚ)
    (hf : f ≠ 0) (hfi : f ∈ I) :
    ∃ c : Fin n → Fin (n + 1) → ℤ,
      (∀ i j, |c i j| ≤ f.totalDegree + 1) ∧
      HasFilteredGenerators I (projectionCoordinateMap I (fun i => integerLinearForm (c i))) := by
  let H := homogeneousComponent f.totalDegree f
  have hH : H.IsHomogeneous f.totalDegree := homogeneousComponent_isHomogeneous _ _
  have hH0 := affineChart_ne_zero_of_homogeneous hH (homogeneousComponent_totalDegree_ne_zero hf)
  obtain ⟨b, hb, hval⟩ := exists_integer_grid_eval_ne_zero (affineChart n H) hH0
    f.totalDegree ((affineChart_totalDegree_le H).trans hH.totalDegree_le)
  rw [affineChart_eval] at hval
  let v : Option (Fin n) → ℚ := Option.elim' 1 (fun i => (b i : ℚ))
  have hv₀ : v none ≠ 0 := one_ne_zero
  let r := renameEquiv ℚ (finSuccEquiv n)
  let F := r f
  let A := eval v (homogeneousComponent F.totalDegree F)
  have heval : A ≠ 0 := by
    dsimp only [A]
    rw [(totalDegree_renameEquiv (finSuccEquiv n) f)]
    change eval v (homogeneousComponent f.totalDegree (rename (finSuccEquiv n) f)) ≠ 0
    rw [← rename_homogeneousComponent, eval_rename]
    convert hval using 3
    exact funext fun i => Fin.cases rfl (fun _ => rfl) i
  let S := hypersurfaceAffineCoordinates 0 v hv₀
  let E := r.trans (S.trans (optionEquivLeft ℚ (Fin n)))
  let p := C A⁻¹ * f
  have hq : E p = optionEquivLeft ℚ (Fin n) (normalizedHypersurfaceCoordinates 0 v hv₀ F) := by
    have hC (a : ℚ) : E (C a) = Polynomial.C (C a) := E.commutes a
    change E (C _ * f) = _
    rw [map_mul, hC, normalizedHypersurfaceCoordinates, map_mul, optionEquivLeft_C]
    rfl
  have hcoef (g : _) (i : ℕ) (hi : i ≤ (E g).natDegree) :
      ((E g).coeff i).totalDegree + i ≤ g.totalDegree :=
    (totalDegree_coeff_optionEquivLeft_add_le ℚ _ (S (r g)) i
      (hi.trans ((natDegree_optionEquivLeft _ _).le.trans (degreeOf_le_totalDegree _ _)))).trans
      ((hypersurfaceAffineCoordinates_totalDegree_le 0 v hv₀ _).trans (totalDegree_rename_le _ _))
  let c (i : Fin n) : Fin (n + 1) → ℤ := Fin.cons (-b i) fun j => if j = i then 1 else 0
  refine ⟨c, ?_, HasFilteredGenerators.of_monic_elimination I E _ ?_ hcoef p
    (by rw [hq]; exact normalizedHypersurfaceCoordinates_monic 0 v hv₀ F heval) ?_ ?_⟩
  · intro i j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa [c, abs_of_nonneg (hb i).1] using (hb i).2.trans (Int.le_add_one (le_refl _))
    · by_cases h : j = i <;> simp [c, h]
      positivity
  · let T := (Ideal.Quotient.mkₐ ℚ I).comp
        (E.symm.toAlgHom.comp (Polynomial.CAlgHom (R := ℚ) (A := MvPolynomial (Fin n) ℚ)))
    have hT : T = projectionCoordinateMap I (fun i => integerLinearForm (c i)) := by
      ext i
      simp [T, E, S, r, originShiftEquiv, hypersurfaceAffineCoordinates, directionCoordinates,
        directionCoordinatesInv, v, integerLinearForm, linearForm, c, Fin.sum_univ_succ,
        apply_ite, sub_eq_add_neg, add_comm]
    exact DFunLike.congr_fun hT
  · rw [hq, normalizedHypersurfaceCoordinates_natDegree 0 v hv₀ F heval,
      totalDegree_renameEquiv]
    simpa [p] using (totalDegree_mul (C A⁻¹) f)
  · exact Ideal.mul_mem_left _ (C A⁻¹) hfi

end
end CCDN
