/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IntegerLinearForms
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Projection.ProjectiveClosureProjection
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import CCDN.Hilbert.FullDimension
import CCDN.Projection.BoundedClosureElimination
import CCDN.Projection.ClosureIntegralComposition
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Constructive bounded linear Noether normalization. The coefficients of
the integer linear forms are bounded by n! (d+1)^n, and the map of projective closures
fixing the homogenizing coordinate is integral as well. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The coefficient bound `n! * (d + 1) ^ n` for the bounded linear Noether normalization of a
degree-`d` variety in `n` variables. -/
def integerNormalizationHeight (n d : ℕ) : ℕ := n.factorial * (d + 1) ^ n

/-- Integer linear normalization of a prime quotient of positive
Hilbert dimension. The resulting polynomial map is both injective and integral. -/
theorem exists_bounded_integer_normalization (m k : ℕ)
    (I : Ideal (MvPolynomial (Fin (m + 1 + k)) ℚ)) [I.IsPrime] (d : ℕ)
    (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ a : Fin (m + 1) → Fin (m + 1 + k) → ℤ,
      (∀ i j, |a i j| ≤ integerNormalizationHeight (m + 1 + k) d) ∧
      (projectionCoordinateMap I (fun i => integerLinearForm (a i))).IsIntegral ∧
      Function.Injective (projectionCoordinateMap I (fun i => integerLinearForm (a i))) := by
  /- The normalization height is positive. -/
  /- Integer linear normalization of a prime quotient of positive Hilbert dimension. The
  resulting polynomial map is injective and integral, and so is the induced map of projective
  closures fixing the homogenizing coordinate. -/
  have hnorm (k : ℕ) (I : Ideal (MvPolynomial (Fin (m + 1 + k)) ℚ)) [I.IsPrime] (d : ℕ)
      (hdimdeg : HasProjectiveDimensionDegree I m d) :
      ∃ a : Fin (m + 1) → Fin (m + 1 + k) → ℤ,
        (∀ i j, |a i j| ≤ integerNormalizationHeight (m + 1 + k) d) ∧
        (projectionCoordinateMap I (fun i => integerLinearForm (a i))).IsIntegral ∧
        Function.Injective (projectionCoordinateMap I (fun i => integerLinearForm (a i))) ∧
        (projectionCoordinateMap (projectiveClosureIdeal I)
          (closureProjectionCoordinates (fun i => integerLinearForm (a i)))).IsIntegral := by
    induction k generalizing d with
    | zero =>
      let a : Fin (m + 1) → Fin (m + 1) → ℤ := fun i j => if j = i then 1 else 0
      have heq : projectionCoordinateMap I (fun i => integerLinearForm (a i)) =
          Ideal.Quotient.mkₐ ℚ I := by
        ext i; simp [projectionCoordinateMap, a, integerLinearForm_identity]
      have hI0 : I = ⊥ := ideal_eq_bot_of_full_hilbert_dimension I (Ideal.IsPrime.ne_top ‹I.IsPrime›)
        (by simpa only [Fintype.card_fin] using hdimdeg.natDegree_eq)
      refine ⟨a, fun i j => ?_, heq ▸ RingHom.isIntegral_of_surjective _ (Ideal.Quotient.mkₐ_surjective ℚ I),
        ?_, ?_⟩
      · by_cases he : j = i
        · simpa [a, he] using (mod_cast Nat.succ_le_of_lt
            (by dsimp [integerNormalizationHeight]; positivity : 0 < integerNormalizationHeight (m + 1) d) :
            (1 : ℤ) ≤ integerNormalizationHeight (m + 1) d)
        · simp [a, he, Nat.cast_nonneg]
      · rw [heq, RingHom.injective_iff_ker_eq_bot]
        change RingHom.ker ((Ideal.Quotient.mkₐ ℚ I) :
          MvPolynomial (Fin (m + 1)) ℚ →+* MvPolynomial (Fin (m + 1)) ℚ ⧸ I) = ⊥
        rwa [Ideal.Quotient.mkₐ_ker]
      · rw [show projectionCoordinateMap (projectiveClosureIdeal I)
            (closureProjectionCoordinates (fun i => integerLinearForm (a i))) =
              Ideal.Quotient.mkₐ ℚ (projectiveClosureIdeal I) by
          ext i; refine Fin.cases ?_ (fun _ => ?_) i <;>
            simp [projectionCoordinateMap, closureProjectionCoordinates, a,
              integerLinearForm_identity]]
        exact RingHom.isIntegral_of_surjective _ (Ideal.Quotient.mkₐ_surjective _ _)
    | succ k ih =>
      obtain ⟨c, e, hc, he, hed, hintc, hprime, hdimdegJ, hconec⟩ :=
        exists_fin_integer_closure_elimination_step (n := m + 1 + k) (m := m) I d hdimdeg (by omega)
      let ψ := projectionCoordinateMap I (fun i => integerLinearForm (c i))
      let J := RingHom.ker ψ
      have : J.IsPrime := hprime
      obtain ⟨a, ha, hinta, hinja, hconea⟩ := ih J e hdimdegJ
      let a' : Fin (m + 1) → Fin (m + 1 + (k + 1)) → ℤ := fun i j => ∑ t, a i t * c t j
      let ψa := projectionCoordinateMap J (fun i => integerLinearForm (a i))
      let φ := Ideal.kerLiftAlg ψ
      have hcomp := RingHom.IsIntegral.trans ψa.toRingHom φ.toRingHom hinta hintc.kerLift
      have heq : φ.comp ψa = projectionCoordinateMap I (fun i => integerLinearForm (a' i)) := by
        ext i
        simp only [AlgHom.comp_apply, ψa, projectionCoordinateMap, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
        change (Ideal.Quotient.mk I)
          (aeval (fun t => integerLinearForm (c t)) (integerLinearForm (a i))) =
            (Ideal.Quotient.mk I) (integerLinearForm (a' i))
        rw [integerLinearForm_comp]; rfl
      refine ⟨a', fun i j => ?_, heq ▸ hcomp, heq ▸ (Ideal.kerLiftAlg_injective ψ).comp hinja, ?_⟩
      · have hbound := integerLinearForm_matrix_height (a i) c
          (integerNormalizationHeight (m + 1 + k) e) (d + 1) (ha i)
          (fun i j => mod_cast hc i j) j
        simp only [Fintype.card_fin] at hbound
        refine hbound.trans (mod_cast ?_)
        have hmono : integerNormalizationHeight (m + 1 + k) e ≤
            integerNormalizationHeight (m + 1 + k) d := by
          dsimp [integerNormalizationHeight]; gcongr
        have hstep : (m + 1 + k) * integerNormalizationHeight (m + 1 + k) d * (d + 1) ≤
            integerNormalizationHeight (m + 1 + k + 1) d := by
          dsimp [integerNormalizationHeight]
          rw [Nat.factorial_succ, pow_succ]
          nlinarith [Nat.zero_le ((m + 1 + k).factorial * (d + 1) ^ (m + 1 + k) * (d + 1))]
        exact (Nat.mul_le_mul_right (d + 1)
          (Nat.mul_le_mul_left (m + 1 + k) hmono)).trans hstep
      · simpa only [integerLinearForm_comp] using closure_projection_integral_comp I
          (fun i => integerLinearForm (c i)) (fun i => linearForm_isHomogeneous _)
          (fun i => integerLinearForm (a i)) hconec hconea
  obtain ⟨a, ha, hint, hinj, -⟩ := hnorm k I d hdimdeg
  exact ⟨a, ha, hint, hinj⟩

end
end CCDN
