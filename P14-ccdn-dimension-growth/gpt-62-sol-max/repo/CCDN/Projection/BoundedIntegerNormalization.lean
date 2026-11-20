/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IntegerLinearForms
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Hilbert.LinearProjectionFiltration
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import CCDN.Hilbert.FullDimension
import CCDN.Projection.BoundedLinearElimination
public import CCDN.Projection.FilteredGenerators
import CCDN.Projection.HilbertLowDegreeEquation
import CCDN.Projection.FilteredProjectionRank
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Constructive bounded linear Noether normalization. The coefficients of
the integer linear forms are bounded by n! (d+1)^n. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The coefficient bound `n! * (d + 1) ^ n` for the bounded linear Noether normalization of a
degree-`d` variety in `n` variables. -/
def integerNormalizationHeight (n d : ℕ) : ℕ := n.factorial * (d + 1) ^ n

/-- The normalization height is positive. -/
lemma integerNormalizationHeight_pos (n d : ℕ) : 0 < integerNormalizationHeight n d := by
  dsimp [integerNormalizationHeight]
  positivity

private lemma integerNormalizationHeight_mono (n : ℕ) {d e : ℕ} (h : d ≤ e) :
    integerNormalizationHeight n d ≤ integerNormalizationHeight n e := by
  dsimp [integerNormalizationHeight]
  gcongr

private lemma integerNormalizationHeight_step (n d : ℕ) :
    n * integerNormalizationHeight n d * (d + 1) ≤
      integerNormalizationHeight (n + 1) d := by
  dsimp [integerNormalizationHeight]
  rw [Nat.factorial_succ, pow_succ]
  grind

section

variable (m k : ℕ)
  (I : Ideal (MvPolynomial (Fin (m + 1 + k)) ℚ)) [I.IsPrime] (d : ℕ)
  (hdimdeg : HasAffineDimensionDegree I (m + 1) d)
include m k I d hdimdeg

/-- A bounded integral and injective map from a polynomial ring into a prime quotient. -/
theorem exists_bounded_integer_normalization :
    ∃ a : Fin (m + 1) → Fin (m + 1 + k) → ℤ,
      (∀ i j, |a i j| ≤ integerNormalizationHeight (m + 1 + k) d) ∧
      HasFilteredGenerators I (projectionCoordinateMap I (fun i => integerLinearForm (a i))) ∧
      Function.Injective (projectionCoordinateMap I (fun i => integerLinearForm (a i))) := by
  induction k generalizing d with
  | zero =>
    let a : Fin (m + 1) → Fin (m + 1) → ℤ := fun i j => if j = i then 1 else 0
    have heq : projectionCoordinateMap I (fun i => integerLinearForm (a i)) =
        Ideal.Quotient.mkₐ ℚ I := by
      ext i
      simp [projectionCoordinateMap, a, integerLinearForm_identity]
    have hI0 := ideal_eq_bot_of_full_hilbert_dimension I (Ideal.IsPrime.ne_top ‹I.IsPrime›)
      (by simp [hdimdeg.natDegree_eq])
    refine ⟨a, ?_, ?_, ?_⟩
    · intro i j
      have hH : (1 : ℤ) ≤ integerNormalizationHeight (m + 1) d := by
        exact_mod_cast Nat.succ_le_of_lt (integerNormalizationHeight_pos (m + 1) d)
      grind
    · rw [heq]
      exact HasFilteredGenerators.quotient I
    · rw [heq]
      exact (RingHom.injective_iff_ker_eq_bot _).mpr ((Ideal.Quotient.mkₐ_ker ℚ I).trans hI0)
  | succ k ih =>
    obtain ⟨f, hf, hfi, hfd⟩ := exists_mem_ideal_degree_le_multiplicity I d hdimdeg (by simp_all)
    obtain ⟨c, hc, hfgc⟩ := exists_integer_elimination_of_mem I f hf hfi
    let ψ := projectionCoordinateMap I (fun i => integerLinearForm (c i))
    let J := RingHom.ker ψ
    let : J.IsPrime := RingHom.ker_isPrime _
    obtain ⟨e, hed, hdimdegJ⟩ := filtered_projection_dimension_degree_le I
      (fun i => integerLinearForm (c i)) (fun i => linearForm_totalDegree_le _) hfgc hdimdeg
    obtain ⟨a, ha, hfga, hinja⟩ := ih J e hdimdegJ
    let a' :=
      fun i j => ∑ t, a i t * c t j
    let ψa := projectionCoordinateMap J (fun i => integerLinearForm (a i))
    let φ := Ideal.kerLiftAlg ψ
    have heq : φ.comp ψa = projectionCoordinateMap I (fun i => integerLinearForm (a' i)) := by
      ext i
      simp only [AlgHom.comp_apply, ψa, projectionCoordinateMap_X, φ, J, Ideal.kerLiftAlg_mk]
      change (Ideal.Quotient.mk I) (aeval (fun t => integerLinearForm (c t)) (integerLinearForm (a i))) = _
      rw [integerLinearForm_comp]
      rfl
    refine ⟨a', ?_, ?_, ?_⟩
    · intro i j
      have hbound := integerLinearForm_matrix_height (a i) c
        (integerNormalizationHeight (m + 1 + k) e) (d + 1) (ha i)
        (fun i j => (hc i j).trans (by exact_mod_cast Nat.add_le_add_right hfd 1)) j
      simp only [Fintype.card_fin] at hbound
      apply hbound.trans
      have hmono := integerNormalizationHeight_mono (m + 1 + k) hed
      have hstep := integerNormalizationHeight_step (m + 1 + k) d
      exact_mod_cast (Nat.mul_le_mul_right (d + 1)
        (Nat.mul_le_mul_left (m + 1 + k) hmono)).trans hstep
    · rw [← heq]
      exact hfgc.comp hfga
    · rw [← heq]
      exact (Ideal.kerLiftAlg_injective ψ).comp hinja

end

end
end CCDN
