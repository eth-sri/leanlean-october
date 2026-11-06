/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hilbert.FilteredIntersection
import Mathlib.RingTheory.Algebraic.Defs
import CCDN.Hilbert.FunctionFieldRank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Localization.Integer

/-! A fraction field of an affine curve is finite over the field of a
transcendental linear parameter, of degree at most its affine Hilbert degree.
Common denominators transfer arbitrary field elements to polynomial classes. -/

namespace CCDN
section

/-- Multiplying a linearly independent family in a field by a common nonzero element keeps it
linearly independent. -/
lemma field_common_multiple_independent {R F ι : Type*} [Field R] [Field F]
    [Algebra R F] [Fintype ι]
    (v : ι → F) (hv : LinearIndependent R v) (b : F) (hb : b ≠ 0) :
    LinearIndependent R (fun i => b * v i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  exact Fintype.linearIndependent_iff.mp hv c (by
    apply mul_left_cancel₀ hb
    rw [mul_zero, Finset.mul_sum]
    simp_all) i

variable {K R F σ : Type*} [Field K] [Field R] [Field F]
  [Algebra K R] [Algebra R F] [Algebra K F] [IsScalarTower K R F] [Fintype σ]
  (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
  [Algebra (MvPolynomial σ K ⧸ I) F] [IsScalarTower K (MvPolynomial σ K ⧸ I) F]
  [IsFractionRing (MvPolynomial σ K ⧸ I) F]

/-- A linear independence bound on finite families gives finiteness and a rank bound. -/
lemma finite_finrank_le_of_card_le {R F : Type*} [Field R] [AddCommGroup F] [Module R F] {N : ℕ}
    (h : ∀ s : Finset F, LinearIndependent R (fun i : s => (i : F)) → s.card ≤ N) :
    Module.Finite R F ∧ Module.finrank R F ≤ N :=
  have hr := rank_le h
  ⟨Module.rank_lt_aleph0_iff.mp (hr.trans_lt Cardinal.natCast_lt_aleph0),
    Module.finrank_le_of_rank_le hr⟩

omit [Fintype σ] [Algebra K R] [IsScalarTower K R F] in
/-- Clearing a common denominator turns independent fractions into independent
polynomial classes. -/
lemma exists_numerators_independent {ι : Type*} [Fintype ι]
    (v : ι → F) (hv : LinearIndependent R v) : ∃ h : ι → MvPolynomial σ K, LinearIndependent R
      (fun i => IsScalarTower.toAlgHom K (MvPolynomial σ K ⧸ I) F ((Ideal.Quotient.mk I) (h i))) := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (MvPolynomial σ K ⧸ I)) v
  choose a ha using hb
  choose h hh using fun i => Ideal.Quotient.mk_surjective (a i)
  refine ⟨h, ?_⟩
  convert field_common_multiple_independent v hv _
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property) using 1
  funext i
  rw [IsScalarTower.toAlgHom_apply, hh]
  exact (ha i).trans (Algebra.smul_def _ _)

variable (d : ℕ) (hdegree : HasFilteredCurveDegree I d) (l : MvPolynomial σ K) (hl : l.totalDegree ≤ 1) (u : R) (hu : Transcendental K u) (he : algebraMap (MvPolynomial σ K ⧸ I) F ((Ideal.Quotient.mk I) l) = algebraMap R F u)
include hdegree hl hu he

/-- The function-field extension is finite and has degree at most d. -/
theorem curve_functionField_finite_rank_le
    :
    Module.Finite R F ∧ Module.finrank R F ≤ d :=
  finite_finrank_le_of_card_le fun s hs => by
    classical
    obtain ⟨h, hlin⟩ := exists_numerators_independent I _ hs
    simpa using polynomial_parameter_rank_le I d hdegree _ l hl u hu he h hlin
