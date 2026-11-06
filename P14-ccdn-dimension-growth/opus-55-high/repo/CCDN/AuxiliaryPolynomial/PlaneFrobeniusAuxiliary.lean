/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Noether.FormalPlaneDifferentiation
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Ideal.Quotient.Operations
import CCDN.Determinant.FormalBranchMultiplicity
import CCDN.ForMathlib.MvPolynomialDerivative
import CCDN.Noether.FormalBranchFaithful
import CCDN.Noether.FormalBranchOrder
import Mathlib.FieldTheory.Finite.Basic

/-!
Frobenius auxiliary polynomials: noncancellation, tangent-derivative
constraints, and their resulting count of smooth rational points.

A polynomial criterion for the multiplicity form of plane Bézout.
All formal branches are constructed from the nonsingularity assumptions.
-/

namespace CCDN
section
open MvPolynomial

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

end

noncomputable section
open MvPolynomial

section
variable {K ι : Type*} [Field K] [Fintype ι] (p : ℕ)

/-- Polynomial used in the Stepanov construction. -/
def planeFrobeniusAuxiliary
    (h a : ι → MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  ∑ i, h i * (a i) ^ p

/-- A nontrivial coefficient class gives a proper section, with the precise
low-degree restriction d*D<p. -/
theorem planeFrobeniusAuxiliary_not_dvd
    [DecidableEq ι] [Fact p.Prime] [CharP K p]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : Fin 2 → K) (j : Fin 2) (hz : eval z f = 0)
    (hj : eval z (pderiv j f) ≠ 0)
    (h a : ι → MvPolynomial (Fin 2) K) {D : ℕ} (hD : f.totalDegree * D < p)
    (hd : ∀ i, (h i).totalDegree ≤ D)
    (hi : LinearIndependent K (fun i => (Ideal.Quotient.mkₐ K (Ideal.span {f})) (h i)))
    (ha : ∃ i, ¬ f ∣ a i) : ¬ f ∣ planeFrobeniusAuxiliary p h a := by
  obtain ⟨ψ, hconst, hparam, hfaith⟩ := exists_faithful_formal_plane_branch f hf z j hz hj
  intro hdiv
  have hzero := powerSeries_frobenius_relation_trivial p 1 (fun i => ψ (h i))
    (fun c hc => by
      have hdiv := formal_plane_jet_detects_divisibility f hf ψ ((hfaith f).mpr dvd_rfl) j.rev
        (z j.rev) hparam (hD.trans_eq (pow_one p).symm) (∑ i, c i • h i) (MvPolynomial.totalDegree_finsetSum_le
          fun i _ => (MvPolynomial.totalDegree_smul_le _ _).trans (hd i)) (by aesop)
      have he := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
      exact Fintype.linearIndependent_iff.mp hi c (by aesop)) (fun i => ψ (a i)) (by
        have he := (hfaith _).mpr hdiv
        simp_all [planeFrobeniusAuxiliary, map_sum, map_mul, map_pow, pow_one])
  obtain ⟨i, hai⟩ := ha
  exact hai ((hfaith (a i)).mp (hzero i))

end

section
variable (p : ℕ)

lemma planeFrobeniusAuxiliary_iterate {K ι : Type*} [Field K] [Fintype ι]
    [CharP K p]
    (D : Derivation K (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) K))
    (h a : ι → MvPolynomial (Fin 2) K) (r : ℕ) :
    D^[r] (planeFrobeniusAuxiliary p h a) = ∑ i, D^[r] (h i) * (a i) ^ p := by
  induction r with
  | zero => rfl
  | succ r hr =>
    rw [Function.iterate_succ_apply', hr, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, smul_zero, zero_add,
      smul_eq_mul, Function.iterate_succ_apply']
    exact mul_comm _ _

end

variable (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin 2) (ZMod p))

/-- Divisibility constraints on the unpowered coefficients force all requested
tangent derivatives to vanish at every rational point over the prime field. -/
theorem planeFrobeniusAuxiliary_tangent_vanishing {ι : Type*} [Fintype ι]
    (j : Fin 2)
    (h a : ι → MvPolynomial (Fin 2) (ZMod p)) (r : ℕ)
    (hdiv : f ∣ ∑ i, (planeTangent f j)^[r] (h i) * a i)
    (z : Fin 2 → ZMod p) (hz : eval z f = 0) :
    eval z ((planeTangent f j)^[r] (planeFrobeniusAuxiliary p h a)) = 0 := by
  rw [planeFrobeniusAuxiliary_iterate]
  have he : eval z (∑ i, (planeTangent f j)^[r] (h i) * a i) = 0 := by
    obtain ⟨u, hu⟩ := hdiv
    grind
  simpa using he

