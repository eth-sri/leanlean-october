/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Noether.FormalPlaneDifferentiation
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
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

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]


/-- Characteristic p allows all requested multiplicities up to p. -/
private theorem plane_tangent_multiplicity_bound_charP  (p : ℕ) [CharP K p]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : ι → Fin 2 → K) (hz : Function.Injective z)
    (hzero : ∀ i, eval (z i) f = 0) (j : ι → Fin 2)
    (hsmooth : ∀ i, eval (z i) (pderiv (j i).rev f) ≠ 0)
    (g : MvPolynomial (Fin 2) K) (hnd : ¬ f ∣ g) (N : ℕ) (hN : N ≤ p)
    (hvan : ∀ i r, r < N → eval (z i) ((planeTangent f (j i))^[r] g) = 0) :
    Fintype.card ι * N ≤ f.totalDegree * g.totalDegree :=
  (by
    let inline_hchar := fun (x : ℕ) (hn : (0 : ℕ) < x) (hnN : x < N) => CharP.natCast_ne_zero_of_lt K (LT.lt.ne' hn) (LT.lt.trans_le hnN hN)
    have hb (i : ι) := exists_faithful_formal_plane_branch f hf (z i) (j i).rev
      (hzero i) (hsmooth i)
    choose ψ hconst hparam hfaith using hb
    apply formal_plane_multiplicity_bound f hf z hz ψ
      (fun i => (hfaith i f).mpr dvd_rfl) hconst j
      (by simp_all) g hnd N
    intro i
    exact formal_plane_multiplicity_of_tangent f (ψ i) ((hfaith i f).mpr dvd_rfl)
      (z i) (hconst i) (j i) (by simp_all)
      (hsmooth i) g N inline_hchar (hvan i))

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

variable {K ι : Type*} [Field K] [Fintype ι]

variable (p : ℕ) (h a : ι → MvPolynomial (Fin 2) K)

/-- Polynomial used in the Stepanov construction. -/
private def planeFrobeniusAuxiliary 
      :=
  ∑ i, h i * (a i) ^ p


private lemma derivation_prime_power_zero {K : Type*} [Field K] (p : ℕ) [CharP K p]
    (D : Derivation K (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) K))
    (g : MvPolynomial (Fin 2) K) : D (g ^ p) = 0 := by
  simp_all

private lemma planeFrobeniusAuxiliary_iterate 
    (p : ℕ) [CharP K p]
    (D : Derivation K (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) K))
    (h a : ι → MvPolynomial (Fin 2) K) (r : ℕ) :
    D^[r] (planeFrobeniusAuxiliary p h a) = ∑ i, D^[r] (h i) * (a i) ^ p := by
  induction r with
  | zero => rfl
  | succ r hr =>
    rw [Function.iterate_succ_apply', hr, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Derivation.leibniz, derivation_prime_power_zero p, smul_zero, zero_add,
      smul_eq_mul, Function.iterate_succ_apply']
    exact mul_comm _ _


/-- The smooth rational-point bound supplied by any nontrivial solution of
the finite linear system defining a Frobenius auxiliary polynomial. -/
theorem planeFrobeniusAuxiliary_point_bound {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin 2) (ZMod p)) (hf : Irreducible f)
    (z : ι → Fin 2 → ZMod p) (hz : Function.Injective z)
    (hzero : ∀ i, eval (z i) f = 0) (j : Fin 2)
    (hsmooth : ∀ i, eval (z i) (pderiv j.rev f) ≠ 0)
    (h a : κ → MvPolynomial (Fin 2) (ZMod p)) {D A N : ℕ}
    (hD : f.totalDegree * D < p) (hN : N ≤ p)
    (hd : ∀ k, (h k).totalDegree ≤ D) (ha : ∀ k, (a k).totalDegree ≤ A)
    (hi : LinearIndependent (ZMod p)
      (fun k => (Ideal.Quotient.mkₐ (ZMod p) (Ideal.span {f})) (h k)))
    (hne : ∃ k, ¬ f ∣ a k)
    (hdiv : ∀ r < N, f ∣ ∑ k, (planeTangent f j)^[r] (h k) * a k) :
    Fintype.card ι * N ≤ f.totalDegree * (D + p * A) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl he => simp
  | inr he =>
    obtain ⟨i⟩ := he
    have hnd := (show ¬f ∣ planeFrobeniusAuxiliary p h a from (by
                  let inline_z := z i
                  let inline_hz : (eval (z i)) f = (0 : ZMod p) := hzero i
                  let inline_hj : (eval (z i)) ((pderiv j.rev) f) ≠ (0 : ZMod p) := hsmooth i
                  obtain ⟨ψ, hconst, hparam, hfaith⟩ := exists_faithful_formal_plane_branch f hf inline_z j.rev inline_hz inline_hj
                  intro hdiv
                  have hrel : ∑ i, ψ (h i) * (ψ (a i)) ^ (p ^ 1) = 0 := by
                    have he := (hfaith _).mpr hdiv
                    simpa only [planeFrobeniusAuxiliary, map_sum, map_mul, map_pow, pow_one] using he
                  have hzero := formal_plane_frobenius_relation_trivial p 1 f hf ψ
                    ((hfaith f).mpr dvd_rfl) j.rev.rev (inline_z j.rev.rev) hparam (by simpa only [pow_one] using hD)
                    h hd hi (fun i => ψ (a i)) hrel
                  obtain ⟨i, hai⟩ := hne
                  exact hai ((hfaith (a i)).mp (hzero i))))
    have hb := plane_tangent_multiplicity_bound_charP p f hf z hz hzero (fun _ => j)
      hsmooth (planeFrobeniusAuxiliary p h a) hnd N hN
      (fun i r hr => (by
                       let inline_hdiv := hdiv r hr
                       let inline_z := z i
                       let inline_hz := hzero i
                       rw [planeFrobeniusAuxiliary_iterate]
                       have he : eval inline_z (∑ i, (planeTangent f j)^[r] (h i) * a i) = 0 := by
                         obtain ⟨u, hu⟩ := inline_hdiv
                         rw [hu, map_mul, inline_hz, zero_mul]
                       simpa only [map_sum, map_mul, map_pow, ZMod.pow_card] using he))
    exact hb.trans (Nat.mul_le_mul_left _ ((by
                                             apply totalDegree_finsetSum_le
                                             intro i _
                                             exact (totalDegree_mul _ _).trans (Nat.add_le_add (hd i)
                                               ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left p (ha i)))))))

end
end CCDN
