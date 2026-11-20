/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

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

/-- Polynomial used in the Stepanov construction. -/
private def planeFrobeniusAuxiliary {K ι : Type*} [Field K] [Fintype ι]
    (p : ℕ) (h a : ι → MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  ∑ i, h i * (a i) ^ p

private lemma planeFrobeniusAuxiliary_degree {K ι : Type*} [Field K] [Fintype ι]
    (p : ℕ) (h a : ι → MvPolynomial (Fin 2) K) {D A : ℕ}
    (hd : ∀ i, (h i).totalDegree ≤ D) (ha : ∀ i, (a i).totalDegree ≤ A) :
    (planeFrobeniusAuxiliary p h a).totalDegree ≤ D + p * A := by
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (Nat.add_le_add (hd i)
    ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left p (ha i))))

private lemma planeFrobeniusAuxiliary_iterate {K ι : Type*} [Field K] [Fintype ι]
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
    simp [Derivation.leibniz, smul_eq_mul, Function.iterate_succ_apply', mul_comm]

/-- Divisibility constraints on the unpowered coefficients force all requested
tangent derivatives to vanish at every rational point over the prime field. -/
private theorem planeFrobeniusAuxiliary_tangent_vanishing {ι : Type*} [Fintype ι]
    (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin 2) (ZMod p)) (j : Fin 2)
    (h a : ι → MvPolynomial (Fin 2) (ZMod p)) (r : ℕ)
    (hdiv : f ∣ ∑ i, (planeTangent f j)^[r] (h i) * a i)
    (z : Fin 2 → ZMod p) (hz : eval z f = 0) :
    eval z ((planeTangent f j)^[r] (planeFrobeniusAuxiliary p h a)) = 0 := by
  rw [planeFrobeniusAuxiliary_iterate]
  have he : eval z (∑ i, (planeTangent f j)^[r] (h i) * a i) = 0 := by
    obtain ⟨u, hu⟩ := hdiv
    simp_all
  aesop

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
    choose ψ hconst hparam hfaith using fun i =>
      exists_faithful_formal_plane_branch f hf (z i) j.rev (hzero i) (hsmooth i)
    have hψ (i) := (hfaith i f).mpr dvd_rfl
    have hpar (i) : ψ i (X j - C (z i j)) = PowerSeries.X := by simpa using hparam i
    let G := planeFrobeniusAuxiliary p h a
    have hnd : ¬ f ∣ G := by
      intro hG
      have hrel : ∑ k, ψ i (h k) * (ψ i (a k)) ^ p = 0 := by
        simpa [G, planeFrobeniusAuxiliary] using (hfaith i G).mpr hG
      have hzero' := formal_plane_frobenius_relation_trivial p f hf (ψ i) (hψ i)
        (z i) (hconst i) j (hpar i) hD h hd hi _ hrel
      exact hne.elim fun k hk => hk ((hfaith i (a k)).mp (hzero' k))
    have hb := formal_plane_multiplicity_bound f hf z hz ψ hψ hconst (fun _ => j) hpar G hnd N
      (fun i => formal_plane_multiplicity_of_tangent f (ψ i) (hψ i) (z i) (hconst i) j
        (hpar i) (hsmooth i) G N
        (fun _ hn hnN => CharP.natCast_ne_zero_of_lt _ hn.ne' (hnN.trans_le hN))
        (fun r hr => planeFrobeniusAuxiliary_tangent_vanishing p f j h a r (hdiv r hr) (z i) (hzero i)))
    exact hb.trans (Nat.mul_le_mul_left _ (planeFrobeniusAuxiliary_degree p h a hd ha))

end
end CCDN
