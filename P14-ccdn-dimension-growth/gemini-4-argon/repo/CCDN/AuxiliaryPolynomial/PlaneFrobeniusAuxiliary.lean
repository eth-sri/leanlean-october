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
  | inl _ => simp
  | inr he =>
    obtain ⟨i0⟩ := he
    let g : MvPolynomial (Fin 2) (ZMod p) := ∑ k, h k * (a k) ^ p
    have hiter (r : ℕ) :
        (planeTangent f j)^[r] g = ∑ k, (planeTangent f j)^[r] (h k) * (a k) ^ p := by
      induction r with
      | zero => rfl
      | succ r hr =>
        rw [Function.iterate_succ_apply', hr, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero,
          zero_mul, smul_zero, zero_add, smul_eq_mul, Function.iterate_succ_apply', mul_comm]
    have hnd : ¬ f ∣ g := by
      obtain ⟨ψ, _, hparam, hfaith⟩ :=
        exists_faithful_formal_plane_branch f hf (z i0) j.rev (hzero i0) (hsmooth i0)
      intro hdvd
      have hrel : ∑ k, ψ (h k) * (ψ (a k)) ^ (p ^ 1) = 0 := by
        simpa only [g, map_sum, map_mul, map_pow, pow_one] using (hfaith _).mpr hdvd
      have htriv := formal_plane_frobenius_relation_trivial p 1 f hf ψ
        ((hfaith f).mpr dvd_rfl) j.rev.rev (z i0 j.rev.rev) hparam
        (by simpa only [pow_one] using hD) h hd hi (fun k => ψ (a k)) hrel
      obtain ⟨k, hak⟩ := hne
      exact hak ((hfaith (a k)).mp (htriv k))
    choose ψ hconst hparam hfaith using fun i : ι =>
      exists_faithful_formal_plane_branch f hf (z i) j.rev (hzero i) (hsmooth i)
    have hb : Fintype.card ι * N ≤ f.totalDegree * g.totalDegree :=
      formal_plane_multiplicity_bound f hf z hz ψ
        (fun i => (hfaith i f).mpr dvd_rfl) hconst (fun _ => j)
        (by simpa only [Fin.rev_rev] using hparam) g hnd N fun i =>
        formal_plane_multiplicity_of_tangent f (ψ i) ((hfaith i f).mpr dvd_rfl)
          (z i) (hconst i) j (by simpa only [Fin.rev_rev] using hparam i)
          (hsmooth i) g N
          (fun _ hn hnN => CharP.natCast_ne_zero_of_lt (ZMod p) hn.ne' (hnN.trans_le hN))
          fun r hr => by
            rw [hiter]
            obtain ⟨u, hu⟩ := hdiv r hr
            have hev : eval (z i) (∑ k, (planeTangent f j)^[r] (h k) * a k) = 0 := by
              rw [hu, map_mul, hzero i, zero_mul]
            simpa only [map_sum, map_mul, map_pow, ZMod.pow_card] using hev
    exact hb.trans (Nat.mul_le_mul_left _ (totalDegree_finsetSum_le fun k _ =>
      (totalDegree_mul _ _).trans (Nat.add_le_add (hd k)
        ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left p (ha k))))))

end
end CCDN
