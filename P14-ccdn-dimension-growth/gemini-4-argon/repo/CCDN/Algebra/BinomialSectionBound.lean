/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredIntersection
import CCDN.ForMathlib.MvPolynomial

/-! Two finite differences of a binomial Hilbert function. This gives a
coefficient-uniform codimension-two bound for filtered coordinate spaces. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The filtered Koszul bound reduces to a codimension-two binomial count. -/
theorem filteredCoordinateSpace_codim_two_bound {K : Type*} [Field K] {n N : ℕ}
    {f g : MvPolynomial (Fin (n + 2)) K} (hf : Prime f) (hfg : ¬ f ∣ g)
    (I : Ideal (MvPolynomial (Fin (n + 2)) K)) (hIf : f ∈ I) (hIg : g ∈ I)
    (hN : f.totalDegree + g.totalDegree ≤ N) :
    Module.finrank K (filteredCoordinateSpace I N) ≤
      f.totalDegree * g.totalDegree * (n + N).choose n := by
  have hshift (m k d : ℕ) :
      (m + 1 + (k + d)).choose (m + 1) = (m + 1 + k).choose (m + 1) +
        ∑ i ∈ Finset.range d, (m + (k + i + 1)).choose m := by
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Finset.sum_range_succ, show m + 1 + (k + (d + 1)) = (m + 1 + (k + d)) + 1 by omega,
        Nat.choose_succ_succ', ih, show m + 1 + (k + d) = m + (k + d + 1) by omega]
      omega
  have h := filteredCoordinateSpace_finrank_bound hf hfg I hIf hIg hN
  simp only [MvPolynomial.finrank_restrictTotalDegree, Fintype.card_fin,
    ← Nat.choose_symm_add (a := n + 2)] at h
  have hc (k d e : ℕ) :
      (n + 2 + (k + d + e)).choose (n + 2) + (n + 2 + k).choose (n + 2) ≤
        (n + 2 + (k + d)).choose (n + 2) + (n + 2 + (k + e)).choose (n + 2) +
          d * e * (n + (k + d + e)).choose n := by
    have h1 := hshift (n + 1) (k + e) d
    have h2 := hshift (n + 1) k d
    have hsum : (∑ i ∈ Finset.range d, (n + 1 + (k + e + i + 1)).choose (n + 1)) ≤
        (∑ i ∈ Finset.range d, (n + 1 + (k + i + 1)).choose (n + 1)) +
          d * e * (n + (k + d + e)).choose n := by
      calc
        _ ≤ ∑ i ∈ Finset.range d,
            ((n + 1 + (k + i + 1)).choose (n + 1) + e * (n + (k + d + e)).choose n) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have h3 := hshift n (k + i + 1) e
          have hb : (n + 1 + (k + i + 1 + e)).choose (n + 1) ≤
              (n + 1 + (k + i + 1)).choose (n + 1) + e * (n + (k + i + 1 + e)).choose n := by
            rw [h3]
            refine Nat.add_le_add_left ?_ _
            calc
              _ ≤ ∑ _j ∈ Finset.range e, (n + (k + i + 1 + e)).choose n :=
                Finset.sum_le_sum fun j hj => Nat.choose_le_choose n (by have := Finset.mem_range.mp hj; omega)
              _ = _ := by simp
          have hm := Nat.mul_le_mul_left e (Nat.choose_le_choose n
            (show n + (k + i + 1 + e) ≤ n + (k + d + e) by have := Finset.mem_range.mp hi; omega))
          rw [show k + i + 1 + e = k + e + i + 1 by omega] at hb hm
          omega
        _ = _ := by rw [Finset.sum_add_distrib]; simp [Nat.mul_assoc]
    rw [show k + e + d = k + d + e by omega] at h1
    rw [show n + 1 + 1 = n + 2 by omega] at h1 h2
    omega
  have hc' := hc (N - (f.totalDegree + g.totalDegree)) f.totalDegree g.totalDegree
  rw [show N - (f.totalDegree + g.totalDegree) + f.totalDegree + g.totalDegree = N by omega,
    show N - (f.totalDegree + g.totalDegree) + f.totalDegree = N - g.totalDegree by omega,
    show N - (f.totalDegree + g.totalDegree) + g.totalDegree = N - f.totalDegree by omega] at hc'
  omega

end
end CCDN
