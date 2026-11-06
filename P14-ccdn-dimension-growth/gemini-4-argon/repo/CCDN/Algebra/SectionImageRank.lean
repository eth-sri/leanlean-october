/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredIntersection
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! A proper section bounds independent classes in any algebra-valued image,
not only distinct point evaluations. This is the multiplicity-ready form of
the Hilbert-function argument. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- Independent polynomial images in a proper section number at most d*m.
This applies to truncated local expansions as well as to point values. -/
theorem section_image_rank_le {K B σ ι : Type*} [Field K]
    [CommRing B] [Algebra K B] [Fintype σ] [Fintype ι] [DecidableEq ι]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (d : ℕ) (hdegree : HasFilteredCurveDegree p d)
    (φ : (MvPolynomial σ K ⧸ p) →ₐ[K] B) (h : ι → MvPolynomial σ K)
    (hlin : LinearIndependent K (fun i => φ ((Ideal.Quotient.mk p) (h i))))
    (l : MvPolynomial σ K) (hl : l ∉ p) (m : ℕ) (hld : l.totalDegree ≤ m)
    (hzero : φ ((Ideal.Quotient.mk p) l) = 0) : Fintype.card ι ≤ d * m := by
  classical
  by_cases hm : m = 0
  · have hlC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (show l.totalDegree = 0 by omega)
    have hc : l.coeff 0 ≠ 0 := fun he => hl (by rw [hlC, he, map_zero]; exact p.zero_mem)
    have hu : IsUnit l := hlC ▸ (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
    have hz : IsUnit (0 : B) := hzero ▸ ((hu.map (Ideal.Quotient.mk p)).map φ.toRingHom)
    let : Subsingleton B := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hz)
    simpa only [Module.finrank_zero_of_subsingleton, hm, Nat.mul_zero] using hlin.fintype_card_le_finrank
  let lbar := (Ideal.Quotient.mk p) l
  have hlbar : lbar ≠ 0 := fun hz => hl (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hpow_ind (M : ℕ) :
      LinearIndependent K (fun t : ι × Fin M => (Ideal.Quotient.mk p) (h t.1) * lbar ^ t.2.val) := by
    induction M with
    | zero => exact linearIndependent_empty_type
    | succ M ih =>
      rw [Fintype.linearIndependent_iff]
      intro a ha t
      have he' : ∑ i, a (i, 0) • φ ((Ideal.Quotient.mk p) (h i)) = 0 := by
        simpa [lbar, Fintype.sum_prod_type, Fin.sum_univ_succ, hzero] using congrArg φ ha
      have hconst : ∀ i, a (i, 0) = 0 := Fintype.linearIndependent_iff.mp hlin _ he'
      have htail : ∑ t : ι × Fin M, a (t.1, t.2.succ) • ((Ideal.Quotient.mk p) (h t.1) * lbar ^ t.2.val) = 0 := by
        apply mul_left_cancel₀ hlbar
        rw [mul_zero, Finset.mul_sum]
        have hsum : (∑ t : ι × Fin (M + 1), a t • ((Ideal.Quotient.mk p) (h t.1) * lbar ^ t.2.val)) =
            ∑ t : ι × Fin M, lbar * (a (t.1, t.2.succ) • ((Ideal.Quotient.mk p) (h t.1) * lbar ^ t.2.val)) := by
          simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, hconst, zero_smul, zero_add]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
          simp only [Fin.val_succ, pow_succ, mul_smul_comm]; congr 1; ring
        rw [← hsum]; exact ha
      have hc := Fintype.linearIndependent_iff.mp ih (fun t => a (t.1, t.2.succ)) htail
      obtain ⟨i, k⟩ := t
      exact Fin.cases (hconst i) (fun k => hc (i, k)) k
  let D := Finset.univ.sup (fun i => (h i).totalDegree)
  obtain ⟨N₀, c, hN₀⟩ := hdegree
  by_contra hbad
  have hcard : d * m + 1 ≤ Fintype.card ι := by omega
  let N := d * D + c.natAbs + N₀ + 1
  have hmem (t : ι × Fin (N + 1)) :
      (Ideal.Quotient.mk p) (h t.1) * lbar ^ t.2.val ∈ filteredCoordinateSpace p (D + m * N) := by
    refine Submodule.mem_map.mpr ⟨h t.1 * l ^ t.2.val, ?_, by simp [lbar]⟩
    rw [MvPolynomial.mem_restrictTotalDegree]
    exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add
      (Finset.le_sup (f := fun i => (h i).totalDegree) (Finset.mem_univ t.1))
      ((MvPolynomial.totalDegree_pow _ _).trans
        ((Nat.mul_le_mul_left _ hld).trans (by nlinarith [t.2.isLt]))))
  let v : ι × Fin (N + 1) → filteredCoordinateSpace p (D + m * N) :=
    fun t => ⟨(Ideal.Quotient.mk p) (h t.1) * lbar ^ t.2.val, hmem t⟩
  have hv : LinearIndependent K v :=
    LinearIndependent.of_comp (filteredCoordinateSpace p (D + m * N)).subtype (hpow_ind (N + 1))
  have hlow : Fintype.card ι * (N + 1) ≤ Module.finrank K (filteredCoordinateSpace p (D + m * N)) := by
    simpa using hv.fintype_card_le_finrank
  have he := hN₀ (D + m * N) (by
    have hN : N₀ ≤ N := by dsimp [N]; omega
    have hm1 : 1 ≤ m := by omega
    nlinarith)
  push_cast at he
  have hlo : (Fintype.card ι : ℤ) * (N + 1) ≤ (d : ℤ) * (D + m * N) + c := by
    rw [← he]; exact_mod_cast hlow
  have hmul : ((d : ℤ) * m + 1) * (N + 1) ≤ (Fintype.card ι : ℤ) * (N + 1) := by
    exact_mod_cast Nat.mul_le_mul_right (N + 1) hcard
  have habs : c ≤ (c.natAbs : ℤ) := Int.le_natAbs
  have hNeq : (N : ℤ) = d * D + c.natAbs + N₀ + 1 := by simp [N]
  nlinarith

end
end CCDN
