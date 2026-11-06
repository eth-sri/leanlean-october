/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.MonomialRays
public import Mathlib.RingTheory.Algebraic.Defs
import CCDN.Hilbert.FunctionFieldRank
import CCDN.Hilbert.StandardMonomials
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Eventual linearity from a linear Hilbert bound

The standard monomial set eventually consists of finitely many disjoint rays.
Its sufficiently high degree shells therefore have constant cardinality.
-/

@[expose] public section
namespace CCDN
noncomputable section

/-- Any linear upper bound on a filtered coordinate ring implies an eventually
affine Hilbert function, with natural slope at most that upper-bound slope. -/
theorem filteredCoordinateSpace_eventually_linear {K σ : Type*} [Field K] [Fintype σ]
    [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) (C : ℕ)
    (hbound : ∀ N ≥ 14, Module.finrank K (filteredCoordinateSpace I N) ≤ C * (N + 2)) :
    ∃ d ≤ C, HasFilteredCurveDegree I d := by
  classical
  let S := Ideal.standardExponents I MonomialOrder.degLex
  have hS := Ideal.isLowerSet_standardExponents I MonomialOrder.degLex
  let B := 2 * C + 14
  have hB : 0 < B := by dsimp [B]; omega
  let Rays := {p : σ × (σ → Fin B) // (p.2 p.1).val = 0 ∧ ∀ n, exponentRay B p.1 p.2 n ∈ S}
  have hray_deg (j : σ) (b : σ → Fin B) (n : ℕ) (hb : (b j).val = 0) :
      Finsupp.degree (exponentRay B j b n) = n + ∑ k, (b k).val := by
    have h := Finsupp.sum_update_add
      (Finsupp.equivFunOnFinite.symm (fun k => (b k).val)) j n
      (fun _ v => v) (fun _ => rfl) (fun _ _ _ => rfl)
    change (exponentRay B j b n).sum (fun _ v => v) = _
    simpa [exponentRay, Finsupp.sum_fintype, hb, add_comm] using h
  have hwt_le (b : σ → Fin B) : (∑ k, (b k).val) ≤ Fintype.card σ * B :=
    (Finset.sum_le_sum fun k _ => (b k).isLt.le).trans_eq (by simp)
  obtain ⟨M, _, hM⟩ := lowerSet_rays_eventually_full S hS B
  let N := M + Fintype.card σ * B
  let d := Nat.card Rays
  have hN (n : ℕ) (hn : N ≤ n) :
      Nat.card {a : σ →₀ ℕ // a ∈ S ∧ Finsupp.degree a = n} = d := by
    have hweight (b : σ → Fin B) : (∑ k, (b k).val) ≤ n := by have := hwt_le b; omega
    have htail (b : σ → Fin B) : M ≤ n - ∑ k, (b k).val := by have := hwt_le b; omega
    let φ : Rays → {a : σ →₀ ℕ // a ∈ S ∧ Finsupp.degree a = n} :=
      fun p => ⟨exponentRay B p.val.1 p.val.2 (n - ∑ k, (p.val.2 k).val), p.property.2 _, by
        rw [hray_deg _ _ _ p.property.1]; exact Nat.sub_add_cancel (hweight p.val.2)⟩
    have hinj : Function.Injective φ := by
      intro p q he
      have he' := congrArg Subtype.val he
      have hj : p.val.1 = q.val.1 := by
        by_contra hj
        have hh := congrArg (fun a : σ →₀ ℕ => a p.val.1) he'
        change exponentRay _ _ _ _ _ = exponentRay _ _ _ _ _ at hh
        simp [hj] at hh
        have := htail p.val.2; have := (q.val.2 p.val.1).isLt; omega
      refine Subtype.ext (Prod.ext hj (funext fun k => Fin.ext ?_))
      by_cases hk : k = p.val.1
      · subst k; rw [p.property.1, hj, q.property.1]
      · have hh := congrArg (fun a : σ →₀ ℕ => a k) he'
        change exponentRay _ _ _ _ _ = exponentRay _ _ _ _ _ at hh
        simpa [hk, show k ≠ q.val.1 by simpa [hj] using hk] using hh
    have hsurj : Function.Surjective φ := by
      intro a
      have hex : ∃ j, B ≤ a.val j := by
        by_contra! h
        have hs : Finsupp.degree a.val ≤ Fintype.card σ * B := by
          rw [Finsupp.degree_eq_sum]
          exact (Finset.sum_le_sum fun k _ => (h k).le).trans_eq (by simp)
        rw [a.property.2] at hs; omega
      obtain ⟨j, hj⟩ := hex
      have hsmall (k : σ) (hk : k ≠ j) : a.val k < B := by
        by_contra h
        exact hk (standard_at_most_one_large I C hbound a.property.1 (by omega) hj)
      let b : σ → Fin B := fun k => if hk : k = j then ⟨0, hB⟩ else ⟨a.val k, hsmall k hk⟩
      have hbj : (b j).val = 0 := by simp [b]
      have heq : exponentRay B j b (a.val j) = a.val := by
        ext k; by_cases hk : k = j <;> simp [exponentRay_apply, hk, b]
      have hdegree : a.val j + ∑ k, (b k).val = n := by
        rw [← hray_deg j b _ hbj, heq]; exact a.property.2
      have hfull : ∀ k, exponentRay B j b k ∈ S :=
        (hM j b (a.val j) (by have := hwt_le b; omega)).mp (heq.symm ▸ a.property.1)
      refine ⟨⟨(j, b), hbj, hfull⟩, Subtype.ext ?_⟩
      change exponentRay B j b (n - ∑ k, (b k).val) = a.val
      rw [show n - ∑ k, (b k).val = a.val j by omega, heq]
    exact (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)).symm
  have hsucc (m : ℕ) : Module.finrank K (filteredCoordinateSpace I (m + 1)) =
      Module.finrank K (filteredCoordinateSpace I m) +
      Nat.card {a : σ →₀ ℕ // a ∈ S ∧ Finsupp.degree a = m + 1} := by
    let A₁ := Ideal.boundedStandardExponents I MonomialOrder.degLex (m + 1)
    let A₀ := Ideal.boundedStandardExponents I MonomialOrder.degLex m
    let E := {a : σ →₀ ℕ // a ∈ S ∧ Finsupp.degree a = m + 1}
    let φ : A₁ → A₀ ⊕ E := fun a =>
      if h : Finsupp.degree a.val ≤ m then Sum.inl ⟨a.val, a.property.1, h⟩
      else Sum.inr ⟨a.val, a.property.1, by have := a.property.2; omega⟩
    let ψ : A₀ ⊕ E → A₁ := fun
      | .inl b => ⟨b.val, b.property.1, b.property.2.trans (by omega)⟩
      | .inr e => ⟨e.val, e.property.1, e.property.2.le⟩
    have hright : Function.RightInverse ψ φ := fun
      | .inl b => by dsimp [ψ, φ]; rw [dite_eq_left b.property.2]
      | .inr e => by dsimp [ψ, φ]; rw [dite_eq_right (by rw [e.property.2]; omega)]
    let : Finite E := Finite.of_injective (fun e : E => ψ (Sum.inr e))
      (fun a b h => Sum.inr.inj (hright.injective h))
    rw [filteredCoordinateSpace_finrank_eq_standard_card,
      filteredCoordinateSpace_finrank_eq_standard_card]
    exact (Nat.card_congr ⟨φ, ψ, fun a => by dsimp [φ]; split_ifs <;> rfl, hright⟩).trans
      Nat.card_sum
  have hformula (k : ℕ) : Module.finrank K (filteredCoordinateSpace I (N + k)) =
      Module.finrank K (filteredCoordinateSpace I N) + d * k := by
    induction k with
    | zero => simp
    | succ k hk =>
      rw [show N + (k + 1) = (N + k) + 1 by omega, hsucc,
        hN (N + k + 1) (by omega), hk]
      ring
  have hd : d ≤ C := by
    by_contra h
    have hbig := hbound (N + (C * (N + 16) + 14)) (by omega)
    rw [hformula] at hbig
    nlinarith [Nat.mul_le_mul_right (C * (N + 16) + 14) (show C + 1 ≤ d by omega)]
  refine ⟨d, hd, N, (Module.finrank K (filteredCoordinateSpace I N) : ℤ) - d * N, fun n hn => ?_⟩
  have he := hformula (n - N)
  rw [Nat.add_sub_of_le hn] at he
  rw [he]; push_cast; rw [Nat.cast_sub hn]; ring

/-- A transcendental coordinate contributes all of its powers to the filtration. -/
theorem transcendental_coordinate_filtered_lower {K σ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) {j : σ}
    (hj : Transcendental K ((Ideal.Quotient.mk I) (MvPolynomial.X j))) (N : ℕ) :
    N + 1 ≤ Module.finrank K (filteredCoordinateSpace I N) := by
  classical
  have hmem (k : Fin (N + 1)) :
      ((Ideal.Quotient.mk I) (MvPolynomial.X j)) ^ k.val ∈ filteredCoordinateSpace I N :=
    Submodule.mem_map.mpr ⟨MvPolynomial.X j ^ k.val, by
      rw [MvPolynomial.mem_restrictTotalDegree, MvPolynomial.totalDegree_X_pow]; omega, by simp⟩
  have hv : LinearIndependent K
      (fun k : Fin (N + 1) => (⟨((Ideal.Quotient.mk I) (MvPolynomial.X j)) ^ k.val, hmem k⟩ :
        filteredCoordinateSpace I N)) :=
    LinearIndependent.of_comp (filteredCoordinateSpace I N).subtype
      (transcendental_powers_independent _ hj (N + 1))
  simpa using hv.fintype_card_le_finrank

end
end CCDN
