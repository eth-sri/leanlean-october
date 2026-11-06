/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.MonomialRays
import Mathlib.RingTheory.Algebraic.Defs
import CCDN.Hilbert.FunctionFieldRank
import CCDN.Hilbert.StandardMonomials
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Eventual linearity from a linear Hilbert bound

The standard monomial set eventually consists of finitely many disjoint rays.
Its sufficiently high degree shells therefore have constant cardinality.
-/

namespace CCDN

section
variable {σ : Type*} [Fintype σ]

/-- Full coordinate rays with uniquely normalized base points. -/
def fullExponentRays [DecidableEq σ]
    (S : Set (σ →₀ ℕ)) (B : ℕ) :=
  {p : σ × (σ → Fin B) // (p.2 p.1).val = 0 ∧
    ∀ n, exponentRay B p.1 p.2 n ∈ S}

lemma exponentRay_degree 
    (B : ℕ) (j : σ) (b : σ → Fin B) (n : ℕ) (hb : (b j).val = 0) :
    Finsupp.degree (exponentRay B j b n) = n + ∑ k, (b k).val := by
  have h := Finsupp.sum_update_add
    (Finsupp.equivFunOnFinite.symm (fun k => (b k).val)) j n
    (fun _ v => v) (fun _ => rfl) (fun _ _ _ => rfl)
  change (exponentRay B j b n).sum (fun _ v => v) = _
  simpa [exponentRay, Finsupp.sum_fintype, hb, add_comm] using h

lemma rayBase_weight_le {B : ℕ} (b : σ → Fin B) :
    (∑ k, (b k).val) ≤ Fintype.card σ * B := by
  calc
    _ ≤ ∑ _ : σ, B := Finset.sum_le_sum (fun k _ => (b k).isLt.le)
    _ = _ := by simp

/-- A lower monomial set confined to coordinate rays has eventually constant
shell cardinalities. -/
theorem lowerSet_shell_card_eventually_constant [DecidableEq σ]
    (S : Set (σ →₀ ℕ)) (hS : IsLowerSet S) (B : ℕ) (hB : 0 < B)
    (hunique : ∀ a ∈ S, ∀ i j, B ≤ a i → B ≤ a j → i = j) :
    ∃ N, ∀ n ≥ N,
      Nat.card {a : σ →₀ ℕ // a ∈ S ∧ Finsupp.degree a = n} =
        Nat.card (fullExponentRays S B) := by
  obtain ⟨M, hMB, hM⟩ : ∃ M ≥ B, ∀ (j : σ) (b : σ → Fin B) (n : ℕ), M ≤ n →
      (exponentRay B j b n ∈ S ↔ ∀ k, exponentRay B j b k ∈ S) := by
    have hex (p : σ × (σ → Fin B)) :
        ∃ m, (∀ k, exponentRay B p.1 p.2 k ∈ S) ∨ exponentRay B p.1 p.2 m ∉ S := by
      by_cases h : ∀ k, exponentRay B p.1 p.2 k ∈ S
      · simp_all
      · grind
    choose m hm using hex
    refine ⟨Finset.univ.sup m + B, by omega, ?_⟩
    intro j b n hn
    constructor
    · intro hmem
      rcases hm (j, b) with hall | hnot
      · exact hall
      · exfalso
        apply hnot
        apply hS _ hmem
        intro k
        simp
        split_ifs
        · have hle := Finset.le_sup (f := m) (Finset.mem_univ (j, b))
          omega
        grind
    · grind
  refine ⟨M + Fintype.card σ * B, ?_⟩
  intro n hn
  have hweight (b : σ → Fin B) : (∑ k, (b k).val) ≤ n := by
    have := rayBase_weight_le b
    omega
  have htail (b : σ → Fin B) : M ≤ n - ∑ k, (b k).val := by
    have := rayBase_weight_le b
    omega
  let φ : fullExponentRays S B → {a : σ →₀ ℕ // a ∈ S ∧ Finsupp.degree a = n} :=
    fun p => ⟨exponentRay B p.val.1 p.val.2 (n - ∑ k, (p.val.2 k).val),
      p.property.2 _, by
        rw [exponentRay_degree B _ _ _ p.property.1]
        simp_all⟩
  have hinj : Function.Injective φ := by
    intro p q he
    have he' := congrArg Subtype.val he
    have hj : p.val.1 = q.val.1 := by
      have hh := congrArg (fun a => a p.val.1) he'
      change exponentRay _ _ _ _ _ = exponentRay _ _ _ _ _ at hh
      simp at hh
      have := htail p.val.2
      grind
    apply Subtype.ext
    apply Prod.ext hj
    funext k
    apply Fin.ext
    by_cases hk : k = p.val.1
    · grind
    · have hkq : k ≠ q.val.1 := by simpa [hj] using hk
      have hh := congrArg (fun a => a k) he'
      change exponentRay _ _ _ _ _ = exponentRay _ _ _ _ _ at hh
      simp_all
  have hsurj : Function.Surjective φ := by
    intro a
    have hex : ∃ j, B ≤ a.val j := by
      by_contra h
      push Not at h
      have hs : Finsupp.degree a.val ≤ Fintype.card σ * B := by
        rw [Finsupp.degree_eq_sum]
        exact (Finset.sum_le_sum (fun k _ => (h k).le)).trans_eq (by simp)
      grind
    obtain ⟨j, hj⟩ := hex
    have hsmall (k : σ) (hk : k ≠ j) : a.val k < B := by grind
    let b : σ → Fin B := fun k => if hk : k = j then ⟨0, hB⟩ else ⟨a.val k, hsmall k hk⟩
    have hbj : (b j).val = 0 := by grind
    have heq : exponentRay B j b (a.val j) = a.val := by aesop
    have hdegree : a.val j + ∑ k, (b k).val = n := by
      rw [← exponentRay_degree B j b _ hbj, heq]
      exact a.property.2
    have hjM : M ≤ a.val j := by
      have := rayBase_weight_le b
      omega
    have hfull :=
      (hM j b (a.val j) hjM).mp (heq.symm ▸ a.property.1)
    refine ⟨⟨(j, b), hbj, hfull⟩, ?_⟩
    grind
  exact (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)).symm

end

variable {K σ : Type*} [Field K] [Fintype σ] (I : Ideal (MvPolynomial σ K))

/-- Splitting off the top degree shell gives the Hilbert-function increment. -/
theorem standard_card_succ
    [LinearOrder σ] (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace I (N + 1)) =
      Module.finrank K (filteredCoordinateSpace I N) +
      Nat.card {a : σ →₀ ℕ // a ∈ Ideal.standardExponents I MonomialOrder.degLex ∧
        Finsupp.degree a = N + 1} := by
  let S := Ideal.standardExponents I MonomialOrder.degLex
  let A := Ideal.boundedStandardExponents I MonomialOrder.degLex (N + 1)
  let B := Ideal.boundedStandardExponents I MonomialOrder.degLex N
  let E := {a : σ →₀ ℕ // a ∈ S ∧ Finsupp.degree a = N + 1}
  let φ : A → B ⊕ E := fun a =>
    if h : Finsupp.degree a.val ≤ N then Sum.inl ⟨a.val, a.property.1, h⟩
    else Sum.inr ⟨a.val, a.property.1, by
      have ha := a.property.2
      omega⟩
  let ψ : B ⊕ E → A := fun p => match p with
    | .inl b => ⟨b.val, b.property.1, b.property.2.trans (by omega)⟩
    | .inr e => ⟨e.val, e.property.1, e.property.2.le⟩
  have hright : Function.RightInverse ψ φ := by
    intro p
    rcases p with b | e
    · have hb := b.property.2
      grind
    grind
  let equiv : A ≃ B ⊕ E := ⟨φ, ψ, (by grind), hright⟩
  let : Finite E := Finite.of_injective (fun e => ψ (Sum.inr e))
    (fun a b h => Sum.inr.inj ((Function.RightInverse.injective hright) h))
  rw [filteredCoordinateSpace_finrank_eq_standard_card,
    filteredCoordinateSpace_finrank_eq_standard_card]
  exact (Nat.card_congr equiv).trans Nat.card_sum

/-- A transcendental coordinate contributes all of its powers to the filtration. -/
theorem transcendental_coordinate_filtered_lower
    {j : σ}
    (hj : Transcendental K ((Ideal.Quotient.mk I) (MvPolynomial.X j))) (N : ℕ) :
    N + 1 ≤ Module.finrank K (filteredCoordinateSpace I N) := by
  have hlin := transcendental_powers_independent
    ((Ideal.Quotient.mk I) (MvPolynomial.X j)) hj (N + 1)
  have hmem (k : Fin (N + 1)) :
      ((Ideal.Quotient.mk I) (MvPolynomial.X j)) ^ k.val ∈ filteredCoordinateSpace I N := by
    apply Submodule.mem_map.mpr
    refine ⟨MvPolynomial.X j ^ k.val, ?_, by simp⟩
    rw [MvPolynomial.mem_restrictTotalDegree, MvPolynomial.totalDegree_X_pow]
    omega
  let v : Fin (N + 1) → filteredCoordinateSpace I N :=
    fun k => ⟨((Ideal.Quotient.mk I) (MvPolynomial.X j)) ^ k.val, hmem k⟩
  have hv : LinearIndependent K v :=
    LinearIndependent.of_comp (filteredCoordinateSpace I N).subtype hlin
  simpa using hv.fintype_card_le_finrank

