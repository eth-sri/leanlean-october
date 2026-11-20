/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.OrthantHilbertPolynomial

/-! The maximal orthants determine the leading term of the Hilbert polynomial.
In particular its factorial-normalized leading coefficient is a positive
integer, counted by cells of the standard-exponent partition. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- A nonempty sum of shifted binomial polynomials of dimensions `dim i` has degree the maximal
dimension `m` and leading coefficient `d / m!`, where `d > 0` is the number of summands of maximal
dimension. -/
lemma sum_preHilbertPoly_leading {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (dim shift : ι → ℕ) :
    let m := s.sup dim
    let d := (s.filter (fun i => dim i = m)).card
    let P := ∑ i ∈ s, Polynomial.preHilbertPoly ℚ (dim i) (shift i)
    0 < d ∧ P.natDegree = m ∧ P.leadingCoeff = (d : ℚ) / m.factorial := by
  dsimp only
  let m := s.sup dim
  let d := (s.filter (fun i => dim i = m)).card
  let P := ∑ i ∈ s, Polynomial.preHilbertPoly ℚ (dim i) (shift i)
  have hd : 0 < d := by
    apply Finset.card_pos.mpr
    obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup s hs dim
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, he.symm⟩⟩
  have hle : P.natDegree ≤ m := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    rw [Polynomial.natDegree_preHilbertPoly]
    exact Finset.le_sup hi
  have hc : P.coeff m = (d : ℚ) * (m.factorial : ℚ)⁻¹ := by
    simp only [P, Polynomial.finsetSum_coeff]
    calc
      _ = ∑ i ∈ s, if dim i = m then (m.factorial : ℚ)⁻¹ else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases he : dim i = m
        · rw [he, Polynomial.coeff_preHilbertPoly_self, ite_eq_left rfl]
        · rw [ite_eq_right he]
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [Polynomial.natDegree_preHilbertPoly]
          exact lt_of_le_of_ne (Finset.le_sup hi) he
      _ = _ := by rw [← Finset.sum_filter]; simp [d]
  have hc0 : P.coeff m ≠ 0 := by
    rw [hc]
    apply mul_ne_zero
    positivity
    · exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero m)
  have he := le_antisymm hle (Polynomial.le_natDegree_of_ne_zero hc0)
  refine ⟨hd, he, ?_⟩
  rw [Polynomial.leadingCoeff, he, hc, div_eq_mul_inv]

lemma lowerSetOrthantPatterns_nonempty {σ : Type*} [Fintype σ]
    {S : Set (σ → ℕ)} {B : ℕ} (hB : ∀ a, a ∈ S ↔ clampExponent B a ∈ S) (hS : S.Nonempty) :
    (lowerSetOrthantPatterns S B).Nonempty := by
  classical
  obtain ⟨a, ha⟩ := hS
  exact ⟨exponentPattern B a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hB a).mp ha⟩⟩

/-- A nonempty orthant polynomial has positive factorial-normalized multiplicity. -/
theorem lowerSetOrthantPolynomial_positive {σ : Type*} [Fintype σ]
    (S : Set (σ → ℕ)) (B : ℕ) (hs : (lowerSetOrthantPatterns S B).Nonempty) :
    let P := lowerSetOrthantPolynomial S B
    ∃ d : ℕ, 0 < d ∧ P.natDegree ≤ Fintype.card σ ∧
      P.leadingCoeff = (d : ℚ) / P.natDegree.factorial := by
  unfold lowerSetOrthantPolynomial
  obtain ⟨hd, hdeg, hlc⟩ := sum_preHilbertPoly_leading _ hs
    (fun b => Fintype.card (orthantFree b)) orthantBaseDegree
  dsimp only
  rw [hdeg]
  exact ⟨_, hd, Finset.sup_le fun b _ => Fintype.card_subtype_le _, hlc⟩

end
end CCDN
