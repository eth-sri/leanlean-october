/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.MonomialOrthants
public import CCDN.ForMathlib.MvPolynomial
public import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.Data.Sym.Card

/-! Counting the finite orthant partition gives an eventual polynomial
for every lower set of exponent vectors, in arbitrary finite dimension. -/

@[expose] public section
namespace CCDN
noncomputable section

open Classical in
/-- The bijection between exponent vectors in `σ → ℕ` of total degree at most `N` and multisets of
size `N` on `Option σ`. -/
def boundedExponentVectorEquivSym (σ : Type*) [Fintype σ] (N : ℕ) :
    {a : σ → ℕ // ∑ i, a i ≤ N} ≃ Sym (Option σ) N :=
  (Sym.equivNatSumLeOfFintype σ N).symm

instance finite_boundedExponentVectors {σ : Type*} [Fintype σ] (N : ℕ) :
    Finite {a : σ → ℕ // ∑ i, a i ≤ N} :=
  Finite.of_equiv (Sym (Option σ) N) (boundedExponentVectorEquivSym σ N).symm

open Classical in
private lemma card_boundedExponentVectors {σ : Type*} [Fintype σ] (N : ℕ) :
    Nat.card {a : σ → ℕ // ∑ i, a i ≤ N} =
      (Fintype.card σ + N).choose (Fintype.card σ) := by
  rw [Nat.card_congr (boundedExponentVectorEquivSym σ N), Nat.card_eq_fintype_card,
    Sym.card_sym_eq_choose, Fintype.card_option]
  rw [show Fintype.card σ + 1 + N - 1 = Fintype.card σ + N by omega]
  exact Nat.choose_symm_add.symm

instance finite_boundedLowerExponents {σ : Type*} [Fintype σ]
    (S : Set (σ → ℕ)) (N : ℕ) : Finite {a : σ → ℕ // a ∈ S ∧ ∑ i, a i ≤ N} :=
  Finite.of_injective (fun a => (⟨a.val, a.property.2⟩ :
    {a : σ → ℕ // ∑ i, a i ≤ N}))
    (fun _ _ h => Subtype.ext (congrArg
      (fun a : {a : σ → ℕ // ∑ i, a i ≤ N} => a.val) h))

private lemma orthantBaseDegree_le {σ : Type*} [Fintype σ] {B : ℕ}
    (b : σ → Fin (B + 1)) : orthantBaseDegree b ≤ Fintype.card σ * B := by
  calc
    _ ≤ ∑ _ : σ, B := Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (b i).isLt)
    _ = _ := by simp

open Classical in
/-- The cells of the clamped orthant partition that lie in `S`. -/
def lowerSetOrthantPatterns {σ : Type*} [Fintype σ]
    (S : Set (σ → ℕ)) (B : ℕ) : Finset (σ → Fin (B + 1)) :=
  Finset.univ.filter (fun b => (fun i => (b i).val) ∈ S)

/-- The orthant polynomial is a finite positive sum of shifted binomial
polynomials. Its coefficients are rational, while its large integer values
count exponent vectors exactly. -/
def lowerSetOrthantPolynomial {σ : Type*} [Fintype σ]
    (S : Set (σ → ℕ)) (B : ℕ) : Polynomial ℚ :=
  ∑ b ∈ lowerSetOrthantPatterns S B,
    Polynomial.preHilbertPoly ℚ (Fintype.card (orthantFree b)) (orthantBaseDegree b)

section

variable {σ : Type*} [Fintype σ]
  (S : Set (σ → ℕ))
include σ S

/-- If membership in `S` is determined by clamping exponents at `B`, then for `N ≥ |σ| · B` the
orthant polynomial of `S` evaluated at `N` counts the vectors of `S` of total degree at most `N`. -/
lemma lowerSetOrthantPolynomial_eval (B : ℕ)
    (hstable : ∀ a, a ∈ S ↔ clampExponent B a ∈ S)
    (N : ℕ) (hN : Fintype.card σ * B ≤ N) :
    (lowerSetOrthantPolynomial S B).eval (N : ℚ) =
      (Nat.card {a : σ → ℕ // a ∈ S ∧ ∑ i, a i ≤ N} : ℚ) := by
  classical
  let A := {a : σ → ℕ // a ∈ S ∧ ∑ i, a i ≤ N}
  let T := lowerSetOrthantPatterns S B
  let f (a : A) : T := ⟨exponentPattern B a.val,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hstable _).mp a.property.1⟩⟩
  change (∑ b ∈ T, Polynomial.preHilbertPoly ℚ (Fintype.card (orthantFree b))
    (orthantBaseDegree b)).eval (N : ℚ) = (Nat.card A : ℚ)
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma, Nat.cast_sum,
    Polynomial.eval_finsetSum, ← Finset.sum_attach, ← Finset.univ_eq_attach]
  apply Finset.sum_congr rfl
  intro b _
  let e := orthantExpandEquiv b.val
  let E : {c : orthantFree b.val → ℕ // ∑ i, c i ≤ N - orthantBaseDegree b.val} ≃
      {a : {a : σ → ℕ // exponentPattern B a = b.val} // ∑ i, a.val i ≤ N} :=
    e.subtypeEquiv fun c => by
      change _ ↔ ∑ i, orthantExpand b.val c i ≤ _
      rw [orthantExpand_sum]
      have := (orthantBaseDegree_le b.val).trans hN
      omega
  let G : {a : A // f a = b} ≃ {a : {a : σ → ℕ // exponentPattern B a = b.val} // ∑ i, a.val i ≤ N} :=
    { toFun := fun a => ⟨⟨a.val.val, congrArg Subtype.val a.property⟩, a.val.property.2⟩
      invFun := fun a => ⟨⟨a.val.val, (hstable _).mpr (by
        change (fun i => (exponentPattern B a.val.val i).val) ∈ S
        rw [a.val.property]
        exact (Finset.mem_filter.mp b.property).2), a.property⟩, Subtype.ext a.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr (G.trans E.symm), card_boundedExponentVectors,
    Polynomial.preHilbertPoly_eq_choose_add_sub]
  · congr 2
    have := (orthantBaseDegree_le b.val).trans hN
    omega
  · exact ((orthantBaseDegree_le b.val).trans hN).trans (Nat.le_add_right _ _)

end

end
end CCDN
