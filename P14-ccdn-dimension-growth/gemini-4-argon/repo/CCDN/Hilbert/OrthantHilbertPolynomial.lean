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

instance finite_boundedLowerExponents {σ : Type*} [Fintype σ]
    (S : Set (σ → ℕ)) (N : ℕ) : Finite {a : σ → ℕ // a ∈ S ∧ ∑ i, a i ≤ N} :=
  Finite.of_injective (fun a => (⟨a.val, a.property.2⟩ :
    {a : σ → ℕ // ∑ i, a i ≤ N}))
    (fun _ _ h => Subtype.ext (congrArg
      (fun a : {a : σ → ℕ // ∑ i, a i ≤ N} => a.val) h))

/-- The orthant polynomial is a finite positive sum of shifted binomial
polynomials. Its coefficients are rational, while its large integer values
count exponent vectors exactly. -/
def lowerSetOrthantPolynomial {σ : Type*} [Fintype σ]
    (S : Set (σ → ℕ)) (B : ℕ) : Polynomial ℚ := by
  classical
  exact ∑ b : σ → Fin (B + 1), if (fun i => (b i).val) ∈ S then
    Polynomial.preHilbertPoly ℚ (Fintype.card (orthantFree b)) (orthantBaseDegree b) else 0

/-- If membership in `S` is determined by clamping exponents at `B`, then for `N ≥ |σ| · B` the
orthant polynomial of `S` evaluated at `N` counts the vectors of `S` of total degree at most `N`. -/
lemma lowerSetOrthantPolynomial_eval {σ : Type*} [Fintype σ]
    (S : Set (σ → ℕ)) (B : ℕ)
    (hstable : ∀ a, a ∈ S ↔ clampExponent B a ∈ S)
    (N : ℕ) (hN : Fintype.card σ * B ≤ N) :
    (lowerSetOrthantPolynomial S B).eval (N : ℚ) =
      (Nat.card {a : σ → ℕ // a ∈ S ∧ ∑ i, a i ≤ N} : ℚ) := by
  classical
  have hob (b : σ → Fin (B + 1)) : orthantBaseDegree b ≤ Fintype.card σ * B :=
    (Finset.sum_le_sum fun i _ => Nat.le_of_lt_succ (b i).isLt).trans_eq (by simp)
  let A := {a : σ → ℕ // a ∈ S ∧ ∑ i, a i ≤ N}
  let f : A → (σ → Fin (B + 1)) := fun a => exponentPattern B a.val
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  simp only [lowerSetOrthantPolynomial, Polynomial.eval_finsetSum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs with hb
  · let E : {a : A // f a = b} ≃
        {a : σ → ℕ // clampExponent B a = (fun i => (b i).val) ∧ ∑ i, a i ≤ N} :=
      { toFun := fun a => ⟨a.val.val, funext fun i => congrArg Fin.val (congrFun a.property i),
          a.val.property.2⟩
        invFun := fun a => ⟨⟨a.val, (hstable a.val).mpr (a.property.1.symm ▸ hb), a.property.2⟩,
          funext fun i => Fin.ext (congrFun a.property.1 i)⟩
        left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
        right_inv := fun _ => Subtype.ext rfl }
    have hbN := (hob b).trans hN
    rw [Nat.card_congr E, ← Nat.card_congr (boundedOrthantEquiv b hbN),
      Nat.card_congr (boundedExponentVectorEquivSym _ _), Nat.card_eq_fintype_card,
      Sym.card_sym_eq_choose, Fintype.card_option,
      show Fintype.card (orthantFree b) + 1 + (N - orthantBaseDegree b) - 1 =
        Fintype.card (orthantFree b) + (N - orthantBaseDegree b) by omega,
      ← Nat.choose_symm_add,
      Polynomial.preHilbertPoly_eq_choose_add_sub _ _ (hbN.trans (Nat.le_add_right _ _))]
    congr 2
    omega
  · have hEmpty : IsEmpty {a : A // f a = b} := ⟨fun a => hb <| by
      have hh := (hstable a.val.val).mp a.val.property.1
      rwa [show clampExponent B a.val.val = (fun i => (b i).val) from
        funext fun i => congrArg Fin.val (congrFun a.property i)] at hh⟩
    rw [Nat.card_eq_zero.mpr (Or.inl hEmpty)]; simp

/-- Every lower exponent set has an eventual counting polynomial.
The threshold and the polynomial are constructed from its finite orthant
partition. -/
theorem lowerSet_eventually_polynomial {σ : Type*} [Fintype σ]
    (S : Set (σ → ℕ)) (hS : IsLowerSet S) :
    ∃ P : Polynomial ℚ, ∃ N : ℕ, ∀ n ≥ N,
      P.eval (n : ℚ) =
        (Nat.card {a : σ → ℕ // a ∈ S ∧ ∑ i, a i ≤ n} : ℚ) := by
  obtain ⟨B, _, hB⟩ := lowerSet_clamp_stabilizes S hS
  exact ⟨lowerSetOrthantPolynomial S B, Fintype.card σ * B,
    fun n hn => lowerSetOrthantPolynomial_eval S B hB n hn⟩

end
end CCDN
