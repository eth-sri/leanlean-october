/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.MultiplicationPairingProduct
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! A field basis containing one supplies the complement used by the
multiplication pairing. The resulting product inequality is independent
of the geometric construction of the basis or the length function. -/

@[expose] public section
namespace CCDN
noncomputable section

variable {F K ι : Type*} [Field F] [Field K] [Algebra F K]

variable [Fintype ι] [DecidableEq ι]

/-- A nonnegative submultiplicative length and a minimum condition on
products detected by the last coordinate give the field-basis product
bound. In lattice applications the minimum condition follows because a
detected product lies outside the preceding coordinate hyperplane. -/
theorem field_basis_multiplication_minimum_product
    (b : Module.Basis ι F K) (p q : ι) (hpq : p ≠ q) (hp : b p = 1)
    (N : K → ℝ) (hN : ∀ x, 0 ≤ N x)
    (hmul : ∀ x y, N (x * y) ≤ N x * N y) (hunit : 1 ≤ N (b p))
    (hminimum : ∀ i j : {i : ι // i ≠ p ∧ i ≠ q},
      b.coord q (b i * b j) ≠ 0 → N (b q) ≤ N (b i * b j)) :
    N (b q) ^ Fintype.card ι ≤ (∏ i, N (b i)) ^ 2 := by
  /- The span of the basis vectors `b i` with `i ≠ p` and `i ≠ q` is the intersection of the kernels
  of the coordinate functionals `b.coord q` and `b.coord p`. -/
  /- The original basis vectors other than the unit and the distinguished
  last vector form a basis of the two coordinate kernels. -/
  /- The vectors of `fieldBasisMiddle b p q` are the original basis vectors `b i`. -/
  have hspan : Submodule.span F (Set.range (fun i : {i : ι // i ≠ p ∧ i ≠ q} ↦ b i)) =
      hyperplaneComplement (b.coord q) (b.coord p) := by
    rw [show Set.range (fun i : {i : ι // i ≠ p ∧ i ≠ q} ↦ b i) = b '' {i : ι | i ≠ p ∧ i ≠ q} by
      ext x; simp]
    ext x
    rw [b.mem_span_image]
    change (↑(b.repr x).support ⊆ {i : ι | i ≠ p ∧ i ≠ q}) ↔ b.repr x q = 0 ∧ b.repr x p = 0
    refine ⟨fun hx => ⟨by_contra fun hq => (hx (Finsupp.mem_support_iff.mpr hq)).2 rfl,
      by_contra fun hp => (hx (Finsupp.mem_support_iff.mpr hp)).1 rfl⟩,
      fun ⟨hq, hp⟩ i hi => ?_⟩
    have hi' := Finsupp.mem_support_iff.mp hi
    exact ⟨fun h ↦ hi' (h ▸ hp), fun h ↦ hi' (h ▸ hq)⟩
  let mid : Module.Basis {i : ι // i ≠ p ∧ i ≠ q} F (hyperplaneComplement (b.coord q) (b.coord p)) :=
    (Module.Basis.span (b.linearIndependent.comp
      (fun i : {i : ι // i ≠ p ∧ i ≠ q} ↦ (i : ι)) Subtype.val_injective)).map
      (LinearEquiv.ofEq _ _ hspan)
  have hℓ : b.coord q ≠ 0 := fun h => by
    have hh := LinearMap.congr_fun h (b q); simp at hh
  have hℓ1 : b.coord q 1 = 0 := by rw [← hp]; simp [Module.Basis.coord_apply, hpq]
  have hμ1 : b.coord p 1 = 1 := by rw [← hp]; simp [Module.Basis.coord_apply]
  have hs (i : ι) : i ∈ (Finset.univ.erase p).erase q ↔ i ≠ p ∧ i ≠ q := by simp [and_comm]
  have hq : q ∈ Finset.univ.erase p := by simp [hpq.symm]
  have hcard : Fintype.card {i : ι // i ≠ p ∧ i ≠ q} + 2 = Fintype.card ι := by
    rw [Fintype.card_of_subtype _ hs]
    have h₁ := Finset.card_erase_add_one hq
    have h₂ := Finset.card_erase_add_one (Finset.mem_univ p)
    simpa only [Finset.card_univ] using (show
      ((Finset.univ.erase p).erase q).card + 2 = Finset.univ.card by omega)
  have hpair := hyperplane_multiplication_minimum_product
    (b.coord q) (b.coord p) hℓ hℓ1 hμ1 mid
    (fun i ↦ N (b i)) (hN (b q)) (fun i j hij ↦
      (hminimum i j (by simpa [mid] using hij)).trans (hmul (b i) (b j)))
  rw [hcard] at hpair
  have hprod : 0 ≤ N (b q) * ∏ i : {i : ι // i ≠ p ∧ i ≠ q}, N (b i) :=
    mul_nonneg (hN _) (Finset.prod_nonneg (fun i _ ↦ hN _))
  have hfull :
      N (b q) * ∏ i : {i : ι // i ≠ p ∧ i ≠ q}, N (b i) ≤ ∏ i, N (b i) := by
    have hprod_eq : ∏ i, N (b i) = N (b p) * N (b q) * ∏ i : {i : ι // i ≠ p ∧ i ≠ q}, N (b i) := by
      rw [← Finset.prod_subtype _ hs (fun x => N (b x)), mul_assoc,
        Finset.mul_prod_erase _ (fun x => N (b x)) hq,
        Finset.mul_prod_erase _ (fun x => N (b x)) (Finset.mem_univ p)]
    rw [hprod_eq, mul_assoc]
    exact le_mul_of_one_le_left hprod hunit
  exact hpair.trans (pow_le_pow_left₀ hprod hfull 2)
end
end CCDN
