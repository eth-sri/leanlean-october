import Mathlib.Tactic

import RequestProject.BlockFamilyB1Finsupp

/-! The triangular two-chain isomorphism for simultaneous slides over a
fixed core. Both the family and the core may have infinitely many cells.
Each input chain uses finitely many of the finite correction columns.

-/

noncomputable section

namespace FiniteChains
open BlockFamily

variable {C S I R : Type u} [Ring R]

@[simp] theorem fsOldOneIncl_single (c : C) (a : R) :
    fsOldOneIncl (Z := S) (Finsupp.single c a) = Finsupp.single (Sum.inl c) a := by classical aesop (add simp [Finsupp.single_apply])

variable (lam : S → C →₀ R)
/-- The off-diagonal correction has values entirely in the retained core. -/
def coreSlideCorrection  :
    ((C ⊕ S) →₀ R) →ₗ[R] ((C ⊕ S) →₀ R) :=
  Finsupp.linearCombination R
    (Sum.elim (fun _ : C => 0) (fun s => fsOldOneIncl (lam s)))

@[simp] theorem coreSlideCorrection_single_inl  (c : C) (a : R) :
    coreSlideCorrection lam (Finsupp.single (Sum.inl c) a) = 0 := by
  simp [coreSlideCorrection]

@[simp] theorem coreSlideCorrection_single_inr  (s : S) (a : R) :
    coreSlideCorrection lam (Finsupp.single (Sum.inr s) a) = a • fsOldOneIncl (lam s) := by
  simp [coreSlideCorrection]

theorem coreSlideCorrection_core  (x : C →₀ R) :
    coreSlideCorrection lam (fsOldOneIncl x) = 0 := by
  induction x using Finsupp.induction_linear <;> simp_all []

variable (x : (C ⊕ S) →₀ R)
theorem coreSlideCorrection_square   :
    coreSlideCorrection lam (coreSlideCorrection lam x) = 0 := by
  induction x using Finsupp.induction_linear <;> aesop (add simp [coreSlideCorrection_core])

def coreSlideForward   :=
  LinearMap.id - coreSlideCorrection lam

def coreSlideReverse   :=
  LinearMap.id + coreSlideCorrection lam

@[simp] theorem coreSlideForward_reverse   :
    coreSlideForward lam (coreSlideReverse lam x) = x := by simp_all [coreSlideForward, coreSlideReverse, coreSlideCorrection_square]

@[simp] theorem coreSlideReverse_forward   :
    coreSlideReverse lam (coreSlideForward lam x) = x := by simp_all [coreSlideForward, coreSlideReverse, coreSlideCorrection_square]

/-- A column calculation suffices for the simultaneous boundary identity. -/
theorem coreSlide_boundary 
    (old new : ((C ⊕ S) →₀ R) →ₗ[R] (I →₀ R))
    (hcore : ∀ c, new (Finsupp.single (Sum.inl c) 1) = old (Finsupp.single (Sum.inl c) 1))
    (hextra : ∀ s, new (Finsupp.single (Sum.inr s) 1) =
      old (Finsupp.single (Sum.inr s) 1) + old (fsOldOneIncl (lam s)))
    (x : (C ⊕ S) →₀ R) : new x = old (coreSlideReverse lam x) := by
  have hm : new = old.comp (coreSlideReverse lam) := by
    aesop (add simp [coreSlideReverse])
  exact LinearMap.congr_fun hm x

theorem coreSlideForward_aug_zero  (ε : R →+* ℤ)
    (x : (C ⊕ S) →₀ R) (hx : ∀ k, ε (x k) = 0) (j : C ⊕ S) :
    ε (coreSlideForward lam x j) = 0 := by
  have hc : ε (coreSlideCorrection lam x j) = 0 := by
    rw [coreSlideCorrection, Finsupp.linearCombination_apply, Finsupp.sum_apply,
      map_finsuppSum]
    apply Finset.sum_eq_zero
    intro k hk
    change ε (x k * _) = 0
    rw [map_mul, hx k, zero_mul]
  change ε (x j - coreSlideCorrection lam x j) = 0
  rw [map_sub, hx j, hc, sub_self]

end FiniteChains
