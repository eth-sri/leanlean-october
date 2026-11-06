import RequestProject.BlockFamilyB1Finsupp
import RequestProject.Tac


/-! The triangular two-chain isomorphism for simultaneous slides over a
fixed core. Both the family and the core may have infinitely many cells.
Each input chain uses finitely many of the finite correction columns.

-/

noncomputable section

namespace FiniteChains
open BlockFamily

universe u
variable {C S I R : Type u} [Ring R]

@[simp] theorem fsOldOneIncl_single (c : C) (a : R) :
    fsOldOneIncl (Z := S) (Finsupp.single c a) = Finsupp.single (Sum.inl c) a := by
  classical
  ext i
  cases i <;> simp [Finsupp.single_apply]

/-- The off-diagonal correction has values entirely in the retained core. -/
def coreSlideCorrection (lam : S → C →₀ R) :
    ((C ⊕ S) →₀ R) →ₗ[R] ((C ⊕ S) →₀ R) :=
  Finsupp.linearCombination R
    (Sum.elim (fun _ : C => 0) (fun s => fsOldOneIncl (lam s)))

@[simp] theorem coreSlideCorrection_single_inl (lam : S → C →₀ R) c a :
    coreSlideCorrection lam (Finsupp.single (Sum.inl c) a) = 0 := by
  simp [coreSlideCorrection]

@[simp] theorem coreSlideCorrection_single_inr (lam : S → C →₀ R) s a :
    coreSlideCorrection lam (Finsupp.single (Sum.inr s) a) = a • fsOldOneIncl (lam s) := by
  simp [coreSlideCorrection]

theorem coreSlideCorrection_core (lam : S → C →₀ R) x :
    coreSlideCorrection lam (fsOldOneIncl x) = 0 := by
  induction x using Finsupp.induction_linear <;> simp_all

theorem coreSlideCorrection_square lam (x : (C ⊕ S) →₀ R) :
    coreSlideCorrection lam (coreSlideCorrection lam x) = 0 := by
  lin_ind x c a =>
      cases c with
      | inl c => simp
      | inr s =>
          rw [coreSlideCorrection_single_inr, map_smul, coreSlideCorrection_core, smul_zero]

def coreSlideForward (lam : S → C →₀ R) :=
  LinearMap.id - coreSlideCorrection lam

def coreSlideReverse (lam : S → C →₀ R) :=
  LinearMap.id + coreSlideCorrection lam

@[simp] theorem coreSlideForward_reverse lam (x : (C ⊕ S) →₀ R) :
    coreSlideForward lam (coreSlideReverse lam x) = x := by
  grind [coreSlideForward, coreSlideReverse, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, map_add, coreSlideCorrection_square]

@[simp] theorem coreSlideReverse_forward lam (x : (C ⊕ S) →₀ R) :
    coreSlideReverse lam (coreSlideForward lam x) = x := by
  grind [coreSlideForward, coreSlideReverse, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub, coreSlideCorrection_square]

/-- A column calculation suffices for the simultaneous boundary identity. -/
theorem coreSlide_boundary lam
    (old new : ((C ⊕ S) →₀ R) →ₗ[R] (I →₀ R))
    (hcore : ∀ c, new (Finsupp.single (Sum.inl c) 1) = old (Finsupp.single (Sum.inl c) 1))
    (hextra : ∀ s, new (Finsupp.single (Sum.inr s) 1) =
      old (Finsupp.single (Sum.inr s) 1) + old (fsOldOneIncl (lam s)))
    x : new x = old (coreSlideReverse lam x) := by
  have hm : new = old.comp (coreSlideReverse lam) := by
    apply Finsupp.lhom_ext
    intro k a
    rw [← Finsupp.smul_single_one k a, map_smul, map_smul]
    congr 1
    cases k with
    | inl c => simp_all [coreSlideReverse]
    | inr s => simp_all [coreSlideReverse, map_add]
  simp_all

theorem coreSlideForward_aug_zero lam (ε : R →+* ℤ)
    x (hx : ∀ k, ε (x k) = 0) (j : C ⊕ S) :
    ε (coreSlideForward lam x j) = 0 := by
  have hc : ε (coreSlideCorrection lam x j) = 0 := by
    rw [coreSlideCorrection, Finsupp.linearCombination_apply, Finsupp.sum_apply,
      map_finsuppSum]
    apply Finset.sum_eq_zero
    simp_all
  change ε (x j - coreSlideCorrection lam x j) = 0
  grind
