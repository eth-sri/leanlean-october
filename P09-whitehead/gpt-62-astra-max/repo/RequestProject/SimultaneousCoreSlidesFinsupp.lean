module

public import RequestProject.BlockFamilyB1Finsupp

@[expose] public section

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

variable (lam : S → C →₀ R)

/-- The off-diagonal correction has values entirely in the retained core. -/
def coreSlideCorrection :
    ((C ⊕ S) →₀ R) →ₗ[R] ((C ⊕ S) →₀ R) :=
  Finsupp.linearCombination R
    (Sum.elim (fun _ : C => 0) (fun s => fsOldOneIncl (lam s)))

@[simp] theorem coreSlideCorrection_single_inl (c : C) (a : R) :
    coreSlideCorrection lam (Finsupp.single (Sum.inl c) a) = 0 := by
  simp [coreSlideCorrection]

@[simp] theorem coreSlideCorrection_single_inr (s : S) (a : R) :
    coreSlideCorrection lam (Finsupp.single (Sum.inr s) a) = a • fsOldOneIncl (lam s) := by
  simp [coreSlideCorrection]

theorem coreSlideCorrection_core (x : C →₀ R) :
    coreSlideCorrection lam (fsOldOneIncl x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp_all
  | single c a => simp

theorem coreSlideCorrection_square (x : (C ⊕ S) →₀ R) :
    coreSlideCorrection lam (coreSlideCorrection lam x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp_all
  | single c a =>
      cases c with
      | inl c => simp
      | inr s =>
          rw [coreSlideCorrection_single_inr, map_smul, coreSlideCorrection_core, smul_zero]

def coreSlideForward :=
  LinearMap.id - coreSlideCorrection lam

def coreSlideReverse :=
  LinearMap.id + coreSlideCorrection lam

variable (x : (C ⊕ S) →₀ R)

@[simp] theorem coreSlideForward_reverse :
    coreSlideForward lam (coreSlideReverse lam x) = x := by
  simp only [coreSlideForward, coreSlideReverse, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.id_apply, map_add, coreSlideCorrection_square]
  abel

@[simp] theorem coreSlideReverse_forward :
    coreSlideReverse lam (coreSlideForward lam x) = x := by
  simp only [coreSlideForward, coreSlideReverse, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.id_apply, map_sub, coreSlideCorrection_square]
  abel

/-- A column calculation suffices for the simultaneous boundary identity. -/
theorem coreSlide_boundary
    (old new : ((C ⊕ S) →₀ R) →ₗ[R] (I →₀ R))
    (hcore : ∀ c, new (Finsupp.single (Sum.inl c) 1) = old (Finsupp.single (Sum.inl c) 1))
    (hextra : ∀ s, new (Finsupp.single (Sum.inr s) 1) =
      old (Finsupp.single (Sum.inr s) 1) + old (fsOldOneIncl (lam s)))
    (x : (C ⊕ S) →₀ R) : new x = old (coreSlideReverse lam x) := by
  have hm : new = old.comp (coreSlideReverse lam) := by
    apply Finsupp.lhom_ext
    intro k a
    rw [← Finsupp.smul_single_one k a, map_smul, map_smul]
    congr 1
    cases k with
    | inl c => simp_all [coreSlideReverse]
    | inr s => simp_all [coreSlideReverse, map_add]
  exact LinearMap.congr_fun hm x

theorem coreSlideForward_aug_zero (ε : R →+* ℤ)
    (x : (C ⊕ S) →₀ R) (hx : ∀ k, ε (x k) = 0) (j : C ⊕ S) :
    ε (coreSlideForward lam x j) = 0 := by
  have hc : ε (coreSlideCorrection lam x j) = 0 := by
    rw [coreSlideCorrection, Finsupp.linearCombination_apply, Finsupp.sum_apply,
      map_finsuppSum]
    apply Finset.sum_eq_zero
    simp [map_mul, hx, zero_mul]
  change ε (x j - coreSlideCorrection lam x j) = 0
  grind

end FiniteChains
