module

public import OAI.Combinatorics.EuclideanRamsey.DifferentialSplitting

@[expose] public section

noncomputable section

open scoped TensorProduct

set_option autoImplicit true
namespace OAI.EuclideanRamsey
set_option hygiene false
local notation "𝔞" => (Lattice k)

variable {k : ℕ}

abbrev Lattice (k : ℕ) := Fin k → ℤ
abbrev RationalSpace (k : ℕ) := Fin k → ℚ
abbrev LatticeRing (k : ℕ) := AddMonoidAlgebra ℚ 𝔞

def rationalize : Lattice k →+ RationalSpace k where
  toFun γ := fun j => γ j
  map_zero' := by aesop
  map_add' γ δ := by aesop

def latticeSpan (Λ : AddSubgroup 𝔞) : Submodule ℚ (RationalSpace k) :=
  Submodule.span ℚ (rationalize '' Λ)

def matrixTensor (C : 𝕄 k ℚ) :
    RationalSpace k ⊗[ℚ] RationalSpace k :=
  ∑ a, ∑ b, C a b • ((Pi.single a (1 : ℚ)) ⊗ₜ[ℚ] (Pi.single b (1 : ℚ)))

def quotientTensor (Λ : AddSubgroup 𝔞) :=
  TensorProduct.map (latticeSpan Λ).mkQ (latticeSpan Λ).mkQ

def mass (ν : LatticeRing k) : ℚ := ν.coeff.sum fun _ q => q

def firstMoment (ν : LatticeRing k) (a : Fin k) : ℚ :=
  ν.coeff.sum fun γ q => q * γ a

def secondMoment (ν : LatticeRing k) (a b : Fin k) : ℚ :=
  ν.coeff.sum fun γ q => q * γ a * γ b

def cosetPushforward (Λ : AddSubgroup 𝔞) (ν : LatticeRing k) :
    (Lattice k ⧸ Λ) →₀ ℚ := Finsupp.mapDomain (QuotientAddGroup.mk' Λ) ν.coeff


instance : IsNoetherianRing (LatticeRing k) := Algebra.FiniteType.isNoetherianRing ℚ _

def augmentationIdeal : Ideal (LatticeRing k) := RingHom.ker (AddMonoidAlgebra.lift ℚ ℚ 𝔞 1)

lemma moments_linear (x : LatticeRing k) : mass x =
    (Finsupp.linearCombination ℚ 1).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap x ∧
    (∀ a, firstMoment x a = (Finsupp.linearCombination ℚ fun γ => (γ a : ℚ)).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap x) ∧
    ∀ a b, secondMoment x a b = (Finsupp.linearCombination ℚ fun γ => (γ a * γ b : ℚ)).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap x := by
  simp [Finsupp.linearCombination_apply, mass, firstMoment, secondMoment, mul_assoc]

lemma moments_mul (x y : LatticeRing k) : mass (x*y) = mass x * mass y ∧
    (∀ a, firstMoment (x*y) a = mass x * firstMoment y a + firstMoment x a * mass y) ∧
    ∀ a b, secondMoment (x*y) a b = mass x * secondMoment y a b + secondMoment x a b * mass y +
      firstMoment x a * firstMoment y b + firstMoment x b * firstMoment y a := by
  simp only [moments_linear]
  induction x using AddMonoidAlgebra.induction_on with
  | «of» γ => induction y using AddMonoidAlgebra.induction_on <;>
    simp_all [ mul_add] <;> ring_nf <;> simp
  | _ => simp_all [add_mul] <;> ring_nf <;> simp

lemma mem_augmentationIdeal (x : LatticeRing k) : x ∈ augmentationIdeal ↔ mass x = 0 := by
  simp [augmentationIdeal, AddMonoidAlgebra.lift_apply, mass]

lemma monomial_sub_one_mem γ :
    AddMonoidAlgebra.single γ 1 - 1 ∈ @augmentationIdeal k := by
  simp [augmentationIdeal]

def jetOne : Ideal (LatticeRing k) where
  carrier := {x | mass x = 0 ∧ ∀ a, firstMoment x a = 0}
  zero_mem' := by aesop
  add_mem' := by simp_all [moments_linear]
  smul_mem' _ _ := by simp_all [moments_mul]

def jetTwo : Ideal (LatticeRing k) where
  carrier := {x | mass x = 0 ∧ (∀ a, firstMoment x a = 0) ∧ ∀ a b, secondMoment x a b = 0}
  zero_mem' := by aesop
  add_mem' := by simp_all [moments_linear]
  smul_mem' _ _ := by simp_all [moments_mul]

lemma augmentation_sq_le_jetOne : @augmentationIdeal k ^ 2 ≤ jetOne := by
  rw [pow_two]
  exact Ideal.mul_le.mpr fun x hx y hy => by simp_all [mem_augmentationIdeal, moments_mul, jetOne]

lemma moments_eq_of_sub_mem_cube
    (h : x-y ∈ @augmentationIdeal k ^ 3) :
    mass x = mass y ∧ (∀ a, firstMoment x a = firstMoment y a) ∧
      ∀ a b, secondMoment x a b = secondMoment y a b := by
  have : @augmentationIdeal k ^ 3 ≤ jetTwo := by
    rw [pow_succ']
    exact Ideal.mul_le.mpr fun x hx y hy => by
      have := augmentation_sq_le_jetOne hy
      simp_all [mem_augmentationIdeal, moments_mul, jetOne, jetTwo]
  simpa [jetTwo, moments_linear, sub_eq_zero] using this h

def quadraticStencil (C : 𝕄 k ℚ) (l : Fin k → LatticeRing k) : LatticeRing k :=
  (1/2 : ℚ) • ∑ a, ∑ b, C a b • (l a * l b)

lemma quadraticStencil_moments C (hC : C.IsSymm)
    (l : Fin k → LatticeRing k) (hm : ∀ a, mass (l a) = 0)
    (hf : ∀ a b, firstMoment (l a) b = if a = b then 1 else 0) :
    mass (quadraticStencil C l) = 0 ∧ (∀ a, firstMoment (quadraticStencil C l) a = 0) ∧
      (∀ a b, secondMoment (quadraticStencil C l) a b = C a b) := by
  have h := fun a b => moments_mul (l a) (l b)
  simp only [moments_linear] at hm hf h ⊢
  simp [quadraticStencil, h, hm, hf, mul_add, Finset.sum_add_distrib, hC.apply]
  intros
  ring
