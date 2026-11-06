/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/LatticeMoments.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.SmoothingMatrix

@[expose] public section

namespace OAI.EuclideanRamsey



noncomputable section

open scoped TensorProduct


abbrev Lattice (k : ℕ) := Fin k → ℤ
abbrev RationalSpace (k : ℕ) := Fin k → ℚ
abbrev LatticeRing (k : ℕ) := AddMonoidAlgebra ℚ (Lattice k)

def rationalize {k : ℕ} : Lattice k →+ RationalSpace k :=
  AddMonoidHom.piMap fun _ => Int.castAddHom ℚ

def latticeSpan {k : ℕ} (Λ : AddSubgroup (Lattice k)) : Submodule ℚ (RationalSpace k) :=
  Submodule.span ℚ (rationalize '' (Λ : Set (Lattice k)))

def matrixTensor {k : ℕ} (C : Matrix (Fin k) (Fin k) ℚ) :
    RationalSpace k ⊗[ℚ] RationalSpace k :=
  ∑ a, ∑ b, C a b • ((Pi.single a (1 : ℚ)) ⊗ₜ[ℚ] (Pi.single b (1 : ℚ)))

def quotientTensor {k : ℕ} (Λ : AddSubgroup (Lattice k)) :=
  TensorProduct.map (latticeSpan Λ).mkQ (latticeSpan Λ).mkQ

def coefficientFunctional {k : ℕ} (g : Lattice k → ℚ) : LatticeRing k →ₗ[ℚ] ℚ :=
  (Finsupp.linearCombination ℚ g).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

def mass {k : ℕ} : LatticeRing k →ₐ[ℚ] ℚ := AddMonoidAlgebra.lift ℚ ℚ (Lattice k) 1

def firstMoment {k : ℕ} : LatticeRing k →ₗ[ℚ] (Fin k → ℚ) :=
  LinearMap.pi fun a => coefficientFunctional (fun γ => γ a)

def secondMoment {k : ℕ} : LatticeRing k →ₗ[ℚ] (Fin k → Fin k → ℚ) :=
  LinearMap.pi fun a => LinearMap.pi fun b => coefficientFunctional (fun γ => (γ a : ℚ) * γ b)

def cosetPushforward {k : ℕ} (Λ : AddSubgroup (Lattice k)) :
    LatticeRing k →ₐ[ℚ] AddMonoidAlgebra ℚ (Lattice k ⧸ Λ) :=
  AddMonoidAlgebra.mapDomainAlgHom ℚ ℚ (QuotientAddGroup.mk' Λ)

variable {k : ℕ}

instance latticeNoetherian : IsNoetherianRing (LatticeRing k) :=
  Algebra.FiniteType.isNoetherianRing ℚ (LatticeRing k)

def augmentationIdeal : Ideal (LatticeRing k) := RingHom.ker (mass (k := k))

@[simp] lemma mass_single (γ : Lattice k) (q : ℚ) : mass (AddMonoidAlgebra.single γ q) = q := by
  simp [mass]
@[simp] lemma firstMoment_single (γ : Lattice k) (q : ℚ) (a : Fin k) :
    firstMoment (AddMonoidAlgebra.single γ q) a = q * γ a := by
  simp [firstMoment, coefficientFunctional]
lemma firstMoment_mul (x y : LatticeRing k) (a : Fin k) :
    firstMoment (x*y) a = mass x * firstMoment y a + firstMoment x a * mass y := by
  induction x using AddMonoidAlgebra.induction_on generalizing y <;>
    induction y using AddMonoidAlgebra.induction_on <;>
    simp_all [AddMonoidAlgebra.of_apply, AddMonoidAlgebra.single_mul_single,
      mul_add, add_mul] <;> ring

lemma secondMoment_mul (x y : LatticeRing k) (a b : Fin k) :
    secondMoment (x*y) a b = mass x * secondMoment y a b + secondMoment x a b * mass y +
      firstMoment x a * firstMoment y b + firstMoment x b * firstMoment y a := by
  induction x using AddMonoidAlgebra.induction_on generalizing y <;>
    induction y using AddMonoidAlgebra.induction_on <;>
    simp_all [AddMonoidAlgebra.of_apply, AddMonoidAlgebra.single_mul_single,
      mul_add, add_mul, secondMoment, coefficientFunctional, mul_assoc] <;> ring

lemma augmentation_sq_moments {x : LatticeRing k}
    (h : x ∈ (augmentationIdeal : Ideal (LatticeRing k)) ^ 2) :
    mass x = 0 ∧ ∀ a, firstMoment x a = 0 := by
  rw [pow_two] at h
  refine Submodule.mul_induction_on h ?_ ?_
  · intro x hx y hy
    change mass x = 0 at hx
    change mass y = 0 at hy
    simp_all [firstMoment_mul]
  · intro x y hx hy
    simp_all

lemma augmentation_cube_moments {x : LatticeRing k}
    (h : x ∈ (augmentationIdeal : Ideal (LatticeRing k)) ^ 3) :
    mass x = 0 ∧ (∀ a, firstMoment x a = 0) ∧ ∀ a b, secondMoment x a b = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ'] at h
  refine Submodule.mul_induction_on h ?_ ?_
  · intro x hx y hy
    change mass x = 0 at hx
    have hy0 := augmentation_sq_moments hy
    simp_all [firstMoment_mul, secondMoment_mul]
  · intro x y hx hy
    simp_all

def quadraticStencil (C : Matrix (Fin k) (Fin k) ℚ) (l : Fin k → LatticeRing k) : LatticeRing k :=
  (1/2 : ℚ) • ∑ a, ∑ b, C a b • (l a * l b)

lemma quadraticStencil_moments (C : Matrix (Fin k) (Fin k) ℚ) (hC : C.IsSymm)
    (l : Fin k → LatticeRing k) (hm : ∀ a, mass (l a) = 0)
    (hf : ∀ a b, firstMoment (l a) b = if a = b then 1 else 0) :
    mass (quadraticStencil C l) = 0 ∧ (∀ a, firstMoment (quadraticStencil C l) a = 0) ∧
      (∀ a b, secondMoment (quadraticStencil C l) a b = C a b) := by
  classical
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp [quadraticStencil, firstMoment_mul, secondMoment_mul, hm, hf, mul_add,
      Finset.sum_add_distrib, hC.apply] <;> ring

end

end OAI.EuclideanRamsey
