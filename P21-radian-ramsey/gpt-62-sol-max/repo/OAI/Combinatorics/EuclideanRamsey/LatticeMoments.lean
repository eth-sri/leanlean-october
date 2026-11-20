/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/LatticeMoments.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Adapted to the Lean module system and simplified for this proof.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.Model

@[expose] public section

namespace OAI.EuclideanRamsey

noncomputable section

open Finset

abbrev Lattice (k : Type) := k → ℤ
abbrev LatticeRing (k : Type) := AddMonoidAlgebra ℚ (Lattice k)

variable {k : Type}

instance latticeNoetherian [Finite k] : IsNoetherianRing (LatticeRing k) :=
  Algebra.FiniteType.isNoetherianRing ℚ (LatticeRing k)

def mass : LatticeRing k →ₐ[ℚ] ℚ := AddMonoidAlgebra.lift ℚ ℚ (Lattice k) 1

lemma mass_apply (x : LatticeRing k) : mass x = x.coeff.sum fun _ q => q := by
  simp only [mass, AddMonoidAlgebra.lift_apply, MonoidHom.one_apply, smul_eq_mul, mul_one]

@[simp] lemma mass_single (γ : Lattice k) (q : ℚ) : mass (AddMonoidAlgebra.single γ q) = q := by
  simp [mass]

abbrev augmentationIdeal : Ideal (LatticeRing k) := RingHom.ker mass

lemma monomial_sub_one_mem (γ : Lattice k) :
    AddMonoidAlgebra.single γ 1 - 1 ∈ (augmentationIdeal : Ideal (LatticeRing k)) := by
  change mass _ = 0
  simp

lemma mem_augmentationIdeal (x : LatticeRing k) : x ∈ augmentationIdeal ↔ mass x = 0 := Iff.rfl

section Integral
variable {V : Type*} [AddCommMonoid V] [Module ℚ V]

/-- Integrate a function against a rational finitely supported measure. -/
def integral (g : Lattice k → V) : LatticeRing k →ₗ[ℚ] V :=
  (Finsupp.linearCombination ℚ g).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

lemma integral_apply (g : Lattice k → V) (x : LatticeRing k) :
    integral g x = x.coeff.sum (fun γ q => q • g γ) := rfl

@[simp] lemma integral_single (g : Lattice k → V) (γ : Lattice k) (q : ℚ) :
    integral g (AddMonoidAlgebra.single γ q) = q • g γ := by
  simp [integral, Finsupp.linearCombination_apply]

@[simp] lemma integral_one (g : Lattice k → V) : integral g 1 = g 0 := by
  change integral g (AddMonoidAlgebra.single 0 1) = _
  rw [integral_single,one_smul]

lemma integral_mul (g : Lattice k → V) (x y : LatticeRing k) :
    integral g (x*y) = x.coeff.sum fun a p => y.coeff.sum fun b q => (p*q) • g (a+b) := by
  simp only [AddMonoidAlgebra.mul_def, Finsupp.sum, map_sum, integral_single]
end Integral

def Centered (x : LatticeRing k) : Prop := ∀ f : Lattice k →+ ℝ, integral f x = 0

def quadratic (f g : Lattice k →+ ℝ) : LatticeRing k →ₗ[ℚ] ℝ := integral fun x => f x * g x

@[simp] lemma quadratic_one (f g : Lattice k →+ ℝ) : quadratic f g 1 = 0 := by simp [quadratic]

lemma integral_addHom_mul (f : Lattice k →+ ℝ) (x y : LatticeRing k) :
    integral f (x*y) = (mass x : ℝ) * integral f y + integral f x * (mass y : ℝ) := by
  rw [integral_mul]
  simp only [integral_apply,mass_apply,Finsupp.sum,map_add,Rat.smul_def,Rat.cast_mul,Rat.cast_sum,
    Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  group

lemma quadratic_mul (f g : Lattice k →+ ℝ) (x y : LatticeRing k) :
    quadratic f g (x*y) = (mass x : ℝ) * quadratic f g y + quadratic f g x * (mass y : ℝ) +
      integral f x * integral g y + integral g x * integral f y := by
  rw [quadratic,integral_mul]
  simp only [integral_apply,mass_apply,Finsupp.sum,map_add,Rat.smul_def,Rat.cast_mul,Rat.cast_sum,
    Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  grind

lemma centered_of_sq {x : LatticeRing k} (h : x ∈ (augmentationIdeal : Ideal (LatticeRing k))^2) :
    Centered x := by
  rw [pow_two] at h
  intro f
  refine Submodule.mul_induction_on h (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · simp [integral_addHom_mul,(mem_augmentationIdeal _).mp ha,(mem_augmentationIdeal _).mp hb]
  · simp [ha,hb]

lemma quadratic_of_cube (f g : Lattice k →+ ℝ) {x : LatticeRing k}
    (h : x ∈ (augmentationIdeal : Ideal (LatticeRing k))^3) : quadratic f g x = 0 := by
  rw [show (3 : ℕ) = 2+1 by rfl,pow_succ'] at h
  refine Submodule.mul_induction_on h (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · have hm := (mem_augmentationIdeal _).mp (Ideal.pow_le_self two_ne_zero hb)
    simp [quadratic_mul,(mem_augmentationIdeal _).mp ha,hm,centered_of_sq hb f,centered_of_sq hb g]
  · simp [ha,hb]
end
end OAI.EuclideanRamsey
