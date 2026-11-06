/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Finiteness.Defs
import CCDN.Hilbert.PrimeComponentTranscendence
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Critical growth of a finite-dimensional coordinate space

If multiplication by the coordinates enlarges a finite-dimensional space by
only one dimension, commutativity forces all coordinates to be affine in one
transcendental coordinate over an algebraically closed field.
-/

namespace CCDN
section

variable {K A : Type*} [Field K]

/-- Critical one-step growth makes every multiplier an affine combination of
a transcendental multiplier and an algebraic element. -/
theorem algebraic_difference_of_critical_growth
    [CommRing A] [IsDomain A] [Algebra K A]
    (U V : Submodule K A) [Module.Finite K U] [Module.Finite K V]
    (hUV : U ≤ V) (hUone : (1 : A) ∈ U)
    (hd : Module.finrank K V = Module.finrank K U + 1)
    {x y : A} (hx : Transcendental K x)
    (hxU : ∀ u ∈ U, x * u ∈ V) (hyU : ∀ u ∈ U, y * u ∈ V) :
    ∃ c : K, IsAlgebraic K (y - c • x) := by
  obtain ⟨w, hwV, hwU, hV⟩ : ∃ w ∈ V, w ∉ U ∧ V = U ⊔ Submodule.span K {w} := by
    have hnot : ¬ V ≤ U := by grind
    obtain ⟨w, hwV, hwU⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
    refine ⟨w, hwV, hwU, ?_⟩
    symm
    have hle :=
      sup_le hUV (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hwV))
    let : Module.Finite K ↥(U ⊔ Submodule.span K {w}) :=
      Submodule.finiteDimensional_of_le hle
    apply Submodule.eq_of_le_of_finrank_eq hle
    have hlow : Module.finrank K U < Module.finrank K ↥(U ⊔ Submodule.span K {w}) := by
      apply Submodule.finrank_lt_finrank_of_lt
      simp_all
    have hhigh := Submodule.finrank_mono hle
    omega
  have hdecomp (v : A) (hv : v ∈ V) : ∃ u ∈ U, ∃ c : K, v = u + c • w := by
    rw [hV, Submodule.mem_sup] at hv
    obtain ⟨u, hu, t, ht, he⟩ := hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
    grind
  obtain ⟨ℓ, hℓx, hℓV⟩ := Submodule.exists_le_ker_of_notMem (by
    intro h
    apply hx
    apply (isIntegral_of_smul_mem_submodule V (by grind) (Module.Finite.iff_fg.mp inferInstance) x ?_).isAlgebraic
    intro v hv
    obtain ⟨u, hu, c, rfl⟩ := hdecomp v hv
    simpa [smul_eq_mul, mul_add, mul_smul_comm] using V.add_mem (hxU u hu) (V.smul_mem c h))
  let c : K := ℓ (y * w) / ℓ (x * w)
  have hstable : ∀ u ∈ U, (y - c • x) * u ∈ U := by
    intro u hu
    obtain ⟨u₁, hu₁, α, hxu⟩ := hdecomp (x * u) (hxU u hu)
    obtain ⟨u₂, hu₂, β, hyu⟩ := hdecomp (y * u) (hyU u hu)
    have h₁ : ℓ (y * u₁) = 0 := hℓV (hyU u₁ hu₁)
    have h₂ : ℓ (x * u₂) = 0 := hℓV (hxU u₂ hu₂)
    have he : α * ℓ (y * w) = β * ℓ (x * w) := by
      have heq : y * (x * u) = x * (y * u) := by ring
      rw [hxu, hyu] at heq
      have he' := congrArg ℓ heq
      simpa [mul_add, mul_smul_comm, map_add, map_smul, h₁, h₂,
        zero_add, smul_eq_mul] using he'
    have hβα : β = c * α := by grind
    have hcalc : (y - c • x) * u = u₂ - c • u₁ := by
      rw [sub_mul, smul_mul_assoc, hxu, hyu, smul_add, smul_smul, hβα]
      abel
    rw [hcalc]
    exact U.sub_mem hu₂ (U.smul_mem c hu₁)
  exact ⟨c, (isIntegral_of_smul_mem_submodule U (by aesop) (Module.Finite.iff_fg.mp inferInstance) _ hstable).isAlgebraic⟩

