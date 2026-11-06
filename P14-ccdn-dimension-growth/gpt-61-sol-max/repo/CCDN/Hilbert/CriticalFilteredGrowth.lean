/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import CCDN.Hilbert.PrimeComponentTranscendence
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Critical growth of a finite-dimensional coordinate space

If multiplication by the coordinates enlarges a finite-dimensional space by
only one dimension, commutativity forces all coordinates to be affine in one
transcendental coordinate over an algebraically closed field.
-/

public section
namespace CCDN

variable {K A : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]

private lemma algebraic_of_stabilizes_submodule  (U : Submodule K A) [Module.Finite K U]
    (hU : U ≠ ⊥) {x : A} (hx : ∀ u ∈ U, x * u ∈ U) : IsAlgebraic K x :=
  (isIntegral_of_smul_mem_submodule U hU (Module.Finite.iff_fg.mp inferInstance) x hx).isAlgebraic


/-- Critical growth over an arbitrary field, provided that the coordinate ring
has a base-field-valued point. -/
theorem affine_of_critical_growth_of_point  (φ : A →ₐ[K] K)
    (U V : Submodule K A) [Module.Finite K U] [Module.Finite K V]
    (hUV : U ≤ V) (hUone : 1 ∈ U)
    (hd : Module.finrank K V = Module.finrank K U + 1)
    {x y : A} (hx : Transcendental K x)
    (hxU : ∀ u ∈ U, x * u ∈ V) (hyU : ∀ u ∈ U, y * u ∈ V) :
    ∃ c d : K, y = c • x + algebraMap K A d := by
  obtain ⟨c, hc⟩ := (show ∃ c, IsAlgebraic K (y - c • x) from (by
                      classical
                      obtain ⟨w, hwV, hwU, hV⟩ := (show ∃ w ∈ V, w ∉ U ∧ V = U ⊔ K ∙ w from (by
                                                    classical
                                                    have hnot : ¬ V ≤ U := by
                                                      grind
                                                    obtain ⟨w, hwV, hwU⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
                                                    refine ⟨w, hwV, hwU, ?_⟩
                                                    symm
                                                    have hle :=
                                                      sup_le hUV (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hwV))
                                                    let : Module.Finite K ↥(U ⊔ Submodule.span K {w}) :=
                                                      Submodule.finiteDimensional_of_le hle
                                                    apply Submodule.eq_of_le_of_finrank_eq hle
                                                    have hlow : Module.finrank K U < Module.finrank K ↥(U ⊔ Submodule.span K {w}) := by
                                                      simp_all [Submodule.finrank_lt_finrank_of_lt, lt_of_le_of_ne, le_sup_left]
                                                    have hhigh := Submodule.finrank_mono hle
                                                    omega))
                      have hdecomp (v : A) (hv : v ∈ V) : ∃ u ∈ U, ∃ c : K, v = u + c • w := by
                        rw [hV, Submodule.mem_sup] at hv
                        obtain ⟨u, hu, t, ht, he⟩ := hv
                        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
                        exact ⟨u, hu, c, he.symm⟩
                      have hVne : V ≠ ⊥ := by
                        grind
                      have hxw : x * w ∉ V := by
                        intro h
                        apply hx
                        apply algebraic_of_stabilizes_submodule V hVne
                        intro v hv
                        obtain ⟨u, hu, c, rfl⟩ := hdecomp v hv
                        simpa only [mul_add, mul_smul_comm] using V.add_mem (hxU u hu) (V.smul_mem c h)
                      obtain ⟨ℓ, hℓx, hℓV⟩ := Submodule.exists_le_ker_of_notMem hxw
                      let c := ℓ (y * w) / ℓ (x * w)
                      have hstable : ∀ u ∈ U, (y - c • x) * u ∈ U := by
                        intro u hu
                        obtain ⟨u₁, hu₁, α, hxu⟩ := hdecomp (x * u) (hxU u hu)
                        obtain ⟨u₂, hu₂, β, hyu⟩ := hdecomp (y * u) (hyU u hu)
                        have h₁ : ℓ (y * u₁) = 0 := hℓV (hyU u₁ hu₁)
                        have h₂ : ℓ (x * u₂) = 0 := hℓV (hxU u₂ hu₂)
                        have he := by
                          have heq : y * (x * u) = x * (y * u) := by ring
                          rw [hxu, hyu] at heq
                          have he' := congrArg ℓ heq
                          simpa only [mul_add, mul_smul_comm, map_add, map_smul, h₁, h₂,
                            zero_add, smul_eq_mul] using he'
                        have hβα : β = c * α := by
                          grind
                        have hcalc : (y - c • x) * u = u₂ - c • u₁ := by
                          grind [sub_mul, smul_mul_assoc, smul_add, smul_smul]
                        rw [hcalc]
                        exact U.sub_mem hu₂ (U.smul_mem c hu₁)
                      have hUne : U ≠ ⊥ := by
                        grind [Submodule.mem_bot, one_ne_zero]
                      exact ⟨c, algebraic_of_stabilizes_submodule U hUne hstable⟩))
  refine ⟨c, φ (y - c • x), ?_⟩
  rw [algebraic_eq_scalar_of_point φ hc]
  abel

end CCDN
