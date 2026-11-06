/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

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

@[expose] public section
namespace CCDN
noncomputable section

/-- Critical growth over an arbitrary field, provided that the coordinate ring
has a base-field-valued point. -/
theorem affine_of_critical_growth_of_point {K A : Type*} [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] (φ : A →ₐ[K] K)
    (U V : Submodule K A) [Module.Finite K U] [Module.Finite K V]
    (hUV : U ≤ V) (hUone : (1 : A) ∈ U)
    (hd : Module.finrank K V = Module.finrank K U + 1)
    {x y : A} (hx : Transcendental K x)
    (hxU : ∀ u ∈ U, x * u ∈ V) (hyU : ∀ u ∈ U, y * u ∈ V) :
    ∃ c d : K, y = c • x + algebraMap K A d := by
  classical
  have halg (W : Submodule K A) [Module.Finite K W] (hW : W ≠ ⊥) {z : A}
      (hz : ∀ u ∈ W, z * u ∈ W) : IsAlgebraic K z :=
    (isIntegral_of_smul_mem_submodule W hW (Module.Finite.iff_fg.mp inferInstance) z hz).isAlgebraic
  have hnot : ¬ V ≤ U := fun h => by rw [le_antisymm hUV h] at hd; omega
  obtain ⟨w, hwV, hwU⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hV : V = U ⊔ Submodule.span K {w} := by
    symm
    have hle : U ⊔ Submodule.span K {w} ≤ V :=
      sup_le hUV (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hwV))
    let : Module.Finite K ↥(U ⊔ Submodule.span K {w}) := Submodule.finiteDimensional_of_le hle
    apply Submodule.eq_of_le_of_finrank_eq hle
    have hlow : Module.finrank K U < Module.finrank K ↥(U ⊔ Submodule.span K {w}) :=
      Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne le_sup_left fun he => hwU <| by
        rw [he]
        exact Submodule.mem_sup.mpr
          ⟨0, U.zero_mem, w, Submodule.subset_span (Set.mem_singleton w), zero_add w⟩)
    have hhigh := Submodule.finrank_mono hle
    omega
  have hdecomp (v : A) (hv : v ∈ V) : ∃ u ∈ U, ∃ c : K, v = u + c • w := by
    rw [hV, Submodule.mem_sup] at hv
    obtain ⟨u, hu, t, ht, he⟩ := hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
    exact ⟨u, hu, c, he.symm⟩
  have hVne : V ≠ ⊥ := fun he => one_ne_zero (by have h1 := hUV hUone; rwa [he, Submodule.mem_bot] at h1)
  have hxw : x * w ∉ V := fun h => hx <| halg V hVne fun v hv => by
    obtain ⟨u, hu, c, rfl⟩ := hdecomp v hv
    simpa only [mul_add, mul_smul_comm] using V.add_mem (hxU u hu) (V.smul_mem c h)
  obtain ⟨ℓ, hℓx, hℓV⟩ := Submodule.exists_le_ker_of_notMem hxw
  let c : K := ℓ (y * w) / ℓ (x * w)
  have hstable : ∀ u ∈ U, (y - c • x) * u ∈ U := by
    intro u hu
    obtain ⟨u₁, hu₁, α, hxu⟩ := hdecomp (x * u) (hxU u hu)
    obtain ⟨u₂, hu₂, β, hyu⟩ := hdecomp (y * u) (hyU u hu)
    have h₁ : ℓ (y * u₁) = 0 := hℓV (hyU u₁ hu₁)
    have h₂ : ℓ (x * u₂) = 0 := hℓV (hxU u₂ hu₂)
    have he : α * ℓ (y * w) = β * ℓ (x * w) := by
      have he' := congrArg ℓ (show y * (x * u) = x * (y * u) by ring)
      rw [hxu, hyu] at he'
      simpa only [mul_add, mul_smul_comm, map_add, map_smul, h₁, h₂,
        zero_add, smul_eq_mul] using he'
    have hβα : β = c * α := by
      dsimp [c]
      rw [div_mul_eq_mul_div]
      exact (eq_div_iff hℓx).mpr (by simpa only [mul_comm] using he.symm)
    rw [show (y - c • x) * u = u₂ - c • u₁ by
      rw [sub_mul, smul_mul_assoc, hxu, hyu, smul_add, smul_smul, hβα]; abel]
    exact U.sub_mem hu₂ (U.smul_mem c hu₁)
  have hc := halg U (fun he => one_ne_zero (by rwa [he, Submodule.mem_bot] at hUone)) hstable
  refine ⟨c, φ (y - c • x), ?_⟩
  rw [algebraic_eq_scalar_of_point φ hc]
  abel

end
end CCDN
