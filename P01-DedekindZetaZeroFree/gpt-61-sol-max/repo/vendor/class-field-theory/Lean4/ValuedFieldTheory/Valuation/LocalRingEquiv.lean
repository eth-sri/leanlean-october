module

public import Mathlib

public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Local-ring equivalences and maximal ideals

Equivalences of local rings preserve the maximal ideal and all of its powers.
The resulting membership criterion is useful when transporting principal-unit
filtrations between equivalent valuation rings.
-/

namespace ValuationTheory

section
variable {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S)
include R S e
/-- A local-ring equivalence maps the maximal ideal onto the maximal ideal. -/
theorem ringEquiv_map_maximalIdeal
      :
    Ideal.map e.toRingHom (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change e x ∈ IsLocalRing.maximalIdeal S
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro h
    have h' := h.map e.symm.toRingHom
    apply hx <;> aesop
  · intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    apply Ideal.mem_map_of_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    intro h
    apply hy <;> aesop

/-- A local-ring equivalence maps every power of the maximal ideal onto the
corresponding power. -/
theorem ringEquiv_map_maximalIdeal_pow
      (n : ℕ) :
    Ideal.map e.toRingHom (IsLocalRing.maximalIdeal R ^ n) =
      IsLocalRing.maximalIdeal S ^ n := by
  rw [Ideal.map_pow, ringEquiv_map_maximalIdeal]

/-- Membership in a maximal-ideal power is preserved by a local-ring
equivalence. -/
theorem ringEquiv_mem_maximalIdeal_pow_iff
      (n : ℕ) (x : R) :
    e x ∈ IsLocalRing.maximalIdeal S ^ n ↔
      x ∈ IsLocalRing.maximalIdeal R ^ n := by
  rw [← ringEquiv_map_maximalIdeal_pow e n]
  constructor
  · intro hx
    rcases (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).1 hx with
      ⟨y, hy, hey⟩
    exact e.injective hey ▸ hy
  · exact Ideal.mem_map_of_mem e.toRingHom
end


































end ValuationTheory
