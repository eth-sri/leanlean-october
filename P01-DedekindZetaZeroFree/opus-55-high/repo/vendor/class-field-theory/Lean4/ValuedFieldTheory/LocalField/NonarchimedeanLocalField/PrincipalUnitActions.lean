module

public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-!
# Actions on principal-unit quotients

Transports valuation-ring automorphisms to maximal-ideal powers, principal
units, and their successive quotients, together with the resulting actions.
-/


namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- A ring equivalence of a valuation integer ring preserves the maximal ideal. -/
theorem integerRingEquiv_mem_maximalIdeal
    (K : Type u) [Field K] [ValuativeRel K]
    (e : 𝒪[K] ≃+* 𝒪[K]) (x : 𝒪[K]) :
    e x ∈ (𝓂[K] : Ideal 𝒪[K]) ↔ x ∈ (𝓂[K] : Ideal 𝒪[K]) := by
  rw [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff e,
    ← IsLocalRing.mem_maximalIdeal]

/-- A ring equivalence of a valuation integer ring maps the maximal ideal to itself. -/
theorem integerRingEquiv_map_maximalIdeal
    (K : Type u) [Field K] [ValuativeRel K]
    (e : 𝒪[K] ≃+* 𝒪[K]) :
    Ideal.map e.toRingHom (𝓂[K] : Ideal 𝒪[K]) = (𝓂[K] : Ideal 𝒪[K]) := by
  ext y
  constructor
  · intro hy
    rcases (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).1 hy with
      ⟨x, hx, rfl⟩
    simp_all
  · intro hy
    refine (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).2 ?_
    refine ⟨e.symm y, ?_, by simp⟩
    simp_all

/-- A ring equivalence of a valuation integer ring maps every maximal-ideal power to itself. -/
theorem integerRingEquiv_map_maximalIdeal_pow
    (K : Type u) [Field K] [ValuativeRel K]
    (e : 𝒪[K] ≃+* 𝒪[K]) (n : Nat) :
    Ideal.map e.toRingHom (𝓂[K] ^ n : Ideal 𝒪[K]) =
      (𝓂[K] ^ n : Ideal 𝒪[K]) := by
  rw [Ideal.map_pow, integerRingEquiv_map_maximalIdeal]

/-- Membership in every maximal-ideal power is invariant under an integer-ring equivalence. -/
theorem integerRingEquiv_mem_maximalIdeal_pow
    (K : Type u) [Field K] [ValuativeRel K]
    (e : 𝒪[K] ≃+* 𝒪[K]) (n : Nat) (x : 𝒪[K]) :
    e x ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) ↔ x ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
  constructor
  · intro hx
    have hxmap :
        e.symm (e x) ∈ Ideal.map e.symm.toRingHom (𝓂[K] ^ n : Ideal 𝒪[K]) :=
      Ideal.mem_map_of_mem e.symm.toRingHom hx
    rw [integerRingEquiv_map_maximalIdeal_pow K e.symm n] at hxmap
    simpa using hxmap
  · intro hx
    have hxmap : e x ∈ Ideal.map e.toRingHom (𝓂[K] ^ n : Ideal 𝒪[K]) :=
      Ideal.mem_map_of_mem e.toRingHom hx
    rw [integerRingEquiv_map_maximalIdeal_pow K e n] at hxmap
    exact hxmap

/-- The induced additive equivalence on the ideal power `𝓂^n`. -/
def maximalIdealPowMapEquivOfIntegerRingEquiv
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ≃+
      ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) where
  toFun a := ⟨e (a : 𝒪[K]), (integerRingEquiv_mem_maximalIdeal_pow K e n a).2 a.2⟩
  invFun a :=
    ⟨e.symm (a : 𝒪[K]), (integerRingEquiv_mem_maximalIdeal_pow K e.symm n a).2 a.2⟩
  left_inv := by
    intro a
    ext
    simp
  right_inv := by
    intro a
    ext
    simp
  map_add' := by
    simp

/-- Principal units are preserved by every valuation-integer-ring equivalence. -/
theorem principalUnits_integerRingEquiv_mem_self
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) (u : 𝒪[K]ˣ)
    (hu : u ∈ principalUnits K n) :
    Units.mapEquiv e.toMulEquiv u ∈ principalUnits K n :=
  principalUnits_integerRingEquiv_mem K n e
    (fun x hx => (integerRingEquiv_mem_maximalIdeal_pow K e n x).2 hx) u hu

/-- The induced multiplicative equivalence on the `n`-th principal-unit group. -/
def principalUnitsMapEquivOfIntegerRingEquiv
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) :
    principalUnits K n ≃* principalUnits K n where
  toFun u :=
    ⟨Units.mapEquiv e.toMulEquiv u.1,
      principalUnits_integerRingEquiv_mem_self K n e u.1 u.2⟩
  invFun u :=
    ⟨Units.mapEquiv e.symm.toMulEquiv u.1,
      principalUnits_integerRingEquiv_mem_self K n e.symm u.1 u.2⟩
  left_inv := by
    intro u
    ext
    simp
  right_inv := by
    intro u
    ext
    simp
  map_mul' := by
    simp
