module

public import Mathlib

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Valuation

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






/-!
# Galois actions on valuation rings

Restricts Galois automorphisms to valuation rings and transports their action
to ideals, ideal-power quotients, principal units, and successive quotients.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

section
variable (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
include K L
/-- A real Galois automorphism preserves the valuation integer ring when that
ring is the integral closure of the base valuation integer ring.

This is the source-producing replacement for proving integer-ring preservation
from a valuation-invariance certificate: integrality is transported by the
`K`-algebra automorphism, and integral-closure membership brings the element
back to `𝒪[L]`. -/
theorem galoisGroup_mem_integerRing_of_isIntegralClosure
     
    (σ : Gal(L / K)) (x : 𝒪[L]) :
    σ (x : L) ∈ 𝒪[L] := by
  have hx : IsIntegral 𝒪[K] (x : L) :=
    (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).2
      ⟨x, rfl⟩
  have hσ : IsIntegral 𝒪[K] (σ (x : L)) :=
    IsIntegral.map σ.toAlgHom hx
  rcases (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).1 hσ
    with ⟨y, hy⟩
  exact hy ▸ y.2

/-- Restrict a real Galois automorphism to the valuation integer ring using the
actual integral-closure property of valuation integer rings. -/
def galoisGroupIntegerRingEquivOfIsIntegralClosure
      (σ : Gal(L / K)) :
    𝒪[L] ≃+* 𝒪[L] where
  toFun x :=
    ⟨σ (x : L), galoisGroup_mem_integerRing_of_isIntegralClosure K L σ x⟩
  invFun x :=
    ⟨σ.symm (x : L), galoisGroup_mem_integerRing_of_isIntegralClosure K L σ.symm x⟩
  left_inv := by
    intro x
    ext
    simp
  right_inv := by
    intro x
    ext
    simp
  map_mul' := by
    intro x y
    ext
    simp
  map_add' := by
    intro x y
    ext
    simp

/-- Restriction sends a field automorphism to the corresponding automorphism of the integral-closure
valuation ring. -/
@[simp]
theorem galoisGroupIntegerRingEquivOfIsIntegralClosure_apply
     
    (σ : Gal(L / K)) (x : 𝒪[L]) :
    ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x) : L) =
      σ (x : L) :=
  rfl

/-- The inverse restriction equivalence extends an integer-ring automorphism to the ambient field. -/
@[simp]
theorem galoisGroupIntegerRingEquivOfIsIntegralClosure_symm_apply
     
    (σ : Gal(L / K)) (x : 𝒪[L]) :
    (((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).symm x) : L) =
      σ.symm (x : L) :=
  rfl

/-- Real Galois automorphisms act on `𝒪[L]` through the actual integral-closure
restriction. -/
def galoisGroupIntegerRingEquivHomOfIsIntegralClosure
      :
    Gal(L / K) →* (𝒪[L] ≃+* 𝒪[L]) where
  toFun := galoisGroupIntegerRingEquivOfIsIntegralClosure K L
  map_one' := by
    ext x
    rfl
  map_mul' := by
    intro σ τ
    ext x
    rfl

/-- The semiring action on the valuation integer ring induced by the actual
integral-closure restriction of `Gal(L / K)`. -/
@[reducible]
def galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure
       :=
  MulSemiringAction.compHom 𝒪[L] (galoisGroupIntegerRingEquivHomOfIsIntegralClosure K L)

/-- Restriction of a Galois automorphism commutes with the inclusion of the integer ring into the
field. -/
theorem galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap
     
    (σ : Gal(L / K)) (x : 𝒪[K]) :
    galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
        (integerRingMapOfValuationExtension K L x) =
      integerRingMapOfValuationExtension K L x := by
  ext
  change σ (algebraMap K L (x : K)) = algebraMap K L (x : K)
  apply σ.commutes
















/-- The actual integral-closure action commutes with the canonical
`𝒪[K]`-scalar action on `𝒪[L]`. -/
theorem galoisGroupIntegerRingSMulCommClassOfIsIntegralClosure
      :
    letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
    SMulCommClass (Gal(L / K)) 𝒪[K] 𝒪[L] := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  refine ⟨?_⟩
  intro σ x y
  rw [Algebra.smul_def, Algebra.smul_def]
  change galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
      (algebraMap 𝒪[K] 𝒪[L] x * y) =
    algebraMap 𝒪[K] 𝒪[L] x *
      galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ y
  rw [map_mul]
  have hx : galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
      (algebraMap 𝒪[K] 𝒪[L] x) = algebraMap 𝒪[K] 𝒪[L] x := by
    apply galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap
  rw [hx]

/-- The actual integral-closure action is compatible with the field-level
`Gal(L / K)` action after coercion to `L`. -/
theorem galoisGroupIntegerRingFieldSMulDistribClassOfIsIntegralClosure
      :
    letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
    SMulDistribClass (Gal(L / K)) 𝒪[L] L := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  refine ⟨?_⟩
  intro σ r s
  change σ ((r : L) * s) =
    ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) : L) * σ s
  rw [map_mul]
  rw [galoisGroupIntegerRingEquivOfIsIntegralClosure_apply]
end


/-- The actual integral-closure action on valuation integer rings is a mathlib
Galois group.  This is the source-producing version of the ring-level Galois
input needed for inertia/cardinality arguments. -/
theorem galoisGroupIntegerRing_isGaloisGroup_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
    IsGaloisGroup (Gal(L / K)) 𝒪[K] 𝒪[L] := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  let := galoisGroupIntegerRingFieldSMulDistribClassOfIsIntegralClosure K L
  let : Algebra.IsIntegral 𝒪[K] 𝒪[L] :=
    IsIntegralClosure.isIntegral_algebra 𝒪[K] L
  exact IsGaloisGroup.of_isFractionRing (Gal(L / K)) 𝒪[K] 𝒪[L] K L

section
variable (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
include K L
/-- The ideal action induced by the actual integral-closure restriction. -/
@[reducible]
def galoisGroupIntegerRingIdealDistribMulActionOfIsIntegralClosure
      :
    DistribMulAction (Gal(L / K)) (Ideal 𝒪[L]) := by
  letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  exact Ideal.pointwiseDistribMulAction

/-- The multiplicative ideal action induced by the actual integral-closure
restriction. -/
@[reducible]
def galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure
       := (galoisGroupIntegerRingIdealDistribMulActionOfIsIntegralClosure K L).toMulAction

/-- The Galois action on an integral-closure valuation ring preserves its maximal ideal. -/
theorem galoisGroupIntegerRingAction_map_maximalIdeal_of_isIntegralClosure
     
    (σ : Gal(L / K)) :
    Ideal.map (@MulSemiringAction.toRingHom (Gal(L / K)) _ 𝒪[L] _
        (galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L) σ)
      (𝓂[L] : Ideal 𝒪[L]) =
      (𝓂[L]) := by
  change Ideal.map
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toRingHom
      (𝓂[L] : Ideal 𝒪[L]) =
    (𝓂[L])
  apply integerRingEquiv_map_maximalIdeal

/-- Every Galois automorphism belongs to the stabilizer of the maximal ideal of the integral-closure
valuation ring. -/
theorem galoisGroupIntegerRingAction_mem_maximalIdeal_stabilizer_of_isIntegralClosure
     
    (σ : Gal(L / K)) :
    σ ∈ @MulAction.stabilizer (Gal(L / K)) (Ideal 𝒪[L]) _
      (galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure K L)
      (𝓂[L] : Ideal 𝒪[L]) := by
  rw [@MulAction.mem_stabilizer_iff (Gal(L / K)) (Ideal 𝒪[L]) _
    (galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure K L)]
  change Ideal.map (@MulSemiringAction.toRingHom (Gal(L / K)) _ 𝒪[L] _
      (galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L) σ)
        (𝓂[L] : Ideal 𝒪[L]) =
    (𝓂[L])
  apply galoisGroupIntegerRingAction_map_maximalIdeal_of_isIntegralClosure

/-- Real Galois automorphisms, viewed inside the maximal-ideal stabilizer, using
the actual integral-closure restriction. -/
def galoisGroupMaximalIdealStabilizerHomOfIsIntegralClosure
      :
    Gal(L / K) →* @MulAction.stabilizer (Gal(L / K)) (Ideal 𝒪[L]) _
      (galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure K L)
      (𝓂[L] : Ideal 𝒪[L]) where
  toFun σ :=
    ⟨σ, galoisGroupIntegerRingAction_mem_maximalIdeal_stabilizer_of_isIntegralClosure K L σ⟩
  map_one' := by
    ext
    rfl
  map_mul' σ τ := by
    ext
    rfl

/-- Actual integral-closure real Galois action on the `n`-th principal-unit
group. -/
def galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure
     
    (n : Nat) (σ : Gal(L / K))  :=
  principalUnitsMapEquivOfIntegerRingEquiv L n
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)

/-- The induced equivalence on principal units applies the restricted Galois automorphism to the
underlying unit. -/
theorem galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure_apply
     
    (n : Nat) (σ : Gal(L / K)) (u : principalUnits L n) :
    ((galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ u) : 𝒪[L]ˣ) =
      Units.mapEquiv
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u.1 :=
  rfl















end





































































































































































































































































































































































































































/-- Actual integral-closure first-order expansion of the real Galois product
attached to a principal-unit representative. -/
theorem galoisGroup_prod_one_add_sub_one_sub_sum_mem_maximalIdeal_pow_succ_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (hn : 1 ≤ n) (a : (𝓂[L] ^ n : Ideal 𝒪[L])) :
    (Finset.univ.prod fun σ : Gal(L / K) =>
        1 + galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) - 1 -
      (Finset.univ.sum fun σ : Gal(L / K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) ∈
        (𝓂[L] ^ (n + 1)) := by
  classical
  refine finset_prod_one_add_sub_one_sub_sum_mem_maximalIdeal_pow_succ L
    (Finset.univ : Finset (Gal(L / K))) n hn
    (fun σ => galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) ?_
  intro σ _
  exact (integerRingEquiv_mem_maximalIdeal_pow L
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) n (a : 𝒪[L])).2 a.2

end
end LocalFieldTheory
