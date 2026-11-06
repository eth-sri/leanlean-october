module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import ValuedFieldTheory.LocalField.GroupTheory.IntegerMultipleSubgroup
public import Mathlib.RingTheory.RootsOfUnity.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Power indices in commutative groups

Reusable kernel, quotient, product, and additive-transport formulas for
`n`-th powers in commutative groups.  The basic power map and its image and
kernel are mathlib's `powMonoidHom`, `MonoidHom.range`, and `MonoidHom.ker`.
-/

noncomputable section

namespace LocalFieldTheory

open LocalFieldTheory.DiscreteValuationField
open scoped Int

section NthPowers

universe uG uH uU

variable (G : Type uG) (H : Type uH) (U : Type uU)
variable [CommGroup G] [CommGroup H] [CommGroup U]

/-- In a finite commutative group, the `n`-th-power quotient has the same
cardinality as the subgroup of `n`-torsion elements.  This is the finite
kernel/cokernel equality for the power endomorphism. -/
theorem card_nthPowerQuotient_eq_nthPowerKernel
    [Finite G] (n : ℕ) :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      Nat.card ((powMonoidHom n : G →* G).ker) := by
  change ((powMonoidHom n : G →* G)).range.index = Nat.card ((powMonoidHom n : G →* G)).ker
  rw [Subgroup.index_range]

/-- A multiplicative equivalence transports `n`-torsion kernels. -/
def nthPowerKernelEquivOfMulEquiv (n : ℕ) (e : G ≃* H) :
    (powMonoidHom n : G →* G).ker ≃* (powMonoidHom n : H →* H).ker where
  toFun x :=
    ⟨e (x : G), by
      have hx : (x : G) ^ n = 1 :=
        (MonoidHom.mem_ker (G := G)).1 x.property
      change (e (x : G)) ^ n = 1
      simpa [map_pow] using congrArg e hx⟩
  invFun y :=
    ⟨e.symm (y : H), by
      have hy : (y : H) ^ n = 1 :=
        (MonoidHom.mem_ker (G := H)).1 y.property
      change (e.symm (y : H)) ^ n = 1
      simpa [map_pow] using congrArg e.symm hy⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_mul' x y := by
    ext
    simp

/-- A multiplicative equivalence carries the range of the `n`-th power map onto the corresponding
range. -/
theorem powMonoidHom_range_map (n : ℕ) (e : G ≃* H) :
    ((powMonoidHom n : G →* G).range).map e.toMonoidHom = (powMonoidHom n : H →* H).range := 
  e.map_range_powMonoidHom n

/-- An injective multiplicative homomorphism transports finiteness of the
ambient power kernel to the source power kernel. -/
theorem finite_nthPowerKernel_of_injective
    (n : ℕ) (f : G →* H) (hf : Function.Injective f)
    [Finite ((powMonoidHom n : H →* H).ker)] :
    Finite ((powMonoidHom n : G →* G).ker) := by
  let mapKernel : (powMonoidHom n : G →* G).ker →
      (powMonoidHom n : H →* H).ker := fun x =>
    ⟨f x, (MonoidHom.mem_ker (G := H)).2 (by
      have hx : (x : G) ^ n = 1 := by
        simpa only [powMonoidHom_apply] using
          (MonoidHom.mem_ker (G := G)).1 x.property
      rw [powMonoidHom_apply, ← map_pow, hx, map_one])⟩
  exact Finite.of_injective mapKernel fun x y hxy => by
    apply Subtype.ext
    exact hf (congrArg Subtype.val hxy)

/-- The power kernel in the unit group of a commutative ring is Mathlib's
group of roots of unity. -/
theorem powMonoidHom_ker_units_eq_rootsOfUnity
    (R : Type*) [CommRing R] (n : ℕ) :
    (powMonoidHom n : Rˣ →* Rˣ).ker = rootsOfUnity n R := by
  rfl

/-- For nonzero exponent over a domain, the unit-group power kernel is
finite because it is the finite set of roots of `X ^ n - 1`. -/
instance finite_powMonoidHom_ker_units
    (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) [NeZero n] :
    Finite ((powMonoidHom n : Rˣ →* Rˣ).ker) := by
  rw [powMonoidHom_ker_units_eq_rootsOfUnity]
  infer_instance

/-- A multiplicative equivalence transports quotients by `n`-th powers. -/
def nthPowerQuotientEquivOfMulEquiv (n : ℕ) (e : G ≃* H) :
    G ⧸ (powMonoidHom n : G →* G).range ≃* H ⧸ (powMonoidHom n : H →* H).range :=
  QuotientGroup.congr ((powMonoidHom n : G →* G).range) ((powMonoidHom n : H →* H).range) e
    (powMonoidHom_range_map G H n e)

/-- The quotient equivalence induced by a multiplicative equivalence maps each power-class
representative to its image. -/
@[simp]
theorem nthPowerQuotientEquivOfMulEquiv_mk (n : ℕ) (e : G ≃* H) (x : G) :
    nthPowerQuotientEquivOfMulEquiv G H n e
        (QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x) =
      QuotientGroup.mk' ((powMonoidHom n : H →* H).range) (e x) :=
  rfl

/-- Finiteness of a power quotient transports backwards along a
multiplicative equivalence. -/
theorem finite_nthPowerQuotient_of_mulEquiv
    (n : ℕ) (e : G ≃* H)
    [Finite (H ⧸ (powMonoidHom n : H →* H).range)] :
    Finite (G ⧸ (powMonoidHom n : G →* G).range) :=
  Finite.of_equiv
    (H ⧸ (powMonoidHom n : H →* H).range)
    (nthPowerQuotientEquivOfMulEquiv G H n e).symm.toEquiv

/-- The `n`-torsion kernel of a product is the product of the two
`n`-torsion kernels. -/
def nthPowerKernelProductEquiv (n : ℕ) :
    (powMonoidHom n : (G × H) →* (G × H)).ker ≃*
      (powMonoidHom n : G →* G).ker × (powMonoidHom n : H →* H).ker where
  toFun x :=
    (⟨(x : G × H).1, by
        have hx : (x : G × H) ^ n = 1 :=
          (MonoidHom.mem_ker (G := G × H)).1 x.property
        have hfst := congrArg Prod.fst hx
        simpa using hfst⟩,
      ⟨(x : G × H).2, by
        have hx : (x : G × H) ^ n = 1 :=
          (MonoidHom.mem_ker (G := G × H)).1 x.property
        have hsnd := congrArg Prod.snd hx
        simpa using hsnd⟩)
  invFun x :=
    ⟨((x.1 : G), (x.2 : H)), by
      have hx₁ : (x.1 : G) ^ n = 1 :=
        (MonoidHom.mem_ker (G := G)).1 x.1.property
      have hx₂ : (x.2 : H) ^ n = 1 :=
        (MonoidHom.mem_ker (G := H)).1 x.2.property
      simp_all⟩
  left_inv x := by
    ext <;> rfl
  right_inv x := by
    ext <;> rfl
  map_mul' x y := by
    ext <;> rfl

/-- Finiteness of the two factor kernels transports across the canonical
product-kernel equivalence. -/
instance finite_powMonoidHom_ker_prod (n : ℕ)
    [Finite ((powMonoidHom n : G →* G).ker)]
    [Finite ((powMonoidHom n : H →* H).ker)] :
    Finite ((powMonoidHom n : (G × H) →* (G × H)).ker) :=
  Finite.of_equiv
    ((powMonoidHom n : G →* G).ker × (powMonoidHom n : H →* H).ker)
    (nthPowerKernelProductEquiv G H n).symm.toEquiv

/-- Cardinality form of `nthPowerKernelProductEquiv`. -/
theorem card_nthPowerKernelProduct (n : ℕ)
    [Finite ((powMonoidHom n : G →* G).ker)]
    [Finite ((powMonoidHom n : H →* H).ker)] :
    Nat.card ((powMonoidHom n : (G × H) →* (G × H)).ker) =
      Nat.card ((powMonoidHom n : G →* G).ker) *
        Nat.card ((powMonoidHom n : H →* H).ker) := by
  rw [Nat.card_congr (nthPowerKernelProductEquiv G H n).toEquiv,
    Nat.card_prod]

/-- A product decomposition of a commutative group splits the cardinality of
the `n`-torsion kernel as the product of the two factor kernels. -/
theorem card_nthPowerKernel_eq_mul_of_mulEquiv_prod
    (n : ℕ) (e : G ≃* H × U)
    [Finite ((powMonoidHom n : G →* G).ker)]
    [Finite ((powMonoidHom n : H →* H).ker)]
    [Finite ((powMonoidHom n : U →* U).ker)] :
    Nat.card ((powMonoidHom n : G →* G).ker) =
      Nat.card ((powMonoidHom n : H →* H).ker) *
        Nat.card ((powMonoidHom n : U →* U).ker) := by
  calc
    Nat.card ((powMonoidHom n : G →* G).ker) =
        Nat.card ((powMonoidHom n : (H × U) →* (H × U)).ker) := by
      rw [Nat.card_congr
        (nthPowerKernelEquivOfMulEquiv G (H × U) n e).toEquiv]
    _ =
        Nat.card ((powMonoidHom n : H →* H).ker) *
          Nat.card ((powMonoidHom n : U →* U).ker) :=
      card_nthPowerKernelProduct H U n

/-- The product map from a product group to the product of its `n`-th-power
quotients. -/
def nthPowerProductQuotientHom (n : ℕ) :
    G × H →* (G ⧸ (powMonoidHom n : G →* G).range) × (H ⧸ (powMonoidHom n : H →* H).range) where
  toFun x :=
    (QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x.1,
      QuotientGroup.mk' ((powMonoidHom n : H →* H).range) x.2)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Every pair of power classes is represented by a power class in the product group. -/
theorem nthPowerProductQuotientHom_surjective (n : ℕ) :
    Function.Surjective (nthPowerProductQuotientHom G H n) := by
  intro q
  rcases q with ⟨qG, qH⟩
  refine Quotient.inductionOn' qG ?_
  intro g
  refine Quotient.inductionOn' qH ?_
  intro h
  exact ⟨(g, h), rfl⟩

/-- The product power-class homomorphism has trivial kernel. -/
theorem nthPowerProductQuotientHom_ker (n : ℕ) :
    (nthPowerProductQuotientHom G H n).ker =
      (powMonoidHom n : (G × H) →* (G × H)).range := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    change
      (QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x.1,
        QuotientGroup.mk' ((powMonoidHom n : H →* H).range) x.2) = 1 at hx
    have hxG :
        QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x.1 = 1 :=
      congrArg Prod.fst hx
    have hxH :
        QuotientGroup.mk' ((powMonoidHom n : H →* H).range) x.2 = 1 :=
      congrArg Prod.snd hx
    have hxGmem : x.1 ∈ (powMonoidHom n : G →* G).range :=
      (QuotientGroup.eq_one_iff x.1).1 hxG
    have hxHmem : x.2 ∈ (powMonoidHom n : H →* H).range :=
      (QuotientGroup.eq_one_iff x.2).1 hxH
    rw [MonoidHom.mem_range] at hxGmem hxHmem ⊢
    rcases hxGmem with ⟨g, hg⟩
    rcases hxHmem with ⟨h, hh⟩
    refine ⟨(g, h), ?_⟩
    simp_all
  · intro hx
    rw [MonoidHom.mem_ker]
    rw [MonoidHom.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    apply Prod.ext
    · exact (QuotientGroup.eq_one_iff ((y.1) ^ n)).2
        ((MonoidHom.mem_range (G := G)).2 ⟨y.1, rfl⟩)
    · exact (QuotientGroup.eq_one_iff ((y.2) ^ n)).2
        ((MonoidHom.mem_range (G := H)).2 ⟨y.2, rfl⟩)

/-- Quotienting a product by `n`-th powers is the product of the two
`n`-th-power quotients. -/
def nthPowerProductQuotientEquiv (n : ℕ) :
    (G × H) ⧸ (powMonoidHom n : (G × H) →* (G × H)).range ≃*
      (G ⧸ (powMonoidHom n : G →* G).range) × (H ⧸ (powMonoidHom n : H →* H).range) :=
  (QuotientGroup.quotientMulEquivOfEq
      (nthPowerProductQuotientHom_ker G H n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (nthPowerProductQuotientHom G H n)
      (nthPowerProductQuotientHom_surjective G H n))

/-- Finiteness of the factor power quotients transports across the canonical
product-quotient equivalence. -/
instance finite_powMonoidHom_rangeQuotient_prod (n : ℕ)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (H ⧸ (powMonoidHom n : H →* H).range)] :
    Finite ((G × H) ⧸ (powMonoidHom n : (G × H) →* (G × H)).range) :=
  Finite.of_equiv
    ((G ⧸ (powMonoidHom n : G →* G).range) × (H ⧸ (powMonoidHom n : H →* H).range))
    (nthPowerProductQuotientEquiv G H n).symm.toEquiv

/-- The number of `n`-th power classes in a product is the product of the two factor class numbers.
The number of `n`-th power classes in a product is the product of the two factor class numbers. -/
theorem card_nthPowerProductQuotient (n : ℕ)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (H ⧸ (powMonoidHom n : H →* H).range)] :
    Nat.card ((G × H) ⧸ (powMonoidHom n : (G × H) →* (G × H)).range) =
      Nat.card (G ⧸ (powMonoidHom n : G →* G).range) *
        Nat.card (H ⧸ (powMonoidHom n : H →* H).range) := by
  rw [Nat.card_congr (nthPowerProductQuotientEquiv G H n).toEquiv,
    Nat.card_prod]

/-- A product decomposition of a commutative group splits the `n`-th-power
quotient index as the product of the two factor indices. -/
theorem card_nthPowerQuotient_eq_mul_of_mulEquiv_prod
    (n : ℕ) (e : G ≃* H × U)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (H ⧸ (powMonoidHom n : H →* H).range)]
    [Finite (U ⧸ (powMonoidHom n : U →* U).range)] :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      Nat.card (H ⧸ (powMonoidHom n : H →* H).range) *
        Nat.card (U ⧸ (powMonoidHom n : U →* U).range) := by
  calc
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
        Nat.card ((H × U) ⧸ (powMonoidHom n : (H × U) →* (H × U)).range) := by
      rw [Nat.card_congr
        (nthPowerQuotientEquivOfMulEquiv G (H × U) n e).toEquiv]
    _ =
        Nat.card (H ⧸ (powMonoidHom n : H →* H).range) *
          Nat.card (U ⧸ (powMonoidHom n : U →* U).range) :=
      card_nthPowerProductQuotient H U n

/-- For multiplicative integers, the range of the `n`-th power map is the subgroup of additive
multiples of `n`. -/
theorem powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup
    (n : ℕ) :
    (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range =
      integerMultipleSubgroup (n : ℤ) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    simp
  · intro hx
    rw [mem_integerMultipleSubgroup_iff] at hx
    rcases hx with ⟨k, hk⟩
    rw [MonoidHom.mem_range]
    refine ⟨Multiplicative.ofAdd k, ?_⟩
    apply Multiplicative.toAdd.injective
    simp_all

/-- For nonzero `n`, multiplicative integers modulo `n`-th powers form a finite quotient. -/
theorem finite_multiplicativeInt_nthPowerQuotient
    {n : ℕ} (hn : n ≠ 0) :
    Finite (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) := by
  rw [powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup]
  have hnabs : (n : ℤ).natAbs ≠ 0 := by omega
  let : NeZero (n : ℤ).natAbs := ⟨hnabs⟩
  exact Finite.of_equiv
    (Multiplicative (ZMod (n : ℤ).natAbs))
    (valueModIntegerMultipleSubgroupEquivZMod (n : ℤ)).symm.toEquiv

/-- An explicit `G ≃ U × ℤ` decomposition transports finiteness of the
unit-factor power quotient to the full group.  This is deliberately a
constructor rather than a global instance: callers must expose the
decomposition and the exact finite boundary. -/
theorem finite_nthPowerQuotient_of_mulEquiv_units_prod_int
    {n : ℕ} [NeZero n] (e : G ≃* U × Multiplicative ℤ)
    [Finite (U ⧸ (powMonoidHom n : U →* U).range)] :
    Finite (G ⧸ (powMonoidHom n : G →* G).range) := by
  let : Finite
      (Multiplicative ℤ ⧸
        (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) :=
    finite_multiplicativeInt_nthPowerQuotient (NeZero.ne n)
  exact finite_nthPowerQuotient_of_mulEquiv
    G (U × Multiplicative ℤ) n e

/-- For nonzero `n`, the multiplicative-integer power quotient has cardinality `n`. -/
theorem card_multiplicativeInt_nthPowerQuotient
    {n : ℕ} (hn : n ≠ 0)
    [Finite (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range)] :
    Nat.card
        (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) = n := by
  rw [Nat.card_congr
    ((QuotientGroup.quotientMulEquivOfEq
      (powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup n)).trans
        (valueModIntegerMultipleSubgroupEquivZMod (n : ℤ))).toEquiv]
  rw [Nat.card_congr
    (Multiplicative.toAdd :
      Multiplicative (ZMod ((n : ℤ).natAbs)) ≃ ZMod ((n : ℤ).natAbs))]
  have hnabs : (n : ℤ).natAbs ≠ 0 := by omega
  simp

/-- For nonzero `n`, the `n`-th power map on multiplicative integers has trivial kernel. -/
theorem powMonoidHom_ker_multiplicativeInt_eq_bot
    {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).ker = ⊥ := by
  ext x
  simp_all

/-- The kernel of a nonzero power map on multiplicative integers is finite. -/
theorem finite_multiplicativeInt_nthPowerKernel
    {n : ℕ} (hn : n ≠ 0) :
    Finite ((powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).ker) := by
  rw [powMonoidHom_ker_multiplicativeInt_eq_bot (n := n) hn]
  infer_instance

/-- The kernel of a nonzero power map on multiplicative integers has one element. -/
theorem card_multiplicativeInt_nthPowerKernel
    {n : ℕ} (hn : n ≠ 0)
    [Finite ((powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).ker)] :
    Nat.card ((powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).ker) = 1 := by
  simp_all

/-- If a commutative group splits as `U × Multiplicative ℤ`, its `n`-th-power
quotient index is `n` times the corresponding quotient index for `U`. -/
theorem card_nthPowerQuotient_eq_mul_of_mulEquiv_units_prod_int
    {n : ℕ} (hn : n ≠ 0) (e : G ≃* U × Multiplicative ℤ)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (U ⧸ (powMonoidHom n : U →* U).range)] :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      n * Nat.card (U ⧸ (powMonoidHom n : U →* U).range) := by
  let := finite_multiplicativeInt_nthPowerQuotient hn
  calc
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
        Nat.card ((U × Multiplicative ℤ) ⧸
          (powMonoidHom n : (U × Multiplicative ℤ) →* (U × Multiplicative ℤ)).range) := by
      rw [Nat.card_congr
        (nthPowerQuotientEquivOfMulEquiv G (U × Multiplicative ℤ) n e).toEquiv]
    _ =
        Nat.card (U ⧸ (powMonoidHom n : U →* U).range) *
          Nat.card (Multiplicative ℤ ⧸
            (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) :=
      card_nthPowerProductQuotient U (Multiplicative ℤ) n
    _ = Nat.card (U ⧸ (powMonoidHom n : U →* U).range) * n := by
      rw [card_multiplicativeInt_nthPowerQuotient hn]
    _ = n * Nat.card (U ⧸ (powMonoidHom n : U →* U).range) := by
      rw [Nat.mul_comm]

/-- For nonzero `n`, a decomposition `G ≃ U × ℤ` identifies the `n`-torsion
kernel of `G` with the `n`-torsion kernel of the unit factor. -/
theorem card_nthPowerKernel_eq_of_mulEquiv_units_prod_int
    {n : ℕ} (hn : n ≠ 0) (e : G ≃* U × Multiplicative ℤ)
    [Finite ((powMonoidHom n : G →* G).ker)]
    [Finite ((powMonoidHom n : U →* U).ker)] :
    Nat.card ((powMonoidHom n : G →* G).ker) =
      Nat.card ((powMonoidHom n : U →* U).ker) := by
  let := finite_multiplicativeInt_nthPowerKernel hn
  rw [card_nthPowerKernel_eq_mul_of_mulEquiv_prod
    G U (Multiplicative ℤ) n e]
  rw [card_multiplicativeInt_nthPowerKernel hn, Nat.mul_one]

end NthPowers

section AdditivePowers

universe uA uB uG

variable (A : Type uA) [AddCommGroup A]

/-- The additive subgroup of `n`-fold multiples. -/
abbrev nsmulAddSubgroup (n : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom n).range

/-- The additive subgroup killed by `x ↦ n • x`. -/
abbrev nsmulAddKernel (n : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom n).ker

/-- Membership in the image of multiplication by `n` is equivalent to being an `n`-fold additive
multiple. -/
@[simp]
theorem mem_nsmulAddSubgroup_iff {n : ℕ} {x : A} :
    x ∈ nsmulAddSubgroup A n ↔ ∃ y : A, n • y = x := by
  simp [nsmulAddSubgroup, AddMonoidHom.mem_range]

/-- Membership in the kernel of multiplication by `n` is equivalent to being annihilated by `n`. -/
@[simp]
theorem mem_nsmulAddKernel_iff {n : ℕ} {x : A} :
    x ∈ nsmulAddKernel A n ↔ n • x = 0 := by
  simp [nsmulAddKernel, AddMonoidHom.mem_ker]

/-- Under the `Multiplicative` wrapper, `n`-th powers are exactly additive
`n`-fold multiples. -/
theorem powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup
    (n : ℕ) :
    (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range =
      AddSubgroup.toSubgroup (nsmulAddSubgroup A n) := by
  rfl

/-- The underlying quotient types in multiplicative and additive notation
are canonically equivalent. -/
def multiplicativeNthPowerQuotientEquivAdditive (n : ℕ) :
    (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) ≃
      (A ⧸ nsmulAddSubgroup A n) := by
  rw [powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup]
  exact Equiv.refl _

/-- Finiteness of the additive quotient transports to its multiplicative
presentation without any choice of representatives. -/
instance finite_multiplicative_nthPowerQuotient
    (n : ℕ) [Finite (A ⧸ nsmulAddSubgroup A n)] :
    Finite
      (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) :=
  Finite.of_equiv (A ⧸ nsmulAddSubgroup A n)
    (multiplicativeNthPowerQuotientEquivAdditive A n).symm

/-- Cardinality/index form of
`powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup`. -/
theorem card_multiplicative_nthPowerQuotient_eq_nsmulAddSubgroup_index
    (n : ℕ)
    [Finite (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range)] :
    Nat.card (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) =
      (nsmulAddSubgroup A n).index := by
  rfl

/-- Under logarithmic/additive notation, the `n`-th-power quotient is the
additive quotient by `n`-fold multiples. -/
theorem card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient
    (n : ℕ)
    [Finite (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range)]
    [Finite (A ⧸ nsmulAddSubgroup A n)] :
    Nat.card (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) =
      Nat.card (A ⧸ nsmulAddSubgroup A n) := by
  rfl

/-- Under the `Multiplicative` wrapper, `n`-torsion is exactly the additive
kernel of `x ↦ n • x`. -/
theorem powMonoidHom_ker_multiplicative_eq_nsmulAddKernel_toSubgroup
    (n : ℕ) :
    (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker =
      AddSubgroup.toSubgroup (nsmulAddKernel A n) := by
  rfl

/-- The multiplicative power kernel and additive scalar kernel have the same
underlying type. -/
def multiplicativeNthPowerKernelEquivAdditive (n : ℕ) :
    (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker ≃ nsmulAddKernel A n := by
  rw [powMonoidHom_ker_multiplicative_eq_nsmulAddKernel_toSubgroup]
  exact Equiv.refl _

/-- Finiteness of the additive scalar kernel transports to multiplicative
notation without introducing a noncanonical enumeration. -/
instance finite_multiplicative_nthPowerKernel
    (n : ℕ) [Finite (nsmulAddKernel A n)] :
    Finite ((powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker) :=
  Finite.of_equiv (nsmulAddKernel A n)
    (multiplicativeNthPowerKernelEquivAdditive A n).symm

section AdditiveProducts

variable (B : Type uB) [AddCommGroup B]

/-- Finiteness of additive scalar quotients is stable under binary products. -/
instance finite_nsmulAddQuotient_prod (n : ℕ)
    [Finite (A ⧸ nsmulAddSubgroup A n)]
    [Finite (B ⧸ nsmulAddSubgroup B n)] :
    Finite ((A × B) ⧸ nsmulAddSubgroup (A × B) n) := by
  let e := MulEquiv.prodMultiplicative A B
  let : Finite
      (Multiplicative (A × B) ⧸
        (powMonoidHom n : (Multiplicative (A × B)) →* (Multiplicative (A × B))).range) :=
    finite_nthPowerQuotient_of_mulEquiv
      (Multiplicative (A × B))
      (Multiplicative A × Multiplicative B) n e
  exact Finite.of_equiv
    (Multiplicative (A × B) ⧸
      (powMonoidHom n : (Multiplicative (A × B)) →* (Multiplicative (A × B))).range)
    (multiplicativeNthPowerQuotientEquivAdditive (A × B) n)

/-- Finiteness of additive scalar kernels is stable under binary products. -/
instance finite_nsmulAddKernel_prod (n : ℕ)
    [Finite (nsmulAddKernel A n)]
    [Finite (nsmulAddKernel B n)] :
    Finite (nsmulAddKernel (A × B) n) := by
  let e := MulEquiv.prodMultiplicative A B
  let : Finite
      ((powMonoidHom n : (Multiplicative (A × B)) →* (Multiplicative (A × B))).ker) :=
    Finite.of_equiv
      ((powMonoidHom n : (Multiplicative A × Multiplicative B) →* (Multiplicative A × Multiplicative B)).ker)
      (nthPowerKernelEquivOfMulEquiv
        (Multiplicative (A × B))
        (Multiplicative A × Multiplicative B) n e).symm.toEquiv
  exact Finite.of_equiv
    ((powMonoidHom n : (Multiplicative (A × B)) →* (Multiplicative (A × B))).ker)
    (multiplicativeNthPowerKernelEquivAdditive (A × B) n)

end AdditiveProducts

/-- Cardinality form of the multiplicative/additive kernel translation. -/
theorem card_multiplicative_nthPowerKernel_eq_nsmulAddKernel
    (n : ℕ)
    [Finite ((powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker)]
    [Finite (nsmulAddKernel A n)] :
    Nat.card ((powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker) =
      Nat.card (nsmulAddKernel A n) := by
  rfl

/-- Finite additive kernel/cokernel equality for the map `x ↦ n • x`, proved
through the multiplicative `n`-th-power translation. -/
theorem card_additive_nsmulQuotient_eq_nsmulKernel
    [Finite A] (n : ℕ) :
    Nat.card (A ⧸ nsmulAddSubgroup A n) =
      Nat.card (nsmulAddKernel A n) := by
  rw [← card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient A n]
  rw [card_nthPowerQuotient_eq_nthPowerKernel
    (Multiplicative A) n]
  rfl

variable (G : Type uG) [CommGroup G]

/-- A logarithmic multiplicative equivalence transports an `n`-th-power quotient
to the additive quotient by `n`-fold multiples. -/
theorem card_nthPowerQuotient_eq_additive_nsmulQuotient_of_mulEquiv
    (n : ℕ) (e : G ≃* Multiplicative A)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (A ⧸ nsmulAddSubgroup A n)] :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      Nat.card (A ⧸ nsmulAddSubgroup A n) := by
  rw [Nat.card_congr
    (nthPowerQuotientEquivOfMulEquiv G (Multiplicative A) n e).toEquiv]
  rfl

/-- A logarithmic multiplicative equivalence transports the `n`-torsion kernel
to the additive kernel of `x ↦ n • x`. -/
theorem card_nthPowerKernel_eq_additive_nsmulKernel_of_mulEquiv
    (n : ℕ) (e : G ≃* Multiplicative A)
    [Finite ((powMonoidHom n : G →* G).ker)]
    [Finite (nsmulAddKernel A n)] :
    Nat.card ((powMonoidHom n : G →* G).ker) =
      Nat.card (nsmulAddKernel A n) := by
  rw [Nat.card_congr
    (nthPowerKernelEquivOfMulEquiv G (Multiplicative A) n e).toEquiv]
  rfl
