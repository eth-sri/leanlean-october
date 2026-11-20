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

set_option autoImplicit false

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

section

variable (n : ℕ) (e : G ≃* H)

/-- A multiplicative equivalence transports `n`-torsion kernels. -/
def nthPowerKernelEquivOfMulEquiv :
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
theorem powMonoidHom_range_map :
    ((powMonoidHom n : G →* G).range).map e.toMonoidHom = (powMonoidHom n : H →* H).range := e.map_range_powMonoidHom n

end

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
        simpa using
          (MonoidHom.mem_ker).1 x.property
      rw [powMonoidHom_apply, ← map_pow, hx, map_one])⟩
  exact Finite.of_injective mapKernel fun x y hxy ↦ Subtype.ext (hf (congrArg Subtype.val hxy))

/-- The power kernel in the unit group of a commutative ring is Mathlib's
group of roots of unity. -/
theorem powMonoidHom_ker_units_eq_rootsOfUnity
    (R : Type*) [CommRing R] (n : ℕ) :
    (powMonoidHom n : Rˣ →* Rˣ).ker = rootsOfUnity n R := by
  rfl

/-- For nonzero exponent over a domain, the unit-group power kernel is
finite because it is the finite set of roots of `X ^ n - 1`. -/
noncomputable instance finite_powMonoidHom_ker_units
    (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) [NeZero n] :
    Finite ((powMonoidHom n : Rˣ →* Rˣ).ker) := by
  rw [powMonoidHom_ker_units_eq_rootsOfUnity]
  infer_instance

section

variable (n : ℕ) (e : G ≃* H)

/-- A multiplicative equivalence transports quotients by `n`-th powers. -/
def nthPowerQuotientEquivOfMulEquiv :
    G ⧸ (powMonoidHom n : G →* G).range ≃* H ⧸ (powMonoidHom n : H →* H).range :=
  QuotientGroup.congr ((powMonoidHom n : G →* G).range) ((powMonoidHom n : H →* H).range) e
    (powMonoidHom_range_map G H n e)

/-- The quotient equivalence induced by a multiplicative equivalence maps each power-class
representative to its image. -/
@[simp]
theorem nthPowerQuotientEquivOfMulEquiv_mk (x : G) :
    nthPowerQuotientEquivOfMulEquiv G H n e
        (QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x) =
      QuotientGroup.mk' ((powMonoidHom n : H →* H).range) (e x) :=
  rfl

include e in
/-- Finiteness of a power quotient transports backwards along a
multiplicative equivalence. -/
theorem finite_nthPowerQuotient_of_mulEquiv
    [Finite (H ⧸ (powMonoidHom n : H →* H).range)] :
    Finite (G ⧸ (powMonoidHom n : G →* G).range) :=
  Finite.of_equiv
    (H ⧸ (powMonoidHom n : H →* H).range)
    (nthPowerQuotientEquivOfMulEquiv G H n e).symm.toEquiv

end

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
      change (((x.1 : G), (x.2 : H)) : G × H) ^ n = 1
      ext <;> simp [hx₁, hx₂]⟩
  left_inv x := by
    ext <;> rfl
  right_inv x := by
    ext <;> rfl
  map_mul' x y := by
    ext <;> rfl

/-- Finiteness of the two factor kernels transports across the canonical
product-kernel equivalence. -/
noncomputable instance finite_powMonoidHom_ker_prod (n : ℕ)
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
    _ =
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
  exact fun q ↦ Prod.casesOn q fun qG qH ↦ Quotient.inductionOn' qG fun g ↦ Quotient.inductionOn' qH fun h ↦ Exists.intro (g, h) rfl

/-- The product power-class homomorphism has trivial kernel. -/
theorem nthPowerProductQuotientHom_ker (n : ℕ) :
    (nthPowerProductQuotientHom G H n).ker =
      (powMonoidHom n : (G × H) →* (G × H)).range := by
  ext x
  constructor
  · intro hx
    simp at hx
    change
      (QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x.1,
        QuotientGroup.mk' ((powMonoidHom n : H →* H).range) x.2) = 1 at hx
    aesop
  · intro hx
    rw [MonoidHom.mem_ker]
    rw [MonoidHom.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    apply Prod.ext
    · exact (QuotientGroup.eq_one_iff ((y.1) ^ n)).2
        ((MonoidHom.mem_range).2 ⟨y.1, rfl⟩)
    · exact (QuotientGroup.eq_one_iff ((y.2) ^ n)).2
        ((MonoidHom.mem_range).2 ⟨y.2, rfl⟩)

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
noncomputable instance finite_powMonoidHom_rangeQuotient_prod (n : ℕ)
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
  simp [Nat.card_congr (nthPowerProductQuotientEquiv G H n).toEquiv]

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
  simpa [Nat.card_congr (nthPowerQuotientEquivOfMulEquiv G (H × U) n e).toEquiv] using card_nthPowerProductQuotient H U n

/-- For multiplicative integers, the range of the `n`-th power map is the subgroup of additive
multiples of `n`. -/
theorem powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup
    (n : ℕ) :
    (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range =
      integerMultipleSubgroup (n : ℤ) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, rfl⟩
    simp
  · intro hx
    rcases hx with ⟨k, hk⟩
    rw [MonoidHom.mem_range]
    solve_by_elim [Multiplicative.ofAdd]

/-- For nonzero `n`, multiplicative integers modulo `n`-th powers form a finite quotient. -/
theorem finite_multiplicativeInt_nthPowerQuotient
    {n : ℕ} (hn : n ≠ 0) :
    Finite (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) := by
  rw [powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup]
  let : NeZero (n : ℤ).natAbs := ⟨by exact hn⟩
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
  let :=
    finite_multiplicativeInt_nthPowerQuotient (NeZero.ne n)
  exact finite_nthPowerQuotient_of_mulEquiv
    G (U × Multiplicative ℤ) n e

variable {n : ℕ} (hn : n ≠ 0)

include hn in
/-- For nonzero `n`, the multiplicative-integer power quotient has cardinality `n`. -/
theorem card_multiplicativeInt_nthPowerQuotient
    [Finite (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range)] :
    Nat.card
        (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) = n := by
  rw [Nat.card_congr
    ((QuotientGroup.quotientMulEquivOfEq
      (powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup n)).trans
        (valueModIntegerMultipleSubgroupEquivZMod (n : ℤ))).toEquiv]
  apply Nat.card_zmod

include hn in
/-- For nonzero `n`, the `n`-th power map on multiplicative integers has trivial kernel. -/
theorem powMonoidHom_ker_multiplicativeInt_eq_bot :
    (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).ker = ⊥ := by
  ext x
  simp_all

include hn in
/-- The kernel of a nonzero power map on multiplicative integers is finite. -/
theorem finite_multiplicativeInt_nthPowerKernel :
    Finite ((powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).ker) := by
  rw [powMonoidHom_ker_multiplicativeInt_eq_bot hn]
  infer_instance

include hn in
/-- The kernel of a nonzero power map on multiplicative integers has one element. -/
theorem card_multiplicativeInt_nthPowerKernel
    [Finite ((powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).ker)] :
    Nat.card ((powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).ker) = 1 := by
  rw [powMonoidHom_ker_multiplicativeInt_eq_bot hn]
  simp

include hn in
/-- If a commutative group splits as `U × Multiplicative ℤ`, its `n`-th-power
quotient index is `n` times the corresponding quotient index for `U`. -/
theorem card_nthPowerQuotient_eq_mul_of_mulEquiv_units_prod_int (e : G ≃* U × Multiplicative ℤ)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (U ⧸ (powMonoidHom n : U →* U).range)] :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      n * Nat.card (U ⧸ (powMonoidHom n : U →* U).range) := by
  let := finite_multiplicativeInt_nthPowerQuotient hn
  let card₀ := Nat.card (U ⧸ (powMonoidHom n : U →* U).range)
  calc
    _ =
        Nat.card ((U × Multiplicative ℤ) ⧸
          (powMonoidHom n : (U × Multiplicative ℤ) →* (U × Multiplicative ℤ)).range) := by
      rw [Nat.card_congr
        (nthPowerQuotientEquivOfMulEquiv G (U × Multiplicative ℤ) n e).toEquiv]
    _ =
        card₀ *
          Nat.card (Multiplicative ℤ ⧸
            (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) :=
      card_nthPowerProductQuotient U (Multiplicative ℤ) n
    _ = card₀ * n := by
      rw [card_multiplicativeInt_nthPowerQuotient hn]
    _ = n * card₀ := by
      rw [Nat.mul_comm]

include hn in
/-- For nonzero `n`, a decomposition `G ≃ U × ℤ` identifies the `n`-torsion
kernel of `G` with the `n`-torsion kernel of the unit factor. -/
theorem card_nthPowerKernel_eq_of_mulEquiv_units_prod_int (e : G ≃* U × Multiplicative ℤ)
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
  rfl

/-- Membership in the kernel of multiplication by `n` is equivalent to being annihilated by `n`. -/
@[simp]
theorem mem_nsmulAddKernel_iff {n : ℕ} {x : A} :
    x ∈ nsmulAddKernel A n ↔ n • x = 0 := by
  rfl

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
noncomputable instance finite_multiplicative_nthPowerQuotient
    (n : ℕ) [Finite (A ⧸ nsmulAddSubgroup A n)] :
    Finite
      (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) :=
  Finite.of_equiv (A ⧸ nsmulAddSubgroup A n)
    (multiplicativeNthPowerQuotientEquivAdditive A n).symm

section

variable (n : ℕ)
    [Finite (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range)]

/-- Cardinality/index form of
`powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup`. -/
theorem card_multiplicative_nthPowerQuotient_eq_nsmulAddSubgroup_index :
    Nat.card (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) =
      (nsmulAddSubgroup A n).index := by
  rfl

/-- Under logarithmic/additive notation, the `n`-th-power quotient is the
additive quotient by `n`-fold multiples. -/
theorem card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient
    [Finite (A ⧸ nsmulAddSubgroup A n)] :
    Nat.card (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) =
      Nat.card (A ⧸ nsmulAddSubgroup A n) := by
  rfl

end

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
noncomputable instance finite_multiplicative_nthPowerKernel
    (n : ℕ) [Finite (nsmulAddKernel A n)] :
    Finite ((powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker) :=
  Finite.of_equiv (nsmulAddKernel A n)
    (multiplicativeNthPowerKernelEquivAdditive A n).symm

section AdditiveProducts

variable (B : Type uB) [AddCommGroup B]

/-- Finiteness of additive scalar quotients is stable under binary products. -/
noncomputable instance finite_nsmulAddQuotient_prod (n : ℕ)
    [Finite (A ⧸ nsmulAddSubgroup A n)]
    [Finite (B ⧸ nsmulAddSubgroup B n)] :
    Finite ((A × B) ⧸ nsmulAddSubgroup (A × B) n) := by
  let :=
    finite_nthPowerQuotient_of_mulEquiv
      (Multiplicative (A × B))
      (Multiplicative A × Multiplicative B) n (MulEquiv.prodMultiplicative A B)
  exact Finite.of_equiv
    (Multiplicative (A × B) ⧸
      (powMonoidHom n : (Multiplicative (A × B)) →* (Multiplicative (A × B))).range)
    (multiplicativeNthPowerQuotientEquivAdditive (A × B) n)

/-- Finiteness of additive scalar kernels is stable under binary products. -/
noncomputable instance finite_nsmulAddKernel_prod (n : ℕ)
    [Finite (nsmulAddKernel A n)]
    [Finite (nsmulAddKernel B n)] :
    Finite (nsmulAddKernel (A × B) n) := by
  let :=
    Finite.of_equiv
      ((powMonoidHom n : (Multiplicative A × Multiplicative B) →* (Multiplicative A × Multiplicative B)).ker)
      (nthPowerKernelEquivOfMulEquiv
        (Multiplicative (A × B))
        (Multiplicative A × Multiplicative B) n (MulEquiv.prodMultiplicative A B)).symm.toEquiv
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
  apply card_multiplicative_nthPowerKernel_eq_nsmulAddKernel

variable (G : Type uG) [CommGroup G]

variable (n : ℕ) (e : G ≃* Multiplicative A)

include e in
/-- A logarithmic multiplicative equivalence transports an `n`-th-power quotient
to the additive quotient by `n`-fold multiples. -/
theorem card_nthPowerQuotient_eq_additive_nsmulQuotient_of_mulEquiv
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (A ⧸ nsmulAddSubgroup A n)] :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      Nat.card (A ⧸ nsmulAddSubgroup A n) := by
  rw [Nat.card_congr
    (nthPowerQuotientEquivOfMulEquiv G (Multiplicative A) n e).toEquiv]
  exact card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient A n

include e in
/-- A logarithmic multiplicative equivalence transports the `n`-torsion kernel
to the additive kernel of `x ↦ n • x`. -/
theorem card_nthPowerKernel_eq_additive_nsmulKernel_of_mulEquiv
    [Finite ((powMonoidHom n : G →* G).ker)]
    [Finite (nsmulAddKernel A n)] :
    Nat.card ((powMonoidHom n : G →* G).ker) =
      Nat.card (nsmulAddKernel A n) := by
  rw [Nat.card_congr
    (nthPowerKernelEquivOfMulEquiv G (Multiplicative A) n e).toEquiv]
  exact card_multiplicative_nthPowerKernel_eq_nsmulAddKernel A n

end AdditivePowers

end LocalFieldTheory

end
