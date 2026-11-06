module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.Units
public import ValuedFieldTheory.LocalField.GroupTheory.IntegerMultipleSubgroup

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

namespace LocalFieldTheory

/-!
# Integer-valued norm data

This file contains the norm-subgroup lemmas used in local CFT from an abstract
integer-valued multiplicative valuation and a norm homomorphism satisfying the
standard valuation formula.
-/

noncomputable section

universe u v

namespace DiscreteValuationField

/-- A multiplicative group valuation with values in additive integers. -/
structure MultiplicativeIntegerValuation (G : Type u) [Group G] where
  /-- The integer valuation of a group element. -/
  val : G → ℤ
  /-- The identity has valuation zero. -/
  map_one : val 1 = 0
  /-- Valuation turns multiplication into integer addition. -/
  map_mul : ∀ x y : G, val (x * y) = val x + val y

namespace MultiplicativeIntegerValuation

variable {G : Type u} [Group G] (V : MultiplicativeIntegerValuation G)

/-- Establishes the identity `V.val (1 : G) = 0`. -/
@[simp] theorem val_one : V.val (1 : G) = 0 :=
  V.map_one

/-- `val` satisfies the multiplication formula `V.val (x * y) = V.val x + V.val y`. -/
@[simp] theorem val_mul (x y : G) :
    V.val (x * y) = V.val x + V.val y :=
  V.map_mul x y

/-- The integer-valued valuation as a multiplicative homomorphism to the
additive group of integers written multiplicatively. -/
def valuationHom : G →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (V.val x)
  map_one' := by
    simp [V.val_one]
  map_mul' x y := by
    rw [V.val_mul, ofAdd_add]

/--
The defining evaluation formula for `valuationHom` is `V.valuationHom x = Multiplicative.ofAdd
(V.val x)`.
-/
@[simp] theorem valuationHom_apply (x : G) :
    V.valuationHom x = Multiplicative.ofAdd (V.val x) :=
  rfl

/-- Characterizes `x ∈ V.valuationHom.ker` by the equivalent condition `V.val x = 0`. -/
theorem mem_valuationHom_ker_iff (x : G) :
    x ∈ V.valuationHom.ker ↔ V.val x = 0 := by
  change V.valuationHom x = 1 ↔ V.val x = 0
  rw [V.valuationHom_apply]
  constructor
  · intro hx
    exact Multiplicative.ofAdd.injective (by simpa using hx)
  · intro hx
    rw [hx]
    simp

/-- `val` satisfies the inverse formula `V.val x⁻¹ = -V.val x`. -/
@[simp] theorem val_inv (x : G) :
    V.val x⁻¹ = -V.val x := by
  have h := V.map_mul x x⁻¹
  have h' : V.val x + V.val x⁻¹ = 0 := by
    simpa [V.map_one] using h.symm
  exact eq_neg_iff_add_eq_zero.2 (by simpa [add_comm] using h')

/-- `val` satisfies the division formula `V.val (x / y) = V.val x - V.val y`. -/
@[simp] theorem val_div (x y : G) :
    V.val (x / y) = V.val x - V.val y := by
  rw [div_eq_mul_inv, V.val_mul, V.val_inv, sub_eq_add_neg]

/-- `val` satisfies the natural-power formula `V.val (x ^ n) = (n : ℤ) * V.val x`. -/
@[simp] theorem val_pow (x : G) (n : ℕ) :
    V.val (x ^ n) = (n : ℤ) * V.val x := by
  induction n with
  | zero =>
      rw [pow_zero, V.val_one]
      simp
  | succ n ih =>
      calc
        V.val (x ^ Nat.succ n) = V.val (x ^ n * x) := by
            rw [pow_succ]
        _ = V.val (x ^ n) + V.val x := V.val_mul _ _
        _ = (n : ℤ) * V.val x + V.val x := by
            rw [ih]
        _ = ((n : ℤ) + 1) * V.val x := by
            rw [add_mul, one_mul]
        _ = (Nat.succ n : ℤ) * V.val x := by
            rw [Nat.cast_succ]

/-- `val` satisfies the integer-power formula `V.val (x ^ n) = n * V.val x`. -/
@[simp] theorem val_zpow (x : G) (n : ℤ) :
    V.val (x ^ n) = n * V.val x := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, V.val_pow]
  | negSucc n =>
      rw [zpow_negSucc, V.val_inv, V.val_pow]
      change -(((n + 1 : ℕ) : ℤ) * V.val x) =
        -(((n + 1 : ℕ) : ℤ)) * V.val x
      rw [neg_mul]

/-- Establishes the identity `V.val x⁻¹ = 0`. -/
theorem val_inv_eq_zero_of_val_eq_zero {x : G} (hx : V.val x = 0) :
    V.val x⁻¹ = 0 := by
  rw [V.val_inv, hx, neg_zero]

/-- Characterizes `V.val (x / y) = 0` by the equivalent condition `V.val x = V.val y`. -/
theorem val_div_eq_zero_iff (x y : G) :
    V.val (x / y) = 0 ↔ V.val x = V.val y := by
  rw [V.val_div]
  constructor
  · exact sub_eq_zero.mp
  · exact sub_eq_zero.mpr









/-- Elements of valuation zero. -/
def zeroSubgroup : Subgroup G where
  carrier := {x | V.val x = 0}
  one_mem' := by simp [V.map_one]
  mul_mem' := by
    intro x y hx hy
    change V.val (x * y) = 0
    rw [V.map_mul, hx, hy, add_zero]
  inv_mem' := by
    intro x hx
    exact V.val_inv_eq_zero_of_val_eq_zero hx

/-- Characterizes `x ∈ V.zeroSubgroup` by the equivalent condition `V.val x = 0`. -/
@[simp] theorem mem_zeroSubgroup_iff (x : G) :
    x ∈ V.zeroSubgroup ↔ V.val x = 0 :=
  Iff.rfl

/-- Establishes the identity `V.valuationHom.ker = V.zeroSubgroup`. -/
theorem valuationHom_ker_eq_zeroSubgroup :
    V.valuationHom.ker = V.zeroSubgroup := by
  ext x
  rw [V.mem_valuationHom_ker_iff, V.mem_zeroSubgroup_iff]

/-- The subgroup appearing in `(V.zeroSubgroup).Normal` is normal. -/
instance zeroSubgroup_normal : (V.zeroSubgroup).Normal := by
  rw [← V.valuationHom_ker_eq_zeroSubgroup]
  infer_instance

/-- The value subgroup of an integer-valued valuation.  It is the range of the
valuation homomorphism `valuationHom`. -/
def valueSubgroup : Subgroup (Multiplicative ℤ) :=
  V.valuationHom.range

/--
Characterizes `n ∈ V.valueSubgroup` by the equivalent condition `∃ x : G, V.valuationHom x = n`.
-/
@[simp] theorem mem_valueSubgroup_iff (n : Multiplicative ℤ) :
    n ∈ V.valueSubgroup ↔ ∃ x : G, V.valuationHom x = n :=
  Iff.rfl











/-- First-isomorphism-theorem form for an integer-valued valuation:
the quotient by valuation-zero elements is the value subgroup. -/
noncomputable def quotientZeroSubgroupEquivValueSubgroup :
    G ⧸ V.zeroSubgroup ≃* V.valueSubgroup :=
  (QuotientGroup.quotientMulEquivOfEq
      (V.valuationHom_ker_eq_zeroSubgroup).symm).trans
    (QuotientGroup.quotientKerEquivRange V.valuationHom)

/--
Establishes the identity `V.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk'
V.zeroSubgroup x) = V.valuationHom.rangeRestrict x`.
-/
@[simp] theorem quotientZeroSubgroupEquivValueSubgroup_mk (x : G) :
    V.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' V.zeroSubgroup x) =
      V.valuationHom.rangeRestrict x :=
  rfl

/--
Establishes the identity `((V.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk'
V.zeroSubgroup x) : V.valueSubgroup) : Multiplicative ℤ) = Multiplicative.ofAdd (V.val x)`.
-/
@[simp] theorem coe_quotientZeroSubgroupEquivValueSubgroup_mk (x : G) :
    ((V.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' V.zeroSubgroup x) : V.valueSubgroup) :
      Multiplicative ℤ) =
      Multiplicative.ofAdd (V.val x) := by
  rw [V.quotientZeroSubgroupEquivValueSubgroup_mk]
  rfl

/--
Establishes the identity `Multiplicative.toAdd (((V.quotientZeroSubgroupEquivValueSubgroup
(QuotientGroup.mk' V.zeroSubgroup x) : V.valueSubgroup) : Multiplicative ℤ)) = V.val x`.
-/
@[simp] theorem toAdd_quotientZeroSubgroupEquivValueSubgroup_mk (x : G) :
    Multiplicative.toAdd
      (((V.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' V.zeroSubgroup x) : V.valueSubgroup) :
        Multiplicative ℤ)) = V.val x := by
  rw [V.coe_quotientZeroSubgroupEquivValueSubgroup_mk, toAdd_ofAdd]

/--
Establishes the identity `Multiplicative.toAdd (((V.quotientZeroSubgroupEquivValueSubgroup
(QuotientGroup.mk' V.zeroSubgroup (x / y)) : V.valueSubgroup) : Multiplicative ℤ)) = V.val x -
V.val y`.
-/
@[simp] theorem toAdd_quotientZeroSubgroupEquivValueSubgroup_div_mk
    (x y : G) :
    Multiplicative.toAdd
      (((V.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' V.zeroSubgroup (x / y)) : V.valueSubgroup) :
        Multiplicative ℤ)) = V.val x - V.val y := by
  rw [V.toAdd_quotientZeroSubgroupEquivValueSubgroup_mk, V.val_div]















/-- A multiplicative element of valuation one. -/
def IsUniformizer (ϖ : G) : Prop :=
  V.val ϖ = 1

/-- Existence of a multiplicative element of valuation one. -/
def HasUniformizer : Prop :=
  ∃ ϖ : G, V.IsUniformizer ϖ

/-- A surjective integer valuation has an element of valuation one. -/
theorem hasUniformizer_of_surjective (hV : Function.Surjective V.val) :
    V.HasUniformizer := by
  rcases hV 1 with ⟨ϖ, hϖ⟩
  exact ⟨ϖ, hϖ⟩

/-- Surjectivity of the integer valuation yields a uniformizer. -/
theorem exists_uniformizer_of_surjective (hV : Function.Surjective V.val) :
    ∃ ϖ : G, V.IsUniformizer ϖ :=
  V.hasUniformizer_of_surjective hV

/-- `val_uniformizer` satisfies the integer-power formula `V.val (ϖ ^ n) = n`. -/
@[simp] theorem val_uniformizer_zpow {ϖ : G} (hϖ : V.IsUniformizer ϖ)
    (n : ℤ) :
    V.val (ϖ ^ n) = n := by
  rw [V.val_zpow, hϖ, mul_one]

/-- `val_uniformizer` satisfies the natural-power formula `V.val (ϖ ^ n) = (n : ℤ)`. -/
@[simp] theorem val_uniformizer_pow {ϖ : G} (hϖ : V.IsUniformizer ϖ)
    (n : ℕ) :
    V.val (ϖ ^ n) = (n : ℤ) := by
  simpa using V.val_uniformizer_zpow hϖ (n : ℤ)













/--
`coe_quotientZeroSubgroupEquivValueSubgroup_uniformizer` satisfies the integer-power formula
`((V.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk' V.zeroSubgroup (ϖ ^ n)) :
V.valueSubgroup) : Multiplicative ℤ) = Multiplicative.ofAdd n`.
-/
@[simp] theorem coe_quotientZeroSubgroupEquivValueSubgroup_uniformizer_zpow
    {ϖ : G} (hϖ : V.IsUniformizer ϖ) (n : ℤ) :
    ((V.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' V.zeroSubgroup (ϖ ^ n)) : V.valueSubgroup) :
      Multiplicative ℤ) = Multiplicative.ofAdd n := by
  rw [V.coe_quotientZeroSubgroupEquivValueSubgroup_mk,
    V.val_uniformizer_zpow hϖ n]

/--
`toAdd_quotientZeroSubgroupEquivValueSubgroup_uniformizer` satisfies the integer-power formula
`Multiplicative.toAdd (((V.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk'
V.zeroSubgroup (ϖ ^ n)) : V.valueSubgroup) : Multiplicative ℤ)) = n`.
-/
@[simp] theorem toAdd_quotientZeroSubgroupEquivValueSubgroup_uniformizer_zpow
    {ϖ : G} (hϖ : V.IsUniformizer ϖ) (n : ℤ) :
    Multiplicative.toAdd
      (((V.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' V.zeroSubgroup (ϖ ^ n)) : V.valueSubgroup) :
        Multiplicative ℤ)) = n := by
  rw [V.coe_quotientZeroSubgroupEquivValueSubgroup_uniformizer_zpow hϖ n,
    toAdd_ofAdd]

/-- A representative-level decomposition `x = u * ϖ^n`, with `u` of valuation
zero.  This is the abstract multiplicative form of `Kˣ = O_Kˣ · ϖ^ℤ`. -/
structure UnitUniformizerDecomposition (ϖ x : G) where
  /-- The valuation-zero factor. -/
  unitPart : G
  /-- The unit factor has valuation zero. -/
  unit_mem : unitPart ∈ V.zeroSubgroup
  /-- The exponent of the chosen uniformizer. -/
  exponent : ℤ
  /-- Reconstruction from the unit factor and uniformizer power. -/
  eq_unit_mul_zpow : x = unitPart * ϖ ^ exponent

/-- Every element admits a unit-uniformizer decomposition with respect to `ϖ`. -/
def HasUnitUniformizerDecomposition (ϖ : G) : Prop :=
  ∀ x : G, Nonempty (V.UnitUniformizerDecomposition ϖ x)

/-- The canonical unit-uniformizer decomposition attached to a uniformizer. -/
def canonicalUnitUniformizerDecomposition {ϖ : G}
    (hϖ : V.IsUniformizer ϖ) (x : G) :
    V.UnitUniformizerDecomposition ϖ x where
  unitPart := x * ϖ ^ (-(V.val x))
  unit_mem := by
    rw [V.mem_zeroSubgroup_iff, V.val_mul, V.val_zpow, hϖ]
    ring
  exponent := V.val x
  eq_unit_mul_zpow := by
    calc
      x = x * 1 := by rw [mul_one]
      _ = x * (ϖ ^ (-(V.val x)) * ϖ ^ V.val x) := by
        rw [← zpow_add, neg_add_cancel, zpow_zero]
      _ = (x * ϖ ^ (-(V.val x))) * ϖ ^ V.val x := by
        rw [mul_assoc]

/--
A chosen uniformizer gives a unit-times-uniformizer-power decomposition of every group element.
-/
theorem hasUnitUniformizerDecomposition_of_uniformizer {ϖ : G}
    (hϖ : V.IsUniformizer ϖ) :
    V.HasUnitUniformizerDecomposition ϖ := by
  intro x
  exact ⟨V.canonicalUnitUniformizerDecomposition hϖ x⟩

/--
Every group element has a unit-times-uniformizer-power decomposition relative to a chosen
uniformizer.
-/
theorem unitUniformizerDecomposition {ϖ : G}
    (hϖ : V.IsUniformizer ϖ) (x : G) :
    Nonempty (V.UnitUniformizerDecomposition ϖ x) :=
  V.hasUnitUniformizerDecomposition_of_uniformizer hϖ x

/--
`exists_zeroSubgroup_mul_uniformizer` satisfies the integer-power formula `∃ u : G, u ∈
V.zeroSubgroup ∧ ∃ n : ℤ, x = u * ϖ ^ n`.
-/
theorem exists_zeroSubgroup_mul_uniformizer_zpow {ϖ : G}
    (hϖ : V.IsUniformizer ϖ) (x : G) :
    ∃ u : G, u ∈ V.zeroSubgroup ∧ ∃ n : ℤ, x = u * ϖ ^ n := by
  rcases V.unitUniformizerDecomposition hϖ x with ⟨d⟩
  exact ⟨d.unitPart, d.unit_mem, d.exponent, d.eq_unit_mul_zpow⟩







namespace UnitUniformizerDecomposition

variable {V : MultiplicativeIntegerValuation G} {ϖ x : G}

/-- Establishes the identity `V.val d.unitPart = 0`. -/
@[simp] theorem unitPart_val_zero
    (d : V.UnitUniformizerDecomposition ϖ x) :
    V.val d.unitPart = 0 :=
  (V.mem_zeroSubgroup_iff d.unitPart).1 d.unit_mem











/-- A valuation-zero multiple of a uniformizer power has valuation equal to
the exponent. -/
theorem val_unit_mul_zpow (hϖ : V.IsUniformizer ϖ)
    {u : G} (hu : u ∈ V.zeroSubgroup) (n : ℤ) :
    V.val (u * ϖ ^ n) = n := by
  rw [V.val_mul, (V.mem_zeroSubgroup_iff u).1 hu,
    V.val_uniformizer_zpow hϖ n, zero_add]

/-- A uniformizer power has valuation equal to its exponent. -/
theorem val_uniformizer_zpow (hϖ : V.IsUniformizer ϖ) (n : ℤ) :
    V.val (ϖ ^ n) = n :=
  V.val_uniformizer_zpow hϖ n

/-- A natural power of a uniformizer has valuation equal to the natural
exponent. -/
theorem val_uniformizer_pow (hϖ : V.IsUniformizer ϖ) (n : ℕ) :
    V.val (ϖ ^ n) = (n : ℤ) :=
  V.val_uniformizer_pow hϖ n

/-- Equality of two unit-uniformizer normal forms forces equality of
exponents. -/
theorem exponent_unique_of_unit_mul_eq (hϖ : V.IsUniformizer ϖ)
    {u w : G} (hu : u ∈ V.zeroSubgroup) (hw : w ∈ V.zeroSubgroup)
    {m n : ℤ} (h : u * ϖ ^ m = w * ϖ ^ n) :
    m = n := by
  have hv := congrArg V.val h
  rw [val_unit_mul_zpow hϖ hu m, val_unit_mul_zpow hϖ hw n] at hv
  exact hv

/-- Equality of two unit-uniformizer normal forms is equivalent to equality of
both the unit part and exponent. -/
theorem unit_mul_zpow_eq_iff (hϖ : V.IsUniformizer ϖ)
    {u w : G} (hu : u ∈ V.zeroSubgroup) (hw : w ∈ V.zeroSubgroup)
    {m n : ℤ} :
    u * ϖ ^ m = w * ϖ ^ n ↔ u = w ∧ m = n := by
  constructor
  · intro h
    have hmn : m = n :=
      exponent_unique_of_unit_mul_eq hϖ hu hw h
    have huw : u = w := by
      calc
        u = (u * ϖ ^ m) * (ϖ ^ m)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
        _ = (w * ϖ ^ n) * (ϖ ^ m)⁻¹ := by
          rw [h]
        _ = (w * ϖ ^ m) * (ϖ ^ m)⁻¹ := by
          rw [hmn]
        _ = w := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
    exact ⟨huw, hmn⟩
  · rintro ⟨huw, hmn⟩
    rw [huw, hmn]



end UnitUniformizerDecomposition





/-- Establishes the identity `V.val (u * ϖ ^ n) = n`. -/
theorem valuation_uniformizer_normal_form {ϖ u : G}
    (hϖ : V.IsUniformizer ϖ) (hu : u ∈ V.zeroSubgroup) (n : ℤ) :
    V.val (u * ϖ ^ n) = n :=
  UnitUniformizerDecomposition.val_unit_mul_zpow hϖ hu n

/-- Characterizes `u * ϖ ^ m = w * ϖ ^ n` by the equivalent condition `u = w ∧ m = n`. -/
theorem unit_uniformizer_normal_form_eq_iff {ϖ u w : G}
    (hϖ : V.IsUniformizer ϖ) (hu : u ∈ V.zeroSubgroup)
    (hw : w ∈ V.zeroSubgroup) {m n : ℤ} :
    u * ϖ ^ m = w * ϖ ^ n ↔ u = w ∧ m = n :=
  UnitUniformizerDecomposition.unit_mul_zpow_eq_iff hϖ hu hw







/-- Characterizes `x / y ∈ V.zeroSubgroup` by the equivalent condition `V.val x = V.val y`. -/
theorem div_mem_zeroSubgroup_iff (x y : G) :
    x / y ∈ V.zeroSubgroup ↔ V.val x = V.val y := by
  rw [MultiplicativeIntegerValuation.mem_zeroSubgroup_iff V (x / y),
    V.val_div_eq_zero_iff]





















/-- Two elements have quotient in the zero-valuation subgroup exactly when the
left element is the right element multiplied on the left by a zero-valuation
element.  This is the right-coset representative form used in
`Kˣ / O_Kˣ` calculations. -/
theorem div_mem_zeroSubgroup_iff_exists_zeroSubgroup_mul_eq (x y : G) :
    x / y ∈ V.zeroSubgroup ↔
      ∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x := by
  constructor
  · intro hxy
    exact ⟨x / y, hxy, by simp [div_eq_mul_inv, mul_assoc]⟩
  · rintro ⟨u, hu, hux⟩
    have hu_eq : u = x / y := by
      have h := congrArg (fun t : G => t * y⁻¹) hux
      simpa [div_eq_mul_inv, mul_assoc] using h
    simpa [← hu_eq] using hu











/--
Characterizes `V.val x = V.val y` by the equivalent condition `∃ u : G, u ∈ V.zeroSubgroup ∧ u * y
= x`.
-/
theorem val_eq_iff_exists_zeroSubgroup_mul_eq (x y : G) :
    V.val x = V.val y ↔
      ∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x := by
  rw [← V.div_mem_zeroSubgroup_iff x y,
    V.div_mem_zeroSubgroup_iff_exists_zeroSubgroup_mul_eq x y]



/-- Establishes the identity `∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x`. -/
theorem exists_zeroSubgroup_mul_eq_of_val_eq {x y : G}
    (hxy : V.val x = V.val y) :
    ∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x :=
  (V.val_eq_iff_exists_zeroSubgroup_mul_eq x y).1 hxy



































end MultiplicativeIntegerValuation

/-- A norm-like homomorphism compatible with integer-valued valuations.

`residueDegree` is proof-attached data: it is the multiplier in
`valuation_formula`, not an independent field-extension invariant.  In the
usual discrete-valued application the source has a uniformizer, and evaluating
`valuation_formula` at that uniformizer uniquely determines this coefficient.
The generic group-level abstraction does not require a uniformizer, so it keeps
the coefficient together with the formula that certifies it. -/
structure ValuedNorm {G : Type u} {H : Type v} [Group G] [Group H]
    (vG : MultiplicativeIntegerValuation G)
    (vH : MultiplicativeIntegerValuation H) where
  /-- The multiplicative norm homomorphism. -/
  toHom : H →* G
  /-- The nonnegative scaling factor in the valuation formula. -/
  residueDegree : ℕ
  /-- Applying the norm scales valuation by the residue-degree factor. -/
  valuation_formula :
    ∀ x : H, vG.val (toHom x) = (residueDegree : ℤ) * vH.val x

end DiscreteValuationField

end

end LocalFieldTheory
