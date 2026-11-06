module

public import Mathlib

public import ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.FiniteField
public import GaloisCohomology.Kummer.Concrete.FiniteDualSeparation
public import GaloisCohomology.Kummer.Concrete.LocalUnitKummerUnramified
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertPairing
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueUnits
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/











set_option autoImplicit false

/-!
# Tame local power-residue formula

This file constructs reduction of local roots of unity, proves its injectivity,
identifies the arithmetic-Frobenius root quotient with the finite-field power
residue symbol, and derives the tame formula for the local Hilbert symbol.
-/

open scoped Classical ValuativeRel

noncomputable section

namespace LocalClassFieldTheory
namespace Kummer

open KummerTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

section
variable (n : ℕ+) (z : nthRootsSubgroup K n)
include n z in
/-- Every field-valued `n`-th root of unity has normalized valuation zero. -/
theorem nthRootsSubgroup_valuationMap_eq_zero
      :
    valuationMap K (Additive.ofMul z.1) = 0 := by
  have hpow := valuationMap_ofMul_pow K z.1 n
  have hzero :
      (n : ℤ) * valuationMap K (Additive.ofMul z.1) = 0 := by
    rw [z.2, valuationMap_ofMul_one] at hpow
    exact hpow.symm
  exact (mul_eq_zero.mp hzero).resolve_left (by exact_mod_cast n.ne_zero)

include n z in
/-- The canonical valuation-ring unit underlying a local `n`-th root of
unity. -/
noncomputable def nthRootIntegerUnit
       :=
  integerUnitOfValuationMapZero K z.1
    (nthRootsSubgroup_valuationMap_eq_zero K n z)

include n z in
@[simp]
theorem integerUnitsToFieldUnits_nthRootIntegerUnit
      :
    integerUnitsToFieldUnits K (nthRootIntegerUnit K n z) = z.1 :=
  integerUnitOfValuationMapZero_spec K z.1
    (nthRootsSubgroup_valuationMap_eq_zero K n z)

include n z in
theorem nthRootIntegerUnit_pow
      :
    nthRootIntegerUnit K n z ^ (n : ℕ) = 1 := by
  apply integerUnitsToFieldUnits_injective K
  rw [map_pow, integerUnitsToFieldUnits_nthRootIntegerUnit, z.2, map_one]

/-- Reduction of roots of unity from a nonarchimedean local field to its
residue field. -/
noncomputable def localNthRootsReduction
    (n : ℕ+) :
    nthRootsSubgroup K n →* rootsOfUnity n 𝓀[K] where
  toFun z :=
    ⟨integerUnitsToResidueUnits K (nthRootIntegerUnit K n z), by
      change
        integerUnitsToResidueUnits K (nthRootIntegerUnit K n z) ^
            (n : ℕ) = 1
      rw [← map_pow, nthRootIntegerUnit_pow, map_one]⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    rfl
  map_mul' := by
    intro z w
    apply Subtype.ext
    apply Units.ext
    rfl

include n z in
@[simp]
theorem localNthRootsReduction_apply
      :
    (localNthRootsReduction K n z).1 =
      integerUnitsToResidueUnits K (nthRootIntegerUnit K n z) :=
  rfl
end


/-- Reduction of roots of unity commutes with extension of valued fields. -/
theorem localNthRootsReduction_nthRootsSubgroupMap
    (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (n : ℕ+) (z : nthRootsSubgroup K n) :
    localNthRootsReduction L n
        (nthRootsSubgroupMap K L n z) =
      ⟨residueUnitsMapOfValuationExtension K L
          (localNthRootsReduction K n z).1,
        by
          change
            residueUnitsMapOfValuationExtension K L
                (localNthRootsReduction K n z).1 ^ (n : ℕ) = 1
          rw [← map_pow, (localNthRootsReduction K n z).2, map_one]⟩ := by
  apply Subtype.ext
  change
    integerUnitsToResidueUnits L
        (nthRootIntegerUnit L n
          (nthRootsSubgroupMap K L n z)) =
      residueUnitsMapOfValuationExtension K L
        (integerUnitsToResidueUnits K (nthRootIntegerUnit K n z))
  rw [residueUnitsMap_integerUnitsToResidueUnits]
  congr 1
  apply Units.ext
  apply Subtype.ext
  rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- An `n`-th root of the image of a valuation-ring unit again has normalized
valuation zero. -/
theorem valuationMap_eq_zero_of_pow_eq_map_integerUnit
    (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (n : ℕ+) (u : 𝒪[K]ˣ) (beta : Lˣ)
    (hbetaPow :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K L).toMonoidHom
          (integerUnitsToFieldUnits K u)) :
    valuationMap L (Additive.ofMul beta) = 0 := by
  have hfieldUnits :
      Units.map (algebraMap K L).toMonoidHom
          (integerUnitsToFieldUnits K u) =
        integerUnitsToFieldUnits L
          (integerUnitsMapOfValuationExtension K L u) := by
    apply Units.ext
    rfl
  have hbaseValuationMap :
      valuationMap L
          (Additive.ofMul
            (Units.map (algebraMap K L).toMonoidHom
              (integerUnitsToFieldUnits K u))) = 0 := by
    rw [hfieldUnits, valuationMap_apply, v_integerUnitsToFieldUnits]
  have hpow := valuationMap_ofMul_pow L beta n
  rw [hbetaPow, hbaseValuationMap] at hpow
  exact (mul_eq_zero.mp hpow.symm).resolve_left (by
    exact_mod_cast n.ne_zero)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The canonical valuation-ring lift of such a root has the prescribed
`n`-th power. -/
theorem integerUnitOfValuationMapZero_pow_eq_integerUnitsMap
    (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (n : ℕ+) (u : 𝒪[K]ˣ) (beta : Lˣ)
    (hbetaPow :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K L).toMonoidHom
          (integerUnitsToFieldUnits K u)) :
    integerUnitOfValuationMapZero L beta
        (valuationMap_eq_zero_of_pow_eq_map_integerUnit
          K L n u beta hbetaPow) ^ (n : ℕ) =
      integerUnitsMapOfValuationExtension K L u := by
  apply integerUnitsToFieldUnits_injective L
  calc
    integerUnitsToFieldUnits L
        (integerUnitOfValuationMapZero L beta
          (valuationMap_eq_zero_of_pow_eq_map_integerUnit
            K L n u beta hbetaPow) ^ (n : ℕ)) =
        beta ^ (n : ℕ) := by
      rw [map_pow, integerUnitOfValuationMapZero_spec]
    _ = Units.map (algebraMap K L).toMonoidHom
        (integerUnitsToFieldUnits K u) := hbetaPow
    _ = integerUnitsToFieldUnits L
        (integerUnitsMapOfValuationExtension K L u) := by
      apply Units.ext
      rfl

section
variable (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L]
include L in
/-- Arithmetic Frobenius divided by the original integer unit reduces to its
`q - 1` power, where `q` is the base residue-field cardinality. -/
theorem residue_arithmeticFrobenius_integerUnitQuotient
     
    (u : 𝒪[L]ˣ) :
    residueUnitsConcreteEquiv L
        (integerUnitsToResidueUnits L
          (Units.mapEquiv
              (galoisGroupIntegerRingEquivOfIsIntegralClosure K L
                (arithmeticFrobeniusOfUnramifiedValuation K L)).toMulEquiv
              u / u)) =
      (residueUnitsConcreteEquiv L (integerUnitsToResidueUnits L u)) ^
        (Nat.card 𝓀[K] - 1) := by
  let : Fintype 𝓀[K] := Fintype.ofFinite _
  let phi  :=
    arithmeticFrobeniusOfUnramifiedValuation K L
  let uBar : 𝓀[L]ˣ :=
    residueUnitsConcreteEquiv L (integerUnitsToResidueUnits L u)
  let uFrobenius  :=
    Units.mapEquiv
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L phi).toMulEquiv u
  have hFrobeniusResidue :
      residueUnitsConcreteEquiv L
          (integerUnitsToResidueUnits L uFrobenius) =
        uBar ^ Nat.card 𝓀[K] := by
    calc
      residueUnitsConcreteEquiv L
          (integerUnitsToResidueUnits L uFrobenius) =
          Units.mapEquiv
            (galoisGroupResidueFieldEquivOfIsIntegralClosure K L phi).toMulEquiv
            uBar := by
        rfl
      _ = uBar ^ Nat.card 𝓀[K] := by
        apply Units.ext
        change
          galoisGroupResidueAlgEquivOfIsIntegralClosure K L phi
              uBar =
            (uBar : 𝓀[L]) ^ Nat.card 𝓀[K]
        apply galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply
  have hcardPos : 0 < Nat.card 𝓀[K] := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨0⟩
  change
    residueUnitsConcreteEquiv L
        (integerUnitsToResidueUnits L (uFrobenius / u)) =
      uBar ^ (Nat.card 𝓀[K] - 1)
  calc
    residueUnitsConcreteEquiv L
        (integerUnitsToResidueUnits L (uFrobenius / u)) =
        residueUnitsConcreteEquiv L
            (integerUnitsToResidueUnits L uFrobenius) / uBar := rfl
    _ = uBar ^ Nat.card 𝓀[K] / uBar := by
      rw [hFrobeniusResidue]
    _ = uBar ^ (Nat.card 𝓀[K] - 1) := by
      have hcard :
          Nat.card 𝓀[K] = (Nat.card 𝓀[K] - 1) + 1 :=
        (Nat.sub_add_cancel hcardPos).symm
      rw [hcard, pow_succ]
      simp

/-- If `n` is a valuation-ring unit, reduction is injective on the local
`n`-th roots of unity. -/
theorem localNthRootsReduction_injective
    (n : ℕ+)
    (hn : ValuativeRel.valuation K (n : K) = 1) :
    Function.Injective (localNthRootsReduction K n) := by
  intro z w hzw
  let zO  := nthRootIntegerUnit K n z
  let wO  := nthRootIntegerUnit K n w
  have hzPow : zO ^ (n : ℕ) = 1 := by
    apply nthRootIntegerUnit_pow
  have hwPow : wO ^ (n : ℕ) = 1 := by
    apply nthRootIntegerUnit_pow
  let f : Polynomial 𝒪[K] := Polynomial.X ^ (n : ℕ) - 1
  have hzRoot : f.IsRoot zO := by
    rw [Polynomial.IsRoot.def]
    dsimp only [f]
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one]
    apply sub_eq_zero.mpr
    change (zO : 𝒪[K]) ^ (n : ℕ) = 1
    exact congrArg Units.val hzPow
  have hwRoot : f.IsRoot wO := by
    rw [Polynomial.IsRoot.def]
    dsimp only [f]
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one]
    apply sub_eq_zero.mpr
    change (wO : 𝒪[K]) ^ (n : ℕ) = 1
    exact congrArg Units.val hwPow
  have hresUnits :
      residueUnitsConcreteEquiv K (integerUnitsToResidueUnits K wO) =
        residueUnitsConcreteEquiv K (integerUnitsToResidueUnits K zO) := by
    change
      (localNthRootsReduction K n w).1 =
        (localNthRootsReduction K n z).1
    exact congrArg Subtype.val hzw.symm
  have hres :
      IsLocalRing.residue 𝒪[K] wO =
        IsLocalRing.residue 𝒪[K] zO := by
    calc
      IsLocalRing.residue 𝒪[K] wO =
          ((residueUnitsConcreteEquiv K
            (integerUnitsToResidueUnits K wO)) : 𝓀[K]) :=
        (integerUnitsToResidueUnits_apply K wO).symm
      _ = ((residueUnitsConcreteEquiv K
            (integerUnitsToResidueUnits K zO)) : 𝓀[K]) :=
        congrArg Units.val hresUnits
      _ = IsLocalRing.residue 𝒪[K] zO :=
        integerUnitsToResidueUnits_apply K zO
  have hnUnit : IsUnit ((n : ℕ) : 𝒪[K]) := by
    apply
      (Valuation.integer.integers
        (ValuativeRel.valuation K)).isUnit_iff_valuation_eq_one.mpr
    change ValuativeRel.valuation K (n : K) = 1
    exact hn
  have hzUnit  := zO.isUnit
  have hderiv : IsUnit (f.derivative.eval (zO : 𝒪[K])) := by
    simpa [f, Polynomial.derivative_sub, Polynomial.derivative_one,
      Polynomial.derivative_X_pow, Polynomial.eval_mul] using
      hnUnit.mul (hzUnit.pow ((n : ℕ) - 1))
  have hwz  :=
    eq_of_simple_roots_of_residue_eq hzRoot hwRoot hres hderiv
  have hO : zO = wO := by
    apply Units.ext
    exact hwz.symm
  apply Subtype.ext
  calc
    z.1 = integerUnitsToFieldUnits K zO := (integerUnitsToFieldUnits_nthRootIntegerUnit K n z).symm
    _ = integerUnitsToFieldUnits K wO := congrArg _ hO
    _ = w.1 := by
      apply integerUnitsToFieldUnits_nthRootIntegerUnit

/-- Away from the residue characteristic, reduction identifies the local
and residue-field `n`-th roots of unity. -/
noncomputable def localNthRootsReductionEquiv
    (n : ℕ+)
    (hn : ValuativeRel.valuation K (n : K) = 1)
    (hmu : (primitiveRoots n K).Nonempty) :
    nthRootsSubgroup K n ≃* rootsOfUnity n 𝓀[K] := by
  letI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  letI : Fintype (rootsOfUnity n 𝓀[K]) := Fintype.ofFinite _
  have hsource :
      Fintype.card (nthRootsSubgroup K n) = (n : ℕ) := by
    obtain ⟨zeta, hzeta⟩ := hmu
    have hzetaPrimitive  :=
      (mem_primitiveRoots n.pos).1 hzeta
    rw [← Nat.card_eq_fintype_card]
    calc
      Nat.card (nthRootsSubgroup K n) =
          Nat.card (rootsOfUnity n K) :=
        Nat.card_congr
          (nthRootsSubgroupEquivRootsOfUnity K n).toEquiv
      _ = (n : ℕ) := hzetaPrimitive.card_rootsOfUnity
  have htargetLe :
      Fintype.card (rootsOfUnity n 𝓀[K]) ≤ (n : ℕ) := by
    rw [← Nat.card_eq_fintype_card]
    apply card_rootsOfUnity
  have hsourceLe  :=
    Fintype.card_le_of_injective (localNthRootsReduction K n)
      (localNthRootsReduction_injective K n hn)
  have htarget :
      Fintype.card (rootsOfUnity n 𝓀[K]) = (n : ℕ) := by
    omega
  apply MulEquiv.ofBijective (localNthRootsReduction K n)
  apply (Fintype.bijective_iff_injective_and_card
    (localNthRootsReduction K n)).2
  exact ⟨localNthRootsReduction_injective K n hn,
    hsource.trans htarget.symm⟩

/-- If `K` contains the `n`-th roots of unity and `n` is a local unit, then
`n` divides the order of the residue-field unit group. -/
theorem dvd_residueCard_sub_one_of_primitiveRoots
    (n : ℕ+)
    (hn : ValuativeRel.valuation K (n : K) = 1)
    (hmu : (primitiveRoots n K).Nonempty) :
    (n : ℕ) ∣ Nat.card 𝓀[K] - 1 := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have hroots :
      Nat.card (rootsOfUnity n 𝓀[K]) = (n : ℕ) := by
    calc
      Nat.card (rootsOfUnity n 𝓀[K]) =
          Nat.card (nthRootsSubgroup K n) :=
        Nat.card_congr
          (localNthRootsReductionEquiv K n hn hmu).symm.toEquiv
      _ = Nat.card (rootsOfUnity n K) :=
        Nat.card_congr
          (nthRootsSubgroupEquivRootsOfUnity K n).toEquiv
      _ = (n : ℕ) := by
        obtain ⟨zeta, hzeta⟩ := hmu
        exact ((mem_primitiveRoots n.pos).1 hzeta).card_rootsOfUnity
  have hdvd :=
    Subgroup.card_dvd_of_injective
      (rootsOfUnity n 𝓀[K]).subtype Subtype.val_injective
  rw [hroots, Nat.card_units] at hdvd
  exact hdvd

include L in
/-- For an `n`-th root of a base integer unit, the residue of its arithmetic
Frobenius quotient is the base residue unit raised to `(q - 1) / n`. -/
theorem residue_arithmeticFrobenius_kummerRootQuotient
     
    (n : ℕ+)
    (hn : ValuativeRel.valuation K (n : K) = 1)
    (hmu : (primitiveRoots n K).Nonempty)
    (u : 𝒪[K]ˣ) (beta : Lˣ)
    (hbetaPow :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K L).toMonoidHom
          (integerUnitsToFieldUnits K u)) :
    let betaO :=
      integerUnitOfValuationMapZero L beta
        (valuationMap_eq_zero_of_pow_eq_map_integerUnit
          K L n u beta hbetaPow)
    residueUnitsConcreteEquiv L
        (integerUnitsToResidueUnits L
          (Units.mapEquiv
              (galoisGroupIntegerRingEquivOfIsIntegralClosure K L
                (arithmeticFrobeniusOfUnramifiedValuation K L)).toMulEquiv
              betaO / betaO)) =
      residueUnitsConcreteEquiv L
          (residueUnitsMapOfValuationExtension K L
            (integerUnitsToResidueUnits K u)) ^
        ((Nat.card 𝓀[K] - 1) / (n : ℕ)) := by
  let betaO  :=
    integerUnitOfValuationMapZero L beta
      (valuationMap_eq_zero_of_pow_eq_map_integerUnit
        K L n u beta hbetaPow)
  let betaBar : 𝓀[L]ˣ :=
    residueUnitsConcreteEquiv L (integerUnitsToResidueUnits L betaO)
  let uBar : 𝓀[L]ˣ :=
    residueUnitsConcreteEquiv L
      (residueUnitsMapOfValuationExtension K L
        (integerUnitsToResidueUnits K u))
  have hdvd  :=
    dvd_residueCard_sub_one_of_primitiveRoots K n hn hmu
  let m := (Nat.card 𝓀[K] - 1) / (n : ℕ)
  have hcard : Nat.card 𝓀[K] - 1 = (n : ℕ) * m := (Nat.div_mul_cancel hdvd).symm.trans (Nat.mul_comm _ _)
  have hbetaOPow :
      betaO ^ (n : ℕ) = integerUnitsMapOfValuationExtension K L u := by
    apply integerUnitOfValuationMapZero_pow_eq_integerUnitsMap <;> assumption
  have hbetaBarPow : betaBar ^ (n : ℕ) = uBar := by
    calc
      betaBar ^ (n : ℕ) =
          residueUnitsConcreteEquiv L
            (integerUnitsToResidueUnits L (betaO ^ (n : ℕ))) := rfl
      _ = residueUnitsConcreteEquiv L
          (integerUnitsToResidueUnits L
            (integerUnitsMapOfValuationExtension K L u)) := by
        rw [hbetaOPow]
      _ = uBar := rfl
  change
    residueUnitsConcreteEquiv L
        (integerUnitsToResidueUnits L
          (Units.mapEquiv
              (galoisGroupIntegerRingEquivOfIsIntegralClosure K L
                (arithmeticFrobeniusOfUnramifiedValuation K L)).toMulEquiv
              betaO / betaO)) = uBar ^ m
  calc
    residueUnitsConcreteEquiv L
        (integerUnitsToResidueUnits L
          (Units.mapEquiv
              (galoisGroupIntegerRingEquivOfIsIntegralClosure K L
                (arithmeticFrobeniusOfUnramifiedValuation K L)).toMulEquiv
              betaO / betaO)) =
        betaBar ^ (Nat.card 𝓀[K] - 1) := by
      apply residue_arithmeticFrobenius_integerUnitQuotient
    _ = betaBar ^ ((n : ℕ) * m) := by rw [hcard]
    _ = (betaBar ^ (n : ℕ)) ^ m := by rw [pow_mul]
    _ = uBar ^ m := by rw [hbetaBarPow]

/-- The finite-field tame power-residue symbol, lifted canonically to the
local `n`-th roots of unity. -/
noncomputable def localTamePowerResidueSymbol
    (n : ℕ+)
    (hn : ValuativeRel.valuation K (n : K) = 1)
    (hmu : (primitiveRoots n K).Nonempty)
    (u : 𝒪[K]ˣ) :
    nthRootsSubgroup K (n : ℕ) := by
  letI : Fintype 𝓀[K] := Fintype.ofFinite _
  exact
    (localNthRootsReductionEquiv K n hn hmu).symm
      (AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol
        𝓀[K] n
        (by
          rw [← Nat.card_eq_fintype_card]
          apply dvd_residueCard_sub_one_of_primitiveRoots <;> assumption)
        (integerUnitsToResidueUnits K u))

/-- Reduction of the lifted tame symbol is the literal finite-field
power-residue symbol. -/
theorem localNthRootsReductionEquiv_localTamePowerResidueSymbol
    (n : ℕ+)
    (hn : ValuativeRel.valuation K (n : K) = 1)
    (hmu : (primitiveRoots n K).Nonempty)
    (u : 𝒪[K]ˣ) :
    letI : Fintype 𝓀[K] := Fintype.ofFinite _
    localNthRootsReductionEquiv K n hn hmu
        (localTamePowerResidueSymbol K n hn hmu u) =
      AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol
        𝓀[K] n
        (by
          rw [← Nat.card_eq_fintype_card]
          exact dvd_residueCard_sub_one_of_primitiveRoots K n hn hmu)
        (integerUnitsToResidueUnits K u) := by
  let : Fintype 𝓀[K] := Fintype.ofFinite _
  exact (localNthRootsReductionEquiv K n hn hmu).apply_symm_apply _

include L in
/-- The tame power-residue symbol embedded in an unramified extension is the
root quotient of an `n`-th root by arithmetic Frobenius. -/
theorem nthRootsSubgroupMap_localTamePowerResidueSymbol_eq_arithmeticFrobenius_rootQuotient
     
    (n : ℕ+)
    (hn : ValuativeRel.valuation K (n : K) = 1)
    (hmu : (primitiveRoots n K).Nonempty)
    (u : 𝒪[K]ˣ) (beta : Lˣ)
    (hbetaPow :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K L).toMonoidHom
          (integerUnitsToFieldUnits K u)) :
    (nthRootsSubgroupMap K L n
        (localTamePowerResidueSymbol K n hn hmu u)).1 =
      rootQuotient (K := K) (L := L) beta
        (arithmeticFrobeniusOfUnramifiedValuation K L) := by
  let : Fintype 𝓀[K] := Fintype.ofFinite _
  let phi  :=
    arithmeticFrobeniusOfUnramifiedValuation K L
  have hbetaPowFixed :
      ∀ sigma : Gal(L / K), sigma • (beta ^ (n : ℕ)) = beta ^ (n : ℕ) := by
    intro sigma
    rw [hbetaPow]
    apply RadicalDatum.smul_algebraMap_unit
  let quotientRoot : nthRootsSubgroup L n :=
    ⟨rootQuotient (K := K) (L := L) beta phi, by
      apply rootQuotient_mem_nthRootsSubgroup_of_pow_fixed <;> assumption⟩
  have hnL : ValuativeRel.valuation L (n : L) = 1 := by
    have hmap :=
      (Valuation.HasExtension.val_map_eq_one_iff
        (ValuativeRel.valuation K) (ValuativeRel.valuation L)
        (n : K)).2 hn
    simpa only [map_natCast] using hmap
  let betaO  :=
    integerUnitOfValuationMapZero L beta
      (valuationMap_eq_zero_of_pow_eq_map_integerUnit
        K L n u beta hbetaPow)
  let betaFrobeniusO  :=
    Units.mapEquiv
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L phi).toMulEquiv
      betaO
  let quotientO  := betaFrobeniusO / betaO
  have hbetaOField : integerUnitsToFieldUnits L betaO = beta := by
    apply integerUnitOfValuationMapZero_spec
  have hbetaFrobeniusOField :
      integerUnitsToFieldUnits L betaFrobeniusO =
        phi • integerUnitsToFieldUnits L betaO := by
    apply Units.ext
    rfl
  have hquotientOField :
      integerUnitsToFieldUnits L quotientO =
        rootQuotient (K := K) (L := L) beta phi := by
    calc
      integerUnitsToFieldUnits L quotientO =
          integerUnitsToFieldUnits L betaFrobeniusO /
            integerUnitsToFieldUnits L betaO := by
        change
          integerUnitsToFieldUnits L (betaFrobeniusO / betaO) =
            integerUnitsToFieldUnits L betaFrobeniusO /
              integerUnitsToFieldUnits L betaO
        apply map_div
      _ = phi • integerUnitsToFieldUnits L betaO /
          integerUnitsToFieldUnits L betaO := rfl
      _ = phi • beta / beta := by rw [hbetaOField]
      _ = rootQuotient (K := K) (L := L) beta phi := rfl
  have hquotientIntegerUnit :
      nthRootIntegerUnit L n quotientRoot = quotientO := by
    apply integerUnitsToFieldUnits_injective L
    rw [integerUnitsToFieldUnits_nthRootIntegerUnit]
    exact hquotientOField.symm
  have hquotientResidue :
      residueUnitsConcreteEquiv L
          (integerUnitsToResidueUnits L quotientO) =
        residueUnitsMapOfValuationExtension K L
            (residueUnitsConcreteEquiv K
              (integerUnitsToResidueUnits K u)) ^
          ((Nat.card 𝓀[K] - 1) / (n : ℕ)) := by
    change
      residueUnitsConcreteEquiv L
          (integerUnitsToResidueUnits L quotientO) =
        residueUnitsConcreteEquiv L
            (residueUnitsMapOfValuationExtension K L
              (integerUnitsToResidueUnits K u)) ^
          ((Nat.card 𝓀[K] - 1) / (n : ℕ))
    apply residue_arithmeticFrobenius_kummerRootQuotient <;> assumption
  have htameReduction :
      localNthRootsReduction K n
          (localTamePowerResidueSymbol K n hn hmu u) =
        AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol
          𝓀[K] n
          (by
            rw [← Nat.card_eq_fintype_card]
            apply dvd_residueCard_sub_one_of_primitiveRoots <;> assumption)
          (integerUnitsToResidueUnits K u) := by
    change
      localNthRootsReductionEquiv K n hn hmu
          (localTamePowerResidueSymbol K n hn hmu u) = _
    exact
      localNthRootsReductionEquiv_localTamePowerResidueSymbol
        K n hn hmu u
  have htameReductionValue :
      (localNthRootsReduction K n
          (localTamePowerResidueSymbol K n hn hmu u)).1 =
        residueUnitsConcreteEquiv K
            (integerUnitsToResidueUnits K u) ^
          ((Nat.card 𝓀[K] - 1) / (n : ℕ)) := by
    have hvalue := congrArg Subtype.val htameReduction
    calc
      (localNthRootsReduction K n
          (localTamePowerResidueSymbol K n hn hmu u)).1 =
          residueUnitsConcreteEquiv K
              (integerUnitsToResidueUnits K u) ^
            ((Fintype.card 𝓀[K] - 1) / (n : ℕ)) := by
        rw [← AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol_apply]
        exact hvalue
      _ = residueUnitsConcreteEquiv K
            (integerUnitsToResidueUnits K u) ^
          ((Nat.card 𝓀[K] - 1) / (n : ℕ)) := by
        rw [Nat.card_eq_fintype_card]
  let tameRoot  :=
    nthRootsSubgroupMap K L n
      (localTamePowerResidueSymbol K n hn hmu u)
  have htameQuotientReduction :
      localNthRootsReduction L n tameRoot =
        localNthRootsReduction L n quotientRoot := by
    rw [show tameRoot =
      nthRootsSubgroupMap K L n
        (localTamePowerResidueSymbol K n hn hmu u) from rfl]
    rw [localNthRootsReduction_nthRootsSubgroupMap]
    apply Subtype.ext
    change
      residueUnitsMapOfValuationExtension K L
          (localNthRootsReduction K n
            (localTamePowerResidueSymbol K n hn hmu u)).1 =
        integerUnitsToResidueUnits L
          (nthRootIntegerUnit L n quotientRoot)
    rw [hquotientIntegerUnit, htameReductionValue, map_pow]
    exact hquotientResidue.symm
  have hroot  :=
    localNthRootsReduction_injective L n hnL htameQuotientReduction
  exact congrArg Subtype.val hroot
end


omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- If `n` is a valuation-ring unit, then its image in the local field is
nonzero.  This supplies the characteristic hypothesis required by the chosen
simple Kummer extension without adding a redundant assumption to the tame
formula. -/
theorem natCast_ne_zero_of_valuation_eq_one
    (n : ℕ+)
    (hn : ValuativeRel.valuation K (n : K) = 1) :
    (n : K) ≠ 0 := by
  intro hn0
  have hzero :
      ValuativeRel.valuation K (0) = 1 := by
    simpa only [hn0] using hn
  exact zero_ne_one ((ValuativeRel.valuation K).map_zero.symm.trans hzero)

section
variable (n : ℕ+)
    (hn : ValuativeRel.valuation K (n : K) = 1)
    (hmu : (primitiveRoots n K).Nonempty)
include n hn hmu in
/-- For a valuation-ring unit `u`, the Hilbert symbol with the chosen inverse
prime element in the first slot is the tame residue symbol of `u`.  The proof
constructs the unramified certificate for the chosen simple Kummer extension
from its unit radical and then uses the arithmetic-Frobenius normalization of
the local Artin map. -/
theorem
    localHilbertSymbol_inverseIntegerRingUniformizerFieldUnit_integerUnit_eq_tame
     
    (u : 𝒪[K]ˣ) :
    localHilbertSymbol K n
        (natCast_ne_zero_of_valuation_eq_one K n hn) hmu
        (inverseIntegerRingUniformizerFieldUnit K)
        (integerUnitsToFieldUnits K u) =
      localTamePowerResidueSymbol K n hn hmu u := by
  let hnK : ((n : ℕ) : K) ≠ 0 :=
    natCast_ne_zero_of_valuation_eq_one K n hn
  let b : Kˣ := integerUnitsToFieldUnits K u
  let E := chosenSimpleKummerExtension K n hnK b
  let beta : Eˣ := chosenSimpleKummerRootUnit K n hnK b
  let : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let  :=
    finiteExtensionSpectralNormedField K E
  let : ValuativeRel E :=
    finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  let : Algebra 𝒪[K] E := Algebra.ofSubsemiring 𝒪[K]
  let : IsIntegralClosure 𝒪[E] 𝒪[K] E :=
    localCompleteDVF_integerRing_isIntegralClosure K E
  let : Module.Finite 𝒪[K] 𝒪[E] :=
    localCompleteDVF_integerRing_moduleFinite K E
  have hbetaPowUnits :
      beta ^ (n : ℕ) = Units.map (algebraMap K E).toMonoidHom b := by
    apply chosenSimpleKummerRootUnit_pow
  have hbetaPow :
      (beta : E) ^ (n : ℕ) = algebraMap K E b := congrArg Units.val hbetaPowUnits
  have hbVal : ValuativeRel.valuation K b = 1 := by
    apply valuation_eq_one_of_valuationMap_eq_zero K
    rw [valuationMap_apply]
    exact v_integerUnitsToFieldUnits K u
  have hbetaVal : ValuativeRel.valuation E beta = 1 := by
    apply valuation_eq_one_of_valuationMap_eq_zero E
    exact
      valuationMap_eq_zero_of_pow_eq_map_integerUnit
        K E n u beta (hbetaPowUnits)
  have hgenIntermediate :
      IntermediateField.adjoin K {(beta : E)} = ⊤ := by
    apply chosenSimpleKummerExtension_adjoin_root_eq_top
  have hgen : Algebra.adjoin K {(beta : E)} = ⊤ := by
    apply
      (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic (beta : E))).mp
    exact hgenIntermediate
  let : IsUnramifiedValuedExtension K E :=
    isUnramifiedValuedExtension_of_unit_kummer_generator
      n b beta hbVal hn hbetaVal hbetaPow hgen
  let piInv  := inverseIntegerRingUniformizerFieldUnit K
  have hArtin :
      chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b piInv =
        arithmeticFrobeniusOfUnramifiedValuation K E := by
    change abelianLocalArtinMonoidHom K E piInv = _
    rw [abelianLocalArtinMonoidHom_eq_frobenius_zpow,
      valuationMap_apply, v_inverseIntegerRingUniformizerFieldUnit, zpow_one]
  have hHilbertVal := congrArg Subtype.val
    (localHilbertSymbol_map_eq_rootQuotient K n hnK hmu piInv b)
  have hTameVal :=
    nthRootsSubgroupMap_localTamePowerResidueSymbol_eq_arithmeticFrobenius_rootQuotient
      K E n hn hmu u beta (hbetaPowUnits)
  change localHilbertSymbol K n hnK hmu piInv b =
    localTamePowerResidueSymbol K n hn hmu u
  apply nthRootsSubgroupMap_injective K E n
  apply Subtype.ext
  calc
    (nthRootsSubgroupMap K E n
        (localHilbertSymbol K n hnK hmu piInv b)).1 =
        rootQuotient (K := K) (L := E) beta
          (chosenSimpleKummerNormResidueAutomorphism
            K n hnK hmu b piInv) := hHilbertVal
    _ = rootQuotient (K := K) (L := E) beta
          (arithmeticFrobeniusOfUnramifiedValuation K E) := by
      rw [hArtin]
    _ = (nthRootsSubgroupMap K E n
        (localTamePowerResidueSymbol K n hn hmu u)).1 := hTameVal.symm

include n hn hmu in
/-- Tame local Hilbert-symbol formula in the unit-first convention.  It is the
skew-symmetric form of the preceding arithmetic-Frobenius calculation. -/
theorem
    localHilbertSymbol_integerUnit_inverseIntegerRingUniformizerFieldUnit_eq_tame_inv
     
    (u : 𝒪[K]ˣ) :
    localHilbertSymbol K n
        (natCast_ne_zero_of_valuation_eq_one K n hn) hmu
        (integerUnitsToFieldUnits K u)
        (inverseIntegerRingUniformizerFieldUnit K) =
      (localTamePowerResidueSymbol K n hn hmu u)⁻¹ := by
  calc
    localHilbertSymbol K n
        (natCast_ne_zero_of_valuation_eq_one K n hn) hmu
        (integerUnitsToFieldUnits K u)
        (inverseIntegerRingUniformizerFieldUnit K) =
        (localHilbertSymbol K n
          (natCast_ne_zero_of_valuation_eq_one K n hn) hmu
          (inverseIntegerRingUniformizerFieldUnit K)
          (integerUnitsToFieldUnits K u))⁻¹ :=
      localHilbertSymbol_skew K n
        (natCast_ne_zero_of_valuation_eq_one K n hn) hmu
        (integerUnitsToFieldUnits K u)
        (inverseIntegerRingUniformizerFieldUnit K)
    _ = (localTamePowerResidueSymbol K n hn hmu u)⁻¹ :=
      congrArg Inv.inv
        (localHilbertSymbol_inverseIntegerRingUniformizerFieldUnit_integerUnit_eq_tame
          K n hn hmu u)

/-- The local Hilbert symbol is compatible with arbitrary integral powers in
its second argument. -/
theorem localHilbertSymbol_zpow_right
    (n : ℕ+) (hnK : (n : K) ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty)
    (a b : Kˣ) (m : ℤ) :
    localHilbertSymbol K n hnK hmu a (b ^ m) =
      localHilbertSymbol K n hnK hmu a b ^ m := by
  calc
    localHilbertSymbol K n hnK hmu a (b ^ m) =
        maximalLocalKummerPairingRightHom K n hnK hmu a (b ^ m) := (maximalLocalKummerPairingRightHom_eq_localHilbertSymbolHom
          K n hnK hmu a (b ^ m)).symm
    _ = maximalLocalKummerPairingRightHom K n hnK hmu a b ^ m := by
      rw [map_zpow]
    _ = localHilbertSymbol K n hnK hmu a b ^ m := by
      rw [maximalLocalKummerPairingRightHom_eq_localHilbertSymbolHom,
        localHilbertSymbolHom_apply]

include n hn hmu in
/-- In the tame case, the local Hilbert symbol of two valuation-ring units is
trivial.  The chosen simple Kummer extension generated by the second unit is
unramified, so the first unit has trivial local Artin symbol. -/
theorem localHilbertSymbol_integerUnit_integerUnit_eq_one
     
    (u v : 𝒪[K]ˣ) :
    localHilbertSymbol K n
        (natCast_ne_zero_of_valuation_eq_one K n hn) hmu
        (integerUnitsToFieldUnits K u)
        (integerUnitsToFieldUnits K v) = 1 := by
  let hnK : ((n : ℕ) : K) ≠ 0 :=
    natCast_ne_zero_of_valuation_eq_one K n hn
  let a : Kˣ := integerUnitsToFieldUnits K u
  let b  := integerUnitsToFieldUnits K v
  let E := chosenSimpleKummerExtension K n hnK b
  let beta : Eˣ := chosenSimpleKummerRootUnit K n hnK b
  let : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let  :=
    finiteExtensionSpectralNormedField K E
  let : ValuativeRel E :=
    finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  let : Algebra 𝒪[K] E := Algebra.ofSubsemiring 𝒪[K]
  let : IsIntegralClosure 𝒪[E] 𝒪[K] E :=
    localCompleteDVF_integerRing_isIntegralClosure K E
  let : Module.Finite 𝒪[K] 𝒪[E] :=
    localCompleteDVF_integerRing_moduleFinite K E
  have hbetaPowUnits :
      beta ^ (n : ℕ) = Units.map (algebraMap K E).toMonoidHom b := by
    apply chosenSimpleKummerRootUnit_pow
  have hbetaPow :
      (beta : E) ^ (n : ℕ) = algebraMap K E b := congrArg Units.val hbetaPowUnits
  have hbVal : ValuativeRel.valuation K b = 1 := by
    apply valuation_eq_one_of_valuationMap_eq_zero K
    rw [valuationMap_apply]
    exact v_integerUnitsToFieldUnits K v
  have hbetaVal : ValuativeRel.valuation E beta = 1 := by
    apply valuation_eq_one_of_valuationMap_eq_zero E
    exact
      valuationMap_eq_zero_of_pow_eq_map_integerUnit
        K E n v beta (hbetaPowUnits)
  have hgenIntermediate :
      IntermediateField.adjoin K {(beta : E)} = ⊤ := by
    apply chosenSimpleKummerExtension_adjoin_root_eq_top
  have hgen : Algebra.adjoin K {(beta : E)} = ⊤ := by
    apply
      (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic (beta : E))).mp
    exact hgenIntermediate
  let : IsUnramifiedValuedExtension K E :=
    isUnramifiedValuedExtension_of_unit_kummer_generator
      n b beta hbVal hn hbetaVal hbetaPow hgen
  have haVal : valuationMap K (Additive.ofMul a) = 0 := by
    rw [valuationMap_apply]
    exact v_integerUnitsToFieldUnits K u
  have hArtin :
      chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b a = 1 := by
    change abelianLocalArtinMonoidHom K E a = 1
    rw [abelianLocalArtinMonoidHom_eq_frobenius_zpow, haVal, zpow_zero]
  have hHilbertVal := congrArg Subtype.val
    (localHilbertSymbol_map_eq_rootQuotient K n hnK hmu a b)
  change localHilbertSymbol K n hnK hmu a b = 1
  apply nthRootsSubgroupMap_injective K E n
  apply Subtype.ext
  calc
    (nthRootsSubgroupMap K E n
        (localHilbertSymbol K n hnK hmu a b)).1 =
        rootQuotient (K := K) (L := E) beta
          (chosenSimpleKummerNormResidueAutomorphism
            K n hnK hmu b a) := hHilbertVal
    _ = rootQuotient (K := K) (L := E) beta 1 := by
      rw [hArtin]
    _ = 1 := rootQuotient_one beta
    _ = (nthRootsSubgroupMap K E n
        (1)).1 := rfl

include n hn hmu in
/-- General tame local Hilbert-symbol formula with a valuation-ring unit in
the first slot.  Decomposing the second argument into its unit factor and the
chosen valuation-one prime power reduces the calculation to the unit-unit
vanishing and the inverse-prime special case above. -/
theorem localHilbertSymbol_tame_formula
     
    (u : 𝒪[K]ˣ) (x : Kˣ) :
    localHilbertSymbol K n
        (natCast_ne_zero_of_valuation_eq_one K n hn) hmu
        (integerUnitsToFieldUnits K u) x =
      localTamePowerResidueSymbol K n hn hmu u ^
        (-valuationMap K (Additive.ofMul x)) := by
  let piInv  := inverseIntegerRingUniformizerFieldUnit K
  have hpiInv : valuationMap K (Additive.ofMul piInv) = 1 := v_inverseIntegerRingUniformizerFieldUnit K
  let xUnit  := uniformizerUnitFactor K piInv hpiInv x
  have hxDecomp :
      integerUnitsToFieldUnits K xUnit *
          piInv ^ valuationMap K (Additive.ofMul x) = x := by
    apply uniformizerUnitFactor_mul_uniformizer_zpow
  calc
    localHilbertSymbol K n
        (natCast_ne_zero_of_valuation_eq_one K n hn) hmu
        (integerUnitsToFieldUnits K u) x =
        localHilbertSymbol K n
          (natCast_ne_zero_of_valuation_eq_one K n hn) hmu
          (integerUnitsToFieldUnits K u)
          (integerUnitsToFieldUnits K xUnit *
            piInv ^ valuationMap K (Additive.ofMul x)) := by
      rw [hxDecomp]
    _ = localHilbertSymbol K n
          (natCast_ne_zero_of_valuation_eq_one K n hn) hmu
          (integerUnitsToFieldUnits K u)
          (integerUnitsToFieldUnits K xUnit) *
        localHilbertSymbol K n
          (natCast_ne_zero_of_valuation_eq_one K n hn) hmu
          (integerUnitsToFieldUnits K u)
          (piInv ^ valuationMap K (Additive.ofMul x)) := by
      rw [localHilbertSymbol_mul_right]
    _ = 1 *
        localHilbertSymbol K n
          (natCast_ne_zero_of_valuation_eq_one K n hn) hmu
          (integerUnitsToFieldUnits K u) piInv ^
            valuationMap K (Additive.ofMul x) := by
      rw [localHilbertSymbol_integerUnit_integerUnit_eq_one
          K n hn hmu u xUnit,
        localHilbertSymbol_zpow_right K n
          (natCast_ne_zero_of_valuation_eq_one K n hn) hmu]
    _ = (localTamePowerResidueSymbol K n hn hmu u)⁻¹ ^
          valuationMap K (Additive.ofMul x) := by
      rw [one_mul]
      exact congrArg
        (fun z : nthRootsSubgroup K (n : ℕ) =>
          z ^ valuationMap K (Additive.ofMul x))
        (localHilbertSymbol_integerUnit_inverseIntegerRingUniformizerFieldUnit_eq_tame_inv
          K n hn hmu u)
    _ = localTamePowerResidueSymbol K n hn hmu u ^
          (-valuationMap K (Additive.ofMul x)) := inv_zpow' _ _
end


end Kummer
end LocalClassFieldTheory

end
