module

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.LocalField.DiscreteValuationField.MixedCharacteristicQp
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
public import ValuedFieldTheory.LocalField.Analytic.PrincipalUnitExpLogEquiv
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.Core
public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicModuleStructure
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.Topology.Algebra.Module.Compact

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# The integral lattice of a mixed-characteristic local field

This file identifies the integer ring of a mixed-characteristic local field
with the integral closure of the p-adic integers.  In particular it supplies
the finite free `Z_p` lattice of rank `[K : Q_p]` used in the proof of
the mixed-characteristic field-unit structure theorem.  The comparison is made for the canonical copy of `Q_p`
constructed in the local-field structure classification, not for a separately assumed scalar action.
-/

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

open scoped WithZero nonZeroDivisors
open Module

variable {K : Type u} [Field K]

/-! ### Canonical mixed-characteristic scalar context -/

/-- The canonical `Q_p` scalar context supplied by a mixed-characteristic
local field.  It carries the residue-characteristic prime witness; installing
it also installs the coherent algebra and finite-dimensional structures. -/
class MixedQPadicContext (F : LocalField.{u, v} K) : Prop where
  /-- The residue characteristic of a mixed-characteristic local field is prime. -/
  residueCharacteristic_prime : F.residueCharacteristic.Prime

/-- The canonical `Q_p` scalar context attached to `F`. -/
theorem mixedQPadicContext (F : LocalField.{u, v} K) :
    MixedQPadicContext F :=
  ⟨F.residueCharacteristic_prime⟩

/-- Registers the mathematical fact `Fact F.residueCharacteristic.Prime` for typeclass inference. -/
instance mixedQPadicContextFact
    (F : LocalField.{u, v} K) [ctx : MixedQPadicContext F] :
    Fact F.residueCharacteristic.Prime :=
  ⟨ctx.residueCharacteristic_prime⟩

/--
Equips the target with its canonical `Algebra` structure, namely `Algebra
ℚ_[F.residueCharacteristic] K`.
-/
noncomputable instance mixedQPadicContextAlgebra
    (F : LocalField.{u, v} K) [CharZero K] [MixedQPadicContext F] :
    Algebra ℚ_[F.residueCharacteristic] K :=
  F.qpadicNumbersAlgebra

/--
Equips the target with its canonical `FiniteDimensional` structure, namely `FiniteDimensional
ℚ_[F.residueCharacteristic] K`.
-/
noncomputable instance mixedQPadicContextFiniteDimensional
    (F : LocalField.{u, v} K) [CharZero K] [MixedQPadicContext F] :
    FiniteDimensional ℚ_[F.residueCharacteristic] K :=
  F.finiteDimensional_over_qpadicNumbers

/-- The DVR valuation on `Q_p` has closed unit ball equal to the usual
subring `Z_p`. -/
theorem padicDVRValuation_le_one_iff_norm_le_one
    (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    Examples.Qp.padicDVRValuation p x ≤ 1 ↔ ‖x‖ ≤ 1 := by
  constructor
  · intro hx
    obtain ⟨z, hz⟩ :=
      IsDiscreteValuationRing.exists_lift_of_le_one
          hx
    have hzx : z = x := by
      exact hz
    rw [← hzx]
    exact PadicInt.norm_le_one z
  · intro hx
    let z : ℤ_[p] := ⟨x, hx⟩
    have hz :=
      (Examples.Qp.padicIntEquivValuationSubring p z).property
    exact hz

section

variable (F : LocalField.{u, v} K) [CharZero K]

/-- The canonical embedding `Q_p → K` takes `Z_p` into the valuation
subring.  This is proved by density of the ordinary natural numbers and
closedness of the valuation subring. -/
theorem qpadicInt_algebraMap_mem_valuationSubring
    (z : ℤ_[F.residueCharacteristic]) :
    letI : MixedQPadicContext F := mixedQPadicContext F
    algebraMap ℚ_[F.residueCharacteristic] K (z : ℚ_[F.residueCharacteristic]) ∈
      F.toCompleteDVF.valuation.valuationSubring := by
  let p := F.residueCharacteristic
  let := mixedQPadicContext F
  let : Fact p.Prime := ⟨F.residueCharacteristic_prime⟩
  let :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  let :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
  have hcontinuous : Continuous (algebraMap ℚ_[p] K) := by
    exact continuous_subtype_val.comp
      F.qpadicNumbersToQpadicClosureSubfield_isUniformInducing.uniformContinuous.continuous
  have hclosed : IsClosed
      {x : ℤ_[p] |
        _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF
            (algebraMap ℚ_[p] K (x : ℚ_[p])) ≤ 1} := by
    have hvclosed : IsClosed
        {x : K | _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF x ≤ 1} := by
      have hset :
          {x : K |
              _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
                F.toCompleteDVF x ≤ 1} =
            ((Valued.v : Valuation K
              (MonoidHom.mrange
                F.toCompleteDVF.valuation.toMonoidWithZeroHom)).valuationSubring :
              Set K) := by
        ext x
        change
          _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
                F.toCompleteDVF x ≤ 1 ↔
            Valued.v x ≤ 1
        rfl
      rw [hset]
      exact Valued.isClosed_valuationSubring K
    exact hvclosed.preimage
      (hcontinuous.comp continuous_subtype_val)
  have hz' :
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF
          (algebraMap ℚ_[p] K z) ≤ 1 := by
    refine PadicInt.denseRange_natCast.induction_on z hclosed ?_
    intro n
    rw [← Subtype.coe_le_coe]
    simpa [_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply] using
      F.valuation_natCast_le_one n
  rw [← Subtype.coe_le_coe] at hz'
  simpa [_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply, p] using hz'

/-- Pulling the valuation ring of `K` back along the canonical `Q_p` map
recovers precisely `Z_p`.  The reverse implication uses the DVR identity
`m_(Z_p) = p Z_p` and the strict inequality `v_K(p) < 1`. -/
theorem qpadicNumbersAlgebra_mem_valuationSubring_iff
    (x : ℚ_[F.residueCharacteristic]) :
    letI : MixedQPadicContext F := mixedQPadicContext F
    algebraMap ℚ_[F.residueCharacteristic] K x ∈
        F.toCompleteDVF.valuation.valuationSubring ↔
      ‖x‖ ≤ 1 := by
  let p := F.residueCharacteristic
  let := mixedQPadicContext F
  let : Fact p.Prime := ⟨F.residueCharacteristic_prime⟩
  constructor
  let algebraMap₀ := algebraMap ℚ_[p] K
  · intro hx
    by_contra hxnorm
    have hnorm := lt_of_not_ge hxnorm
    have hx0 : x ≠ 0 := by
      intro hzero
      have : ¬ (1 : ℝ) < 0 := not_lt_of_ge zero_le_one
      exact this (by simpa [hzero] using hnorm)
    have hinvnorm : ‖x⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hnorm
    let y : ℤ_[p] := ⟨x⁻¹, hinvnorm.le⟩
    have hymax : y ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      exact hinvnorm
    rw [PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton] at hymax
    obtain ⟨c, hc⟩ := hymax
    have hpval :
        F.toCompleteDVF.valuation
            (algebraMap₀ p) < 1 := by
      simpa [p] using
        F.valuation_natCast_residueCharacteristic_lt_one
    have hyfield : (y : ℚ_[p]) = (p : ℚ_[p]) * (c : ℚ_[p]) := by
      simpa [mul_comm] using congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hc
    have hyval :
        F.toCompleteDVF.valuation
            (algebraMap₀ (y : ℚ_[p])) < 1 := by
      rw [hyfield, map_mul, F.toCompleteDVF.valuation.map_mul]
      exact mul_lt_one_of_lt_of_le hpval ((F.toCompleteDVF.mem_valuationSubring_iff _).1 (by
        simpa [p] using
          F.qpadicInt_algebraMap_mem_valuationSubring c))
    have hprod :
        F.toCompleteDVF.valuation (algebraMap₀ x) *
            F.toCompleteDVF.valuation
              (algebraMap₀ (x⁻¹)) < 1 := by
      apply Right.mul_lt_one_of_le_of_lt
      · exact (F.toCompleteDVF.mem_valuationSubring_iff _).1 hx
      · simpa [y] using hyval
    have hone_lt :
        F.toCompleteDVF.valuation
            (algebraMap₀ (x * x⁻¹)) < 1 := by
      simpa using hprod
    rw [mul_inv_cancel₀ hx0, map_one,
      F.toCompleteDVF.valuation.map_one] at hone_lt
    exact (lt_irrefl (1 : F.toCompleteDVF.ValueGroup)) hone_lt
  · intro hx
    let z : ℤ_[p] := ⟨x, hx⟩
    simpa [z, p] using
      F.qpadicInt_algebraMap_mem_valuationSubring z

/-- The actual valuation of a mixed-characteristic local field extends the
DVR valuation on the canonical `Q_p` subfield. -/
theorem qpadicDVRValuation_hasExtension :
    letI : MixedQPadicContext F := mixedQPadicContext F
    (Examples.Qp.padicDVRValuation F.residueCharacteristic).HasExtension
      F.toCompleteDVF.valuation := by
  let p := F.residueCharacteristic
  let := mixedQPadicContext F
  refine ⟨(_root_.Valuation.isEquiv_iff_val_le_one).2 ?_⟩
  intro x
  exact
    (padicDVRValuation_le_one_iff_norm_le_one p x).trans
      ((F.toCompleteDVF.mem_valuationSubring_iff _).symm.trans
        (by solve_by_elim [F.qpadicNumbersAlgebra_mem_valuationSubring_iff])).symm

end

/-- The `p`-adic valuation extends to the valuation on the mixed-characteristic local field. -/
noncomputable instance mixedQPadicContextValuationExtension
    (F : LocalField.{u, v} K) [CharZero K] [MixedQPadicContext F] :
    (Examples.Qp.padicCompleteDVF F.residueCharacteristic).valuation.HasExtension
      F.toCompleteDVF.valuation :=
  F.qpadicDVRValuation_hasExtension

/--
Equips the target with its canonical `IsScalarTower` structure, namely `IsScalarTower
(Examples.Qp.padicCompleteDVF F.residueCharacteristic).valuationSubring
F.toCompleteDVF.valuationSubring K`.
-/
instance mixedQPadicContextValuationSubringTower
    (F : LocalField.{u, v} K) [CharZero K] [MixedQPadicContext F] :
    IsScalarTower
      (Examples.Qp.padicCompleteDVF F.residueCharacteristic).valuationSubring
      F.toCompleteDVF.valuationSubring K :=
  IsScalarTower.of_algebraMap_eq (by intro a; rfl)

/-! ### the canonical `Z_p` integral basis -/

section

variable (F : LocalField.{u, v} K) [CharZero K]

/-- The canonical ring map `Z_p → O_K`, obtained by restricting the
canonical `Q_p → K` map proved above. -/
noncomputable def padicIntToValuationSubring :
    ℤ_[F.residueCharacteristic] →+* F.toCompleteDVF.valuationSubring := by
  letI : MixedQPadicContext F := mixedQPadicContext F
  exact
    ((algebraMap ℚ_[F.residueCharacteristic] K).comp PadicInt.Coe.ringHom).codRestrict
      F.toCompleteDVF.valuation.valuationSubring
      (fun z => F.qpadicInt_algebraMap_mem_valuationSubring z)

/--
The embedding of `ℤ_p` into the valuation ring has underlying field value given by the `ℚ_p`
algebra map.
-/
@[simp]
theorem padicIntToValuationSubring_coe
    (z : ℤ_[F.residueCharacteristic]) :
    letI : MixedQPadicContext F := mixedQPadicContext F
    ((F.padicIntToValuationSubring z : F.toCompleteDVF.valuationSubring) : K) =
      algebraMap ℚ_[F.residueCharacteristic] K
        (z : ℚ_[F.residueCharacteristic]) := rfl

/-- The corresponding `Z_p`-algebra structure on `O_K`. -/
@[implicit_reducible]
noncomputable def padicIntValuationSubringAlgebra :
    Algebra ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring :=
  RingHom.toAlgebra F.padicIntToValuationSubring

/-- The corresponding `Z_p`-algebra structure on `K`. -/
@[implicit_reducible]
noncomputable def padicIntFieldAlgebra :
    Algebra ℤ_[F.residueCharacteristic] K := by
  letI : MixedQPadicContext F := mixedQPadicContext F
  exact RingHom.toAlgebra
    ((algebraMap ℚ_[F.residueCharacteristic] K).comp PadicInt.Coe.ringHom)

/-- The restricted algebra structures form the expected tower
`Z_p → O_K → K`. -/
theorem padicIntValuationSubring_isScalarTower :
    letI : Algebra ℤ_[F.residueCharacteristic]
        F.toCompleteDVF.valuationSubring :=
      F.padicIntValuationSubringAlgebra
    letI : Algebra ℤ_[F.residueCharacteristic] K :=
      F.padicIntFieldAlgebra
    IsScalarTower ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring K := by
  solve_by_elim [IsScalarTower.of_algebraMap_eq]

end

/-- The coherent canonical `Z_p → O_K → K` algebra model.  The bundle
retains its canonical `Q_p` context and installs both integral algebra
structures and their scalar towers. -/
class MixedIntegralAlgebraContext (F : LocalField.{u, v} K) : Prop where
  /-- The canonical `Q_p` scalar context underlying the integral algebra structure. -/
  qpadic : MixedQPadicContext F

/-- The canonical integral algebra context attached to `F`. -/
theorem mixedIntegralAlgebraContext (F : LocalField.{u, v} K) :
    MixedIntegralAlgebraContext F :=
  ⟨mixedQPadicContext F⟩

/--
Equips the target with its canonical `MixedQPadicContext` structure, namely `MixedQPadicContext
F`.
-/
instance mixedIntegralAlgebraContextQPadic
    (F : LocalField.{u, v} K) [ctx : MixedIntegralAlgebraContext F] :
    MixedQPadicContext F :=
  ctx.qpadic

/--
Equips the target with its canonical `Algebra` structure, namely `Algebra
ℤ_[F.residueCharacteristic] F.toCompleteDVF.valuationSubring`.
-/
noncomputable instance mixedIntegralAlgebraContextValuationSubringAlgebra
    (F : LocalField.{u, v} K) [CharZero K]
    [MixedIntegralAlgebraContext F] :
    Algebra ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring :=
  F.padicIntValuationSubringAlgebra

/--
Equips the target with its canonical `Algebra` structure, namely `Algebra
ℤ_[F.residueCharacteristic] K`.
-/
noncomputable instance mixedIntegralAlgebraContextFieldAlgebra
    (F : LocalField.{u, v} K) [CharZero K]
    [MixedIntegralAlgebraContext F] :
    Algebra ℤ_[F.residueCharacteristic] K :=
  F.padicIntFieldAlgebra

/--
Equips the target with its canonical `IsScalarTower` structure, namely `IsScalarTower
ℤ_[F.residueCharacteristic] ℚ_[F.residueCharacteristic] K`.
-/
instance mixedIntegralAlgebraContextQPadicTower
    (F : LocalField.{u, v} K) [CharZero K]
    [MixedIntegralAlgebraContext F] :
    IsScalarTower ℤ_[F.residueCharacteristic]
      ℚ_[F.residueCharacteristic] K :=
  IsScalarTower.of_algebraMap_eq (by intro z; rfl)

/--
Equips the target with its canonical `IsScalarTower` structure, namely `IsScalarTower
ℤ_[F.residueCharacteristic] F.toCompleteDVF.valuationSubring K`.
-/
instance mixedIntegralAlgebraContextValuationSubringTower
    (F : LocalField.{u, v} K) [CharZero K]
    [MixedIntegralAlgebraContext F] :
    IsScalarTower ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring K :=
  F.padicIntValuationSubring_isScalarTower

/-- canonical integral-closure form: `O_K` is the integral closure of
`Z_p` in `K` for the canonical `Q_p`-algebra structure. -/
theorem valuationSubring_isIntegralClosure_over_padicInt
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : MixedIntegralAlgebraContext F :=
      mixedIntegralAlgebraContext F
    IsIntegralClosure F.toCompleteDVF.valuationSubring
      ℤ_[F.residueCharacteristic] K := by
  let p := F.residueCharacteristic
  let :=
    mixedIntegralAlgebraContext F
  let : Algebra.IsSeparable ℚ_[p] K := by infer_instance
  let e :=
    Examples.Qp.padicIntEquivValuationSubring p
  refine
    { algebraMap_injective := fun a b hab => Subtype.ext hab
      isIntegral_iff := ?_ }
  intro x
  refine (e.isIntegral_iff ?_ x).trans (_root_.ValuationTheory.DiscreteValuationField.ValuedExtension.target_valuationSubring_isIntegralClosure_of_finite_separable
    (Examples.Qp.padicCompleteDVF p) F.toCompleteDVF).isIntegral_iff
  ext z
  rfl

section

variable (F : LocalField.{u, v} K) [CharZero K]

/-- The mixed-characteristic field-unit structure theorem, integral-basis finiteness: `O_K` is a finite
`Z_p`-module, with no separately assumed module structure. -/
theorem mixed_valuationSubring_moduleFinite :
    letI : MixedIntegralAlgebraContext F :=
      mixedIntegralAlgebraContext F
    Module.Finite ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring := by
  let p := F.residueCharacteristic
  let :=
    mixedIntegralAlgebraContext F
  let :=
    F.valuationSubring_isIntegralClosure_over_padicInt
  exact IsIntegralClosure.finite ℤ_[p] ℚ_[p] K
    F.toCompleteDVF.valuationSubring

/-- The mixed-characteristic field-unit structure theorem, integral-basis freeness. -/
theorem mixed_valuationSubring_moduleFree :
    letI : MixedIntegralAlgebraContext F :=
      mixedIntegralAlgebraContext F
    Module.Free ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring := by
  let p := F.residueCharacteristic
  let :=
    mixedIntegralAlgebraContext F
  let :=
    F.valuationSubring_isIntegralClosure_over_padicInt
  let :=
    FaithfulSMul.of_field_isFractionRing ℤ_[p] K ℚ_[p] K
  let : Module.IsTorsionFree ℤ_[p] K := inferInstance
  exact IsIntegralClosure.module_free
    ℤ_[p] ℚ_[p] K F.toCompleteDVF.valuationSubring

/-- The mixed-characteristic field-unit structure theorem, exact integral-basis rank. -/
theorem mixed_valuationSubring_finrank :
    letI : MixedIntegralAlgebraContext F :=
      mixedIntegralAlgebraContext F
    Module.finrank ℤ_[F.residueCharacteristic]
        F.toCompleteDVF.valuationSubring =
      Module.finrank ℚ_[F.residueCharacteristic] K := by
  let p := F.residueCharacteristic
  let :=
    mixedIntegralAlgebraContext F
  let :=
    F.valuationSubring_isIntegralClosure_over_padicInt
  let :=
    FaithfulSMul.of_field_isFractionRing ℤ_[p] K ℚ_[p] K
  let : Module.IsTorsionFree ℤ_[p] K := inferInstance
  exact IsIntegralClosure.rank
    ℤ_[p] ℚ_[p] K F.toCompleteDVF.valuationSubring

end

/-- The finite free canonical `Z_p` lattice model of `O_K`.  It retains the
integral algebra context and installs the finite and free module instances. -/
class MixedIntegralLatticeContext (F : LocalField.{u, v} K) : Prop where
  /-- The canonical `Z_p → O_K → K` algebra context underlying the lattice. -/
  integralAlgebra : MixedIntegralAlgebraContext F

/-- The canonical finite free integral-lattice context attached to `F`. -/
theorem mixedIntegralLatticeContext (F : LocalField.{u, v} K) :
    MixedIntegralLatticeContext F :=
  ⟨mixedIntegralAlgebraContext F⟩

/-- The valued field carries the integral algebra context `MixedIntegralAlgebraContext F`. -/
instance mixedIntegralLatticeContextAlgebra
    (F : LocalField.{u, v} K) [ctx : MixedIntegralLatticeContext F] :
    MixedIntegralAlgebraContext F :=
  ctx.integralAlgebra

/--
Equips the target with its canonical `Module.Finite` structure, namely `Module.Finite
ℤ_[F.residueCharacteristic] F.toCompleteDVF.valuationSubring`.
-/
noncomputable instance mixedIntegralLatticeContextModuleFinite
    (F : LocalField.{u, v} K) [CharZero K]
    [MixedIntegralLatticeContext F] :
    Module.Finite ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring :=
  F.mixed_valuationSubring_moduleFinite

/--
Equips the target with its canonical `Module.Free` structure, namely `Module.Free
ℤ_[F.residueCharacteristic] F.toCompleteDVF.valuationSubring`.
-/
noncomputable instance mixedIntegralLatticeContextModuleFree
    (F : LocalField.{u, v} K) [CharZero K]
    [MixedIntegralLatticeContext F] :
    Module.Free ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring :=
  F.mixed_valuationSubring_moduleFree

/-- A concrete integral basis indexed by the field degree `d = [K:Q_p]`. -/
noncomputable def mixed_integralBasis
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : MixedIntegralLatticeContext F :=
      mixedIntegralLatticeContext F
    Basis (Fin (Module.finrank ℚ_[F.residueCharacteristic] K))
      ℤ_[F.residueCharacteristic] F.toCompleteDVF.valuationSubring := by
  letI : MixedIntegralLatticeContext F :=
    mixedIntegralLatticeContext F
  exact Module.finBasisOfFinrankEq ℤ_[F.residueCharacteristic] F.toCompleteDVF.valuationSubring
    F.mixed_valuationSubring_finrank

/-- Coordinate form of the integral basis used in the free factor of
the mixed-characteristic field-unit structure theorem. -/
noncomputable def mixed_valuationSubringLinearEquivPi
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : MixedIntegralLatticeContext F :=
      mixedIntegralLatticeContext F
    F.toCompleteDVF.valuationSubring ≃ₗ[ℤ_[F.residueCharacteristic]]
      (Fin (Module.finrank ℚ_[F.residueCharacteristic] K) →
        ℤ_[F.residueCharacteristic]) := by
  letI : MixedIntegralLatticeContext F :=
    mixedIntegralLatticeContext F
  exact F.mixed_integralBasis.equivFun

section

variable (F : LocalField.{u, v} K) [CharZero K] (n : ℕ)

/-- Every power of the maximal ideal is a finite `Z_p`-module. -/
theorem mixed_maximalIdealPow_moduleFinite :
    letI : MixedIntegralLatticeContext F :=
      mixedIntegralLatticeContext F
    Module.Finite ℤ_[F.residueCharacteristic]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) := by
  let :=
    mixedIntegralLatticeContext F
  exact Module.Finite.of_injective
    (((F.toCompleteDVF.maximalIdeal ^ n :
      Ideal F.toCompleteDVF.valuationSubring).subtype).restrictScalars ℤ_[F.residueCharacteristic])
    Subtype.val_injective

/-- Every maximal-ideal power is free over `Z_p`. -/
theorem mixed_maximalIdealPow_moduleFree :
    letI : MixedIntegralLatticeContext F :=
      mixedIntegralLatticeContext F
    Module.Free ℤ_[F.residueCharacteristic]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) := by
  let p := F.residueCharacteristic
  let :=
    mixedIntegralLatticeContext F
  exact Module.free_of_finite_type_torsion_free'

end

/-- The finite free `Z_p` model of one maximal-ideal power.  The ambient
integral-lattice context is an explicit dependency, while the indexed bundle
owns the finite and free witnesses for the selected power. -/
class MixedMaximalIdealPowContext
    (F : LocalField.{u, v} K) [CharZero K] (n : ℕ)
    [MixedIntegralLatticeContext F] : Prop where
  /-- The `n`th maximal-ideal power is finitely generated over `Z_p`. -/
  moduleFinite : Module.Finite ℤ_[F.residueCharacteristic]
    ((F.toCompleteDVF.maximalIdeal ^ n :
      Ideal F.toCompleteDVF.valuationSubring))
  /-- The `n`th maximal-ideal power is free over `Z_p`. -/
  moduleFree : Module.Free ℤ_[F.residueCharacteristic]
    ((F.toCompleteDVF.maximalIdeal ^ n :
      Ideal F.toCompleteDVF.valuationSubring))

/-- The canonical maximal-ideal-power context. -/
theorem mixedMaximalIdealPowContext
    (F : LocalField.{u, v} K) [CharZero K] (n : ℕ) :
    letI : MixedIntegralLatticeContext F :=
      mixedIntegralLatticeContext F
    MixedMaximalIdealPowContext F n := by
  let :=
    mixedIntegralLatticeContext F
  exact
    ⟨F.mixed_maximalIdealPow_moduleFinite n,
      F.mixed_maximalIdealPow_moduleFree n⟩

/--
Equips the target with its canonical `Module.Finite` structure, namely `Module.Finite
ℤ_[F.residueCharacteristic] ((F.toCompleteDVF.maximalIdeal ^ n : Ideal
F.toCompleteDVF.valuationSubring))`.
-/
noncomputable instance mixedMaximalIdealPowContextModuleFinite
    (F : LocalField.{u, v} K) [CharZero K] (n : ℕ)
    [MixedIntegralLatticeContext F]
    [ctx : MixedMaximalIdealPowContext F n] :
    Module.Finite ℤ_[F.residueCharacteristic]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) :=
  ctx.moduleFinite

/--
Equips the target with its canonical `Module.Free` structure, namely `Module.Free
ℤ_[F.residueCharacteristic] ((F.toCompleteDVF.maximalIdeal ^ n : Ideal
F.toCompleteDVF.valuationSubring))`.
-/
noncomputable instance mixedMaximalIdealPowContextModuleFree
    (F : LocalField.{u, v} K) [CharZero K] (n : ℕ)
    [MixedIntegralLatticeContext F]
    [ctx : MixedMaximalIdealPowContext F n] :
    Module.Free ℤ_[F.residueCharacteristic]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) :=
  ctx.moduleFree

section

variable (F : LocalField.{u, v} K) [CharZero K] (n : ℕ)

/-- A nonzero maximal-ideal power has the same `Z_p` rank as `O_K`, hence
rank exactly `[K:Q_p]`. -/
theorem mixed_maximalIdealPow_finrank :
    letI : MixedIntegralLatticeContext F :=
      mixedIntegralLatticeContext F
    letI : MixedMaximalIdealPowContext F n :=
      mixedMaximalIdealPowContext F n
    Module.finrank ℤ_[F.residueCharacteristic]
        ((F.toCompleteDVF.maximalIdeal ^ n :
          Ideal F.toCompleteDVF.valuationSubring)) =
      Module.finrank ℚ_[F.residueCharacteristic] K := by
  let p := F.residueCharacteristic
  let :=
    mixedIntegralLatticeContext F
  let :=
    mixedMaximalIdealPowContext F n
  calc
    _ =
        Module.finrank ℤ_[p] F.toCompleteDVF.valuationSubring := Ideal.finrank_eq_finrank
            F.mixed_integralBasis
            (F.toCompleteDVF.maximalIdeal ^ n)
            (pow_ne_zero n F.toCompleteDVF.maximalIdeal_ne_bot)
    _ = Module.finrank ℚ_[p] K :=
      F.mixed_valuationSubring_finrank

/-- Coordinate form for a deep additive ideal, the source side of
the deep exponential–logarithm equivalence. -/
noncomputable def mixed_maximalIdealPowLinearEquivPi :
    letI : MixedIntegralLatticeContext F :=
      mixedIntegralLatticeContext F
    letI : MixedMaximalIdealPowContext F n :=
      mixedMaximalIdealPowContext F n
    ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring))
      ≃ₗ[ℤ_[F.residueCharacteristic]]
        (Fin (Module.finrank ℚ_[F.residueCharacteristic] K) →
          ℤ_[F.residueCharacteristic]) := by
  letI : MixedIntegralLatticeContext F :=
    mixedIntegralLatticeContext F
  letI : MixedMaximalIdealPowContext F n :=
    mixedMaximalIdealPowContext F n
  exact
    (Module.finBasisOfFinrankEq ℤ_[F.residueCharacteristic]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring))
      (F.mixed_maximalIdealPow_finrank n)).equivFun

end

/-! ### The canonical `Z_p` action on `U^r` -/

section

variable (F : LocalField.{u, v} K) {r : ℕ} (hr : 1 ≤ r)

/-- Inclusion of a higher principal-unit group into `U^1`. -/
def higherPrincipalUnitToFirst :
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r →*
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1 where
  toFun x := ⟨(x : F.toCompleteDVF.valuationSubringˣ),
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.antitone F.toCompleteDVF hr x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The specified map is injective: `Function.Injective (F.higherPrincipalUnitToFirst hr)`. -/
theorem higherPrincipalUnitToFirst_injective :
    Function.Injective (F.higherPrincipalUnitToFirst hr) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun z : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1 =>
      (z : F.toCompleteDVF.valuationSubringˣ)) hxy

/-- Additive form of the inclusion `U^r → U^1`. -/
def higherPrincipalUnitAddToFirst :
    Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r) →+
      Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1) :=
  MonoidHom.toAdditive (F.higherPrincipalUnitToFirst hr)

/-- The specified map is injective: `Function.Injective (F.higherPrincipalUnitAddToFirst hr)`. -/
theorem higherPrincipalUnitAddToFirst_injective :
    Function.Injective (F.higherPrincipalUnitAddToFirst hr) := by
  solve_by_elim [F.higherPrincipalUnitToFirst_injective]

/-- Restrict the canonical p-adic scalar action on `U^1` to the stable
subgroup `U^r`. -/
@[reducible]
noncomputable def higherPrincipalUnitPadicSMul :
    SMul ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) where
  smul a x := by
    let x1 : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1 :=
      F.higherPrincipalUnitToFirst hr (Additive.toMul x)
    let y1 : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1 :=
      Additive.toMul (a • Additive.ofMul x1)
    exact Additive.ofMul ⟨(y1 : F.toCompleteDVF.valuationSubringˣ),
      CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_mem_higher
        F hr a x1 (by simp [x1, higherPrincipalUnitToFirst])⟩

/-- The additive inclusion `U^r → U^1` commutes with the canonical `ℤ_p`-scalar action. -/
@[simp]
theorem higherPrincipalUnitAddToFirst_smul
    (a : ℤ_[F.residueCharacteristic])
    (x : Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) :
    letI : SMul ℤ_[F.residueCharacteristic]
        (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) :=
      F.higherPrincipalUnitPadicSMul hr
    F.higherPrincipalUnitAddToFirst hr (a • x) =
      a • F.higherPrincipalUnitAddToFirst hr x := rfl

/-- The stable subgroup `U^r` with its canonical `Z_p`-module structure. -/
@[reducible]
noncomputable def higherPrincipalUnitPadicModule :
    Module ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) := by
  letI : SMul ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) :=
    F.higherPrincipalUnitPadicSMul hr
  exact Module.ofMinimalAxioms
    (fun a x y => by
      apply F.higherPrincipalUnitAddToFirst_injective hr
      simp only [map_add, F.higherPrincipalUnitAddToFirst_smul]
      exact smul_add a
        (F.higherPrincipalUnitAddToFirst hr x :
          Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1))
        (F.higherPrincipalUnitAddToFirst hr y :
          Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1)))
    (fun a b x => by
      apply F.higherPrincipalUnitAddToFirst_injective hr
      simp only [map_add, F.higherPrincipalUnitAddToFirst_smul]
      exact add_smul a b
        (F.higherPrincipalUnitAddToFirst hr x :
          Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1)))
    (fun a b x => by
      apply F.higherPrincipalUnitAddToFirst_injective hr
      simp only [F.higherPrincipalUnitAddToFirst_smul, mul_smul])
    (fun x => by
      apply F.higherPrincipalUnitAddToFirst_injective hr
      simp only [F.higherPrincipalUnitAddToFirst_smul, one_smul])

/-- The deep principal units, regarded as a `Z_p`-submodule of `U^1`. -/
noncomputable def higherPrincipalUnitPadicSubmodule :
    Submodule ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1)) where
  carrier := {x | ((Additive.toMul x :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1) :
        F.toCompleteDVF.valuationSubringˣ) ∈
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r}
  zero_mem' := by
    change (1 : F.toCompleteDVF.valuationSubringˣ) ∈
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r
    exact Subgroup.one_mem _
  add_mem' {x y} hx hy := by
    change (((Additive.toMul x :
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1) :
          F.toCompleteDVF.valuationSubringˣ) *
      ((Additive.toMul y :
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1) :
          F.toCompleteDVF.valuationSubringˣ)) ∈
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r
    exact Subgroup.mul_mem _ hx hy
  smul_mem' a x hx :=
    CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_mem_higher
      F hr a (Additive.toMul x) hx

end

/-- A higher principal-unit group is linearly equivalent to its image in
`U^1`.  This is the submodule used in the finite-index argument in the
proof of the mixed-characteristic field-unit structure theorem. -/
noncomputable def higherPrincipalUnitLinearEquivPadicSubmodule
    (F : LocalField.{u, v} K) {r : ℕ} (hr : 1 ≤ r) :
    letI : Module ℤ_[F.residueCharacteristic]
        (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) :=
      F.higherPrincipalUnitPadicModule hr
    Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r) ≃ₗ[
        ℤ_[F.residueCharacteristic]] F.higherPrincipalUnitPadicSubmodule hr := by
  letI : Module ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) :=
    F.higherPrincipalUnitPadicModule hr
  exact
    { toFun := fun x => ⟨F.higherPrincipalUnitAddToFirst hr x,
        (Additive.toMul x).property⟩
      invFun := fun x => Additive.ofMul
        ⟨((Additive.toMul x.1 :
          LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1) :
            F.toCompleteDVF.valuationSubringˣ), x.2⟩
      left_inv := fun x => by
        apply Additive.toMul.injective
        apply Subtype.ext
        rfl
      right_inv := fun x => by
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Subtype.ext
        rfl
      map_add' := fun x y => by
        apply Subtype.ext
        exact map_add (F.higherPrincipalUnitAddToFirst hr) x y
      map_smul' := fun a x => by
        apply Subtype.ext
        exact F.higherPrincipalUnitAddToFirst_smul hr a x }

section

variable (F : LocalField.{u, v} K) (n : ℕ)

/-- Projection of `U^1` to the wrapped quotient `U^1/U^(n+1)`, as a
`Z_p`-linear map. -/
noncomputable def principalUnitQuotientProjectionLinear :
    Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1) →ₗ[
        ℤ_[F.residueCharacteristic]]
      CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient
        F.toCompleteDVF n :=
  (CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsCoordinateLinear
    F n).comp
    (CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.linearEquivUnderlying
      F).symm.toLinearMap

/-- The canonically indexed image of `U^(n+1)` inside `U^1`. -/
noncomputable def principalUnitSuccPadicSubmodule :
    Submodule ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1)) :=
  F.higherPrincipalUnitPadicSubmodule
    (Nat.succ_le_succ (Nat.zero_le n))

/-- The kernel of the finite projection is exactly the image of
`U^(n+1) \hookrightarrow U^1`. -/
theorem principalUnitQuotientProjectionLinear_ker :
    LinearMap.ker (F.principalUnitQuotientProjectionLinear n) =
      F.principalUnitSuccPadicSubmodule n := by
  ext x
  rw [LinearMap.mem_ker]
  constructor
  · intro hx
    have hxq :
        (QuotientGroup.mk (Additive.toMul x) :
          CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier
            F.toCompleteDVF n) = 1 := by
      have hx' := congrArg
        (CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv
          F.toCompleteDVF n) hx
      have hxadd : Additive.ofMul
          (QuotientGroup.mk (Additive.toMul x) :
            CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier
              F.toCompleteDVF n) = 0 := by
        rw [map_zero] at hx'
        change Additive.ofMul
          (QuotientGroup.mk (Additive.toMul x) :
            CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier
              F.toCompleteDVF n) = 0 at hx'
        exact hx'
      exact (congrArg Additive.toMul hxadd)
    have hxmem := (QuotientGroup.eq_one_iff
        (N := (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)).subgroupOf
          (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1))
        (Additive.toMul x)).mp hxq
    exact hxmem
  · intro hx
    apply (CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv
      F.toCompleteDVF n).injective
    apply Additive.ofMul.injective
    apply (QuotientGroup.eq_one_iff
      (N := (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)).subgroupOf
        (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1))
      (Additive.toMul x)).mpr
    exact hx

/-- Every wrapped local-field coordinate `U^1/U^(n+1)` is a torsion
`Z_p`-module. -/
theorem discretePrincipalUnitQuotient_moduleIsTorsion :
    Module.IsTorsion ℤ_[F.residueCharacteristic]
      (CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient
        F.toCompleteDVF n) := by
  let exponent := F.residueCharacteristic ^
    ((CompleteDVF.higherPrincipalUnitGroup.principalUnitResidueDegree F : ℕ) * n)
  intro x
  refine ⟨(⟨exponent, by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact_mod_cast (pow_ne_zero _ F.residueCharacteristic_prime.ne_zero)⟩), ?_⟩
  change (exponent : ℤ_[F.residueCharacteristic]) • x = 0
  rw [Nat.cast_smul_eq_nsmul]
  exact
    CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotient_nsmul_residueCharacteristic_pow_eq_zero
      F n x

/-- The same finite coordinate is a `p`-group, with its exact cardinality
coming from the principal-unit filtration. -/
theorem discretePrincipalUnitQuotient_isPGroup :
    IsPGroup F.residueCharacteristic
      (Multiplicative
        (CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient
          F.toCompleteDVF n)) := by
  apply IsPGroup.of_card

  calc
    _ =
        Nat.card
          (CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient
            F.toCompleteDVF n) :=
      Nat.card_congr Multiplicative.toAdd
    _ = F.residueCharacteristic ^
          ((CompleteDVF.higherPrincipalUnitGroup.principalUnitResidueDegree F : ℕ) * n) :=
      CompleteDVF.higherPrincipalUnitGroup.card_discretePrincipalUnitQuotient_eq_residueCharacteristic_pow
        F n

end

/-- Finite generation passes from a higher principal-unit group to its
image as a submodule of `U^1`. -/
theorem higherPrincipalUnitPadicSubmodule_moduleFinite
    (F : LocalField.{u, v} K) {r : ℕ} (hr : 1 ≤ r)
    (hfinite : @Module.Finite ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) _ _
      (F.higherPrincipalUnitPadicModule hr)) :
    Module.Finite ℤ_[F.residueCharacteristic]
      (F.higherPrincipalUnitPadicSubmodule hr) := by
  let :=
    F.higherPrincipalUnitPadicModule hr
  let := hfinite
  exact Module.Finite.equiv
    (F.higherPrincipalUnitLinearEquivPadicSubmodule hr)

end LocalField
end LocalFieldTheory.DiscreteValuationField

end
