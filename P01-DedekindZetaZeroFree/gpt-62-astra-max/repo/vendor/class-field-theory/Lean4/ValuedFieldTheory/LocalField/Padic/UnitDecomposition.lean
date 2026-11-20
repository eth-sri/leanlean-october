module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitStructure
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
public import ValuedFieldTheory.LocalField.Padic.NonarchimedeanLocalField
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.GroupTheory.Torsion

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Unit decomposition of the p-adic integers

This file constructs the reusable topological decomposition of
`ℤ_[p]ˣ` into its finite factor and its principal `p`-adic factor.
-/

open scoped Topology

noncomputable section

namespace LocalFieldTheory
namespace Padic

open scoped WithZero
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

theorem padicDVRValuation_surjective
    (p : ℕ) [Fact p.Prime] :
    Function.Surjective (padicDVRValuation p) := by
  intro y
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  let π :=
    valuation_exists_uniformizer ℚ_[p]
      (IsDiscreteValuationRing.maximalIdeal ℤ_[p]) |>.choose
  refine ⟨π ^ (- WithZero.log y), ?_⟩
  rw [map_zpow₀ (padicDVRValuation p) π (- WithZero.log y)]
  rw [(valuation_exists_uniformizer ℚ_[p]
    (IsDiscreteValuationRing.maximalIdeal ℤ_[p]) |>.choose_spec)]
  rw [← WithZero.exp_zsmul]
  simpa using WithZero.exp_log hy

local instance padicDVRResidueFinite
    (p : ℕ) [Fact p.Prime] :
    Finite
      (IsLocalRing.ResidueField
        (padicDVRValuation p).valuationSubring) := by
  simpa [padicCompleteDVF] using
    padicCompleteDVF_residueField_finite p

section

variable (p : ℕ) [Fact p.Prime]

/-- The residue field of the valuation-theoretic presentation of `ℚ_[p]`
is canonically `ZMod p`. -/
noncomputable def padicResidueEquivZMod :
    (LocalField.ofWithZeroValuation
      (padicDVRValuation p)).residueField ≃+* ZMod p :=
  (IsLocalRing.ResidueField.mapEquiv
      (padicIntEquivValuationSubring p)).symm.trans
    (padicIntResidueFieldEquivZMod p)

theorem padic_residueCharacteristic_eq :
    (LocalField.ofWithZeroValuation
      (padicDVRValuation p)).residueCharacteristic = p := by
  let F :=
    LocalField.ofWithZeroValuation
      (padicDVRValuation p)
  let e :=
    padicResidueEquivZMod p
  have : CharP F.residueField p := by
    constructor
    intro n
    rw [← e.injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff (ZMod p) p n
  apply ringChar.eq

theorem padicDVRValued_uniformSpace_eq_standard :
    (Valued.mk' (padicDVRValuation p)).toUniformSpace =
      (inferInstance : UniformSpace ℚ_[p]) := by
  let v := padicDVRValuation p
  let standard : Valued ℚ_[p] NNReal :=
    NormedField.toValued
  let w := standard.v
  have hvw : v.IsEquiv w := by
    apply Valuation.isEquiv_of_val_le_one
    intro x
    rw [LocalField.padicDVRValuation_le_one_iff_norm_le_one]
    change
      (↑‖x‖₊ : ℝ) ≤ (↑(1 : NNReal) : ℝ) ↔ ‖x‖₊ ≤ 1
    exact NNReal.coe_le_coe
  have hmk :
      (Valued.mk' v).toUniformSpace =
        (Valued.mk' w).toUniformSpace := by
    apply le_antisymm
    · exact hvw.symm.uniformContinuous
    · exact hvw.uniformContinuous
  exact hmk.trans ((@Valued.toUniformSpace_eq ℚ_[p] _ NNReal _ standard).trans
    (@Valued.toUniformSpace_eq ℚ_[p] _ NNReal _
      (Valued.mk' w)).symm).symm

theorem padic_finrank_eq_one :
    let v := padicDVRValuation p
    let F := LocalField.ofWithZeroValuation v
    letI : LocalField.MixedWithZeroValuationContext v :=
      LocalField.mixedWithZeroValuationContext v
    Module.finrank ℚ_[F.residueCharacteristic] ℚ_[p] = 1 := by
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  let :=
    LocalField.mixedWithZeroValuationContext v
  dsimp only
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
  refine ⟨RingHom.injective _, ?_⟩
  let restricted :=
    CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  let algebraMap₀ := algebraMap ℚ_[F.residueCharacteristic] ℚ_[p]
  have hrestricted :
      @IsUniformInducing
        ℚ_[F.residueCharacteristic] ℚ_[p]
        inferInstance restricted.toUniformSpace
        (algebraMap₀) := by
    let := restricted
    exact isUniformEmbedding_subtype_val.isUniformInducing.comp
      F.qpadicNumbersToQpadicClosureSubfield_isUniformInducing
  have huniform :
      (Valued.mk' v).toUniformSpace = restricted.toUniformSpace := by
    change
      (Valued.mk' v).toUniformSpace =
        (CompleteDVF.mrangeRestrictValued
          (WithZeroValuationTopology.completeDVF v)).toUniformSpace
    exact WithZeroValuationTopology.valuedMk_uniformSpace_eq_mrangeRestrict v
  have hclosed :
      @IsClosed ℚ_[p] restricted.toTopologicalSpace
        (Set.range
          (algebraMap₀)) := by
    have hembedding :
        @IsUniformEmbedding
          ℚ_[F.residueCharacteristic] ℚ_[p]
          inferInstance restricted.toUniformSpace
          (algebraMap₀) :=
      ⟨hrestricted, RingHom.injective _⟩
    exact hembedding.isClosedEmbedding.isClosed_range
  have hratDense :
      @DenseRange ℚ_[p] restricted.toTopologicalSpace
        ℚ ((↑) : ℚ → ℚ_[p]) := by
    exact (congrArg (fun T : TopologicalSpace ℚ_[p] =>
      @DenseRange ℚ_[p] T ℚ ((↑) : ℚ → ℚ_[p])) (congrArg (fun U : UniformSpace ℚ_[p] => U.toTopologicalSpace) ((padicDVRValued_uniformSpace_eq_standard p).symm.trans huniform))).mp (Padic.denseRange_ratCast p)
  have hdense :
      @DenseRange ℚ_[p] restricted.toTopologicalSpace
        ℚ_[F.residueCharacteristic]
        (algebraMap₀) := by
    apply DenseRange.of_comp

    have hcomp :
        (algebraMap₀) ∘
            ((↑) : ℚ → ℚ_[F.residueCharacteristic]) =
          ((↑) : ℚ → ℚ_[p]) := by
      funext q
      simpa using
        (map_ratCast
          (algebraMap₀) q)
    rw [hcomp]
    exact hratDense
  rw [← Set.range_eq_univ]
  exact hclosed.closure_eq.symm.trans hdense.closure_range

end

/-- After identifying the residue characteristic with `p` and the relative
degree with one, the free additive factor is canonically `ℤ_[p]`. -/
noncomputable def padicFreeContinuousAddEquivOfEq
    (p q d : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hq : q = p) (hd : d = 1) :
    (Fin d → ℤ_[q]) ≃ₜ+ ℤ_[p] := by
  subst q
  subst d
  exact
    { AddEquiv.funUnique (Fin 1) ℤ_[p] with
      continuous_toFun := continuous_apply 0
      continuous_invFun := continuous_pi fun _ => continuous_id }

/-- The free additive factor in the mixed-characteristic structure theorem
for `ℚ_[p]` is continuously equivalent to `ℤ_[p]`. -/
noncomputable def padicFreeContinuousAddEquiv
    (p : ℕ) [Fact p.Prime] :
    let v := padicDVRValuation p
    let F := LocalField.ofWithZeroValuation v
    letI : LocalField.MixedWithZeroValuationContext v :=
      LocalField.mixedWithZeroValuationContext v
    let d := Module.finrank ℚ_[F.residueCharacteristic] ℚ_[p]
    (Fin d → ℤ_[F.residueCharacteristic]) ≃ₜ+ ℤ_[p] := by
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  letI : LocalField.MixedWithZeroValuationContext v :=
    LocalField.mixedWithZeroValuationContext v
  let q := F.residueCharacteristic
  let d := Module.finrank ℚ_[q] ℚ_[p]
  refine padicFreeContinuousAddEquivOfEq p q d ?_ ?_
  · simpa [q, F, v] using padic_residueCharacteristic_eq p
  · simpa [d, F, v] using padic_finrank_eq_one p

section

variable (p : ℕ) [Fact p.Prime]

theorem padicIntEquivValuationSubring_coe (z : ℤ_[p]) :
    ((padicIntEquivValuationSubring p z :
      (padicDVRValuation p).valuationSubring) : ℚ_[p]) =
        (z : ℚ_[p]) := rfl

theorem padicIntEquivValuationSubring_symm_coe
    (z : (padicDVRValuation p).valuationSubring) :
    (((padicIntEquivValuationSubring p).symm z : ℤ_[p]) : ℚ_[p]) =
      (z : ℚ_[p]) := by
  calc
    _ =
        ((padicIntEquivValuationSubring p
          ((padicIntEquivValuationSubring p).symm z) :
            (padicDVRValuation p).valuationSubring) : ℚ_[p]) := by
      exact padicIntEquivValuationSubring_coe p _
    _ = z := by
      simp

/-- The standard `p`-adic integers and the valuation subring of `ℚ_[p]`
are continuously multiplicatively equivalent. -/
noncomputable def padicIntValuationSubringContinuousMulEquiv :
    let v := padicDVRValuation p
    ℤ_[p] ≃ₜ* v.valuationSubring := by
  exact
    { (padicIntEquivValuationSubring p).toMulEquiv with
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact isometry_subtype_coe.continuous.congr fun z =>
          padicIntEquivValuationSubring_coe p z
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact isometry_subtype_coe.continuous.congr fun z =>
          (padicIntEquivValuationSubring_symm_coe p z).symm }

end

/-- Multiplicative tagging turns a continuous additive equivalence into a
continuous multiplicative equivalence. -/
noncomputable def continuousMultiplicativeEquivOfAddEquiv
    {A B : Type*} [AddZeroClass A] [AddZeroClass B]
    [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ+ B) :
    Multiplicative A ≃ₜ* Multiplicative B :=
  { e.toAddEquiv.toMultiplicative with
    continuous_toFun := e.continuous_toFun
    continuous_invFun := e.continuous_invFun }

/-- Multiplicative tagging commutes continuously with binary products. -/
noncomputable def prodMultiplicativeContinuousMulEquiv
    (A B : Type*) [AddZeroClass A] [AddZeroClass B]
    [TopologicalSpace A] [TopologicalSpace B] :
    Multiplicative (A × B) ≃ₜ*
      Multiplicative A × Multiplicative B :=
  { MulEquiv.prodMultiplicative A B with
    continuous_toFun := continuous_fst.prodMk continuous_snd
    continuous_invFun := continuous_fst.prodMk continuous_snd }

/-- The product of two continuous multiplicative equivalences. -/
noncomputable def continuousMulEquivProdCongr
    {A B C D : Type*}
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D]
    [MulOneClass A] [MulOneClass B] [MulOneClass C] [MulOneClass D]
    (e : A ≃ₜ* B) (f : C ≃ₜ* D) :
    A × C ≃ₜ* B × D :=
  { MulEquiv.prodCongr e.toMulEquiv f.toMulEquiv with
    continuous_toFun :=
      (e.continuous_toFun.comp continuous_fst).prodMk
        (f.continuous_toFun.comp continuous_snd)
    continuous_invFun :=
      (e.continuous_invFun.comp continuous_fst).prodMk
        (f.continuous_invFun.comp continuous_snd) }

/-- Continuous multiplicative reassociation of a triple product. -/
noncomputable def continuousMulEquivProdAssoc
    (A B C : Type*) [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [MulOneClass A] [MulOneClass B] [MulOneClass C] :
    (A × B) × C ≃ₜ* A × (B × C) :=
  { MulEquiv.prodAssoc with
    continuous_toFun :=
      (continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    continuous_invFun :=
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd) }

section

variable (p : ℕ) [Fact p.Prime]

/-- The topology on the first principal-unit group induced directly from
the valuation topology on `ℚ_[p]`. -/
@[implicit_reducible]
noncomputable def padicPrincipalUnitDirectTopology :
    let v := padicDVRValuation p
    let F := LocalField.ofWithZeroValuation v
    TopologicalSpace
      (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1) := by
  let v := padicDVRValuation p
  letI : Valued ℚ_[p] (WithZero (Multiplicative ℤ)) :=
    Valued.mk' v
  exact inferInstance

/-- The standard topology on the first principal-unit group of `ℚ_[p]`. -/
@[implicit_reducible]
noncomputable def padicPrincipalUnitStandardTopology :
    let v := padicDVRValuation p
    let F := LocalField.ofWithZeroValuation v
    TopologicalSpace
      (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1) := inferInstance

/-- The directly induced valuation topology agrees with the standard topology
on the first principal-unit group of `ℚ_[p]`. -/
theorem padicPrincipalUnitDirectTopology_eq_standard :
    padicPrincipalUnitDirectTopology p =
      padicPrincipalUnitStandardTopology p := by
  let v := padicDVRValuation p
  let U := CompleteDVF.higherPrincipalUnitGroup (LocalField.ofWithZeroValuation v).toCompleteDVF 1
  let liftTopology := fun T : TopologicalSpace ℚ_[p] => by
    exact (inferInstance : TopologicalSpace U)
  unfold padicPrincipalUnitDirectTopology
    padicPrincipalUnitStandardTopology
  exact congrArg liftTopology
    (congrArg (fun U : UniformSpace ℚ_[p] => U.toTopologicalSpace)
      (padicDVRValued_uniformSpace_eq_standard p))

/-- The first-principal-unit structure data transported to the standard
`p`-adic topology. -/
noncomputable def padicPrincipalData :
    let v := padicDVRValuation p
    let F := LocalField.ofWithZeroValuation v
    letI : LocalField.MixedWithZeroValuationContext v :=
      LocalField.mixedWithZeroValuationContext v
    let d := Module.finrank ℚ_[F.residueCharacteristic] ℚ_[p]
    Σ a : ℕ,
      Multiplicative
          (ZMod (F.residueCharacteristic ^ a) ×
            (Fin d → ℤ_[F.residueCharacteristic])) ≃ₜ*
        CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1 := by
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  letI : LocalField.MixedWithZeroValuationContext v :=
    LocalField.mixedWithZeroValuationContext v
  let U := CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1
  letI : Valued ℚ_[p] (WithZero (Multiplicative ℤ)) := (Valued.mk' v)
  let directTopology : TopologicalSpace U := inferInstance
  let standardTopology :=
    padicPrincipalUnitStandardTopology p
  have hdirect :
      directTopology = padicPrincipalUnitDirectTopology p := by
    unfold directTopology padicPrincipalUnitDirectTopology
    rfl
  let P : TopologicalSpace U → Type := fun T => by
    letI : TopologicalSpace U := T
    exact Σ a : ℕ,
      Multiplicative
          (ZMod (F.residueCharacteristic ^ a) ×
            (Fin (Module.finrank ℚ_[F.residueCharacteristic] ℚ_[p]) → ℤ_[F.residueCharacteristic])) ≃ₜ* U
  exact (congrArg P (hdirect.trans (padicPrincipalUnitDirectTopology_eq_standard p))).mp (LocalField.chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation
    v (padicDVRValuation_surjective p))

end

/-- The finite factor in the topological decomposition of `ℤ_pˣ`. -/
noncomputable abbrev padicUnitFiniteFactor
    (p : ℕ) [Fact p.Prime] : Type :=
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  letI : LocalField.MixedWithZeroValuationContext v :=
    LocalField.mixedWithZeroValuationContext v
  Multiplicative
      (ZMod (Nat.card F.residueField - 1)) ×
    Multiplicative
      (ZMod
        (F.residueCharacteristic ^ (padicPrincipalData p).1))

/-- The standard topological decomposition
`ℤ_pˣ ≃ finite × ℤ_p` used in the local reciprocity calculation. -/
noncomputable def padicUnitDecomposition
    (p : ℕ) [Fact p.Prime] :
    padicUnitFiniteFactor p × Multiplicative ℤ_[p] ≃ₜ*
      ℤ_[p]ˣ := by
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  letI : LocalField.MixedWithZeroValuationContext v :=
    LocalField.mixedWithZeroValuationContext v
  let a := (padicPrincipalData p).1
  let RootCyc :=
    Multiplicative
      (ZMod (Nat.card F.residueField - 1))
  let FinCyc :=
    Multiplicative (ZMod (F.residueCharacteristic ^ a))
  let Free :=
    Fin (Module.finrank ℚ_[F.residueCharacteristic] ℚ_[p]) → ℤ_[F.residueCharacteristic]
  let RootGroup :=
    CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup
      F.toCompleteDVF
  let U :=
    CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1
  let rootsAlg : RootCyc ≃* RootGroup := by
    letI : Valued ℚ_[p]
        (MonoidHom.mrange
          F.toCompleteDVF.valuation.toMonoidWithZeroHom) :=
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued
        F.toCompleteDVF
    exact
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityContinuousMulEquivZMod
        F.toCompleteDVF).toMulEquiv
  letI : Finite RootGroup :=
    Finite.of_equiv F.residueFieldˣ
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits
        F.toCompleteDVF).symm.toEquiv
  letI : Finite RootCyc :=
    Finite.of_equiv RootGroup rootsAlg.symm.toEquiv
  letI : NeZero (F.residueCharacteristic ^ a) :=
    ⟨pow_ne_zero _
      F.residueCharacteristic_prime.ne_zero⟩
  let factors :=
    (continuousMulEquivProdAssoc
      RootCyc FinCyc (Multiplicative ℤ_[p])).trans
        (continuousMulEquivProdCongr ({ rootsAlg with
          continuous_toFun := continuous_of_discreteTopology
          continuous_invFun := continuous_of_discreteTopology}) ((continuousMulEquivProdCongr
          (ContinuousMulEquiv.refl FinCyc) (continuousMultiplicativeEquivOfAddEquiv
            (padicFreeContinuousAddEquiv p)).symm).trans
            ((prodMultiplicativeContinuousMulEquiv
              (ZMod (F.residueCharacteristic ^ a)) Free).symm.trans
                ((padicPrincipalData p).2))))
  let unitsAlg :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F.toCompleteDVF
  let totalAlg :=
    factors.toMulEquiv.trans unitsAlg
  have hUnitsAlg : Continuous unitsAlg := by
    refine ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).congr ?_
    intro z
    exact
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply
        F.toCompleteDVF z).symm
  let integral := Units.mapContinuousMulEquiv
      (padicIntValuationSubringContinuousMulEquiv p)
  exact (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.continuousMulEquivOfCompactToT2
    totalAlg (hUnitsAlg.comp factors.continuous_toFun)).trans integral.symm

noncomputable instance padicUnitFiniteFactor_finite
    (p : ℕ) [Fact p.Prime] :
    Finite (padicUnitFiniteFactor p) := by
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  let : LocalField.MixedWithZeroValuationContext v :=
    LocalField.mixedWithZeroValuationContext v
  let a := (padicPrincipalData p).1
  change Finite
    (Multiplicative
        (ZMod (Nat.card F.residueField - 1)) ×
      Multiplicative
        (ZMod (F.residueCharacteristic ^ a)))
  let : NeZero (Nat.card F.residueField - 1) :=
    ⟨by
      have hcard : 1 < Nat.card F.residueField :=
        Finite.one_lt_card
      omega⟩
  let : NeZero (F.residueCharacteristic ^ a) :=
    ⟨pow_ne_zero _ F.residueCharacteristic_prime.ne_zero⟩
  infer_instance

end Padic
end LocalFieldTheory

end
