module

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestriction
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CyclicValueGroup
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.SeriesValuationEstimates
public import ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNorm
public import Mathlib.RingTheory.Valuation.Extension
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CompleteRangeRestriction
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.UniformizerIntegerValuation
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestrictedTopology
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuationSubringUnitMap
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.LocalFieldRangeRestriction
public import ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal
public import ValuedFieldTheory.Valuation.DiscreteValuationField.CompleteDVRExpansion
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
public import Mathlib.LinearAlgebra.Dimension.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/























set_option autoImplicit false

/-!
# Equal-characteristic Laurent-series input for the local-field structure classification

This file starts the equal-characteristic branch of the local-field structure classification, the local-field structure classification.  Given the Teichmuller coefficient-field section
`κ -> O_K -> K` and a uniformizer `π`, it constructs the induced evaluation
map `κ((X)) -> K` by first evaluating `κ⟦X⟧` at `X = π`, then using the
localization description `κ((X)) = κ⟦X⟧[X⁻¹]`.
-/

noncomputable section

universe u v

open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF

open scoped PowerSeries LaurentSeries Filter Topology BigOperators
open Filter

variable {K : Type u} [Field K]
variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

namespace EqualCharacteristicLaurent

section

variable [Finite F.residueField] (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p] {n : ℕ+}
  (hcard : Nat.card F.residueField = p ^ (n : ℕ))
include n hcard

/-- The Teichmuller coefficient-field section `κ -> O_K` used before passing
to the fraction field. -/
abbrev coeffSubringHom :
    F.residueField →+* F.valuationSubring :=
  LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP
    (F := F) p hcard

/-- The Teichmuller coefficient-field embedding `κ -> K` used in the
equal-characteristic Laurent-series branch. -/
abbrev coeffHom :
    F.residueField →+* K :=
  LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP
    (F := F) p hcard

/-- The Teichmuller section is a representative system for the residue field. -/
noncomputable def teichmullerRepresentativeSystem :
    LubinTate.Valuations.residueRepresentativeSystem F where
  repr := coeffSubringHom (F := F) p hcard
  residue_repr := by
    intro a
    have hcomp :=
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueMap_comp_residueTeichmullerRingHomOfCharP
        (F := F) p hcard
    simpa [coeffSubringHom, RingHom.comp_apply] using
      congrFun (congrArg DFunLike.coe hcomp) a
  repr_zero := by
    simp [coeffSubringHom]

/-- The field-valued coefficient embedding is the valuation-ring coefficient
section followed by the valuation-subring inclusion. -/
@[simp] theorem coeffHom_apply
    (a : F.residueField) :
    coeffHom (F := F) p hcard a =
      (coeffSubringHom (F := F) p hcard a : K) := by
  rfl


/-- The valuation-ring Teichmuller coefficient section is continuous from the
discrete residue-field topology to any topology on the valuation ring. -/
theorem continuous_coeffSubringHom_of_discrete
    [UniformSpace F.residueField] [DiscreteUniformity F.residueField]
    [TopologicalSpace F.valuationSubring] :
    Continuous (coeffSubringHom (F := F) p hcard) :=
  continuous_of_discreteTopology

end


/-- The maximal-ideal adic topology on the valuation ring is linear. -/
private theorem valuationSubring_isLinearTopology_adic :
    letI : TopologicalSpace F.valuationSubring := F.maximalIdeal.adicTopology
    IsLinearTopology F.valuationSubring F.valuationSubring := by
  let : TopologicalSpace F.valuationSubring := F.maximalIdeal.adicTopology
  exact
    IsLinearTopology.mk_of_hasBasis F.valuationSubring
      (Ideal.hasBasis_nhds_zero_adic F.maximalIdeal)

/-- The `WithIdeal` adic topology on the valuation ring is linear. -/
 theorem valuationSubring_isLinearTopology_withIdeal :
    letI : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
    IsLinearTopology F.valuationSubring F.valuationSubring := by
  exact valuationSubring_isLinearTopology_adic ..

/-- The valuation ring is complete for its maximal-ideal adic topology. -/
 theorem valuationSubring_completeSpace_withIdeal :
    letI : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
    CompleteSpace F.valuationSubring := by
  let : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  have hadic : IsAdic F.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp F.isAdicComplete).1

/-- The valuation ring is Hausdorff for its maximal-ideal adic topology. -/
 theorem valuationSubring_t2Space_withIdeal :
    letI : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
    T2Space F.valuationSubring := by
  let : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  have hadic : IsAdic F.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp F.isAdicComplete).2

/-- A complete-DVF uniformizer is topologically nilpotent in the valuation
ring for the maximal-ideal adic topology. -/
theorem uniformizer_hasEval_valuationSubring_withIdeal
    {π : F.valuationSubring}
    (hπ : F.valuation.IsUniformizer (π : K)) :
    letI : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
    PowerSeries.HasEval π := by
  let : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  change Filter.Tendsto (fun m : ℕ => π ^ m) Filter.atTop
    (nhds (0 : F.valuationSubring))
  refine (F.maximalIdeal.hasBasis_nhds_zero_adic).tendsto_right_iff.2 ?_
  intro n _
  refine Filter.eventually_atTop.2 ⟨n, fun m hm => ?_⟩
  have hπmem : π ∈ F.maximalIdeal :=
    F.uniformizer_mem_maximalIdeal hπ
  have hpow : π ^ m ∈ F.maximalIdeal ^ m :=
    Ideal.pow_mem_pow hπmem m
  exact Ideal.pow_le_pow_right hm hpow

section

variable [Finite F.residueField] (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p] {n : ℕ+}
  (hcard : Nat.card F.residueField = p ^ (n : ℕ)) (π : F.valuationSubring)
  [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
  [IsTopologicalSemiring F.residueField] [UniformSpace F.valuationSubring]
  [IsUniformAddGroup F.valuationSubring] [T2Space F.valuationSubring]
  [CompleteSpace F.valuationSubring] [IsTopologicalRing F.valuationSubring]
  [IsLinearTopology F.valuationSubring F.valuationSubring]

/-- Evaluation of power series into the valuation ring through the
Teichmuller coefficient section, sending `X` to a chosen uniformizer. -/
noncomputable def powerSeriesEvalSubringHom
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    F.residueField⟦X⟧ →+* F.valuationSubring :=
  PowerSeries.eval₂Hom hcoeff hπeval

/--
Establishes the identity `powerSeriesEvalSubringHom (F := F) p hcard π hcoeff hπeval
(PowerSeries.C a) = coeffSubringHom (F := F) p hcard a`.
-/
@[simp] theorem powerSeriesEvalSubringHom_C
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) (a : F.residueField) :
    powerSeriesEvalSubringHom (F := F) p hcard π hcoeff hπeval
        (PowerSeries.C a) =
      coeffSubringHom (F := F) p hcard a := by
  have hfun :
      ⇑(PowerSeries.eval₂Hom hcoeff hπeval) =
        PowerSeries.eval₂ (coeffSubringHom (F := F) p hcard) π :=
    PowerSeries.coe_eval₂Hom hcoeff hπeval
  have happ := congrFun hfun (PowerSeries.C a)
  simpa [powerSeriesEvalSubringHom, PowerSeries.eval₂_C] using happ

/--
Establishes the identity `powerSeriesEvalSubringHom (F := F) p hcard π hcoeff hπeval PowerSeries.X
= π`.
-/
@[simp] theorem powerSeriesEvalSubringHom_X
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    powerSeriesEvalSubringHom (F := F) p hcard π hcoeff hπeval
        PowerSeries.X =
      π := by
  have hfun :
      ⇑(PowerSeries.eval₂Hom hcoeff hπeval) =
        PowerSeries.eval₂ (coeffSubringHom (F := F) p hcard) π :=
    PowerSeries.coe_eval₂Hom hcoeff hπeval
  have happ := congrFun hfun PowerSeries.X
  simpa [powerSeriesEvalSubringHom, PowerSeries.eval₂_X] using happ

/-- The valuation-ring evaluation composed with the inclusion `O_K -> K`. -/
noncomputable def powerSeriesEvalHom
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    F.residueField⟦X⟧ →+* K :=
  F.valuation.valuationSubring.subtype.comp
    (powerSeriesEvalSubringHom (F := F) p hcard π hcoeff hπeval)

/--
Establishes the identity `powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval (PowerSeries.C a) =
coeffHom (F := F) p hcard a`.
-/
@[simp] theorem powerSeriesEvalHom_C
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) (a : F.residueField) :
    powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval
        (PowerSeries.C a) =
      coeffHom (F := F) p hcard a := by
  have hsub :=
    powerSeriesEvalSubringHom_C
      (F := F) p hcard π hcoeff hπeval a
  exact congrArg F.valuation.valuationSubring.subtype hsub

/--
Establishes the identity `powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval PowerSeries.X = (π :
K)`.
-/
@[simp] theorem powerSeriesEvalHom_X
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval
        PowerSeries.X =
      (π : K) := by
  have hsub :=
    powerSeriesEvalSubringHom_X
      (F := F) p hcard π hcoeff hπeval
  exact congrArg F.valuation.valuationSubring.subtype hsub

end

section

variable [Finite F.residueField] (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p] {n : ℕ+}
  (hcard : Nat.card F.residueField = p ^ (n : ℕ)) (π : F.valuationSubring)
  (hπ : F.valuation.IsUniformizer (π : K)) [UniformSpace F.residueField]
  [IsUniformAddGroup F.residueField] [IsTopologicalSemiring F.residueField]
  [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
  [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
  [IsTopologicalRing F.valuationSubring]
  [IsLinearTopology F.valuationSubring F.valuationSubring]
include hπ

/--
Proves that the specified element is a unit: `IsUnit (powerSeriesEvalHom (F := F) p hcard π hcoeff
hπeval PowerSeries.X)`.
-/
theorem powerSeriesEvalHom_X_isUnit
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    IsUnit
      (powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval
        PowerSeries.X) := by
  simpa using
    (isUnit_iff_ne_zero.mpr hπ.ne_zero : IsUnit (π : K))

/-- The Laurent-series evaluation map `κ((X)) -> K` attached to the
Teichmuller coefficient field and the chosen uniformizer. -/
noncomputable def laurentSeriesEvalHom
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    F.residueField⸨X⸩ →+* K :=
  IsLocalization.Away.lift
    (S := F.residueField⸨X⸩)
    (P := K)
    (x := (PowerSeries.X : F.residueField⟦X⟧))
    (g := powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval)
    (powerSeriesEvalHom_X_isUnit
      (F := F) p hcard π hπ hcoeff hπeval)

/--
Establishes the identity `(laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval).comp
(algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩) = powerSeriesEvalHom (F := F) p hcard π hcoeff
hπeval`.
-/
theorem laurentSeriesEvalHom_comp_powerSeries
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    (laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval).comp
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩) =
      powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval := by
  exact
    IsLocalization.Away.lift_comp
      (S := F.residueField⸨X⸩)
      (P := K)
      (x := (PowerSeries.X : F.residueField⟦X⟧))
      (g := powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval)
      (powerSeriesEvalHom_X_isUnit
        (F := F) p hcard π hπ hcoeff hπeval)

/--
Establishes the identity `laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval (algebraMap
F.residueField⟦X⟧ F.residueField⸨X⸩ (PowerSeries.C a)) = coeffHom (F := F) p hcard a`.
-/
@[simp] theorem laurentSeriesEvalHom_algebraMap_C
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) (a : F.residueField) :
    laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
          (PowerSeries.C a)) =
      coeffHom (F := F) p hcard a := by
  change
    ((laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval).comp
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩))
        (PowerSeries.C a) =
      coeffHom (F := F) p hcard a
  rw [laurentSeriesEvalHom_comp_powerSeries, powerSeriesEvalHom_C]

/--
Establishes the identity `laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval (algebraMap
F.residueField⟦X⟧ F.residueField⸨X⸩ (PowerSeries.X : F.residueField⟦X⟧)) = (π : K)`.
-/
@[simp] theorem laurentSeriesEvalHom_algebraMap_X
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
          (PowerSeries.X : F.residueField⟦X⟧)) =
      (π : K) := by
  change
    ((laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval).comp
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩))
        (PowerSeries.X : F.residueField⟦X⟧) =
      (π : K)
  rw [laurentSeriesEvalHom_comp_powerSeries, powerSeriesEvalHom_X]

end



section

variable [Finite F.residueField] (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p] {n : ℕ+}
  (hcard : Nat.card F.residueField = p ^ (n : ℕ)) (π : F.valuationSubring)
  (hπ : F.valuation.IsUniformizer (π : K))
include n hcard π hπ

/-- The adic valuation-ring power-series evaluation with all topology
instances supplied from the complete-DVF structure. -/
noncomputable def adicPowerSeriesEvalSubringHom :
    F.residueField⟦X⟧ →+* F.valuationSubring := by
  letI : UniformSpace F.residueField := ⊥
  haveI : DiscreteUniformity F.residueField := inferInstance
  haveI : IsUniformAddGroup F.residueField :=
    inferInstance
  letI : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  haveI : IsLinearTopology F.valuationSubring F.valuationSubring :=
    valuationSubring_isLinearTopology_withIdeal (F := F)
  haveI : CompleteSpace F.valuationSubring :=
    valuationSubring_completeSpace_withIdeal (F := F)
  haveI : T2Space F.valuationSubring :=
    valuationSubring_t2Space_withIdeal (F := F)
  exact
    powerSeriesEvalSubringHom (F := F) p hcard π
      (continuous_coeffSubringHom_of_discrete (F := F) p hcard)
      (uniformizer_hasEval_valuationSubring_withIdeal (F := F) hπ)


/-- The adic Laurent-series evaluation with all topology instances supplied
from the complete-DVF structure. -/
noncomputable def adicLaurentSeriesEvalHom :
    F.residueField⸨X⸩ →+* K := by
  letI : UniformSpace F.residueField := ⊥
  haveI : DiscreteUniformity F.residueField := inferInstance
  haveI : IsUniformAddGroup F.residueField :=
    inferInstance
  letI : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  haveI : IsLinearTopology F.valuationSubring F.valuationSubring :=
    valuationSubring_isLinearTopology_withIdeal (F := F)
  haveI : CompleteSpace F.valuationSubring :=
    valuationSubring_completeSpace_withIdeal (F := F)
  haveI : T2Space F.valuationSubring :=
    valuationSubring_t2Space_withIdeal (F := F)
  exact
    laurentSeriesEvalHom (F := F) p hcard π hπ
      (continuous_coeffSubringHom_of_discrete (F := F) p hcard)
      (uniformizer_hasEval_valuationSubring_withIdeal (F := F) hπ)

/--
Establishes the identity `adicLaurentSeriesEvalHom (F := F) p hcard π hπ (algebraMap
F.residueField⟦X⟧ F.residueField⸨X⸩ (PowerSeries.C a)) = coeffHom (F := F) p hcard a`.
-/
@[simp] theorem adicLaurentSeriesEvalHom_algebraMap_C (a : F.residueField) :
    adicLaurentSeriesEvalHom (F := F) p hcard π hπ
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
          (PowerSeries.C a)) =
      coeffHom (F := F) p hcard a := by
  let : UniformSpace F.residueField := ⊥
  have : DiscreteUniformity F.residueField := inferInstance
  have : IsUniformAddGroup F.residueField :=
    inferInstance
  let : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  have : IsLinearTopology F.valuationSubring F.valuationSubring :=
    valuationSubring_isLinearTopology_withIdeal (F := F)
  have : CompleteSpace F.valuationSubring :=
    valuationSubring_completeSpace_withIdeal (F := F)
  have : T2Space F.valuationSubring :=
    valuationSubring_t2Space_withIdeal (F := F)
  simpa [adicLaurentSeriesEvalHom] using
    laurentSeriesEvalHom_algebraMap_C
      (F := F) p hcard π hπ
      (continuous_coeffSubringHom_of_discrete (F := F) p hcard)
      (uniformizer_hasEval_valuationSubring_withIdeal (F := F) hπ) a

/--
Establishes the identity `adicLaurentSeriesEvalHom (F := F) p hcard π hπ (algebraMap
F.residueField⟦X⟧ F.residueField⸨X⸩ (PowerSeries.X : F.residueField⟦X⟧)) = (π : K)`.
-/
@[simp] theorem adicLaurentSeriesEvalHom_algebraMap_X :
    adicLaurentSeriesEvalHom (F := F) p hcard π hπ
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
          (PowerSeries.X : F.residueField⟦X⟧)) =
      (π : K) := by
  let : UniformSpace F.residueField := ⊥
  have : DiscreteUniformity F.residueField := inferInstance
  have : IsUniformAddGroup F.residueField :=
    inferInstance
  let : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  have : IsLinearTopology F.valuationSubring F.valuationSubring :=
    valuationSubring_isLinearTopology_withIdeal (F := F)
  have : CompleteSpace F.valuationSubring :=
    valuationSubring_completeSpace_withIdeal (F := F)
  have : T2Space F.valuationSubring :=
    valuationSubring_t2Space_withIdeal (F := F)
  simpa [adicLaurentSeriesEvalHom] using
    laurentSeriesEvalHom_algebraMap_X
      (F := F) p hcard π hπ
      (continuous_coeffSubringHom_of_discrete (F := F) p hcard)
      (uniformizer_hasEval_valuationSubring_withIdeal (F := F) hπ)

end



end EqualCharacteristicLaurent
end CompleteDVF


namespace LocalField

open scoped PowerSeries LaurentSeries Filter Topology BigOperators

variable {K : Type u} [Field K]
variable (F : LocalField.{u, v} K)

section

variable (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p] {n : ℕ+}
  (hcard : Nat.card F.residueField = p ^ (n : ℕ)) (π : F.valuationSubring)
  (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
include n hcard π hπ

/-- The image in `K` of the equal-characteristic Laurent-series evaluation.
This is the candidate base field for the converse direction of the local-field structure classification. -/
noncomputable def laurentImageSubfield :
    Subfield K :=
  (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom
    (F := F.toCompleteDVF) p hcard π hπ).fieldRange



/-- The Laurent-series field is identified with its image in `K`. -/
noncomputable def laurentSeriesEquivLaurentImageSubfield :
    F.residueField⸨X⸩ ≃+*
      F.laurentImageSubfield p hcard π hπ :=
  RingHom.rangeRestrictFieldEquiv
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom
      (F := F.toCompleteDVF) p hcard π hπ)

/--
Establishes the identity `((F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ x :
F.laurentImageSubfield p hcard π hπ) : K) =
CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom (F := F.toCompleteDVF) p hcard π
hπ x`.
-/
@[simp] theorem laurentSeriesEquivLaurentImageSubfield_apply_coe
    (x : F.residueField⸨X⸩) :
    ((F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ x :
        F.laurentImageSubfield p hcard π hπ) : K) =
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom
        (F := F.toCompleteDVF) p hcard π hπ x := by
  rfl

/--
Establishes the identity `((F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ (algebraMap
F.residueField⟦X⟧ F.residueField⸨X⸩ (PowerSeries.C a)) : F.laurentImageSubfield p hcard π hπ) : K)
= CompleteDVF.EqualCharacteristicLaurent.coeffHom (F := F.toCompleteDVF) p hcard a`.
-/
@[simp] theorem laurentSeriesEquivLaurentImageSubfield_algebraMap_C
    (a : F.residueField) :
    ((F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
          (PowerSeries.C a)) :
        F.laurentImageSubfield p hcard π hπ) : K) =
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom
        (F := F.toCompleteDVF) p hcard a := by
  simpa using
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom_algebraMap_C
      (F := F.toCompleteDVF) p hcard π hπ a

/--
Establishes the identity `((F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ (algebraMap
F.residueField⟦X⟧ F.residueField⸨X⸩ (PowerSeries.X : F.residueField⟦X⟧)) : F.laurentImageSubfield
p hcard π hπ) : K) = (π : K)`.
-/
@[simp] theorem laurentSeriesEquivLaurentImageSubfield_algebraMap_X :
    ((F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
          (PowerSeries.X : F.residueField⟦X⟧)) :
        F.laurentImageSubfield p hcard π hπ) : K) =
      (π : K) := by
  simpa using
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom_algebraMap_X
      (F := F.toCompleteDVF) p hcard π hπ

end








end LocalField
end LocalFieldTheory.DiscreteValuationField

end
