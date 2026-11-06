module

public import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.Homomorphisms
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The concrete p-adic field `ℚ_[p]`

This file is the first concrete example leaf for the DVF navigation library.
It deliberately uses mathlib's public p-adic objects directly in theorem
statements instead of introducing public aliases for `ℚ_[p]` or its unit group.
-/

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField
namespace Examples
namespace Qp

open Filter
open scoped Topology
open scoped WithZero

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

/-- The DVR valuation on `ℚ_[p]` obtained from the discrete valuation ring
`ℤ_[p]`.  This is the chosen-valuation side of the local-field structure theory,
the local-field structure classification, for the basic `p`-adic field. -/
abbrev padicDVRValuation (p : ℕ) [Fact p.Prime] :
    _root_.Valuation ℚ_[p] ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p]

/-- The valuation subring of the DVR valuation on `ℚ_[p]` is the usual
`p`-adic integer ring. -/
def padicIntEquivValuationSubring
    (p : ℕ) [Fact p.Prime] :
    ℤ_[p] ≃+* (padicDVRValuation p).valuationSubring :=
  IsDiscreteValuationRing.equivValuationSubring (A := ℤ_[p]) (K := ℚ_[p])

/-- The valuation-subring equivalence is the usual inclusion into `ℚ_[p]`
after forgetting the integrality proof. -/
@[simp]
theorem padicIntEquivValuationSubring_coe
    (p : ℕ) [Fact p.Prime] (x : ℤ_[p]) :
    ((padicIntEquivValuationSubring p x :
        (padicDVRValuation p).valuationSubring) : ℚ_[p]) =
      (x : ℚ_[p]) :=
  rfl

/-- The residue field of `ℤ_[p]` is `ZMod p`. -/
def padicIntResidueFieldEquivZMod
    (p : ℕ) [Fact p.Prime] :
    IsLocalRing.ResidueField ℤ_[p] ≃+* ZMod p :=
  PadicInt.residueField

/-- The residue field of `ℤ_[p]` is finite. -/
theorem padicInt_residueField_finite
    (p : ℕ) [Fact p.Prime] :
    Finite (IsLocalRing.ResidueField ℤ_[p]) :=
  Finite.of_equiv (ZMod p)
    (padicIntResidueFieldEquivZMod p).symm.toEquiv

/-- The valuation in `(padicDVRValuation p).IsRankOneDiscrete` is rank-one and discrete. -/
instance padicDVRValuation_isRankOneDiscrete
    (p : ℕ) [Fact p.Prime] :
    (padicDVRValuation p).IsRankOneDiscrete := by
  dsimp [padicDVRValuation]
  infer_instance

/-- The canonical prime element has normalized value `exp (-1)` for the
chosen DVR valuation on `ℚ_[p]`. -/
theorem padicDVRValuation_apply_p
    (p : ℕ) [Fact p.Prime] :
    padicDVRValuation p (p : ℚ_[p]) =
      WithZero.exp (-1 : ℤ) := by
  change (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p]
      (((p : ℤ_[p]) : ℚ_[p])) = WithZero.exp (-1 : ℤ)
  calc
    (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p]
        (((p : ℤ_[p]) : ℚ_[p])) =
        (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).intValuation
          (p : ℤ_[p]) := by
      simpa using
        (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation_of_algebraMap
          (K := ℚ_[p]) (p : ℤ_[p])
    _ = WithZero.exp (-1 : ℤ) :=
      IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
        (IsDiscreteValuationRing.maximalIdeal ℤ_[p])
        (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
        PadicInt.maximalIdeal_eq_span_p

/-- The canonical prime element is a uniformizer for the chosen DVR
valuation on `ℚ_[p]`. -/
theorem padicDVRValuation_isUniformizer_p
    (p : ℕ) [Fact p.Prime] :
    (padicDVRValuation p).IsUniformizer (p : ℚ_[p]) :=
  WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one
    (padicDVRValuation p) (p : ℚ_[p])
    (padicDVRValuation_apply_p p)

/-- The valuation subring of the DVR valuation on `ℚ_[p]` is complete for its
maximal-ideal topology.  The proof transports mathlib's adic completeness of
`ℤ_[p]` across the explicit valuation-subring equivalence. -/
theorem padicDVRValuation_isAdicComplete
    (p : ℕ) [Fact p.Prime] :
    IsAdicComplete
      (IsLocalRing.maximalIdeal (padicDVRValuation p).valuationSubring)
      (padicDVRValuation p).valuationSubring := by
  let e : ℤ_[p] ≃+* (padicDVRValuation p).valuationSubring :=
    padicIntEquivValuationSubring p
  let : Algebra ℤ_[p] (padicDVRValuation p).valuationSubring :=
    e.toRingHom.toAlgebra
  let eLin : ℤ_[p] ≃ₗ[ℤ_[p]] (padicDVRValuation p).valuationSubring :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro r x
        rfl }
  have hcompleteZp :
      IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p] :=
    inferInstance
  let : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p] :=
    hcompleteZp
  have hcompleteAsZp :
      IsAdicComplete
        (IsLocalRing.maximalIdeal ℤ_[p])
        (padicDVRValuation p).valuationSubring :=
    isAdicComplete_of_linearEquiv
      (M := ℤ_[p]) (N := (padicDVRValuation p).valuationSubring)
      (IsLocalRing.maximalIdeal ℤ_[p]) eLin
  have hcompleteMap :
      IsAdicComplete
        ((IsLocalRing.maximalIdeal ℤ_[p]).map
          (algebraMap ℤ_[p] (padicDVRValuation p).valuationSubring))
        (padicDVRValuation p).valuationSubring :=
    (isAdicComplete_map_algebraMap_iff
      (I := IsLocalRing.maximalIdeal ℤ_[p])
      (S := (padicDVRValuation p).valuationSubring)).2 hcompleteAsZp
  have hmem (x : ℤ_[p]) :
      algebraMap ℤ_[p] (padicDVRValuation p).valuationSubring x ∈
          IsLocalRing.maximalIdeal (padicDVRValuation p).valuationSubring ↔
        x ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hx hunit
      exact hx (hunit.map (algebraMap ℤ_[p]
        (padicDVRValuation p).valuationSubring))
    · intro hx hunit
      apply hx
      have hpre := hunit.map e.symm.toRingHom
      simpa [RingHom.algebraMap_toAlgebra] using hpre
  have hmapMax :
      (IsLocalRing.maximalIdeal ℤ_[p]).map
          (algebraMap ℤ_[p] (padicDVRValuation p).valuationSubring) =
        IsLocalRing.maximalIdeal (padicDVRValuation p).valuationSubring := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      exact (hmem x).2 hx
    · intro y hy
      have hx :
          e.symm y ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
        simp_all
      have hmap :=
        Ideal.mem_map_of_mem
          (algebraMap ℤ_[p] (padicDVRValuation p).valuationSubring) hx
      simpa [RingHom.algebraMap_toAlgebra] using hmap
  simpa [hmapMax] using hcompleteMap

/-- The standard `p`-adic valuation is complete as a discrete valuation. -/
instance padicDVRValuation_isCompleteDiscrete
    (p : ℕ) [Fact p.Prime] :
    Valuation.IsCompleteDiscrete (padicDVRValuation p) where
  isAdicComplete := padicDVRValuation_isAdicComplete p

/-- The concrete complete-DVF package for the `p`-adic field `ℚ_[p]`. -/
def padicCompleteDVF
    (p : ℕ) [Fact p.Prime] :
    CompleteDVF ℚ_[p] where
  ValueGroup := ℤᵐ⁰
  valuation := padicDVRValuation p
  instCompleteDiscrete := inferInstance

/-- The residue field of the complete-DVF package on `ℚ_[p]` is finite. -/
theorem padicCompleteDVF_residueField_finite
    (p : ℕ) [Fact p.Prime] :
    Finite (padicCompleteDVF p).residueField := by
  let e : ℤ_[p] ≃+* (padicDVRValuation p).valuationSubring :=
    padicIntEquivValuationSubring p
  let : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    padicInt_residueField_finite p
  have hfiniteVal :
      Finite (IsLocalRing.ResidueField
        (padicDVRValuation p).valuationSubring) :=
    Finite.of_equiv (IsLocalRing.ResidueField ℤ_[p])
      (IsLocalRing.ResidueField.mapEquiv e)
  simpa [padicCompleteDVF, CompleteDVF.residueField,
    CompleteDVF.valuationSubring, CompleteDVF.toDVF] using hfiniteVal

/-- The residue field of the concrete complete-DVF package on `ℚ_[p]` has
cardinality exactly `p`. -/
theorem padicCompleteDVF_residueField_card
    (p : ℕ) [Fact p.Prime] :
    Nat.card (padicCompleteDVF p).residueField = p := by
  let eO : ℤ_[p] ≃+* (padicDVRValuation p).valuationSubring :=
    padicIntEquivValuationSubring p
  let eRes :
      IsLocalRing.ResidueField (padicDVRValuation p).valuationSubring ≃+*
        ZMod p :=
    (IsLocalRing.ResidueField.mapEquiv eO).symm.trans
      (padicIntResidueFieldEquivZMod p)
  change
    Nat.card
        (IsLocalRing.ResidueField
          (padicDVRValuation p).valuationSubring) =
      p
  calc
    Nat.card
        (IsLocalRing.ResidueField
          (padicDVRValuation p).valuationSubring) =
        Nat.card (ZMod p) :=
      Nat.card_congr eRes.toEquiv
    _ = p := Nat.card_zmod p

/-- The local-field structure theory, the local-field structure classification, `p`-adic base-field direction:
`ℚ_[p]` is a local field in the chosen-complete-DVF sense used in this
formalization. -/
def padicLocalField
    (p : ℕ) [Fact p.Prime] :
    LocalField ℚ_[p] := by
  let F : CompleteDVF ℚ_[p] := padicCompleteDVF p
  haveI : Finite F.residueField := by
    simpa [F] using padicCompleteDVF_residueField_finite p
  exact { toCompleteDVF := F }
