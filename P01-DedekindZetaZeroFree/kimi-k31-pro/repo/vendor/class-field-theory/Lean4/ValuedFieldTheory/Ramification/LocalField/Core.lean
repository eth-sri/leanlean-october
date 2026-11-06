module

public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import Mathlib.FieldTheory.Galois.Basic
public import ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction
public import ValuedFieldTheory.Ramification.Herbrand.Function
public import ValuedFieldTheory.Ramification.HilbertRamification.FiniteGaloisLevelIndependence
public import ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction
public import ValuedFieldTheory.Ramification.HilbertRamification.HerbrandTheorem

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/









set_option autoImplicit false

/-!
# Upper ramification jumps

The actual finite-level upper filtration attached to the canonical
complete-DVF structure of a nonarchimedean local field, together with its
right-limit subgroup and the intrinsic predicate for an upper jump.
-/

noncomputable section

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open scoped ValuativeRel

universe y

namespace LocalFieldTheory

/-- Uniqueness after forgetting completeness, in the form consumed by the
real lower and upper ramification APIs. -/
theorem chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{0, 0, 0, 0, y}
      (localCompleteDVF K).toDVF
      (chosenLocalExtensionCompleteDVF K L).toDVF :=
  chosenLocalExtensionCompleteDVF_hasUniqueValuationExtension K L

end LocalFieldTheory

namespace RamificationTheory.LocalField

open LocalFieldTheory
open RamificationTheory
open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.Higher

/-- Pull a complete discrete valuation back along a field equivalence. -/
 noncomputable def completeDVFComapAlgEquiv
    {L M : Type} [Field L] [Field M]
    (target : CompleteDVF.{0, 0} M) (e : L ≃+* M) :
    CompleteDVF.{0, 0} L where
  ValueGroup := target.ValueGroup
  valuation := target.valuation.comap e.toRingHom
  instCompleteDiscrete :=
    Valuation.isCompleteDiscrete_comap_ringEquiv target.valuation e

/-- Pullback along a base-linear equivalence preserves extension of the base
valuation. -/
private theorem completeDVFComapAlgEquiv_hasExtension
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (base : CompleteDVF.{0, 0} K)
    (target : CompleteDVF.{0, 0} M)
    [base.valuation.HasExtension target.valuation]
    (e : L ≃ₐ[K] M) :
    base.valuation.HasExtension
      (completeDVFComapAlgEquiv target e.toRingEquiv).valuation where
  val_isEquiv_comap := by
    rw [_root_.Valuation.isEquiv_iff_val_le_one]
    intro a
    change
      base.valuation a ≤ 1 ↔
        target.valuation (e ((algebraMap K L) a)) ≤ 1
    rw [e.commutes]
    exact
      (_root_.Valuation.HasExtension.val_map_le_one_iff
        (vR := base.valuation) (vA := target.valuation) a).symm

/-- The actual real lower ramification group of an arbitrary finite Galois
extension of nonarchimedean local fields, using its integral-closure
valuation. -/
noncomputable def localLowerRamificationGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (t : ℝ) : Subgroup Gal(L / K) :=
  Higher.lowerRamificationGroup
    (base := (localCompleteDVF K).toDVF)
    (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
    (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L) t

/-- The actual real upper ramification group of an arbitrary finite Galois
extension of nonarchimedean local fields. -/
noncomputable def localUpperRamificationGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (t : ℝ) : Subgroup Gal(L / K) :=
  Higher.upperRamificationGroupOfUniqueExtension
    (base := (localCompleteDVF K).toDVF)
    (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
    (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L) t

/-- A base-linear field equivalence transports every local upper ramification
group to the corresponding group of the equivalent extension. -/
theorem localUpperRamificationGroup_map_autCongr
    (K L M : Type)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (e : L ≃ₐ[K] M) (t : ℝ) :
    Subgroup.map (AlgEquiv.autCongr e).toMonoidHom
        (localUpperRamificationGroup K L t) =
      localUpperRamificationGroup K M t := by
  let base := localCompleteDVF K
  let targetL := chosenLocalExtensionCompleteDVF K L
  let targetM := chosenLocalExtensionCompleteDVF K M
  let pulled := completeDVFComapAlgEquiv targetM e.toRingEquiv
  let hExtL : base.valuation.HasExtension targetL.valuation :=
    chosenLocalExtensionCompleteDVF_hasExtension K L
  let hExtM : base.valuation.HasExtension targetM.valuation :=
    chosenLocalExtensionCompleteDVF_hasExtension K M
  let hExtPulled : base.valuation.HasExtension pulled.valuation :=
    completeDVFComapAlgEquiv_hasExtension K L M base targetM e
  let huniqL :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF targetL.toDVF :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L
  let huniqM :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF targetM.toDVF :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K M
  let huniqPulled :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF pulled.toDVF :=
    hasUniqueValuationExtension_of_finite_separable base pulled
  let φ : Gal(L/K) ≃* Gal(M/K) := AlgEquiv.autCongr e
  let r : pulled.valuationSubring ≃+* targetM.valuationSubring :=
    by
      change
        (targetM.valuation.comap e.toRingHom).valuationSubring ≃+*
          targetM.valuation.valuationSubring
      exact
        Valuation.valuationSubringRingEquivOfComap
          targetM.valuation e.toRingEquiv
  have hmapMaximalIdeal :
      Ideal.map
          (r : pulled.valuationSubring →+* targetM.valuationSubring)
          (IsLocalRing.maximalIdeal pulled.valuationSubring) =
        IsLocalRing.maximalIdeal targetM.valuationSubring := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      change r x ∈ IsLocalRing.maximalIdeal targetM.valuationSubring
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
      intro h
      have h' := h.map r.symm.toRingHom
      exact hx (by simpa using h')
    · intro y hy
      obtain ⟨x, rfl⟩ := r.surjective y
      apply Ideal.mem_map_of_mem
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
      intro h
      exact hy (h.map r.toRingHom)
  have hmapIdeal (s : ℝ) :
      Ideal.map (r : pulled.valuationSubring →+* targetM.valuationSubring)
          (realRamificationIdeal pulled.toDVF s) =
        realRamificationIdeal targetM.toDVF s := by
    unfold realRamificationIdeal
    rw [Ideal.map_pow, hmapMaximalIdeal]
  have hideal (s : ℝ) (x : pulled.valuationSubring) :
      x ∈ realRamificationIdeal pulled.toDVF s ↔
        r x ∈ realRamificationIdeal targetM.toDVF s := by
    constructor
    · intro hx
      have hrx :
          r x ∈ Ideal.map
            (r : pulled.valuationSubring →+* targetM.valuationSubring)
            (realRamificationIdeal pulled.toDVF s) :=
        Ideal.mem_map_of_mem
          (r : pulled.valuationSubring →+* targetM.valuationSubring) hx
      simpa only [hmapIdeal s] using hrx
    · intro hrx
      have hrx' :
          r x ∈ Ideal.map
            (r : pulled.valuationSubring →+* targetM.valuationSubring)
            (realRamificationIdeal pulled.toDVF s) := by
        simpa only [hmapIdeal s] using hrx
      exact Ideal.apply_mem_of_equiv_iff.mp hrx'
  have hdisplacement (σ : Gal(L/K)) (a : pulled.valuationSubring) :
      r (valuationSubringAutOfUniqueExtension
            (base := base.toDVF) (target := pulled.toDVF)
            huniqPulled σ a - a) =
        valuationSubringAutOfUniqueExtension
            (base := base.toDVF) (target := targetM.toDVF)
            huniqM (φ σ) (r a) - r a := by
    apply Subtype.ext
    change
      e (σ (a : L) - (a : L)) =
        (AlgEquiv.autCongr e σ) (e (a : L)) - e (a : L)
    simp [AlgEquiv.autCongr_apply]
  have hmem (s : ℝ) (σ : Gal(L/K)) :
      σ ∈ lowerRamificationGroup
            (base := base.toDVF) (target := pulled.toDVF)
            huniqPulled s ↔
        φ σ ∈ lowerRamificationGroup
            (base := base.toDVF) (target := targetM.toDVF)
            huniqM s := by
    constructor
    · intro hσ a
      let b : pulled.valuationSubring := r.symm a
      have hb := (hideal s
        (valuationSubringAutOfUniqueExtension
              (base := base.toDVF) (target := pulled.toDVF)
              huniqPulled σ b - b)).1 (hσ b)
      rw [hdisplacement σ b] at hb
      simpa [b] using hb
    · intro hσ a
      have ha := hσ (r a)
      rw [← hdisplacement σ a] at ha
      exact (hideal s _).2 ha
  have hlower (s : ℝ) :
      Subgroup.map φ.toMonoidHom
          (lowerRamificationGroup
            (base := base.toDVF) (target := pulled.toDVF)
            huniqPulled s) =
        lowerRamificationGroup
          (base := base.toDVF) (target := targetM.toDVF)
          huniqM s := by
    ext τ
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact (hmem s σ).1 hσ
    · intro hτ
      refine ⟨φ.symm τ, (hmem s (φ.symm τ)).2 ?_, by simp⟩
      simpa using hτ
  have hcard (n : ℕ) :
      Nat.card
          ((lowerRamificationFiltrationOfUniqueExtension
            (base := base.toDVF) (target := pulled.toDVF)
            huniqPulled).lower n) =
        Nat.card
          ((lowerRamificationFiltrationOfUniqueExtension
            (base := base.toDVF) (target := targetM.toDVF)
            huniqM).lower n) := by
    let H :=
      lowerRamificationGroup
        (base := base.toDVF) (target := pulled.toDVF)
        huniqPulled (n : ℝ)
    let q :=
      (φ.subgroupMap H).trans
        (MulEquiv.subgroupCongr (hlower (n : ℝ)))
    exact Nat.card_congr q.toEquiv
  have hherbrand (s : ℝ) :
      herbrandFunctionOfUniqueExtension
          (base := base.toDVF) (target := pulled.toDVF)
          huniqPulled s =
        herbrandFunctionOfUniqueExtension
          (base := base.toDVF) (target := targetM.toDVF)
          huniqM s := by
    exact
      RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_eq_of_card_lower_eq
        _ _ hcard s
  have hinverse (u : ℝ) :
      inverseHerbrandFunctionOfUniqueExtension
          (base := base.toDVF) (target := pulled.toDVF)
          huniqPulled u =
        inverseHerbrandFunctionOfUniqueExtension
          (base := base.toDVF) (target := targetM.toDVF)
          huniqM u := by
    apply
      (herbrandFunctionOfUniqueExtension_strictMono
        (base := base.toDVF) (target := targetM.toDVF)
        huniqM).injective
    rw [herbrandFunctionOfUniqueExtension_psi]
    rw [← hherbrand]
    rw [herbrandFunctionOfUniqueExtension_psi]
  have hpulled :
      Subgroup.map φ.toMonoidHom
          (upperRamificationGroupOfUniqueExtension
            (base := base.toDVF) (target := pulled.toDVF)
            huniqPulled t) =
        upperRamificationGroupOfUniqueExtension
          (base := base.toDVF) (target := targetM.toDVF)
          huniqM t := by
    change
      Subgroup.map φ.toMonoidHom
          (lowerRamificationGroup
            (base := base.toDVF) (target := pulled.toDVF)
            huniqPulled
            (inverseHerbrandFunctionOfUniqueExtension
              (base := base.toDVF) (target := pulled.toDVF)
              huniqPulled t)) =
        lowerRamificationGroup
          (base := base.toDVF) (target := targetM.toDVF)
          huniqM
          (inverseHerbrandFunctionOfUniqueExtension
            (base := base.toDVF) (target := targetM.toDVF)
            huniqM t)
    rw [hinverse]
    exact hlower _
  have hvaluationSubring :
      targetL.valuation.valuationSubring =
        pulled.valuation.valuationSubring := by
    exact
      (_root_.Valuation.isEquiv_iff_valuationSubring
        targetL.valuation pulled.valuation).1
        (huniqL pulled.valuation)
  have hchosen :
      upperRamificationGroupOfUniqueExtension
          (base := base.toDVF) (target := targetL.toDVF)
          huniqL t =
        upperRamificationGroupOfUniqueExtension
          (base := base.toDVF) (target := pulled.toDVF)
          huniqPulled t :=
    upperRamificationGroup_eq_of_valuationSubring_eq
      huniqL huniqPulled hvaluationSubring t
  change
    Subgroup.map φ.toMonoidHom
        (upperRamificationGroupOfUniqueExtension
          (base := base.toDVF) (target := targetL.toDVF)
          huniqL t) =
      upperRamificationGroupOfUniqueExtension
        (base := base.toDVF) (target := targetM.toDVF)
        huniqM t
  rw [hchosen]
  exact hpulled

private theorem fixedFieldUpperRamificationGroup_map_autCongr
    (K L M : Type)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : Subgroup Gal(L / K)) [H.Normal]
    (e : IntermediateField.fixedField H ≃ₐ[K] M)
    (t : ℝ) :
    Subgroup.map (AlgEquiv.autCongr e).toMonoidHom
        (fixedFieldUpperRamificationGroup
          (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension
            K L) H t) =
      localUpperRamificationGroup K M t := by
  let base := localCompleteDVF K
  let targetL := chosenLocalExtensionCompleteDVF K L
  let targetM := chosenLocalExtensionCompleteDVF K M
  let pulled := completeDVFComapAlgEquiv targetM e.toRingEquiv
  let hExtL : base.valuation.HasExtension targetL.valuation :=
    chosenLocalExtensionCompleteDVF_hasExtension K L
  let hExtM : base.valuation.HasExtension targetM.valuation :=
    chosenLocalExtensionCompleteDVF_hasExtension K M
  let hExtPulled : base.valuation.HasExtension pulled.valuation :=
    completeDVFComapAlgEquiv_hasExtension K
      (IntermediateField.fixedField H) M base targetM e
  let huniqL :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF targetL.toDVF :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L
  let huniqM :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF targetM.toDVF :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K M
  let huniqPulled :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF pulled.toDVF :=
    hasUniqueValuationExtension_of_finite_separable base pulled
  let B :=
    fixedFieldValuationSubringDVF
      (K := K) (target := targetL.toDVF) H
  let hExtB : base.valuation.HasExtension B.valuation :=
    base_hasExtension_fixedFieldValuationSubringDVF
      (base := base.toDVF) (target := targetL.toDVF) H
  have hpulledB :
      pulled.valuation.valuationSubring = B := by
    calc
      pulled.valuation.valuationSubring =
          B.valuation.valuationSubring :=
        (_root_.Valuation.isEquiv_iff_valuationSubring
          pulled.valuation B.valuation).1
            (huniqPulled B.valuation)
      _ = B := ValuationSubring.valuationSubring_valuation B
  let r : B ≃+* targetM.valuationSubring :=
    { toFun := fun a =>
        ⟨e (a : IntermediateField.fixedField H), by
          change (a : IntermediateField.fixedField H) ∈
            pulled.valuation.valuationSubring
          rw [hpulledB]
          exact a.property⟩
      invFun := fun a =>
        ⟨e.symm (a : M), by
          rw [← hpulledB]
          change
            targetM.valuation (e (e.symm (a : M))) ≤ 1
          rw [e.apply_symm_apply]
          exact
            (_root_.Valuation.mem_valuationSubring_iff
              targetM.valuation (a : M)).1 a.property⟩
      left_inv := by
        intro a
        apply Subtype.ext
        exact e.symm_apply_apply (a : IntermediateField.fixedField H)
      right_inv := by
        intro a
        apply Subtype.ext
        exact e.apply_symm_apply (a : M)
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact e.map_mul (a : IntermediateField.fixedField H)
          (b : IntermediateField.fixedField H)
      map_add' := by
        intro a b
        apply Subtype.ext
        exact e.map_add (a : IntermediateField.fixedField H)
          (b : IntermediateField.fixedField H) }
  have hmapMaximalIdeal :
      Ideal.map (r : B →+* targetM.valuationSubring)
          (IsLocalRing.maximalIdeal B) =
        IsLocalRing.maximalIdeal targetM.valuationSubring := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      change r x ∈ IsLocalRing.maximalIdeal targetM.valuationSubring
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
      intro h
      have h' := h.map r.symm.toRingHom
      exact hx (by simpa using h')
    · intro y hy
      obtain ⟨x, rfl⟩ := r.surjective y
      apply Ideal.mem_map_of_mem
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
      intro h
      exact hy (h.map r.toRingHom)
  have hmapIdeal (s : ℝ) :
      Ideal.map (r : B →+* targetM.valuationSubring)
          (fixedFieldRamificationIdealDVF
            (K := K) (target := targetL.toDVF) H s) =
        realRamificationIdeal targetM.toDVF s := by
    unfold fixedFieldRamificationIdealDVF realRamificationIdeal
    rw [Ideal.map_pow, hmapMaximalIdeal]
  have hideal (s : ℝ) (x : B) :
      x ∈ fixedFieldRamificationIdealDVF
            (K := K) (target := targetL.toDVF) H s ↔
        r x ∈ realRamificationIdeal targetM.toDVF s := by
    constructor
    · intro hx
      have hrx :
          r x ∈ Ideal.map (r : B →+* targetM.valuationSubring)
            (fixedFieldRamificationIdealDVF
              (K := K) (target := targetL.toDVF) H s) :=
        Ideal.mem_map_of_mem (r : B →+* targetM.valuationSubring) hx
      simpa only [hmapIdeal s] using hrx
    · intro hrx
      have hrx' :
          r x ∈ Ideal.map (r : B →+* targetM.valuationSubring)
            (fixedFieldRamificationIdealDVF
              (K := K) (target := targetL.toDVF) H s) := by
        simpa only [hmapIdeal s] using hrx
      exact Ideal.apply_mem_of_equiv_iff.mp hrx'
  let φ :
      Gal(IntermediateField.fixedField H / K) ≃*
        Gal(M / K) :=
    AlgEquiv.autCongr e
  have hdisplacement
      (σ : Gal(IntermediateField.fixedField H / K))
      (a : B) :
      r (fixedFieldValuationSubringAutDVF
            (base := base.toDVF) (target := targetL.toDVF)
            huniqL H σ a - a) =
        valuationSubringAutOfUniqueExtension
            (base := base.toDVF) (target := targetM.toDVF)
            huniqM (φ σ) (r a) - r a := by
    apply Subtype.ext
    change
      e (σ (a : IntermediateField.fixedField H) -
          (a : IntermediateField.fixedField H)) =
        (AlgEquiv.autCongr e σ) (e (a : IntermediateField.fixedField H)) -
          e (a : IntermediateField.fixedField H)
    simp [AlgEquiv.autCongr_apply]
  have hmem (s : ℝ)
      (σ : Gal(IntermediateField.fixedField H / K)) :
      σ ∈ fixedFieldLowerRamificationGroup
            (base := base.toDVF) (target := targetL.toDVF)
            huniqL H s ↔
        φ σ ∈ lowerRamificationGroup
            (base := base.toDVF) (target := targetM.toDVF)
            huniqM s := by
    constructor
    · intro hσ a
      let b : B := r.symm a
      have hb :=
        (hideal s
          (fixedFieldValuationSubringAutDVF
              (base := base.toDVF) (target := targetL.toDVF)
              huniqL H σ b - b)).1 (hσ b)
      rw [hdisplacement σ b] at hb
      simpa [b] using hb
    · intro hσ a
      have ha := hσ (r a)
      rw [← hdisplacement σ a] at ha
      exact (hideal s _).2 ha
  have hlower (s : ℝ) :
      Subgroup.map φ.toMonoidHom
          (fixedFieldLowerRamificationGroup
            (base := base.toDVF) (target := targetL.toDVF)
            huniqL H s) =
        lowerRamificationGroup
          (base := base.toDVF) (target := targetM.toDVF)
          huniqM s := by
    ext τ
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact (hmem s σ).1 hσ
    · intro hτ
      refine ⟨φ.symm τ, (hmem s (φ.symm τ)).2 ?_, by simp⟩
      simpa using hτ
  have hcard (n : ℕ) :
      Nat.card
          ((fixedFieldLowerRamificationFiltration
            (base := base.toDVF) (target := targetL.toDVF)
            huniqL H).lower n) =
        Nat.card
          ((lowerRamificationFiltrationOfUniqueExtension
            (base := base.toDVF) (target := targetM.toDVF)
            huniqM).lower n) := by
    let A :=
      fixedFieldLowerRamificationGroup
        (base := base.toDVF) (target := targetL.toDVF)
        huniqL H (n : ℝ)
    let q :=
      (φ.subgroupMap A).trans
        (MulEquiv.subgroupCongr (hlower (n : ℝ)))
    exact Nat.card_congr q.toEquiv
  have hherbrand (s : ℝ) :
      fixedFieldHerbrandFunction
          (base := base.toDVF) (target := targetL.toDVF)
          huniqL H s =
        herbrandFunctionOfUniqueExtension
          (base := base.toDVF) (target := targetM.toDVF)
          huniqM s := by
    exact
      RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_eq_of_card_lower_eq
        _ _ hcard s
  have hinverse (u : ℝ) :
      fixedFieldInverseHerbrandFunction
          (base := base.toDVF) (target := targetL.toDVF)
          huniqL H u =
        inverseHerbrandFunctionOfUniqueExtension
          (base := base.toDVF) (target := targetM.toDVF)
          huniqM u := by
    apply
      (herbrandFunctionOfUniqueExtension_strictMono
        (base := base.toDVF) (target := targetM.toDVF)
        huniqM).injective
    rw [herbrandFunctionOfUniqueExtension_psi]
    rw [← hherbrand]
    rw [fixedFieldHerbrandFunction_inverseHerbrandFunction]
  change
    Subgroup.map φ.toMonoidHom
        (fixedFieldLowerRamificationGroup
          (base := base.toDVF) (target := targetL.toDVF)
          huniqL H
          (fixedFieldInverseHerbrandFunction
            (base := base.toDVF) (target := targetL.toDVF)
            huniqL H t)) =
      lowerRamificationGroup
        (base := base.toDVF) (target := targetM.toDVF)
        huniqM
        (inverseHerbrandFunctionOfUniqueExtension
          (base := base.toDVF) (target := targetM.toDVF)
          huniqM t)
  rw [hinverse]
  exact hlower _

private theorem fixedFieldUpperRamificationGroup_eq_local
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : Subgroup Gal(L / K)) [H.Normal]
    (t : ℝ) :
    fixedFieldUpperRamificationGroup
        (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension
          K L) H t =
      localUpperRamificationGroup K (IntermediateField.fixedField H) t := by
  simpa using
    fixedFieldUpperRamificationGroup_map_autCongr
      K L (IntermediateField.fixedField H) H
      (AlgEquiv.refl : IntermediateField.fixedField H ≃ₐ[K]
        IntermediateField.fixedField H) t

/-- Upper ramification groups descend along restriction between finite
Galois intermediate fields in a common separable closure. -/
theorem localUpperRamificationGroup_map_restrict
    (K : Type) [Field K]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsGalois K E] [IsGalois K F]
    (t : ℝ) :
    Subgroup.map
        (intermediateFieldRestrictNormalHom E F hEF)
        (localUpperRamificationGroup K F t) =
      localUpperRamificationGroup K E t := by
  let EF : IntermediateField K F := E.comap F.val
  let eEF : EF ≃ₐ[K] E :=
    { toFun := fun x => ⟨F.val x, x.property⟩
      invFun := fun x =>
        ⟨IntermediateField.inclusion hEF x, by
          change F.val (IntermediateField.inclusion hEF x) ∈ E
          exact x.property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply F.val.injective
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        rfl
      map_mul' := by
        intro x y
        apply Subtype.ext
        rfl
      map_add' := by
        intro x y
        apply Subtype.ext
        rfl
      commutes' := by
        intro x
        apply Subtype.ext
        rfl }
  let : IsGalois K EF := IsGalois.of_algEquiv eEF.symm
  let H : Subgroup Gal(F / K) := EF.fixingSubgroup
  let : H.Normal := by
    dsimp only [H]
    infer_instance
  let eFixed : IntermediateField.fixedField H ≃ₐ[K] E :=
    (IntermediateField.equivOfEq
      (IsGalois.fixedField_fixingSubgroup EF)).trans eEF
  let qEquiv :
      (Gal(F / K) ⧸ H) ≃* Gal(E / K) :=
    (IsGalois.normalAutEquivQuotient H).trans
      (AlgEquiv.autCongr eFixed)
  let base := (localCompleteDVF K).toDVF
  let target := (chosenLocalExtensionCompleteDVF K F).toDVF
  let huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base target :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K F
  let : Finite (localCompleteDVF K).residueField := by
    change Finite 𝓀[K]
    infer_instance
  let : Module.Finite
      base.valuationSubring target.valuationSubring :=
    chosenLocalExtensionCompleteDVF_valuationSubring_moduleFinite K F
  let : FiniteDimensional base.residueField target.residueField :=
    residueField_finiteDimensional_of_moduleFinite_dvf
      (base := base) (target := target)
  have hquot :=
    upperRamificationGroup_quotient
      (base := base) (target := target) huniq H t
  have hrestrict :
      intermediateFieldRestrictNormalHom E F hEF =
        qEquiv.toMonoidHom.comp (QuotientGroup.mk' H) := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply E.val.injective
    change
      E.val (intermediateFieldRestrictNormalHom E F hEF σ x) =
        E.val ((qEquiv.toMonoidHom.comp (QuotientGroup.mk' H)) σ x)
    rw [intermediateFieldRestrictNormalHom_apply_val]
    simp [qEquiv, eFixed, eEF, EF, H, AlgEquiv.autCongr_apply,
      IsGalois.normalAutEquivQuotient_apply]
    symm
    exact
      AlgEquiv.restrictNormal_commutes σ
        (IntermediateField.fixedField H) (eFixed.symm x)
  have hmapComap :
      Subgroup.map
          (IsGalois.normalAutEquivQuotient H).toMonoidHom
          (Subgroup.comap
            (IsGalois.normalAutEquivQuotient H).toMonoidHom
            (fixedFieldUpperRamificationGroup
              (base := base) (target := target) huniq H t)) =
        fixedFieldUpperRamificationGroup
          (base := base) (target := target) huniq H t := by
    exact
      Subgroup.map_comap_eq_self_of_surjective
        (IsGalois.normalAutEquivQuotient H).surjective _
  rw [hrestrict]
  change
    Subgroup.map
        (qEquiv.toMonoidHom.comp (QuotientGroup.mk' H))
        (upperRamificationGroupOfUniqueExtension
          (base := base) (target := target) huniq t) =
      localUpperRamificationGroup K E t
  rw [← Subgroup.map_map, hquot]
  change
    Subgroup.map
        ((AlgEquiv.autCongr eFixed).toMonoidHom.comp
          (IsGalois.normalAutEquivQuotient H).toMonoidHom)
        (Subgroup.comap
          (IsGalois.normalAutEquivQuotient H).toMonoidHom
          (fixedFieldUpperRamificationGroup
            (base := base) (target := target) huniq H t)) =
      localUpperRamificationGroup K E t
  rw [← Subgroup.map_map]
  rw [hmapComap]
  rw [fixedFieldUpperRamificationGroup_eq_local K F H t]
  exact
    localUpperRamificationGroup_map_autCongr
      K (IntermediateField.fixedField H) E eFixed t





























end RamificationTheory.LocalField

end
