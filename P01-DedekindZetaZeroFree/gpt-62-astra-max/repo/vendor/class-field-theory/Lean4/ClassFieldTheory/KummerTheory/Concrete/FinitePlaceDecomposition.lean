module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.FinitePlaces
public import GaloisCohomology.Kummer.Concrete.RootCharacters
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Kummer radicals and finite-place decomposition fields

For a finite Galois extension containing an `n`-th root `β` of a
base-field unit `a`, this file identifies the local `n`-th-power
condition on `a` with membership of `β` in the decomposition field.

The proof uses the canonical comparison between the two models of the
finite-place completion and the algebraic localization realization of
the decomposition field.  The only Kummer input is the usual fact that
two roots with the same `n`-th power differ by an `n`-th root of unity.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory

noncomputable section

namespace KummerTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField K] [FiniteDimensional K L] in
/-- If a Kummer radicand is an `n`-th power in an absolute-value
completion, its chosen root lies in the corresponding decomposition
field.  This is the completion-level source behind both the finite and
archimedean localization arguments. -/
theorem
    kummerRadicand_root_mem_decompositionFixedField_of_mem_nthPowerSubgroup
    (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : Kˣ) (beta : Lˣ)
    (hbeta :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K L).toMonoidHom a)
    (ha :
      Units.map
            (algebraMap K vK.Completion).toMonoidHom a ∈
        (powMonoidHom (n : ℕ) :
          vK.Completionˣ →* vK.Completionˣ).range) :
    (beta : L) ∈
      IntermediateField.fixedField
        (absoluteValueDecompositionGroup K w.1) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let C := vK.Completion
  let E := LocalizedCompletion vK w
  let toE :=
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let aC :=
    Units.map (algebraMap K C).toMonoidHom a
  have hbeta_val :
      (beta : L) ^ (n : ℕ) =
        algebraMap K L (a : K) := by
    exact congrArg Units.val hbeta
  obtain ⟨yC, hyC⟩ :=
    (MonoidHom.mem_range
      ).mp ha
  rw [powMonoidHom_apply] at hyC
  let betaE :=
    Units.map toE.toMonoidHom beta
  let map₀ := Units.map (algebraMap C E).toMonoidHom
  let yE :=
    map₀ yC
  let toE₀ := toE (beta : L)
  have hbetaE :
      betaE ^ (n : ℕ) =
        map₀ aC := by
    apply Units.ext
    change
      toE₀ ^ (n : ℕ) =
        algebraMap C E (algebraMap K C (a : K))
    calc
      toE₀ ^ (n : ℕ) =
          toE ((beta : L) ^ (n : ℕ)) := by
        exact
          (map_pow toE (beta : L) (n : ℕ)).symm
      _ = toE (algebraMap K L (a : K)) := by
        rw [hbeta_val]
      _ = algebraMap C E (algebraMap K C (a : K)) :=
        AbsoluteValue.toAlgebraicLocalization_algebraMap
          vK w.1 w.2 (a : K)
  have hyE :
      yE ^ (n : ℕ) =
        map₀ aC := by
    calc
      _ =
          map₀
            (yC ^ (n : ℕ)) := (map_pow
            (map₀)
            yC (n : ℕ)).symm
      _ = map₀ aC := by
        rw [hyC]
  let q := betaE / yE
  obtain ⟨zeta, hzeta_mem⟩ := hmu
  obtain ⟨i, _hi, hzetaq⟩ :=
    ((((mem_primitiveRoots n.pos).mp hzeta_mem).map_of_injective
        (algebraMap K C).injective).map_of_injective
      (algebraMap C E).injective).eq_pow_of_pow_eq_one (by
      exact congrArg Units.val (KummerTheory.div_pow_eq_one_of_pow_eq_pow
        (hbetaE.trans hyE.symm)))
  have hbeta_base :
      toE₀ ∈
        Set.range (algebraMap C E) := by
    refine
      ⟨(algebraMap K C zeta) ^ i * (yC : C), ?_⟩
    calc
      algebraMap C E
            ((algebraMap K C zeta) ^ i * (yC : C)) =
          (algebraMap C E (algebraMap K C zeta)) ^ i *
            algebraMap C E (yC : C) := by
        rw [map_mul, map_pow]
      _ = (q : E) * (yE : E) := by
        rw [hzetaq]
        rfl
      _ = toE₀ := by
        simpa [betaE] using
          congrArg Units.val
            (show q * yE = betaE by simp [q])
  have hcomap :
      (beta : L) ∈
        ((algebraMap C E).fieldRange).comap toE :=
    hbeta_base
  rw [
    localizedCompletion_baseField_comap_eq_fixedField_decompositionGroup
      vK hvK w] at hcomap
  simpa [C, E, toE] using hcomap

omit [FiniteDimensional K L] in
/-- A Kummer radicand is an `n`-th power in the finite-place completion
exactly when its chosen root belongs to the decomposition field at the
chosen extension of that place. -/
theorem
    finitePlaceKummerRadicand_mem_nthPowerSubgroup_iff_root_mem_decompositionFixedField
    (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : Kˣ) (beta : Lˣ)
    (hbeta :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K L).toMonoidHom a) :
    Units.map
          (algebraMap K (v.adicCompletion K)).toMonoidHom a ∈
        (powMonoidHom (n : ℕ) :
          (v.adicCompletion K)ˣ →*
            (v.adicCompletion K)ˣ).range ↔
      (beta : L) ∈
        IntermediateField.fixedField
          (absoluteValueDecompositionGroup K
            (chosenFinitePlaceExtension (L := L) v).1) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let C := vK.Completion
  let E := LocalizedCompletion vK w
  let toE :=
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let e :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  let aC :=
    Units.map (algebraMap K C).toMonoidHom a
  let map₀ := Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom
  have he_base (u : Kˣ) :
      e (Units.map (algebraMap K C).toMonoidHom u) =
        map₀ u := by
    apply Units.ext
    change
      finitePlaceCompletionRingHom v (((WithAbs.equiv vK).symm (u : K)) : C) =
        algebraMap K (v.adicCompletion K) (u : K)
    rw [finitePlaceCompletionRingHom_coe]
    rfl
  have hbeta_val :
      (beta : L) ^ (n : ℕ) =
        algebraMap K L (a : K) := by
    exact congrArg Units.val hbeta
  constructor
  · intro ha
    apply
      kummerRadicand_root_mem_decompositionFixedField_of_mem_nthPowerSubgroup
          vK hvK w n hmu a beta hbeta
    obtain ⟨y, hy⟩ :=
      (MonoidHom.mem_range
        ).mp ha
    rw [powMonoidHom_apply] at hy
    apply
      (MonoidHom.mem_range
        ).mpr
    refine ⟨e.symm y, ?_⟩
    rw [powMonoidHom_apply]
    apply e.injective
    calc
      _ =
          (e (e.symm y)) ^ (n : ℕ) :=
        map_pow e (e.symm y) (n : ℕ)
      _ = y ^ (n : ℕ) := by
        rw [e.apply_symm_apply]
      _ =
          map₀ a := hy
      _ = e aC := (he_base a).symm
  · intro hfixed
    have hcomap :
        (beta : L) ∈
          ((algebraMap C E).fieldRange).comap toE := by
      rw [
        localizedCompletion_baseField_comap_eq_fixedField_decompositionGroup
          vK hvK w]
      simpa [vK, w] using hfixed
    change
      toE (beta : L) ∈ Set.range (algebraMap C E)
      at hcomap
    obtain ⟨y, hy⟩ := hcomap
    have hy_ne : y ≠ 0 := by
      intro hy_zero
      apply beta.ne_zero
      apply toE.injective
      calc
        _ =
            algebraMap C E y := hy.symm
        _ = 0 := by rw [hy_zero, map_zero]
        _ = toE 0 := (map_zero toE).symm
    let yC := Units.mk0 y hy_ne
    have hyC : yC ^ (n : ℕ) = aC := by
      apply Units.ext
      apply (algebraMap C E).injective
      change
        algebraMap C E (y ^ (n : ℕ)) =
          algebraMap C E (algebraMap K C (a : K))
      calc
        algebraMap C E (y ^ (n : ℕ)) =
            (algebraMap C E y) ^ (n : ℕ) := by
          exact
            map_pow (algebraMap C E) y (n : ℕ)
        _ = toE (beta : L) ^ (n : ℕ) := by
          rw [hy]
        _ = toE ((beta : L) ^ (n : ℕ)) := by
          exact
            (map_pow toE (beta : L) (n : ℕ)).symm
        _ = toE (algebraMap K L (a : K)) := by
          rw [hbeta_val]
        _ = algebraMap C E (algebraMap K C (a : K)) :=
          AbsoluteValue.toAlgebraicLocalization_algebraMap
            vK w.1 w.2 (a : K)
    apply
      (MonoidHom.mem_range
        ).mpr
    refine ⟨e yC, ?_⟩
    rw [powMonoidHom_apply]
    calc
      _ =
          e (yC ^ (n : ℕ)) := (map_pow e yC (n : ℕ)).symm
      _ = e aC := by rw [hyC]
      _ =
          map₀ a :=
        he_base a

end KummerTheory

end
