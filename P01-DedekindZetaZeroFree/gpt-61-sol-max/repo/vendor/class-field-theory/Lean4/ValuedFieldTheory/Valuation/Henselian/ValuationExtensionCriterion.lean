module

public import Mathlib

public import ValuedFieldTheory.Valuation.Henselian.NonmonicReduction

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# the factor-lifting criterion

Artin's monic coprime-factor lifting criterion implies the exact primitive
factorization form of Hensel's lemma from the primitive factorization definition.
-/

noncomputable section

open Polynomial

namespace DiscreteValuationField
open ValuationTheory.DiscreteValuationField

universe u

/-- The unit-leading-coefficient branch of the factor-lifting criterion.  Normalize the
ground-field irreducible polynomial to be monic, then normalize both residual
factors without changing their product or coprimality. -/
theorem MonicResidualCoprimeFactorLifting.leadingCoeff_unit_branch
    {K : Type u} [Field K] {V : ValuationSubring K}
    (hlift : MonicResidualCoprimeFactorLifting V)
    {Q : Polynomial V} (hQprim : Q.IsPrimitive)
    (hQirr : Irreducible (Q.map V.subtype))
    (hlead : IsUnit Q.leadingCoeff) :
    let qbar := Q.map (IsLocalRing.residue V)
    qbar.natDegree = Q.natDegree ∧
      ∀ a b : Polynomial (IsLocalRing.ResidueField V),
        qbar = a * b → IsCoprime a b →
          a.natDegree = 0 ∨ b.natDegree = 0 := by
  let qbar : Polynomial (IsLocalRing.ResidueField V) :=
    Q.map (IsLocalRing.residue V)
  have hdegree : qbar.natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff
      (IsLocalRing.residue V) hlead
  refine ⟨hdegree, ?_⟩
  intro a b hfactor hcoprime
  let u  := hlead.unit
  let F : Polynomial V := Polynomial.C ((u⁻¹ : Vˣ) : V) * Q
  have hu : (u : V) = Q.leadingCoeff := hlead.unit_spec
  have hFmonic : F.Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    change (((u⁻¹ : Vˣ) : V) * Q.leadingCoeff) = 1
    rw [← hu]
    simp
  have hscalarUnitK : IsUnit (((u⁻¹ : Vˣ) : V) : K) := by
    apply isUnit_iff_ne_zero.mpr <;> aesop
  have hCunitK  :=
    Polynomial.isUnit_C.mpr hscalarUnitK
  have hFmap :
      F.map V.subtype =
        Polynomial.C (((u⁻¹ : Vˣ) : V) : K) * Q.map V.subtype := by
    dsimp [F]
    rw [Polynomial.map_mul, Polynomial.map_C]
    rfl
  have hFirr : Irreducible (F.map V.subtype) := by
    have hassoc : Associated (F.map V.subtype) (Q.map V.subtype) := by
      rw [hFmap]
      exact associated_unit_mul_left _ _ hCunitK
    exact hassoc.symm.irreducible hQirr
  let c  :=
    IsLocalRing.residue V (((u⁻¹ : Vˣ) : V))
  have hcunit : IsUnit c :=
    (IsLocalRing.residue V).isUnit_map (Units.isUnit (u⁻¹))
  have hCunit : IsUnit (Polynomial.C c) :=
    Polynomial.isUnit_C.mpr hcunit
  let a' : Polynomial (IsLocalRing.ResidueField V) := Polynomial.C c * a
  have hfactor' : F.map (IsLocalRing.residue V) = a' * b := by
    dsimp [F, a', c]
    rw [Polynomial.map_mul, Polynomial.map_C, hfactor]
    ring
  have hcoprime' : IsCoprime a' b :=
    (isCoprime_mul_unit_left_left hCunit a b).2 hcoprime
  have hqbar0 : qbar ≠ 0 :=
    residue_ne_zero_of_isPrimitive_valuationSubring V hQprim
  have hab0 : a ≠ 0 ∧ b ≠ 0 := by
    have hab : a * b ≠ 0 := by
      rw [← hfactor]
      exact hqbar0
    exact ⟨left_ne_zero_of_mul hab, right_ne_zero_of_mul hab⟩
  have ha'0 : a' ≠ 0 := by
    dsimp [a']
    exact mul_ne_zero hCunit.ne_zero hab0.1
  have ha'lead0  :=
    Polynomial.leadingCoeff_ne_zero.mpr ha'0
  have hleadProduct : a'.leadingCoeff * b.leadingCoeff = 1 := by
    have hproductMonic : (a' * b).Monic := by
      rw [← hfactor']
      apply hFmonic.map
    simpa only [Polynomial.Monic, Polynomial.leadingCoeff_mul] using hproductMonic
  let A  :=
    Polynomial.C a'.leadingCoeff⁻¹ * a'
  let B  :=
    Polynomial.C a'.leadingCoeff * b
  have hAmonic : A.Monic := by
    dsimp [A]
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    exact inv_mul_cancel₀ ha'lead0
  have hBmonic : B.Monic := by
    dsimp [B]
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    exact hleadProduct
  have hfactorAB : F.map (IsLocalRing.residue V) = A * B := by
    rw [hfactor']
    dsimp [A, B]
    rw [show
      (Polynomial.C a'.leadingCoeff⁻¹ * a') *
          (Polynomial.C a'.leadingCoeff * b) =
        (Polynomial.C a'.leadingCoeff⁻¹ *
          Polynomial.C a'.leadingCoeff) * (a' * b) by ring]
    rw [← Polynomial.C_mul, inv_mul_cancel₀ ha'lead0]
    simp
  have hCinvUnit : IsUnit (Polynomial.C a'.leadingCoeff⁻¹) :=
    Polynomial.isUnit_C.mpr
      (isUnit_iff_ne_zero.mpr (inv_ne_zero ha'lead0))
  have hCleadUnit  :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha'lead0)
  have hcoprimeAB : IsCoprime A B := by
    dsimp [A, B]
    exact
      (isCoprime_mul_units_left hCinvUnit hCleadUnit a' b).2 hcoprime'
  have hdegrees  :=
    hlift.irreducible_monic_reduction_coprime_factor_degree_zero
      hFmonic hFirr hAmonic hBmonic hfactorAB hcoprimeAB
  have hAdegree : A.natDegree = a'.natDegree := by
    dsimp [A]
    rw [Polynomial.natDegree_mul hCinvUnit.ne_zero ha'0,
      Polynomial.natDegree_C, Nat.zero_add]
  have hBdegree : B.natDegree = b.natDegree := by
    dsimp [B]
    rw [Polynomial.natDegree_mul hCleadUnit.ne_zero hab0.2,
      Polynomial.natDegree_C, Nat.zero_add]
  have ha'degree : a'.natDegree = a.natDegree := by
    dsimp [a']
    rw [Polynomial.natDegree_mul hCunit.ne_zero hab0.1,
      Polynomial.natDegree_C, Nat.zero_add]
  exact hdegrees.elim
    (fun hA ↦ Or.inl (ha'degree.symm.trans (hAdegree.symm.trans hA)))
    (fun hB ↦ Or.inr (hBdegree.symm.trans hB))


































































end DiscreteValuationField

end
