module
public import ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization

public import ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Recursive monomial corrections for Lubin--Tate intertwiners

The coefficient selected in `RecursiveCoefficient` is inserted as a single
monomial.  This file proves that the insertion preserves the prescribed linear
term and cancels the defect coefficient in precisely that total degree.
-/

noncomputable section

open scoped BigOperators

universe u v w

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- The single monomial inserted at one step of the recursive construction. -/
noncomputable def monomialCorrection
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    MvPowerSeries σ F.valuationSubring :=
  MvPowerSeries.monomial d
    (correctionCoefficient hπ e ebar hH d hd)

/-- Insert the recursive correction into the current approximation. -/
noncomputable def correctedIntertwiner
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    MvPowerSeries σ F.valuationSubring :=
  H + monomialCorrection hπ e ebar hH d hd

private theorem degree_le_order_monomial
    {R : Type*} [CommRing R] {τ : Type*}
    (d : τ →₀ ℕ) (c : R) :
    (d.degree : ℕ∞) ≤ (MvPowerSeries.monomial d c).order := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  · rw [MvPowerSeries.order_monomial_of_ne_zero hc]

private alias natCast_le_order_pow_of_one_le_order := DegreeStabilization.natCast_le_order_pow_of_one_le_order_stabilization

private alias le_order_finset_sum := DegreeStabilization.le_order_finset_sum_stabilization

private alias natCast_sum_le_order_finset_prod_pow := DegreeStabilization.natCast_sum_le_order_finset_prod_pow_stabilization

private alias order_sub_add_pred_le_order_pow_sub_pow := DegreeStabilization.order_sub_add_pred_le_order_pow_sub_pow_stabilization

private alias natCast_sum_add_one_le_order_prod_pow_sub_prod_pow := DegreeStabilization.natCast_sum_add_one_le_order_prod_pow_sub_prod_pow_stabilization

/-- The linear part of `e(X_i)` for a same-uniformizer Lubin--Tate series. -/
 noncomputable def linearInVariable
    (π : F.valuationSubring) (i : σ) :
    MvPowerSeries σ F.valuationSubring :=
  MvPowerSeries.C π * MvPowerSeries.X i

omit [Fintype σ] in
private theorem linearInVariable_constantCoeff
    (π : F.valuationSubring) (i : σ) :
    MvPowerSeries.constantCoeff (linearInVariable π i) = 0 := by
  simp [linearInVariable]

omit [Fintype σ] in
private theorem two_le_order_inVariable_sub_linearInVariable
    (ebar : LubinTateSeries F π) (i : σ) :
    (2 : ℕ∞) ≤ (inVariable ebar i - linearInVariable π i).order := by
  classical
  apply MvPowerSeries.nat_le_order
  intro d hd
  have hdNat : d.degree < 2 := by
    exact_mod_cast hd
  rw [map_sub]
  by_cases hdi : d = Finsupp.single i (d i)
  · by_cases hzero : d i = 0
    · have hd0 : d = 0 := by
        rw [hdi, hzero]
        simp
      subst d
      simp [inVariable, linearInVariable,
        PowerSeries.coeff_subst_single,
        LubinTateSeries.constantCoeff_eq_zero]
    · have hone : d i = 1 := by
        rw [hdi, Finsupp.degree_single] at hdNat
        omega
      have hd1 : d = Finsupp.single i 1 := by
        rw [hdi, hone]
      subst d
      simp [inVariable, linearInVariable,
        PowerSeries.coeff_subst_single,
        LubinTateSeries.coeff_one_eq_uniformizer]
  · have hsingle : d ≠ Finsupp.single i 1 := by
      intro h
      apply hdi
      rw [h]
      simp
    simp [inVariable, linearInVariable,
      PowerSeries.coeff_subst_single, hdi,
      MvPowerSeries.coeff_X, hsingle]

private theorem degree_add_one_le_order_subst_monomial_sub_linear
    (ebar : LubinTateSeries F π)
    (d : σ →₀ ℕ) (c : F.valuationSubring) :
    ((d.degree + 1 : ℕ) : ℕ∞) ≤
      (MvPowerSeries.subst (fun i : σ => inVariable ebar i)
          (MvPowerSeries.monomial d c) -
        MvPowerSeries.subst (linearInVariable (σ := σ) π)
          (MvPowerSeries.monomial d c)).order := by
  have hprod :
      ((d.degree + 1 : ℕ) : ℕ∞) ≤
        (d.prod (fun i n => (inVariable ebar i) ^ n) -
          d.prod (fun i n => (linearInVariable π i) ^ n)).order := by
    simpa only [Finsupp.prod, Finsupp.degree_apply] using
      natCast_sum_add_one_le_order_prod_pow_sub_prod_pow
        (s := d.support)
        (fun i : σ => inVariable ebar i)
        (linearInVariable (σ := σ) π)
        (fun i => d i)
        (fun i hi => Finsupp.mem_support_iff.mp hi)
        (fun i _ => (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
    (constantCoeff_inVariable ebar i)))
        (fun i _ => (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
    (linearInVariable_constantCoeff π i)))
        (fun i _ =>
          two_le_order_inVariable_sub_linearInVariable ebar i)
  rw [
    MvPowerSeries.subst_monomial
      (inVariable_hasSubst ebar) d c,
    MvPowerSeries.subst_monomial
      ((MvPowerSeries.hasSubst_of_constantCoeff_zero
    (linearInVariable_constantCoeff π))) d c,
    ← MvPowerSeries.c_eq_algebraMap]
  rw [show
    MvPowerSeries.C c *
          d.prod (fun i n => (inVariable ebar i) ^ n) -
        MvPowerSeries.C c *
          d.prod (fun i n => (linearInVariable π i) ^ n) =
      c •
        (d.prod (fun i n => (inVariable ebar i) ^ n) -
          d.prod (fun i n => (linearInVariable π i) ^ n)) by
    rw [MvPowerSeries.smul_eq_C_mul]
    ring]
  exact hprod.trans MvPowerSeries.le_order_smul

omit [Fintype σ] in
private theorem coeff_subst_linearInVariable_monomial
    (d : σ →₀ ℕ) (c : F.valuationSubring) :
    MvPowerSeries.coeff d
        (MvPowerSeries.subst (linearInVariable (σ := σ) π)
          (MvPowerSeries.monomial d c)) =
      π ^ d.degree * c := by
  have hlinear :
      (Function.const σ π •
          (MvPowerSeries.X :
            σ → MvPowerSeries σ F.valuationSubring)) =
        linearInVariable (σ := σ) π := by
    funext i
    simp [linearInVariable, MvPowerSeries.smul_eq_C_mul]
  rw [← hlinear, ← MvPowerSeries.rescale_eq_subst,
    MvPowerSeries.coeff_rescale,
    MvPowerSeries.coeff_monomial_same]
  simp only [Finsupp.prod, Function.const_apply,
    Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

private theorem coeff_subst_inVariables_monomial
    (ebar : LubinTateSeries F π)
    (d : σ →₀ ℕ) (c : F.valuationSubring) :
    MvPowerSeries.coeff d
        (MvPowerSeries.subst (fun i : σ => inVariable ebar i)
          (MvPowerSeries.monomial d c)) =
      π ^ d.degree * c := by
  have hlt :
      d.degree <
        (MvPowerSeries.subst (fun i : σ => inVariable ebar i)
            (MvPowerSeries.monomial d c) -
          MvPowerSeries.subst (linearInVariable π)
            (MvPowerSeries.monomial d c)).order :=
    by
      have hdegree_lt :
          d.degree < ((d.degree + 1 : ℕ) : ℕ∞) := by
        exact_mod_cast Nat.lt_succ_self d.degree
      exact hdegree_lt.trans_le (degree_add_one_le_order_subst_monomial_sub_linear ebar d c)
  have hcoeff :=
    MvPowerSeries.coeff_of_lt_order hlt
  rw [map_sub, sub_eq_zero] at hcoeff
  rw [hcoeff, coeff_subst_linearInVariable_monomial]

private theorem coeff_subst_inVariables_add_monomial
    (ebar : LubinTateSeries F π)
    (H : MvPowerSeries σ F.valuationSubring)
    (d : σ →₀ ℕ) (c : F.valuationSubring) :
    MvPowerSeries.coeff d
        (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i)
          (H + MvPowerSeries.monomial d c)) =
      MvPowerSeries.coeff d
          (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H) +
        π ^ d.degree * c := by
  rw [
    MvPowerSeries.subst_add (inVariable_hasSubst ebar),
    map_add,
    coeff_subst_inVariables_monomial]

private alias constantCoeff_monomial_eq_zero := DegreeStabilization.constantCoeff_monomial_eq_zero_stabilization

private theorem coeff_pow_add_monomial_sub_pow
    {R : Type*} [CommRing R] {τ : Type*}
    {H : MvPowerSeries τ R}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (d : τ →₀ ℕ) (hd : 2 ≤ d.degree) (c : R) (n : ℕ) :
    MvPowerSeries.coeff d
        ((H + MvPowerSeries.monomial d c) ^ n - H ^ n) =
      if n = 1 then c else 0 := by
  classical
  have hd0 : d ≠ 0 := by
    intro h
    subst d
    simp at hd
  by_cases hn : n = 1
  · simp_all [MvPowerSeries.coeff_monomial_same]
  · rcases n with _ | n
    · simp
    · have hn0 : n ≠ 0 := by
        intro h
        apply hn
        omega
      let M := MvPowerSeries.monomial d c
      let A := H + M
      have hMconstant :
          MvPowerSeries.constantCoeff M = 0 :=
        constantCoeff_monomial_eq_zero hd0 c
      have hAconstant :
          MvPowerSeries.constantCoeff A = 0 := by
        simp [A, hH, hMconstant]
      have hAorder : (1 : ℕ∞) ≤ A.order :=
        MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hAconstant
      have hpow :
          M.order + (n : ℕ∞) ≤
            (A ^ (n + 1) - H ^ (n + 1)).order := by
        simpa [A, M, add_sub_cancel_left] using
          order_sub_add_pred_le_order_pow_sub_pow
            A H hAorder (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hH) (n + 1)
      have horder :
          ((d.degree + 1 : ℕ) : ℕ∞) ≤
            (A ^ (n + 1) - H ^ (n + 1)).order := by
        calc
          _ =
              (d.degree : ℕ∞) + 1 := by norm_cast
          _ ≤ M.order + (n : ℕ∞) :=
            add_le_add (degree_le_order_monomial d c) (by
              exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0)
          _ ≤ (A ^ (n + 1) - H ^ (n + 1)).order :=
            hpow
      have hlt :
          d.degree <
            (A ^ (n + 1) - H ^ (n + 1)).order :=
        by
          have hdegree_lt :
              d.degree < ((d.degree + 1 : ℕ) : ℕ∞) := by
            exact_mod_cast Nat.lt_succ_self d.degree
          exact hdegree_lt.trans_le horder
      grind [MvPowerSeries.coeff_of_lt_order]

private theorem coeff_pow_add_monomial
    {R : Type*} [CommRing R] {τ : Type*}
    {H : MvPowerSeries τ R}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (d : τ →₀ ℕ) (hd : 2 ≤ d.degree) (c : R) (n : ℕ) :
    MvPowerSeries.coeff d
        ((H + MvPowerSeries.monomial d c) ^ n) =
      MvPowerSeries.coeff d (H ^ n) +
        if n = 1 then c else 0 := by
  simpa [add_comm, map_sub, sub_eq_iff_eq_add] using coeff_pow_add_monomial_sub_pow hH d hd c n

private theorem coeff_subst_lubinTateSeries_add_monomial
    (e : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree)
    (c : F.valuationSubring) :
    MvPowerSeries.coeff d
        (PowerSeries.subst
          (H + MvPowerSeries.monomial d c)
          e.toPowerSeries) =
      MvPowerSeries.coeff d
          (PowerSeries.subst H e.toPowerSeries) +
        π * c := by
  have hd0 : d ≠ 0 := by
    intro h
    subst d
    simp at hd
  have hHconstant :=
    hH.constantCoeff_eq_zero
  let oldTerm := fun n =>
    PowerSeries.coeff n e.toPowerSeries •
      MvPowerSeries.coeff d (H ^ n)
  let deltaTerm := fun n =>
    PowerSeries.coeff n e.toPowerSeries •
      if n = 1 then c else 0
  have hold : Function.HasFiniteSupport oldTerm := by
    simpa only [oldTerm] using
      PowerSeries.coeff_subst_finite hH.hasSubst e.toPowerSeries d
  have hdelta : Function.HasFiniteSupport deltaTerm := by
    rw [Function.HasFiniteSupport]
    refine (Set.finite_singleton 1).subset ?_
    intro n hn
    simp only [Function.mem_support] at hn
    simp only [Set.mem_singleton_iff]
    by_contra hne
    apply hn
    simp [deltaTerm, hne]
  rw [
    PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by
      simp [hHconstant, (constantCoeff_monomial_eq_zero hd0 c)])) e.toPowerSeries d,
    PowerSeries.coeff_subst hH.hasSubst e.toPowerSeries d]
  calc
    _ =
        ∑ᶠ n : ℕ, (oldTerm n + deltaTerm n) := by
      apply finsum_congr
      intro n
      rw [coeff_pow_add_monomial hHconstant d hd c n,
        smul_add]
    _ = (∑ᶠ n : ℕ, oldTerm n) +
        ∑ᶠ n : ℕ, deltaTerm n :=
      finsum_add_distrib hold hdelta
    _ = (∑ᶠ n : ℕ, oldTerm n) +
        PowerSeries.coeff 1 e.toPowerSeries * c := by
      congr 1
      rw [finsum_eq_single _ 1]
      · rfl
      · intro n hn
        simp [deltaTerm, hn]
    _ = (∑ᶠ n : ℕ, oldTerm n) + π * c := by
      simp

private theorem coeff_defect_add_monomial
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree)
    (c : F.valuationSubring) :
    MvPowerSeries.coeff d
        (defect e ebar (H + MvPowerSeries.monomial d c)) =
      MvPowerSeries.coeff d (defect e ebar H) +
        π * ((1 - π ^ (d.degree - 1)) * c) := by
  have hpow :
      π ^ d.degree = π * π ^ (d.degree - 1) := by
    calc
      π ^ d.degree = π ^ ((d.degree - 1) + 1) :=
        congrArg (fun n : ℕ => π ^ n) (by
          omega)
      _ = π ^ (d.degree - 1) * π := by
        rw [pow_succ]
      _ = π * π ^ (d.degree - 1) := by
        rw [mul_comm]
  simp only [
    defect,
    map_sub,
    coeff_subst_lubinTateSeries_add_monomial e hH d hd c,
    coeff_subst_inVariables_add_monomial ebar H d c,
    hpow]
  ring

/-- A correction in total degree at least two does not change the prescribed
linear term. -/
theorem correctedIntertwiner_hasLinearTerm
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    HasLinearTerm (correctedIntertwiner hπ e ebar hH d hd) L := by
  rw [correctedIntertwiner, HasLinearTerm]
  have hd' : (2 : ℕ∞) ≤ d.degree := by
    exact_mod_cast hd
  rw [show
    H + monomialCorrection hπ e ebar hH d hd - linearForm L =
      (H - linearForm L) +
        monomialCorrection hπ e ebar hH d hd by ring]
  exact
    (le_min hH (hd'.trans
      (degree_le_order_monomial d
        (correctionCoefficient hπ e ebar hH d hd)))).trans
      MvPowerSeries.min_order_le_add

/-- The recursively selected degree-`d` monomial cancels the degree-`d`
coefficient of the intertwining defect. -/
theorem coeff_defect_correctedIntertwiner_eq_zero
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    MvPowerSeries.coeff d
        (defect e ebar
          (correctedIntertwiner hπ e ebar hH d hd)) = 0 := by
  rw [
    correctedIntertwiner,
    monomialCorrection,
    coeff_defect_add_monomial e ebar hH d hd,
    ← uniformizer_mul_normalizedDefectCoefficient hπ e ebar hH d,
    correctionCoefficient_spec hπ e ebar hH d hd]
  ring

end SameUniformizer
end LubinTate

end
