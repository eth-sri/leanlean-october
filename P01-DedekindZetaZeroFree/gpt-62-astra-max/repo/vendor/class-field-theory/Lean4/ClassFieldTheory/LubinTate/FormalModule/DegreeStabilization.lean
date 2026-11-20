module

public import ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient
public import Mathlib.RingTheory.MvPowerSeries.Trunc

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Finite-degree stabilization for Lubin--Tate intertwining defects

The coefficient of an intertwining defect in total degree at most `m`
depends only on the coefficients of the proposed intertwiner in total degree
at most `m`.  This is the finite-degree continuity statement needed to pass
from recursively corrected finite approximations to one full multivariable
power series.

The proof uses total-degree truncation.  On the left side of the
intertwining equation, truncation commutes with substituting a series with
zero constant coefficient into the fixed Lubin--Tate series.  On the right
side, truncation of multivariable substitution depends only on the same
truncation of the outer series.
-/

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

universe u v w

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

/-- Equality of total-degree truncations through degree `m` is equivalent to
coefficientwise equality in every total degree at most `m`. -/
theorem truncTotal_succ_eq_iff_coeff_eq_degree_le
    {R : Type*} [CommSemiring R]
    {τ : Type*} [Finite τ]
    {H H' : MvPowerSeries τ R} (m : ℕ) :
    H.truncTotal (m + 1) = H'.truncTotal (m + 1) ↔
      ∀ d : τ →₀ ℕ, d.degree ≤ m →
        MvPowerSeries.coeff d H = MvPowerSeries.coeff d H' := by
  constructor
  · intro h d hd
    have hd' := Nat.lt_succ_iff.mpr hd
    calc
      MvPowerSeries.coeff d H =
          (H.truncTotal (m + 1)).coeff d :=
        (MvPowerSeries.coeff_truncTotal H hd').symm
      _ = (H'.truncTotal (m + 1)).coeff d := by rw [h]
      _ = MvPowerSeries.coeff d H' :=
        MvPowerSeries.coeff_truncTotal H' hd'
  · intro h
    ext d
    by_cases hd : d.degree < m + 1
    · simp_all [MvPowerSeries.coeff_truncTotal]
    · simp_all [MvPowerSeries.coeff_truncTotal_eq_zero]

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

private theorem truncTotal_powerSeries_subst_eq_of_truncTotal_eq
    (e : LubinTateSeries F π)
    {H H' : MvPowerSeries σ F.valuationSubring}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (hH' : MvPowerSeries.constantCoeff H' = 0)
    {k : ℕ} (htrunc : H.truncTotal k = H'.truncTotal k) :
    (PowerSeries.subst H e.toPowerSeries).truncTotal k =
      (PowerSeries.subst H' e.toPowerSeries).truncTotal k := by
  calc
    _ =
        (MvPowerSeries.subst
          (fun _ : Unit ↦ (H.truncTotal k).toMvPowerSeries)
          e.toPowerSeries).truncTotal k := MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le

           (PowerSeries.HasSubst.of_constantCoeff_zero hH).const (fun _ ↦ le_rfl)
    _ = (MvPowerSeries.subst
          (fun _ : Unit ↦ (H'.truncTotal k).toMvPowerSeries)
          e.toPowerSeries).truncTotal k := by
      rw [htrunc]
    _ = (MvPowerSeries.subst (fun _ : Unit ↦ H')
          e.toPowerSeries).truncTotal k := (MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le

           (PowerSeries.HasSubst.of_constantCoeff_zero hH').const
          (fun _ ↦ le_rfl)).symm

private theorem truncTotal_inVariables_subst_eq_of_truncTotal_eq
    (ebar : LubinTateSeries F π)
    {H H' : MvPowerSeries σ F.valuationSubring}
    {k : ℕ} (htrunc : H.truncTotal k = H'.truncTotal k) :
    (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H).truncTotal k =
      (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H').truncTotal k := by
  have hconstant :
      ∀ i : σ,
        MvPowerSeries.constantCoeff (inVariable ebar i) = 0 :=
    fun i ↦ constantCoeff_inVariable ebar i
  calc
    _ =
        (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i)
          (H.truncTotal k).toMvPowerSeries).truncTotal k := MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst
            hconstant
    _ = (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i)
          (H'.truncTotal k).toMvPowerSeries).truncTotal k := by
      rw [htrunc]
    _ = (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H').truncTotal k := (MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst
            hconstant).symm

/-- The degree-`d` coefficient of the same-uniformizer intertwining defect
depends only on coefficients of the proposed intertwiner through total degree
`d.degree`.

The slightly more general bound `m` is convenient for a recursive tower of
finite approximations: agreement through degree `m` makes every defect
coefficient of degree at most `m` stable. -/
theorem coeff_defect_eq_of_coeff_eq_degree_le
    (e ebar : LubinTateSeries F π)
    {H H' : MvPowerSeries σ F.valuationSubring}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (hH' : MvPowerSeries.constantCoeff H' = 0)
    {m : ℕ}
    (hcoeff : ∀ q : σ →₀ ℕ, q.degree ≤ m →
      MvPowerSeries.coeff q H = MvPowerSeries.coeff q H')
    {d : σ →₀ ℕ} (hd : d.degree ≤ m) :
    MvPowerSeries.coeff d (defect e ebar H) =
      MvPowerSeries.coeff d (defect e ebar H') := by
  let k := m + 1
  have htrunc := (truncTotal_succ_eq_iff_coeff_eq_degree_le
          m).2 hcoeff
  have hdefect :
      (defect e ebar H).truncTotal k =
        (defect e ebar H').truncTotal k := by
    calc
      _ =
          (PowerSeries.subst H e.toPowerSeries).truncTotal k -
            (MvPowerSeries.subst
              (fun i : σ ↦ inVariable ebar i) H).truncTotal k := by
        rw [defect, map_sub]
      _ = (PowerSeries.subst H' e.toPowerSeries).truncTotal k -
            (MvPowerSeries.subst
              (fun i : σ ↦ inVariable ebar i) H').truncTotal k := by
        rw [(truncTotal_powerSeries_subst_eq_of_truncTotal_eq
          e hH hH' htrunc), (truncTotal_inVariables_subst_eq_of_truncTotal_eq ebar htrunc)]
      _ = (defect e ebar H').truncTotal k := by
        rw [defect, map_sub]
  have hd' : d.degree < k := by
    dsimp only [k]
    exact Nat.lt_succ_iff.mpr hd
  calc
    _ =
        ((defect e ebar H).truncTotal k).coeff d :=
      (MvPowerSeries.coeff_truncTotal (defect e ebar H) hd').symm
    _ = ((defect e ebar H').truncTotal k).coeff d := by
      rw [hdefect]
    _ = MvPowerSeries.coeff d (defect e ebar H') :=
      MvPowerSeries.coeff_truncTotal (defect e ebar H') hd'

private theorem degree_le_order_monomial_stabilization
    {R : Type*} [CommRing R] {τ : Type*}
    (d : τ →₀ ℕ) (c : R) :
    (d.degree : ℕ∞) ≤ (MvPowerSeries.monomial d c).order := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  · rw [MvPowerSeries.order_monomial_of_ne_zero hc]

alias DegreeStabilization.degree_le_order_monomial_stabilization := degree_le_order_monomial_stabilization

private theorem natCast_le_order_pow_of_one_le_order_stabilization
    {R : Type*} [CommRing R] {τ : Type*}
    (f : MvPowerSeries τ R) (n : ℕ)
    (hf : (1 : ℕ∞) ≤ f.order) :
    (n : ℕ∞) ≤ (f ^ n).order := by
  calc
    _ = n • (1 : ℕ∞) := by simp
    _ ≤ n • f.order := nsmul_le_nsmul_right hf n
    _ ≤ (f ^ n).order := MvPowerSeries.le_order_pow n

alias DegreeStabilization.natCast_le_order_pow_of_one_le_order_stabilization := natCast_le_order_pow_of_one_le_order_stabilization

private theorem le_order_finset_sum_stabilization
    {R : Type*} [CommRing R] {τ ι : Type*}
    {s : Finset ι} {f : ι → MvPowerSeries τ R} {m : ℕ∞}
    (h : ∀ i ∈ s, m ≤ (f i).order) :
    m ≤ (∑ i ∈ s, f i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact
        (le_min
          (h i (Finset.mem_insert_self i s))
          (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).trans
        MvPowerSeries.min_order_le_add

alias DegreeStabilization.le_order_finset_sum_stabilization := le_order_finset_sum_stabilization

private theorem natCast_sum_le_order_finset_prod_pow_stabilization
    {R : Type*} [CommRing R] {τ ι : Type*}
    {s : Finset ι} (f : ι → MvPowerSeries τ R) (n : ι → ℕ)
    (hf : ∀ i ∈ s, (1 : ℕ∞) ≤ (f i).order) :
    ((∑ i ∈ s, n i : ℕ) : ℕ∞) ≤
      (∏ i ∈ s, (f i) ^ n i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      calc
        ((n i + ∑ j ∈ s, n j : ℕ) : ℕ∞) =
            (n i : ℕ∞) + ((∑ j ∈ s, n j : ℕ) : ℕ∞) := by
          norm_cast
        _ ≤ ((f i) ^ n i).order +
            (∏ j ∈ s, (f j) ^ n j).order :=
          add_le_add
            (natCast_le_order_pow_of_one_le_order_stabilization
              (f i) (n i) (hf i (Finset.mem_insert_self i s)))
            (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
        _ ≤ ((f i) ^ n i * ∏ j ∈ s, (f j) ^ n j).order :=
          MvPowerSeries.le_order_mul

alias DegreeStabilization.natCast_sum_le_order_finset_prod_pow_stabilization := natCast_sum_le_order_finset_prod_pow_stabilization

private theorem order_sub_add_pred_le_order_pow_sub_pow_stabilization
    {R : Type*} [CommRing R] {τ : Type*}
    (f g : MvPowerSeries τ R)
    (hf : (1 : ℕ∞) ≤ f.order)
    (hg : (1 : ℕ∞) ≤ g.order)
    (n : ℕ) :
    (f - g).order + ((n - 1 : ℕ) : ℕ∞) ≤
      (f ^ n - g ^ n).order := by
  let q :=
    ∑ i ∈ Finset.range n, f ^ i * g ^ (n - 1 - i)
  have hq : ((n - 1 : ℕ) : ℕ∞) ≤ q.order := by
    apply le_order_finset_sum_stabilization
    intro i hi
    have hi' := Finset.mem_range.mp hi
    calc
      ((n - 1 : ℕ) : ℕ∞) =
          (i : ℕ∞) + ((n - 1 - i : ℕ) : ℕ∞) := by
        norm_cast
        omega
      _ ≤ (f ^ i).order + (g ^ (n - 1 - i)).order :=
        add_le_add
          (natCast_le_order_pow_of_one_le_order_stabilization f i hf)
          (natCast_le_order_pow_of_one_le_order_stabilization
            g (n - 1 - i) hg)
      _ ≤ (f ^ i * g ^ (n - 1 - i)).order :=
        MvPowerSeries.le_order_mul
  calc
    _ ≤
        (f - g).order + q.order :=
      add_le_add_right hq _
    _ ≤ ((f - g) * q).order :=
      MvPowerSeries.le_order_mul
    _ = (f ^ n - g ^ n).order :=
      congrArg (fun h : MvPowerSeries τ R => h.order) ((Commute.all f g).mul_geom_sum₂ n)

alias DegreeStabilization.order_sub_add_pred_le_order_pow_sub_pow_stabilization := order_sub_add_pred_le_order_pow_sub_pow_stabilization

private theorem natCast_sum_add_one_le_order_prod_pow_sub_prod_pow_stabilization
    {R : Type*} [CommRing R] {τ ι : Type*}
    {s : Finset ι}
    (f g : ι → MvPowerSeries τ R) (n : ι → ℕ)
    (hn : ∀ i ∈ s, n i ≠ 0)
    (hf : ∀ i ∈ s, (1 : ℕ∞) ≤ (f i).order)
    (hg : ∀ i ∈ s, (1 : ℕ∞) ≤ (g i).order)
    (hfg : ∀ i ∈ s, (2 : ℕ∞) ≤ (f i - g i).order) :
    (((∑ i ∈ s, n i) + 1 : ℕ) : ℕ∞) ≤
      ((∏ i ∈ s, (f i) ^ n i) -
        ∏ i ∈ s, (g i) ^ n i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hni :=
        hn i (Finset.mem_insert_self i s)
      have hpowDifference :
          ((n i + 1 : ℕ) : ℕ∞) ≤
            ((f i) ^ n i - (g i) ^ n i).order := by
        calc
          ((n i + 1 : ℕ) : ℕ∞) =
              (2 : ℕ∞) + ((n i - 1 : ℕ) : ℕ∞) := by
            norm_cast
            omega
          _ ≤ (f i - g i).order +
              ((n i - 1 : ℕ) : ℕ∞) :=
            add_le_add_left
              (hfg i (Finset.mem_insert_self i s)) _
          _ ≤ ((f i) ^ n i - (g i) ^ n i).order :=
            order_sub_add_pred_le_order_pow_sub_pow_stabilization
              (f i) (g i)
              (hf i (Finset.mem_insert_self i s))
              (hg i (Finset.mem_insert_self i s))
              (n i)
      have hprodDifference :=
        ih
          (fun j hj => hn j (Finset.mem_insert_of_mem hj))
          (fun j hj => hf j (Finset.mem_insert_of_mem hj))
          (fun j hj => hg j (Finset.mem_insert_of_mem hj))
          (fun j hj => hfg j (Finset.mem_insert_of_mem hj))
      have hleft :
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) ≤
            (((f i) ^ n i - (g i) ^ n i) *
              ∏ j ∈ s, (f j) ^ n j).order := by
        calc
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) =
              ((n i + 1 : ℕ) : ℕ∞) +
                ((∑ j ∈ s, n j : ℕ) : ℕ∞) := by
            norm_cast
            omega
          _ ≤ ((f i) ^ n i - (g i) ^ n i).order +
              (∏ j ∈ s, (f j) ^ n j).order :=
            add_le_add hpowDifference (natCast_sum_le_order_finset_prod_pow_stabilization f n
              (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
          _ ≤ (((f i) ^ n i - (g i) ^ n i) *
              ∏ j ∈ s, (f j) ^ n j).order :=
            MvPowerSeries.le_order_mul
      have hright :
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) ≤
            ((g i) ^ n i *
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j)).order := by
        calc
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) =
              (n i : ℕ∞) +
                (((∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) := by
            norm_cast
          _ ≤ ((g i) ^ n i).order +
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j).order :=
            add_le_add (natCast_le_order_pow_of_one_le_order_stabilization
              (g i) (n i) (hg i (Finset.mem_insert_self i s))) hprodDifference
          _ ≤ ((g i) ^ n i *
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j)).order :=
            MvPowerSeries.le_order_mul
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        Finset.prod_insert hi]
      rw [show
        (f i) ^ n i * (∏ j ∈ s, (f j) ^ n j) -
            (g i) ^ n i * (∏ j ∈ s, (g j) ^ n j) =
          ((f i) ^ n i - (g i) ^ n i) *
              (∏ j ∈ s, (f j) ^ n j) +
            (g i) ^ n i *
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j) by ring]
      exact
        (le_min hleft hright).trans
          MvPowerSeries.min_order_le_add

alias DegreeStabilization.natCast_sum_add_one_le_order_prod_pow_sub_prod_pow_stabilization := natCast_sum_add_one_le_order_prod_pow_sub_prod_pow_stabilization

 noncomputable def linearInVariableStabilization
    (π : F.valuationSubring) (i : σ) :
    MvPowerSeries σ F.valuationSubring :=
  MvPowerSeries.C π * MvPowerSeries.X i

omit [Fintype σ] in
private theorem linearInVariableStabilization_constantCoeff
    (π : F.valuationSubring) (i : σ) :
    MvPowerSeries.constantCoeff
        (linearInVariableStabilization π i) = 0 := by
  simp [linearInVariableStabilization]

private theorem linearInVariableStabilization_hasSubst
    (π : F.valuationSubring) :
    MvPowerSeries.HasSubst
      (linearInVariableStabilization (σ := σ) π) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero
    (linearInVariableStabilization_constantCoeff π)

alias DegreeStabilization.linearInVariableStabilization_hasSubst := linearInVariableStabilization_hasSubst

omit [Fintype σ] in
private theorem two_le_order_inVariable_sub_linearInVariableStabilization
    (ebar : LubinTateSeries F π) (i : σ) :
    (2 : ℕ∞) ≤
      (inVariable ebar i -
        linearInVariableStabilization π i).order := by
  classical
  apply MvPowerSeries.nat_le_order
  intro d hd
  rw [map_sub]
  by_cases hdi : d = Finsupp.single i (d i)
  · by_cases hzero : d i = 0
    · have hd0 : d = 0 := by
        rw [hdi, hzero]
        simp
      subst d
      simp [inVariable, linearInVariableStabilization,
        PowerSeries.coeff_subst_single,
        LubinTateSeries.constantCoeff_eq_zero]
    · have hone : d i = 1 := by
        have hdegree : d.degree = d i := by
          simpa using
            congrArg Finsupp.degree hdi
        have hlt : d i < 2 := by
          rw [← hdegree]
          exact hd
        omega
      have hd1 : d = Finsupp.single i 1 := by
        rw [hdi, hone]
      subst d
      simp [inVariable, linearInVariableStabilization,
        PowerSeries.coeff_subst_single,
        LubinTateSeries.coeff_one_eq_uniformizer]
  · have hsingle : d ≠ Finsupp.single i 1 := by
      intro h
      apply hdi
      rw [h]
      simp
    have hX :
        MvPowerSeries.coeff d
          (MvPowerSeries.X i :
            MvPowerSeries σ F.valuationSubring) = 0 := by
      rw [MvPowerSeries.coeff_X, ite_eq_right hsingle]
    simp_all [inVariable, linearInVariableStabilization, PowerSeries.coeff_subst_single]

private theorem degree_add_one_le_order_subst_monomial_sub_linear_stabilization
    (ebar : LubinTateSeries F π)
    (d : σ →₀ ℕ) (c : F.valuationSubring) :
    ((d.degree + 1 : ℕ) : ℕ∞) ≤
      (MvPowerSeries.subst (fun i : σ => inVariable ebar i)
          (MvPowerSeries.monomial d c) -
        MvPowerSeries.subst
          (linearInVariableStabilization (σ := σ) π)
          (MvPowerSeries.monomial d c)).order := by
  have hprod :
      ((d.degree + 1 : ℕ) : ℕ∞) ≤
        (d.prod (fun i n => (inVariable ebar i) ^ n) -
          d.prod (fun i n =>
            (linearInVariableStabilization π i) ^ n)).order := by
    simpa only [Finsupp.prod, Finsupp.degree_apply] using
      natCast_sum_add_one_le_order_prod_pow_sub_prod_pow_stabilization
        (s := d.support)
        (fun i : σ => inVariable ebar i)
        (linearInVariableStabilization (σ := σ) π)
        (fun i => d i)
        (fun i hi => Finsupp.mem_support_iff.mp hi)
        (fun i _ => (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
    (constantCoeff_inVariable ebar i)))
        (fun i _ =>
          (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
    (linearInVariableStabilization_constantCoeff π i)))
        (fun i _ =>
          two_le_order_inVariable_sub_linearInVariableStabilization
            ebar i)
  rw [
    MvPowerSeries.subst_monomial
      (inVariable_hasSubst ebar) d c,
    MvPowerSeries.subst_monomial
      (linearInVariableStabilization_hasSubst π) d c,
    ← MvPowerSeries.c_eq_algebraMap]
  rw [show
    MvPowerSeries.C c *
          d.prod (fun i n => (inVariable ebar i) ^ n) -
        MvPowerSeries.C c *
          d.prod (fun i n =>
            (linearInVariableStabilization π i) ^ n) =
      c •
        (d.prod (fun i n => (inVariable ebar i) ^ n) -
          d.prod (fun i n =>
            (linearInVariableStabilization π i) ^ n)) by
    rw [MvPowerSeries.smul_eq_C_mul]
    ring]
  exact hprod.trans MvPowerSeries.le_order_smul

alias DegreeStabilization.degree_add_one_le_order_subst_monomial_sub_linear_stabilization := degree_add_one_le_order_subst_monomial_sub_linear_stabilization

omit [Fintype σ] in
private theorem coeff_subst_linearInVariableStabilization_monomial
    (q d : σ →₀ ℕ) (c : F.valuationSubring) :
    MvPowerSeries.coeff q
        (MvPowerSeries.subst
          (linearInVariableStabilization (σ := σ) π)
          (MvPowerSeries.monomial d c)) =
      if q = d then π ^ d.degree * c else 0 := by
  have hlinear :
      (Function.const σ π •
          (MvPowerSeries.X :
            σ → MvPowerSeries σ F.valuationSubring)) =
        linearInVariableStabilization (σ := σ) π := by
    funext i
    simp [linearInVariableStabilization, Pi.smul_apply',
      MvPowerSeries.smul_eq_C_mul]
  rw [← hlinear, ← MvPowerSeries.rescale_eq_subst,
    MvPowerSeries.coeff_rescale]
  by_cases hqd : q = d
  · subst q
    rw [MvPowerSeries.coeff_monomial_same, ite_eq_left rfl]
    simp only [Finsupp.prod, Function.const_apply,
      Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  · rw [MvPowerSeries.coeff_monomial_ne hqd, mul_zero,
      ite_eq_right hqd]

private theorem coeff_subst_inVariables_monomial_of_degree_le
    (ebar : LubinTateSeries F π)
    (q d : σ →₀ ℕ) (hq : q.degree ≤ d.degree)
    (c : F.valuationSubring) :
    MvPowerSeries.coeff q
        (MvPowerSeries.subst (fun i : σ => inVariable ebar i)
          (MvPowerSeries.monomial d c)) =
      if q = d then π ^ d.degree * c else 0 := by
  have hlt :
      q.degree <
        (MvPowerSeries.subst (fun i : σ => inVariable ebar i)
            (MvPowerSeries.monomial d c) -
          MvPowerSeries.subst
            (linearInVariableStabilization π)
            (MvPowerSeries.monomial d c)).order :=
    by
      have hqCast :
          q.degree < ((d.degree + 1 : ℕ) : ℕ∞) := by
        exact_mod_cast (Nat.lt_succ_of_le hq)
      exact hqCast.trans_le (degree_add_one_le_order_subst_monomial_sub_linear_stabilization
        ebar d c)
  have hcoeff :=
    MvPowerSeries.coeff_of_lt_order hlt
  rw [map_sub, sub_eq_zero] at hcoeff
  rw [hcoeff,
    coeff_subst_linearInVariableStabilization_monomial]

private theorem coeff_subst_inVariables_add_monomial_of_degree_le
    (ebar : LubinTateSeries F π)
    (H : MvPowerSeries σ F.valuationSubring)
    (q d : σ →₀ ℕ) (hq : q.degree ≤ d.degree)
    (c : F.valuationSubring) :
    MvPowerSeries.coeff q
        (MvPowerSeries.subst (fun i : σ => inVariable ebar i)
          (H + MvPowerSeries.monomial d c)) =
      MvPowerSeries.coeff q
          (MvPowerSeries.subst (fun i : σ => inVariable ebar i) H) +
        if q = d then π ^ d.degree * c else 0 := by
  rw [
    MvPowerSeries.subst_add (inVariable_hasSubst ebar),
    map_add,
    coeff_subst_inVariables_monomial_of_degree_le ebar q d hq c]

private theorem constantCoeff_monomial_eq_zero_stabilization
    {R : Type*} [CommRing R] {τ : Type*}
    {d : τ →₀ ℕ} (hd : d ≠ 0) (c : R) :
    MvPowerSeries.constantCoeff (MvPowerSeries.monomial d c) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_monomial_ne]
  exact Ne.symm hd

alias DegreeStabilization.constantCoeff_monomial_eq_zero_stabilization := constantCoeff_monomial_eq_zero_stabilization

private theorem coeff_pow_add_monomial_sub_pow_of_degree_le
    {R : Type*} [CommRing R] {τ : Type*}
    {H : MvPowerSeries τ R}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (q d : τ →₀ ℕ) (hq : q.degree ≤ d.degree)
    (hd : 1 ≤ d.degree) (c : R) (n : ℕ) :
    MvPowerSeries.coeff q
        ((H + MvPowerSeries.monomial d c) ^ n - H ^ n) =
      if n = 1 then (if q = d then c else 0) else 0 := by
  classical
  have hd0 : d ≠ 0 := by
    intro h
    subst d
    simp at hd
  by_cases hn : n = 1
  · simp_all [MvPowerSeries.coeff_monomial]
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
        constantCoeff_monomial_eq_zero_stabilization hd0 c
      have hAconstant :
          MvPowerSeries.constantCoeff A = 0 := by
        simp [A, hH, hMconstant]
      have hAorder : (1 : ℕ∞) ≤ A.order :=
        MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hAconstant
      have hpow :
          M.order + (n : ℕ∞) ≤
            (A ^ (n + 1) - H ^ (n + 1)).order := by
        simpa [A, M, add_sub_cancel_left] using
          order_sub_add_pred_le_order_pow_sub_pow_stabilization
            A H hAorder (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hH) (n + 1)
      have horder :
          ((d.degree + 1 : ℕ) : ℕ∞) ≤
            (A ^ (n + 1) - H ^ (n + 1)).order := by
        calc
          _ =
              (d.degree : ℕ∞) + 1 := by norm_cast
          _ ≤ M.order + (n : ℕ∞) :=
            add_le_add (degree_le_order_monomial_stabilization d c) (by
              exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0)
          _ ≤ (A ^ (n + 1) - H ^ (n + 1)).order :=
            hpow
      have hlt :
          q.degree <
            (A ^ (n + 1) - H ^ (n + 1)).order :=
        by
          have hqCast :
              q.degree <
                ((d.degree + 1 : ℕ) : ℕ∞) := by
            exact_mod_cast (Nat.lt_succ_of_le hq)
          exact hqCast.trans_le horder
      grind [MvPowerSeries.coeff_of_lt_order]

private theorem coeff_pow_add_monomial_of_degree_le
    {R : Type*} [CommRing R] {τ : Type*}
    {H : MvPowerSeries τ R}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (q d : τ →₀ ℕ) (hq : q.degree ≤ d.degree)
    (hd : 1 ≤ d.degree) (c : R) (n : ℕ) :
    MvPowerSeries.coeff q
        ((H + MvPowerSeries.monomial d c) ^ n) =
      MvPowerSeries.coeff q (H ^ n) +
        if n = 1 then (if q = d then c else 0) else 0 := by
  simpa [add_comm, map_sub, sub_eq_iff_eq_add] using coeff_pow_add_monomial_sub_pow_of_degree_le hH q d hq hd c n

omit [Fintype σ] in
private theorem coeff_subst_lubinTateSeries_add_monomial_of_degree_le
    (e : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (q d : σ →₀ ℕ) (hq : q.degree ≤ d.degree)
    (hd : 1 ≤ d.degree) (c : F.valuationSubring) :
    MvPowerSeries.coeff q
        (PowerSeries.subst
          (H + MvPowerSeries.monomial d c)
          e.toPowerSeries) =
      MvPowerSeries.coeff q
          (PowerSeries.subst H e.toPowerSeries) +
        π * (if q = d then c else 0) := by
  have hd0 : d ≠ 0 := by
    intro h
    subst d
    simp at hd
  have hHsubst :=
    PowerSeries.HasSubst.of_constantCoeff_zero hH
  let oldTerm := fun n =>
    PowerSeries.coeff n e.toPowerSeries •
      MvPowerSeries.coeff q (H ^ n)
  let deltaTerm := fun n =>
    PowerSeries.coeff n e.toPowerSeries •
      if n = 1 then (if q = d then c else 0) else 0
  have hold : Function.HasFiniteSupport oldTerm := by
    simpa only [oldTerm] using
      PowerSeries.coeff_subst_finite hHsubst e.toPowerSeries q
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
      simp [hH, (constantCoeff_monomial_eq_zero_stabilization hd0 c)])) e.toPowerSeries q,
    PowerSeries.coeff_subst hHsubst e.toPowerSeries q]
  calc
    _ =
        (∑ᶠ n : ℕ, (oldTerm n + deltaTerm n)) := by
      apply finsum_congr
      intro n
      rw [coeff_pow_add_monomial_of_degree_le
        hH q d hq hd c n, smul_add]
    _ = (∑ᶠ n : ℕ, oldTerm n) +
        ∑ᶠ n : ℕ, deltaTerm n :=
      finsum_add_distrib hold hdelta
    _ = (∑ᶠ n : ℕ, oldTerm n) +
        PowerSeries.coeff 1 e.toPowerSeries *
          (if q = d then c else 0) := by
      congr 1
      rw [finsum_eq_single _ 1]
      · rfl
      · intro n hn
        simp [deltaTerm, hn]
    _ = (∑ᶠ n : ℕ, oldTerm n) +
        π * (if q = d then c else 0) := by
      simp

private theorem coeff_defect_add_monomial_eq_of_degree_le_constantCoeff
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (q d : σ →₀ ℕ) (hq : q.degree ≤ d.degree)
    (hd : 1 ≤ d.degree) (c : F.valuationSubring) :
    MvPowerSeries.coeff q
        (defect e ebar (H + MvPowerSeries.monomial d c)) =
      MvPowerSeries.coeff q (defect e ebar H) +
        if q = d then
          π * ((1 - π ^ (d.degree - 1)) * c)
        else 0 := by
  simp only [
    defect,
    map_sub,
    coeff_subst_lubinTateSeries_add_monomial_of_degree_le
      e hH q d hq hd c,
    coeff_subst_inVariables_add_monomial_of_degree_le
      ebar H q d hq c]
  by_cases hqd : q = d
  · subst q
    simp only [ite_eq_left]
    have hpow :
        π ^ d.degree = π * π ^ (d.degree - 1) := by
      calc
        π ^ d.degree =
            π ^ ((d.degree - 1) + 1) :=
          congrArg (fun n : ℕ => π ^ n) (by
            omega)
        _ = π * π ^ (d.degree - 1) := by
          rw [pow_succ, mul_comm]
    rw [hpow]
    ring
  · simp [hqd]

/-- Adding a monomial of degree `d.degree` changes no defect coefficient in
lower total degree and changes the same-degree block only in the `d`
coordinate. -/
theorem coeff_defect_add_monomial_eq_of_degree_le
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (q d : σ →₀ ℕ) (hq : q.degree ≤ d.degree)
    (hd : 2 ≤ d.degree) (c : F.valuationSubring) :
    MvPowerSeries.coeff q
        (defect e ebar (H + MvPowerSeries.monomial d c)) =
      MvPowerSeries.coeff q (defect e ebar H) +
        if q = d then
          π * ((1 - π ^ (d.degree - 1)) * c)
        else 0 :=
  coeff_defect_add_monomial_eq_of_degree_le_constantCoeff
    e ebar hH.constantCoeff_eq_zero q d hq (by omega) c

private theorem linearForm_eq_sum_monomial_stabilization
    (L : σ → F.valuationSubring) :
    linearForm L =
      ∑ i, MvPowerSeries.monomial
        (Finsupp.single i 1) (L i) := by
  rw [linearForm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← MvPowerSeries.monomial_zero_eq_C_apply,
    MvPowerSeries.X_def,
    MvPowerSeries.monomial_mul_monomial]
  simp

private theorem coeff_defect_sum_linear_monomials_eq_zero
    (e ebar : LubinTateSeries F π)
    (L : σ → F.valuationSubring)
    (s : Finset σ) (q : σ →₀ ℕ) (hq : q.degree ≤ 1) :
    MvPowerSeries.coeff q
        (defect e ebar
          (∑ i ∈ s, MvPowerSeries.monomial
            (Finsupp.single i 1) (L i))) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      have hright :
          MvPowerSeries.subst
            (fun i : σ => inVariable ebar i)
            (0 : MvPowerSeries σ F.valuationSubring) = 0 := by
        rw [← MvPowerSeries.substAlgHom_apply
          (inVariable_hasSubst ebar), map_zero]
      simp [defect, (PowerSeries.subst_zero_of_constantCoeff_zero
        e.constantCoeff_eq_zero), hright]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, add_comm]
      have hconstant :
          MvPowerSeries.constantCoeff
            (∑ j ∈ s, MvPowerSeries.monomial
              (Finsupp.single j 1) (L j)) = 0 := by
        rw [map_sum]
        apply Finset.sum_eq_zero
        intro j _
        exact
          constantCoeff_monomial_eq_zero_stabilization
            (Finsupp.single_ne_zero.mpr one_ne_zero) (L j)
      have hq' :
          q.degree ≤ (Finsupp.single i 1).degree := by
        simpa using hq
      rw [
        coeff_defect_add_monomial_eq_of_degree_le_constantCoeff
          e ebar hconstant q (Finsupp.single i 1) hq'
          (by simp) (L i),
        ih]
      simp

/-- The same-uniformizer defect of a series with prescribed linear term has
no constant or linear coefficient. -/
theorem two_le_order_defect
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L) :
    (2 : ℕ∞) ≤ (defect e ebar H).order := by
  classical
  apply MvPowerSeries.nat_le_order
  intro q hq
  have hqle :=
    Nat.le_of_lt_succ (by exact hq)
  have hcoeff :
      ∀ r : σ →₀ ℕ, r.degree ≤ 1 →
        MvPowerSeries.coeff r H =
          MvPowerSeries.coeff r (linearForm L) := by
    intro r hr
    have hlt :
        r.degree < (H - linearForm L).order :=
      by
        have hrCast : r.degree < (2 : ℕ∞) := by
          exact_mod_cast (Nat.lt_succ_of_le hr)
        exact hrCast.trans_le hH
    have hzero := MvPowerSeries.coeff_of_lt_order hlt
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero
  have hdefect :=
    coeff_defect_eq_of_coeff_eq_degree_le
      e ebar hH.constantCoeff_eq_zero
      (constantCoeff_linearForm L)
       hcoeff hqle
  rw [hdefect]
  rw [linearForm_eq_sum_monomial_stabilization]
  simpa using
    coeff_defect_sum_linear_monomials_eq_zero
      e ebar L Finset.univ q hqle

end SameUniformizer
end LubinTate

end
