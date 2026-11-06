module

public import Mathlib

public import ValuedFieldTheory.Valuation.Henselian.UniqueAlgebraicExtensions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Algebra.Algebra.Tower
public import ValuedFieldTheory.Valuation.LocalRingEquiv

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/










set_option autoImplicit false

/-!
# the fundamental inequality and identity

The first part follows the proof on pp. 149--150: residue-basis lifts are
multiplied by representatives of distinct value-group cosets, and the
resulting family is linearly independent over the base field.  The second
part uses the actual valuation rings.  For a discrete Henselian base and a
finite separable extension, the finite norm-formula theorem identifies the target valuation ring
with the integral closure, so the local Dedekind ramification identity applies
without completeness.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicNumberTheory
namespace Valuations

open Module

 section
variable {K : Type*} [Field K]
    (v : LubinTate.Valuations.ExponentialValuation K)
include K v
def ramificationAddValuation    :=
  AddValuation.of v
    ((v.eq_top_iff 0).mpr rfl)
    (LubinTate.Valuations.exponentialValuation_one v)
    v.add_le_min v.map_mul

@[simp]
private theorem ramificationAddValuation_apply   (x : K) :
    ramificationAddValuation v x = v x :=
  rfl














































































































































































































































































































































































































































































































































































































































































































/-- The canonical multiplicative presentation `exp (-v(x))` of an exponential
exponential valuation. -/
noncomputable def exponentialAssociatedAbsoluteValue
      :
    AbsoluteValue K ℝ := by
  classical
  refine
    { toFun := fun x ↦ if x = 0 then 0 else Real.exp (-(v x).untop₀)
      map_mul' := ?_
      nonneg' := ?_
      eq_zero' := ?_
      add_le' := ?_ }
  · intro x y
    by_cases hx : x = 0
    · subst x
      simp
    by_cases hy : y = 0
    · subst y
      simp
    have hxy  := mul_ne_zero hx hy
    have hreal : (v (x * y)).untop₀ =
        (v x).untop₀ + (v y).untop₀ := by
      apply WithTop.coe_eq_coe.mp
      rw [WithTop.coe_add,
        WithTop.coe_untop₀_of_ne_top
          (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hxy),
        WithTop.coe_untop₀_of_ne_top
          (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hx),
        WithTop.coe_untop₀_of_ne_top
          (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hy)]
      exact v.map_mul x y
    simp only [hx, hy, hxy, ite_false]
    rw [hreal, neg_add, Real.exp_add]
  · intro x
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx, Real.exp_nonneg]
  · intro x
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx, Real.exp_ne_zero]
  · intro x y
    by_cases hx : x = 0
    · subst x
      simp
    by_cases hy : y = 0
    · subst y
      simp
    by_cases hxy : x + y = 0
    · simp only [hx, hy, hxy, ite_false, ite_true]
      positivity
    let r := (v x).untop₀
    let s := (v y).untop₀
    let t := (v (x + y)).untop₀
    have hvr : v x = (r : WithTop ℝ) :=
      (WithTop.coe_untop₀_of_ne_top
        (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hx)).symm
    have hvs : v y = (s : WithTop ℝ) :=
      (WithTop.coe_untop₀_of_ne_top
        (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hy)).symm
    have hvt : v (x + y) = (t : WithTop ℝ) :=
      (WithTop.coe_untop₀_of_ne_top
        (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hxy)).symm
    have hmin : min r s ≤ t := by
      have h := v.add_le_min x y
      rw [hvr, hvs, hvt] at h
      apply WithTop.coe_le_coe.mp <;> assumption
    have hmain : Real.exp (-t) ≤ Real.exp (-r) + Real.exp (-s) := by
      refine (Real.exp_le_exp.mpr (neg_le_neg hmin)).trans ?_
      by_cases hrs : r ≤ s
      · rw [min_eq_left hrs]
        exact le_add_of_nonneg_right (Real.exp_nonneg _)
      · rw [min_eq_right (le_of_not_ge hrs)]
        exact le_add_of_nonneg_left (Real.exp_nonneg _)
    simpa only [hx, hy, hxy, ite_false, r, s, t] using hmain

/-- The canonical multiplicative presentation is associated to `v`, with
the fixed base `e = exp 1`. -/
theorem exponentialAssociatedAbsoluteValue_associated
      :
    LubinTate.Valuations.AssociatedAbsoluteValue v (Real.exp 1)
      (exponentialAssociatedAbsoluteValue v) := by
  refine ⟨Real.one_lt_exp_iff.mpr zero_lt_one, ?_⟩
  intro x hx
  refine ⟨(v x).untop₀, ?_, ?_⟩
  · exact (WithTop.coe_untop₀_of_ne_top
      (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hx)).symm
  · simp [exponentialAssociatedAbsoluteValue, hx, Real.exp_one_rpow]

/-- An absolute value associated to a exponential valuation is
nonarchimedean; the strong triangle inequality is the exponential
ultrametric inequality transported through the decreasing map
`r ↦ q ^ (-r)`. -/
theorem associatedAbsoluteValue_nonarchimedean
      (q : ℝ)
    (abv : AbsoluteValue K ℝ)
    (hassoc : LubinTate.Valuations.AssociatedAbsoluteValue v q abv) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue abv := by
  apply LubinTate.Valuations.nonarchimedean_of_strong_triangle
  intro x y
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hy : y = 0
  · subst y
    simp
  by_cases hxy : x + y = 0
  · simp [hxy]
  obtain ⟨r, hvr, habvr⟩ := hassoc.2 x hx
  obtain ⟨s, hvs, habvs⟩ := hassoc.2 y hy
  obtain ⟨t, hvt, habvt⟩ := hassoc.2 (x + y) hxy
  have hmin : min r s ≤ t := by
    have h := v.add_le_min x y
    rw [hvr, hvs, hvt] at h
    apply WithTop.coe_le_coe.mp <;> assumption
  rw [habvr, habvs, habvt]
  have hpow : q ^ (-t) ≤ q ^ (-(min r s)) :=
    Real.rpow_le_rpow_of_exponent_le (le_of_lt hassoc.1)
      (neg_le_neg hmin)
  refine hpow.trans ?_
  by_cases hrs : r ≤ s
  · rw [min_eq_left hrs]
    exact le_max_left _ _
  · have hsr : s ≤ r := le_of_not_ge hrs
    rw [min_eq_right hsr]
    exact le_max_right _ _

/-- Associated additive and multiplicative presentations have the same
valuation subring. -/
theorem associatedAbsoluteValue_valuationSubring_eq
      (q : ℝ)
    (abv : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue abv)
    (hassoc : LubinTate.Valuations.AssociatedAbsoluteValue v q abv) :
    LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v =
      absoluteValueValuationSubring abv hnonarch := by
  ext x
  rw [LubinTate.Valuations.mem_exponentialValuationSubringAsValuationSubring_iff,
    mem_absoluteValueValuationSubring_iff]
  by_cases hx : x = 0
  · subst x
    simp [(v.eq_top_iff 0).mpr rfl]
  · exact (LubinTate.Valuations.associatedAbsoluteValue_le_one_iff hassoc hx).symm
end


/-- Exact extension of associated exponential valuations gives exact
extension of the associated absolute values. -/
theorem associatedAbsoluteValue_extends
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (q : ℝ) (av : AbsoluteValue K ℝ) (aw : AbsoluteValue L ℝ)
    (hav : LubinTate.Valuations.AssociatedAbsoluteValue v q av)
    (haw : LubinTate.Valuations.AssociatedAbsoluteValue w q aw) :
    ∀ a : K, aw (algebraMap K L a) = av a := by
  intro a
  by_cases ha : a = 0
  · subst a
    simp
  · have hma : algebraMap K L a ≠ 0 :=
      (map_ne_zero (algebraMap K L)).mpr ha
    obtain ⟨r, hvr, havr⟩ := hav.2 a ha
    obtain ⟨s, hws, haws⟩ := haw.2 (algebraMap K L a) hma
    have hrs : r = s := by
      rw [hExt, hvr] at hws
      exact WithTop.coe_eq_coe.mp hws
    rw [havr, haws, hrs]

























/-- the finite norm-formula theorem applied directly to the exponential presentation: a chosen
extension of a Henselian valuation has valuation ring equal to the actual
integral closure. The required multiplicative presentations are constructed
internally. -/
theorem exponentialValuationSubring_eq_integralClosure_of_henselian
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation) :
    (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w).toSubring =
      (integralClosure
        (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v) L).toSubring := by
  let av := exponentialAssociatedAbsoluteValue v
  let aw := exponentialAssociatedAbsoluteValue w
  have hav : LubinTate.Valuations.AssociatedAbsoluteValue v (Real.exp 1) av :=
    exponentialAssociatedAbsoluteValue_associated v
  have haw : LubinTate.Valuations.AssociatedAbsoluteValue w (Real.exp 1) aw :=
    exponentialAssociatedAbsoluteValue_associated w
  have havNonarch  :=
    associatedAbsoluteValue_nonarchimedean v (Real.exp 1) av hav
  have hawNonarch  :=
    associatedAbsoluteValue_nonarchimedean w (Real.exp 1) aw haw
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v
  let Wv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w
  let Va := absoluteValueValuationSubring av havNonarch
  let Wa := absoluteValueValuationSubring aw hawNonarch
  have hV : Vv = Va :=
    associatedAbsoluteValue_valuationSubring_eq
      v (Real.exp 1) av havNonarch hav
  have hW : Wv = Wa :=
    associatedAbsoluteValue_valuationSubring_eq
      w (Real.exp 1) aw hawNonarch haw
  have hhensA : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization Va.valuation := by
    rw [← hV]
    exact hhens
  have habsExt  :=
    associatedAbsoluteValue_extends
      v w hExt (Real.exp 1) av aw hav haw
  have hWaExt : Va.valuation.HasExtension Wa.valuation :=
    absoluteValueValuation_hasExtension_of_extends
      av aw havNonarch hawNonarch habsExt
  let  := hWaExt
  obtain ⟨B, hB, _hBuniq⟩ :=
    normFormula_algebraic_extension (K := K) (L := L)
      av havNonarch hhensA
  obtain ⟨C, hC, hCuniq⟩ :=
    henselianUniqueExtension_unique_algebraic_valuationSubring_extension_of_henselian
      (K := K) (L := L) av havNonarch hhensA
  have hWaC  := hCuniq Wa hWaExt
  have hBC  := hCuniq B hB.1
  have hWaB  := hWaC.trans hBC.symm
  calc
    Wv.toSubring = Wa.toSubring := congrArg ValuationSubring.toSubring hW
    _ = B.toSubring := congrArg ValuationSubring.toSubring hWaB
    _ = (integralClosure Va L).toSubring := hB.2
    _ = (integralClosure Vv L).toSubring := by rw [hV]







































































































































































































































































































































































































































































































































































































end Valuations
end AlgebraicNumberTheory

end
