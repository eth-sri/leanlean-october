module

public import Expdb.ExponentialSums.ExponentSumGrowth

import Expdb.Basic.AutomaticUniformity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import WeylPort.Analytic.RealLaplace

/-!
# Non-asymptotic exponential sum growth bounds

This module formalizes the non-asymptotic definition of exponential sum exponent from the
blueprint's Exponential sum growth exponents chapter (`beta-chapter`). It gives a fixed-parameter,
epsilon--delta characterization of the exponential sum growth exponent.
-/

@[expose] public section

open Filter Topology
open scoped ContDiff Expdb FourierTransform NNReal

noncomputable section

namespace Expdb

/-! ## Fixed-parameter formulation -/

/-- The fixed data satisfying the hypotheses of the non-asymptotic exponential-sum bound. -/
structure IsModelPhaseSumSetupAt
    (α σ δ : ℝ) (P : ℕ) (C T N : ℝ) (F : ℝ → ℝ) (a b : ℕ) : Prop where
  /-- The phase parameter is above the uniform threshold. -/
  threshold_le_param : C ≤ T
  /-- The scale is at least the lower power allowed by `δ`. -/
  rpow_sub_le_scale : T ^ (α - δ) ≤ N
  /-- The scale is at most the upper power allowed by `δ`. -/
  scale_le_rpow_add : N ≤ T ^ (α + δ)
  /-- The phase approximates the model phase through order `P`. -/
  isApproximateModelPhase : IsApproximateModelPhaseFunction F σ P δ
  /-- The summation interval begins in the dyadic block. -/
  scale_le_start : N ≤ (a : ℝ)
  /-- The summation interval ends in the dyadic block. -/
  end_le_two_mul_scale : (b : ℝ) ≤ 2 * N

/-- The fixed-parameter epsilon--delta bound from the blueprint lemma `beta-asymp`
    (Non-asymptotic definition of `β`). -/
def IsExponentSumBoundNonAsymptotic (α : ℝ≥0) (β : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ σ : ℝ, 0 < σ →
      ∃ δ : ℝ, 0 < δ ∧
        ∃ P : ℕ, 1 ≤ P ∧
          ∃ C : ℝ, 1 ≤ C ∧
            ∀ (T N : ℝ) (F : ℝ → ℝ) (a b : ℕ),
              IsModelPhaseSumSetupAt (α : ℝ) σ δ P C T N F a b →
              ‖exponentialSumAt F T N a b‖ ≤ C * T ^ (β + ε)

/-! ## From fixed bounds to asymptotic bounds -/

private lemma isExponentSumBound_of_nonAsymptotic
    {α : ℝ≥0} {β : ℝ}
    (hbound : IsExponentSumBoundNonAsymptotic α β) :
    IsExponentSumBound α β := by
  pm_2747
  apply (isPowerBounded_iff_forall_pos
    (exponentialSum F T N a b) T β hT hTunbounded).2
  intro ε hε
  pm_2748
  have hTC : ∀ᶠ i in atTop, C ≤ T i := by
    have hnorm := (VariableObject.isUnbounded_iff_forall_eventually_norm_ge T).1
      hTunbounded C
    filter_upwards [hnorm] with i hi
    simpa [Real.norm_eq_abs, abs_of_nonneg
      (le_trans zero_le_one (hT i))] using hi
  have hNT' :=
    hNT.eventually_between
      (Filter.Eventually.of_forall hT) hδ
  pm_6913
  filter_upwards [hTC, hNT', happrox] with i hiT hiNT hiF
  simpa only [exponentialSum_apply, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (le_trans zero_le_one (hT i)) _)] using
      hfixed (T i) (N i) (F i) (a i) (b i)
        ⟨hiT, hiNT.1, hiNT.2, hiF, (hab i).1, (hab i).2⟩

/-! ## Uniform bounds for approximate model phases -/

/-! ## Building asymptotic counterexamples -/

private lemma isModelPhaseFunction_of_approximations
    {F : VariableFunction (VariableObject.fixed ℝ) ℝ}
    {σ : ℝ} {P : VariableObject ℕ} {δ : VariableObject ℝ}
    (hσ : 0 < σ)
    (hP : ∀ p : ℕ, ∀ᶠ i in atTop, p ≤ P i)
    (hδ : δ.IsInfinitesimal)
    (happrox : ∀ i, IsApproximateModelPhaseFunction (F i) σ (P i) (δ i)) :
    IsModelPhaseFunction F := by pm_2749

section
variable {α : ℝ≥0} {β : ℝ}
include α β
private lemma nonAsymptotic_of_isExponentSumBound (hbound : IsExponentSumBound α β) :
    IsExponentSumBoundNonAsymptotic α β := by
  pm_2750
  have hlower : ∀ i, T i ^ ((α : ℝ) - δ i) ≤ N i :=
    fun i ↦ (hdata i).1.rpow_sub_le_scale
  have hupper : ∀ i, N i ≤ T i ^ ((α : ℝ) + δ i) :=
    fun i ↦ (hdata i).1.scale_le_rpow_add
  pm_2752
  have hviolate : ∀ i,
      C i * T i ^ (β + ε) <
        ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖ :=
    fun i ↦ (hdata i).2
  have hTgt : ∀ i, 1 < T i := fun i ↦ by grind
  have hTone : ∀ i, 1 ≤ T i := fun i ↦ (hTgt i).le
  have hTunbounded : VariableObject.IsUnbounded T := by
    apply (VariableObject.isUnbounded_iff_forall_eventually_norm_ge T).2
    intro D
    pm_2753 k hk D
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one (hTone i))]
    calc
      D ≤ (k : ℝ) := hk
      _ ≤ (i : ℝ) := by exact_mod_cast hi
      _ ≤ C i := by
        dsimp [C]
        linarith
      _ ≤ T i := hCT i
  pm_2751
  have hNpos : ∀ i, 0 < N i := fun i ↦
    lt_of_lt_of_le
      (Real.rpow_pos_of_pos (lt_trans zero_lt_one (hTgt i)) _)
      (hlower i)
  have hβnonneg : 0 ≤ β := hbound.nonneg
  have hNone : ∀ i, 1 ≤ N i := by
    intro i
    by_contra hiN
    have hNlt : N i < 1 := lt_of_not_ge hiN
    have hblt : (b i : ℝ) < 2 := lt_of_le_of_lt (hb i) (by linarith)
    have hbNat : b i < 2 := by exact_mod_cast hblt
    have hsum :
        ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖ ≤ 2 := by
      calc
        ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖ ≤
            (b i : ℝ) + 1 :=
          norm_exponentialSumAt_le_add_one
            (F i) (T i) (N i) (a i) (b i)
        _ ≤ 2 := by
          have : b i ≤ 1 := by omega
          exact_mod_cast Nat.add_le_add_right this 1
    have hpow : 1 ≤ T i ^ (β + ε) :=
      Real.one_le_rpow (hTone i) (by linarith)
    have hCthree : 3 ≤ C i := by
      dsimp [C]
      exact le_add_of_nonneg_left (Nat.cast_nonneg i)
    have hrhs : 3 ≤ C i * T i ^ (β + ε) := by
      calc
        3 ≤ C i := hCthree
        _ = C i * 1 := by ring
        _ ≤ C i * T i ^ (β + ε) :=
          mul_le_mul_of_nonneg_left hpow (le_trans (by norm_num) hCthree)
    linarith [hviolate i]
  have hNT : IsPowerAsymptotic N T (α : ℝ) :=
    isPowerAsymptotic_of_between_of_infinitesimal hTgt hNpos
      hδinfinitesimal
      (fun i ↦ ⟨hlower i, hupper i⟩)
  pm_8038
  have hasymptotic :=
    hbound N T F a b hNone hTone hTunbounded hNT hF
      (fun i ↦ ⟨ha i, hb i⟩)
  have hO :=
    (isPowerBounded_iff_forall_pos
      (exponentialSum F T N a b) T β hTone hTunbounded).1
      hasymptotic (ε / 2) (by linarith)
  obtain ⟨K, hK⟩ := hO.bound
  have hCK : ∀ᶠ i in atTop, K ≤ C i := by
    pm_2753 k hk K
    calc
      K ≤ (k : ℝ) := hk
      _ ≤ (i : ℝ) := by exact_mod_cast hi
      _ ≤ C i := by
        dsimp [C]
        linarith
  obtain ⟨i, hiK, hiCK⟩ := (hK.and hCK).exists
  have hnorm :
      ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖ ≤
        K * T i ^ (β + ε / 2) := by
    simpa only [exponentialSum_apply, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (le_trans zero_le_one (hTone i)) _)] using hiK
  have hdominated :
      ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖ ≤
        C i * T i ^ (β + ε) := by
    calc
      ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖ ≤
          K * T i ^ (β + ε / 2) := hnorm
      _ ≤ C i * T i ^ (β + ε / 2) := by
        exact mul_le_mul_of_nonneg_right hiCK
          (Real.rpow_nonneg (le_trans zero_le_one (hTone i)) _)
      _ ≤ C i * T i ^ (β + ε) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (hTone i) (by linarith))
          (le_trans zero_le_one (hCone i))
  grind

/-! ## Equivalence with the asymptotic definition -/

/-- The non-asymptotic characterization of the exponential sum growth exponent. -/
theorem exponentSumGrowthExponent_le_iff_nonAsymptotic :
    exponentSumGrowthExponent α ≤ β ↔
      IsExponentSumBoundNonAsymptotic α β := by
  rw [exponentSumGrowthExponent_le_iff]
  exact ⟨nonAsymptotic_of_isExponentSumBound,
    isExponentSumBound_of_nonAsymptotic⟩
end

end Expdb
