module
public import TaoTrudgianYang2025.AsymptoticBridge

@[expose] public section

/-!
# Exponent-pair semantics

This module records the analytic, rather than polyhedral, meaning of an
exponent pair in Tao--Trudgian--Yang. The asymptotic predicate below follows
Definition `exp-pair-def`: the sum is bounded by
`(T / N) ^ (k + o(1)) * N ^ (l + o(1))`, uniformly for model phases and
subintervals of the dyadic block. A separate fixed-parameter predicate
records the epsilon--delta form, proved equivalent below.
-/

open Filter Topology
open scoped Expdb

noncomputable section

namespace TaoTrudgianYang2025

open Expdb

/-- The closed triangle in which the paper defines exponent pairs. -/
def InExponentPairTriangle (k l : ℝ) : Prop :=
  0 ≤ k ∧ k ≤ 1 / 2 ∧ 1 / 2 ≤ l ∧ l ≤ 1 ∧ k + l ≤ 1

/-- The direct variable-quantity estimate
`(T/N)^(k+o(1)) N^(l+o(1))` from the paper's exponent-pair definition. -/
def IsExponentPairEstimate (k l : ℝ) : Prop :=
  ∀ (N T : VariableObject ℝ)
    (F : VariableFunction (VariableObject.fixed ℝ) ℝ)
    (a b : VariableObject ℕ),
    (∀ i, 1 ≤ N i) →
    (∀ᶠ i in atTop, N i ≤ T i) →
    T.IsUnbounded →
    IsModelPhaseFunction F →
    (∀ i, N i ≤ (a i : ℝ) ∧ (b i : ℝ) ≤ 2 * N i) →
    ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO atTop (exponentialSum F T N a b)
        (fun i ↦
          (T i / N i) ^ (k + ε) * N i ^ (l + ε))

/-- A fixed exponential-sum setup for the non-asymptotic exponent-pair
estimate. Its fields make the dependence of constants and the dyadic range
visible. -/
structure IsExponentPairSetupAt
    (σ δ : ℝ) (P : ℕ) (C T N : ℝ) (F : ℝ → ℝ) (a b : ℕ) : Prop where
  threshold_le_param : C ≤ T
  one_le_scale : 1 ≤ N
  scale_le_param : N ≤ T
  isApproximateModelPhase : IsApproximateModelPhaseFunction F σ P δ
  scale_le_start : N ≤ (a : ℝ)
  end_le_two_mul_scale : (b : ℝ) ≤ 2 * N

/-- The epsilon--delta formulation of the paper's exponent-pair estimate.
The model exponent `σ` is quantified before the uniform constants. -/
def IsExponentPairEstimateNonAsymptotic (k l : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ σ : ℝ, 0 < σ →
      ∃ δ : ℝ, 0 < δ ∧
        ∃ P : ℕ, 1 ≤ P ∧
          ∃ C : ℝ, 1 ≤ C ∧
            ∀ (T N : ℝ) (F : ℝ → ℝ) (a b : ℕ),
              IsExponentPairSetupAt σ δ P C T N F a b →
              ‖exponentialSumAt F T N a b‖ ≤
                C * (T / N) ^ (k + ε) * N ^ (l + ε)

private theorem isModelPhaseFunction_of_approximations
    {F : VariableFunction (VariableObject.fixed ℝ) ℝ}
    {σ : ℝ} {P : VariableObject ℕ} {δ : VariableObject ℝ}
    (hσ : 0 < σ)
    (hP : ∀ p : ℕ, ∀ᶠ i in atTop, p ≤ P i)
    (hδ : δ.IsInfinitesimal)
    (happrox : ∀ i, IsApproximateModelPhaseFunction (F i) σ (P i) (δ i)) :
    IsModelPhaseFunction F := by
  refine ⟨fun i ↦ (happrox i).1, σ, hσ, ?_⟩
  intro p
  apply (VariableFunction.isChoicewiseInfinitesimal_iff_forall_pos_uniform
    (VariableObject.fixed phaseInterval)
    (fun _ ↦ ⟨1, by simp [phaseInterval]⟩)
    (modelPhaseError F σ p)).2
  intro ε hε
  have hδsmall :=
    (VariableObject.isInfinitesimal_iff_forall_pos δ).1 hδ ε hε
  filter_upwards [hP p, hδsmall] with i hip hiδ
  intro u
  have herror := (happrox i).2 p hip u
  rw [Real.norm_eq_abs] at hiδ
  exact lt_of_le_of_lt herror ((le_abs_self (δ i)).trans_lt hiδ)

private theorem isExponentPairEstimate_of_nonAsymptotic
    {k l : ℝ} (hbound : IsExponentPairEstimateNonAsymptotic k l) :
    IsExponentPairEstimate k l := by
  intro N T F a b hN hNT hTunbounded hF hab ε hε
  rcases hF with ⟨hphase, σ, hσ, herror⟩
  obtain ⟨δ, hδ, P, hP, C, hC, hfixed⟩ :=
    hbound ε hε σ hσ
  have hTC : ∀ᶠ i in atTop, C ≤ T i := by
    have hnorm :=
      (VariableObject.isUnbounded_iff_forall_eventually_norm_ge T).1 hTunbounded C
    filter_upwards [hnorm, hNT] with i hi hiNT
    simpa [Real.norm_eq_abs, abs_of_nonneg
      (zero_le_one.trans ((hN i).trans hiNT))] using hi
  have happrox :=
    (IsModelPhaseFunctionWith.mk hphase herror).eventually_isApproximate P hδ
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hTC, happrox, hNT] with i hiT hiF hiNT
  have hratioNonneg : 0 ≤ T i / N i :=
    div_nonneg (zero_le_one.trans ((hN i).trans hiNT))
      (zero_le_one.trans (hN i))
  simpa only [exponentialSum_apply, Real.norm_eq_abs, mul_assoc,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hratioNonneg _)
      (Real.rpow_nonneg (zero_le_one.trans (hN i)) _))] using
    hfixed (T i) (N i) (F i) (a i) (b i)
      ⟨hiT, hN i, hiNT, hiF, (hab i).1, (hab i).2⟩

private theorem nonAsymptotic_of_isExponentPairEstimate
    {k l : ℝ} (hbound : IsExponentPairEstimate k l) :
    IsExponentPairEstimateNonAsymptotic k l := by
  intro ε hε σ hσ
  by_contra hfailure
  push Not at hfailure
  let δ : VariableObject ℝ := fun i ↦ 1 / ((i : ℝ) + 1)
  let P : VariableObject ℕ := fun i ↦ i + 1
  let C : VariableObject ℝ := fun i ↦ (i : ℝ) + 3
  have hδpos : ∀ i, 0 < δ i := fun i ↦ by
    dsimp [δ]
    positivity
  have hPone : ∀ i, 1 ≤ P i := fun i ↦ by
    dsimp [P]
    omega
  have hCone : ∀ i, 1 ≤ C i := fun i ↦ by
    dsimp [C]
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  choose T N F a b hdata using fun i ↦
    hfailure (δ i) (hδpos i) (P i) (hPone i) (C i) (hCone i)
  have hCT : ∀ i, C i ≤ T i :=
    fun i ↦ (hdata i).1.threshold_le_param
  have hNone : ∀ i, 1 ≤ N i :=
    fun i ↦ (hdata i).1.one_le_scale
  have hNT : ∀ i, N i ≤ T i :=
    fun i ↦ (hdata i).1.scale_le_param
  have happrox : ∀ i,
      IsApproximateModelPhaseFunction (F i) σ (P i) (δ i) :=
    fun i ↦ (hdata i).1.isApproximateModelPhase
  have ha : ∀ i, N i ≤ (a i : ℝ) :=
    fun i ↦ (hdata i).1.scale_le_start
  have hb : ∀ i, (b i : ℝ) ≤ 2 * N i :=
    fun i ↦ (hdata i).1.end_le_two_mul_scale
  have hviolate : ∀ i,
      C i * (T i / N i) ^ (k + ε) * N i ^ (l + ε) <
        ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖ :=
    fun i ↦ (hdata i).2
  have hTone : ∀ i, 1 ≤ T i :=
    fun i ↦ (hNone i).trans (hNT i)
  have hTunbounded : VariableObject.IsUnbounded T := by
    apply (VariableObject.isUnbounded_iff_forall_eventually_norm_ge T).2
    intro D
    obtain ⟨j : ℕ, hj : D ≤ (j : ℝ)⟩ := exists_nat_ge D
    filter_upwards [eventually_ge_atTop j] with i hi
    rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans (hTone i))]
    calc
      D ≤ (j : ℝ) := hj
      _ ≤ (i : ℝ) := by exact_mod_cast hi
      _ ≤ C i := by dsimp [C]; linarith
      _ ≤ T i := hCT i
  have hδinfinitesimal : δ.IsInfinitesimal := by
    rw [VariableObject.IsInfinitesimal]
    have hlim : Tendsto (fun i : ℕ ↦ 1 / ((i : ℝ) + 1))
        atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    convert hlim using 1
    ext i
    rw [Real.norm_eq_abs, abs_of_pos (hδpos i)]
  have hPtop : ∀ p : ℕ, ∀ᶠ i in atTop, p ≤ P i := by
    intro p
    filter_upwards [eventually_ge_atTop p] with i hi
    dsimp [P]
    omega
  have hF : IsModelPhaseFunction F :=
    isModelPhaseFunction_of_approximations hσ hPtop
      hδinfinitesimal happrox
  have hasymptotic :=
    hbound N T F a b hNone (Filter.Eventually.of_forall hNT) hTunbounded hF
      (fun i ↦ ⟨ha i, hb i⟩) (ε / 2) (by linarith)
  obtain ⟨K, hK⟩ := hasymptotic.bound
  have hCK : ∀ᶠ i in atTop, K ≤ C i := by
    obtain ⟨j : ℕ, hj : K ≤ (j : ℝ)⟩ := exists_nat_ge K
    filter_upwards [eventually_ge_atTop j] with i hi
    calc
      K ≤ (j : ℝ) := hj
      _ ≤ (i : ℝ) := by exact_mod_cast hi
      _ ≤ C i := by dsimp [C]; linarith
  obtain ⟨i, hiK, hiCK⟩ := (hK.and hCK).exists
  have hratioOne : 1 ≤ T i / N i := by
    exact (le_div_iff₀ (zero_lt_one.trans_le (hNone i))).2 (by simpa using hNT i)
  have hratioNonneg : 0 ≤ T i / N i := zero_le_one.trans hratioOne
  have hnorm :
      ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖ ≤
        K * ((T i / N i) ^ (k + ε / 2) * N i ^ (l + ε / 2)) := by
    simpa only [exponentialSum_apply, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hratioNonneg _)
        (Real.rpow_nonneg (zero_le_one.trans (hNone i)) _))] using hiK
  have hdominated :
      ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖ ≤
        C i * (T i / N i) ^ (k + ε) * N i ^ (l + ε) := by
    calc
      _ ≤ K * ((T i / N i) ^ (k + ε / 2) *
          N i ^ (l + ε / 2)) := hnorm
      _ ≤ C i * ((T i / N i) ^ (k + ε / 2) *
          N i ^ (l + ε / 2)) := by
        exact mul_le_mul_of_nonneg_right hiCK
          (mul_nonneg (Real.rpow_nonneg hratioNonneg _)
            (Real.rpow_nonneg (zero_le_one.trans (hNone i)) _))
      _ ≤ C i * ((T i / N i) ^ (k + ε) * N i ^ (l + ε)) := by
        apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (hCone i))
        apply mul_le_mul
        · exact Real.rpow_le_rpow_of_exponent_le hratioOne (by linarith)
        · exact Real.rpow_le_rpow_of_exponent_le (hNone i) (by linarith)
        · exact Real.rpow_nonneg (zero_le_one.trans (hNone i)) _
        · exact Real.rpow_nonneg hratioNonneg _
      _ = C i * (T i / N i) ^ (k + ε) * N i ^ (l + ε) := by ring
  exact (not_lt_of_ge hdominated) (hviolate i)

/-- The direct asymptotic model-phase definition and its fixed-parameter
epsilon--delta formulation are equivalent. -/
theorem isExponentPairEstimate_iff_nonAsymptotic {k l : ℝ} :
    IsExponentPairEstimate k l ↔
      IsExponentPairEstimateNonAsymptotic k l :=
  ⟨nonAsymptotic_of_isExponentPairEstimate,
    isExponentPairEstimate_of_nonAsymptotic⟩

/-- The paper's analytic definition of an exponent pair: triangle membership
plus the uniform model-phase exponential-sum estimate. -/
def ExponentPair (k l : ℝ) : Prop :=
  InExponentPairTriangle k l ∧ IsExponentPairEstimate k l

theorem ExponentPair.inTriangle {k l : ℝ} (h : ExponentPair k l) :
    InExponentPairTriangle k l :=
  h.1

theorem ExponentPair.estimate {k l : ℝ} (h : ExponentPair k l) :
    IsExponentPairEstimate k l :=
  h.2

end TaoTrudgianYang2025
