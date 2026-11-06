module
public import NearlyMinimax.MixtureRisk
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Data.Nat.Choose.Bounds
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
theorem paper_score_to_risk {Α : Type*} [MeasurableSpace Α] {d n : ℕ}
    (C : ModelConstants d) (σ : ℝ → Measure Α)
    (L : ℝ → Kernel Α (Fin n → Observation d))
    (θ : ℝ → Α → RegressionParameter d) (V : ℝ → ℝ)
    (R : ℝ → (Fin n → Observation d) → ℝ) (δ ε : ℝ) (hδ : 0 ≤ δ)
    (hσ : ∀ t ∈ Icc 0 δ, IsProbabilityMeasure (σ t))
    (hLprob : ∀ t ∈ Icc 0 δ, IsMarkovKernel (L t))
    (hL : ∀ t ∈ Icc 0 δ, ∀ a, L t a = sampleLaw (θ t a) n)
    (hVθ : ∀ t ∈ Icc 0 δ, ∀ a, (θ t a).variance = V t)
    (hV : ∀ t ∈ Icc 0 δ, V t ∈ Icc C.varianceLower (effectiveVarianceUpper C))
    (bad : ℝ → Set Α) (hbad : ∀ t ∈ Icc 0 δ, MeasurableSet (bad t))
    (hlegal : ∀ t ∈ Icc 0 δ, ∀ a ∉ bad t, Admissible C (θ t a))
    (hmass : ∀ t ∈ Icc 0 δ, (σ t).real (bad t) ≤ ε)
    (hR : ∀ᵐ t ∂volume, t ∈ Icc 0 δ → MemLp (R t) 2 (L t ∘ₘ σ t))
    (hcenter : ∀ᵐ t ∂volume, t ∈ Icc 0 δ →
      (∫ x, R t x ∂(L t ∘ₘ σ t)) = 0)
    (hAC : ∀ T : BoundedEstimator C n, AbsolutelyContinuousOnInterval
      (fun t => ∫ x, T.val.val x ∂(L t ∘ₘ σ t)) 0 δ)
    (hderiv : ∀ T : BoundedEstimator C n, ∀ᵐ t ∂volume, t ∈ Icc 0 δ →
      HasDerivAt (fun u => ∫ x, T.val.val x ∂(L u ∘ₘ σ u))
        (∫ x, T.val.val x * R t x ∂(L t ∘ₘ σ t)) t)
    (hscoreInt : IntervalIntegrable
      (fun t => Real.sqrt (∫ x, (R t x) ^ 2 ∂(L t ∘ₘ σ t))) volume 0 δ) :
    ENNReal.ofReal ((V δ - V 0) ^ 2 /
      (2 + ∫ t in ↑0..δ, Real.sqrt (∫ x, (R t x) ^ 2 ∂(L t ∘ₘ σ t))) ^ 2
      - (effectiveVarianceUpper C - C.varianceLower) ^ 2 * ε) ≤ minimaxRisk C n := by
  let P (t : ℝ) := L t ∘ₘ σ t
  have hprob (t : ℝ) (ht : t ∈ Icc 0 δ) : IsProbabilityMeasure (P t) := by
    let _ := hσ t ht
    let _ := hLprob t ht
    dsimp only [P]
    infer_instance
  rw [minimaxRisk_eq_inf_bounded]
  apply le_iInf
  intro T
  let risk := worstCaseRisk C T.val
  let D := effectiveVarianceUpper C - C.varianceLower
  let r := Real.sqrt (risk.toReal + D ^ 2 * ε)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrEq : r ^ 2 = risk.toReal + D ^ 2 * ε :=
    Real.sq_sqrt (add_nonneg ENNReal.toReal_nonneg (mul_nonneg (sq_nonneg _) ((measureReal_nonneg).trans (hmass 0 ⟨le_rfl, hδ⟩))))
  have hTrisk (t : ℝ) (ht : t ∈ Icc 0 δ) :
      (∫ x, (T.val.val x - V t) ^ 2 ∂P t) ≤ r ^ 2 := by
    let _ := hσ t ht
    let _ := hLprob t ht
    rw [hrEq]
    exact boundedEstimator_mixture_risk_le_of_exceptional_set C T (σ t) (L t) (θ t) (V t) ε
      (hL t ht) (hVθ t ht) (hV t ht) (bad t) (hbad t ht) (hlegal t ht) (hmass t ht)
  have hT (t : ℝ) (ht : t ∈ Icc 0 δ) : MemLp T.val.val 2 (P t) := by
    let _ := hprob t ht
    apply MemLp.of_bound T.val.property.aestronglyMeasurable (effectiveVarianceUpper C)
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (C.varianceLower_pos.le.trans (T.property z).1)]
    exact (T.property z).2
  have h_probability_absolutelyContinuous_score_path_risk_lower_bound : (V δ - V 0) ^ 2 /
      (2 + ∫ t in ↑0..δ, Real.sqrt (∫ x, (R t x) ^ 2 ∂P t)) ^ 2
      - D ^ 2 * ε ≤ risk.toReal := by
    have hAC : AbsolutelyContinuousOnInterval (fun t => ∫ x, T.val.val x ∂P t) 0 δ := hAC T
    have hderiv : ∀ᵐ t ∂volume, t ∈ Icc 0 δ →
      HasDerivAt (fun u => ∫ x, T.val.val x ∂P u) (∫ x, T.val.val x * R t x ∂P t) t := hderiv T
    have h_probability_absolutelyContinuous_score_path_separation_le : |V δ - V 0| ≤
        (2 + ∫ t in ↑0..δ, Real.sqrt (∫ x, (R t x) ^ 2 ∂P t)) * r := by
      apply absolutelyContinuous_path_separation_le hδ hAC hscoreInt
      · filter_upwards [hR, hcenter, hderiv] with t hRt hct hdt ht
        let _ := hprob t ht
        rw [(hdt ht).deriv]
        exact probability_score_bound (P t) T.val.val (R t) (V t) r
          (hT t ht) (hRt ht) hr (hct ht) (hTrisk t ht)
      · let _ := hprob 0 ⟨le_rfl, hδ⟩
        exact probability_mean_error_le (P 0) T.val.val (V 0) r
          (hT 0 ⟨le_rfl, hδ⟩) hr (hTrisk 0 ⟨le_rfl, hδ⟩)
      · let _ := hprob δ ⟨hδ, le_rfl⟩
        exact probability_mean_error_le (P δ) T.val.val (V δ) r
          (hT δ ⟨hδ, le_rfl⟩) hr (hTrisk δ ⟨hδ, le_rfl⟩)
    simpa only [sq_abs] using
      path_risk_lower_bound (intervalIntegral.integral_nonneg_of_forall hδ (fun t => Real.sqrt_nonneg _)) hr (abs_nonneg (V δ - V 0)) (h_probability_absolutelyContinuous_score_path_separation_le) hrEq
  simpa only [P, D, risk, ENNReal.ofReal_toReal
    (boundedEstimator_worstCaseRisk_finite C T).ne] using (ENNReal.ofReal_le_ofReal (h_probability_absolutelyContinuous_score_path_risk_lower_bound))
def localScorePathLength (c B I : ℝ) : ℝ := c / (1 + B + I)
theorem localScorePathLength_pos  (hc : 0 < c)
    (hB : 0 ≤ B) (hI : 0 ≤ I) : 0 < localScorePathLength c B I := div_pos hc (by linarith only [hB, hI])
theorem localScorePathLength_energy_le  (hc : 0 ≤ c)
    (hB : 0 ≤ B) (hI : 0 ≤ I) : localScorePathLength c B I * I ≤ c := by
  rw [localScorePathLength, div_mul_eq_mul_div]
  apply (div_le_iff₀ (by linarith only [hB, hI])).mpr
  exact mul_le_mul_of_nonneg_left (by linarith only [hB]) hc
def poissonCountWeight (x : ℝ) (k : ℕ) : ℝ := x ^ k / k.factorial
theorem poissonCountWeight_nonneg  (hx : 0 ≤ x) (k ) :
    0 ≤ poissonCountWeight x k := by unfold poissonCountWeight; positivity
theorem poissonCountWeight_summable (x ) : Summable (poissonCountWeight x) :=
  Real.summable_pow_div_factorial x
theorem polynomial_count_factor_le (k r : ℕ) :
    (k : ℝ) ^ r ≤ ((2 : ℝ) ^ r) ^ k := by
  have h := pow_le_pow_left₀ (Nat.cast_nonneg k) (by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le : (k : ℝ) ≤ 2 ^ k) r
  simpa only [← pow_mul, Nat.mul_comm] using h
theorem poissonCountWeight_mono  (hx : 0 ≤ x) (hxy : x ≤ y) (k ) :
    poissonCountWeight x k ≤ poissonCountWeight y k := div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy k) (Nat.cast_nonneg _)
theorem finite_poissonCountWeight_tail_le  (hx : 0 ≤ x) (a J : ℕ) :
    (∑ j ∈ Finset.range J, poissonCountWeight x (a + j)) ≤
      Real.exp x * poissonCountWeight x a := by
  have h_poissonCountWeight_tail_le : (∑' j, poissonCountWeight x (a + j)) ≤ Real.exp x * poissonCountWeight x a := by
    have h_poissonCountWeight_add_le j : poissonCountWeight x (a + j) ≤ poissonCountWeight x a * poissonCountWeight x j := by
      have hfNat  :=
        Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add a j)
      have hf : a.factorial * j.factorial ≤ ((a + j).factorial : ℝ) := by
        exact_mod_cast hfNat
      have h := div_le_div_of_nonneg_left (pow_nonneg hx (a + j))
        (mul_pos (by exact_mod_cast Nat.factorial_pos a) (by exact_mod_cast Nat.factorial_pos j)) hf
      simpa only [poissonCountWeight, pow_add, div_mul_div_comm] using h
    calc
      _ ≤ ∑' j, poissonCountWeight x a * poissonCountWeight x j :=
        ((poissonCountWeight_summable x).comp_injective (fun _ _ h => Nat.add_left_cancel h)).tsum_le_tsum h_poissonCountWeight_add_le ((poissonCountWeight_summable x).mul_left _)
      _ = Real.exp x * poissonCountWeight x a := by
        have h_poissonCountWeight_tsum : (∑' k, poissonCountWeight x k) = Real.exp x := by
          simpa only [poissonCountWeight, Real.exp_eq_exp_ℝ] using
            (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq
        rw [tsum_mul_left, h_poissonCountWeight_tsum, mul_comm]
  exact (((poissonCountWeight_summable x).comp_injective (fun _ _ h => Nat.add_left_cancel h)).sum_le_tsum _ (fun j _ => poissonCountWeight_nonneg hx _)).trans
    h_poissonCountWeight_tail_le
def aliasTailConstant (A Csharp C L : ℝ) : ℝ :=
  1 + A * Real.exp (Csharp * C) + Csharp * C * Real.exp L
theorem aliasTailConstant_ge_one {A Csharp C L : ℝ}
    (hA : 0 ≤ A) (hCs : 0 ≤ Csharp) (hC : 0 ≤ C) :
    1 ≤ aliasTailConstant A Csharp C L := by
  unfold aliasTailConstant
  have h1 : 0 ≤ A * Real.exp (Csharp * C) := by positivity
  have h2 : 0 ≤ Csharp * C * Real.exp L := by positivity
  linarith only [h1, h2]
theorem finite_alias_energy_tail_le {A P Csharp C L mu : ℝ}
    (hA : 0 ≤ A) (hP : 0 ≤ P) (hCs : 0 ≤ Csharp) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (M J : ℕ) (R : ℕ → ℝ)
    (hR : ∀ j ∈ Finset.range J, R (M + 1 + j) ≤
      A * P * Real.exp (L * M) * C ^ (M + 1 + j)) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * mu) (M + 1 + j) * R (M + 1 + j)) ≤
      aliasTailConstant A Csharp C L * P *
        poissonCountWeight (aliasTailConstant A Csharp C L * mu) (M + 1) := by
  let K := aliasTailConstant A Csharp C L
  have hK1 : 1 ≤ K := aliasTailConstant_ge_one hA hCs hC
  have hK0 : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans hK1
  have hb j (hj : j ∈ Finset.range J) :
      poissonCountWeight (Csharp * mu) (M + 1 + j) * R (M + 1 + j) ≤
      A * P * Real.exp (L * M) * poissonCountWeight (Csharp * C * mu) (M + 1 + j) := by
    have h := mul_le_mul_of_nonneg_left (hR j hj)
      (poissonCountWeight_nonneg (mul_nonneg hCs hmu) (M + 1 + j))
    convert h using 1 <;> unfold poissonCountWeight <;> rw [mul_pow, mul_pow] <;> ring
  have hs := Finset.sum_le_sum hb
  rw [← Finset.mul_sum] at hs
  have ht := finite_poissonCountWeight_tail_le (by positivity : 0 ≤ Csharp * C * mu) (M + 1) J
  have hm := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ A * P * Real.exp (L * M))
  have hexp : Real.exp (Csharp * C * mu) ≤ Real.exp (Csharp * C) :=
    Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hCs hC, hmu1])
  have h_aliasTailConstant_ge_base : Csharp * C * Real.exp L ≤ aliasTailConstant A Csharp C L := by
    unfold aliasTailConstant
    have h : 0 ≤ A * Real.exp (Csharp * C) := by positivity
    linarith only [h]
  have hbase : Csharp * C * Real.exp L * mu ≤ K * mu :=
    mul_le_mul_of_nonneg_right h_aliasTailConstant_ge_base hmu
  have h_poissonCountWeight_exp_absorption {x : ℝ} (hx : 0 ≤ x) : Real.exp (L * M) * poissonCountWeight x (M + 1) ≤
      poissonCountWeight (x * Real.exp L) (M + 1) := by
    have he : Real.exp (L * M) ≤ Real.exp (L * (M + 1)) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hL]
    have h := mul_le_mul_of_nonneg_right he (poissonCountWeight_nonneg hx (M + 1))
    have heq : Real.exp (L * (↑M + 1)) = Real.exp L ^ (M + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [heq] at h
    simpa only [poissonCountWeight, mul_pow, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  calc
    _ ≤ A * P * Real.exp (L * M) *
        (Real.exp (Csharp * C * mu) * poissonCountWeight (Csharp * C * mu) (M + 1)) := hs.trans hm
    _ ≤ A * P * Real.exp (L * M) *
        (Real.exp (Csharp * C) * poissonCountWeight (Csharp * C * mu) (M + 1)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hexp (poissonCountWeight_nonneg (by positivity) _)) (by positivity)
    _ = A * Real.exp (Csharp * C) * P *
        (Real.exp (L * M) * poissonCountWeight (Csharp * C * mu) (M + 1)) := by ring
    _ ≤ A * Real.exp (Csharp * C) * P *
        poissonCountWeight ((Csharp * C * mu) * Real.exp L) (M + 1) :=
      mul_le_mul_of_nonneg_left (h_poissonCountWeight_exp_absorption (by positivity)) (by positivity)
    _ ≤ K * P * poissonCountWeight (K * mu) (M + 1) := by
      have h_aliasTailConstant_ge_prefactor : A * Real.exp (Csharp * C) ≤ aliasTailConstant A Csharp C L := by
        unfold aliasTailConstant
        have h : 0 ≤ Csharp * C * Real.exp L := by positivity
        linarith only [h]
      apply mul_le_mul
        (mul_le_mul_of_nonneg_right h_aliasTailConstant_ge_prefactor hP)
        (poissonCountWeight_mono (by positivity) (by nlinarith only [hbase]) _)
        (poissonCountWeight_nonneg (by positivity) _)
        (mul_nonneg hK0 hP)
    _ = _ := rfl
end NearlyMinimax
