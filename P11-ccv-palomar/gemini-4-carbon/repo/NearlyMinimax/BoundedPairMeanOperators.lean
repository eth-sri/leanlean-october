module

public import Mathlib
public import NearlyMinimax.CellProjection
public import NearlyMinimax.CoordinatePartialBridge
public import NearlyMinimax.Model
public import NearlyMinimax.ModelRegularity
public import NearlyMinimax.Moments
public import NearlyMinimax.Risk
public import RoughRegime.HolderTaylorApproximation

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace

-- ============================================================================
-- 1. Order-Two U-Statistic & Pair Counting (`NearlyMinimax.PairUStatistic`)
-- ============================================================================

namespace NearlyMinimax.PairUStatistic
section UStatistic
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def orderedPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 ≠ p.2

theorem sum_orderedPairs {n : ℕ} (f : Fin n × Fin n → ℝ) :
    (∑ p ∈ orderedPairs n, f p) = ∑ i, ∑ j with j ≠ i, f (i, j) := by
  simp only [orderedPairs, Finset.sum_filter, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by simp only [ne_comm]

private lemma orderedPairs_card (n : ℕ) : (orderedPairs n).card = n * (n - 1) := by
  have he := sum_orderedPairs (n := n) fun _ => (1 : ℝ)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
    show ∀ i : Fin n, Finset.univ.filter (fun j : Fin n => j ≠ i) = Finset.univ.erase i from fun i => by ext; simp,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at he
  exact_mod_cast he

private lemma orderedPairs_first_count {n : ℕ} (i : Fin n) :
    (∑ p ∈ orderedPairs n, if p.1 = i then (1 : ℝ) else 0) = (n - 1 : ℕ) := by
  rw [sum_orderedPairs, Finset.sum_eq_single i]
  · rw [show Finset.univ.filter (fun k : Fin n => k ≠ i) = Finset.univ.erase i by ext; simp]; simp
  · intro j _ hji; simp [hji]
  · simp

private lemma orderedPairs_second_count {n : ℕ} (i : Fin n) :
    (∑ p ∈ orderedPairs n, if p.2 = i then (1 : ℝ) else 0) = (n - 1 : ℕ) := by
  refine (Finset.sum_bij (fun p _ => p.swap) ?_ (fun _ _ _ _ hab => Prod.swap_injective hab) ?_ (fun _ _ => rfl)).symm.trans
    (orderedPairs_first_count i)
  · intro p hp; simpa only [orderedPairs, Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap, ne_comm] using hp
  · intro b hb; exact ⟨b.swap, by simpa only [orderedPairs, Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap, ne_comm] using hb, by simp⟩

def overlapMajorant {n : ℕ} (p q : Fin n × Fin n) (A B : ℝ) : ℝ :=
  B * ((if q.1 = p.1 then 1 else 0) + (if q.2 = p.1 then 1 else 0) +
    (if q.1 = p.2 then 1 else 0) + (if q.2 = p.2 then 1 else 0)) +
  A * ((if q = p then 1 else 0) + (if q = p.swap then 1 else 0))

section KernelEstimates
variable {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
variable {ν : Measure Ω} {μ : Measure E} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] in
private lemma integral_comp_mp (f : Ω → E) (hf : MeasurePreserving f ν μ) (g : E → ℝ) (hg : Measurable g) :
    (∫ x, g (f x) ∂ν) = ∫ y, g y ∂μ := by
  rw [← hf.map_eq]; exact (integral_map hf.aemeasurable hg.aestronglyMeasurable).symm

omit [IsProbabilityMeasure μ] in
theorem pair_measurePreserving (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ) {i j : ι} (hij : i ≠ j) :
    MeasurePreserving (fun x => (X i x, X j x)) ν (μ.prod μ) :=
  ⟨(hX i).measurable.prodMk (hX j).measurable, by
    rw [(hind.indepFun hij).map_prod_eq_prod_map_map (hX i).aemeasurable (hX j).aemeasurable,
      (hX i).map_eq, (hX j).map_eq]⟩

private lemma kernel_pair_memLp (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ)) {i j : ι} (hij : i ≠ j) :
    MemLp (fun x => K (X i x, X j x)) 2 ν :=
  hK.comp_measurePreserving (pair_measurePreserving X hind hX hij)

private lemma kernel_pair_integral (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hK : Measurable K) {i j : ι} (hij : i ≠ j) :
    (∫ x, K (X i x, X j x) ∂ν) = ∫ z, K z ∂μ.prod μ :=
  integral_comp_mp _ (pair_measurePreserving X hind hX hij) K hK

def rowIntegral (K : E × E → ℝ) (x : E) : ℝ := ∫ y, K (x, y) ∂μ

private lemma shared_product_integrable {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    Integrable (fun z : (E × E) × E => K z.1 * K (z.1.1, z.2)) ((μ.prod μ).prod μ) :=
  (hK.comp_measurePreserving measurePreserving_fst).integrable_mul
    (hK.comp_measurePreserving (measurePreserving_fst.prod (MeasurePreserving.id μ)))

theorem rowIntegral_sq_integrable {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    Integrable (fun x => rowIntegral (μ := μ) K x ^ 2) μ := by
  have hi := (shared_product_integrable hK).integral_prod_left
  simp only [integral_const_mul] at hi
  simpa only [integral_mul_const, rowIntegral, pow_two] using hi.integral_prod_left

private lemma kernel_shared_product_integral (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ))
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∫ x, K (X i x, X j x) * K (X i x, X k x) ∂ν) = ∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ := by
  have htr : MeasurePreserving (fun x => ((X i x, X j x), X k x)) ν ((μ.prod μ).prod μ) :=
    ⟨((hX i).measurable.prodMk (hX j).measurable).prodMk (hX k).measurable, by
      rw [(hind.indepFun_prodMk (fun i => (hX i).measurable) i j k hik hjk).map_prod_eq_prod_map_map
          ((hX i).aemeasurable.prodMk (hX j).aemeasurable) (hX k).aemeasurable,
        (pair_measurePreserving X hind hX hij).map_eq, (hX k).map_eq]⟩
  rw [integral_comp_mp _ htr (fun z : (E × E) × E => K z.1 * K (z.1.1, z.2))
      ((hmK.comp measurable_fst).mul (hmK.comp (measurable_fst.fst.prodMk measurable_snd))),
    integral_prod _ (shared_product_integrable hK)]
  simp only [integral_const_mul]
  have hrp : Integrable (fun z : E × E => K z * rowIntegral (μ := μ) K z.1) (μ.prod μ) := by
    simpa only [integral_const_mul, rowIntegral] using (shared_product_integrable hK).integral_prod_left
  change (∫ z : E × E, K z * rowIntegral (μ := μ) K z.1 ∂μ.prod μ) = _
  rw [integral_prod _ hrp]; simp only [integral_mul_const, rowIntegral, pow_two]

def pairAverage (n : ℕ) (K : E × E → ℝ) (x : Fin n → E) : ℝ :=
  ((n : ℝ) * (n - 1 : ℕ))⁻¹ * ∑ i, ∑ j with j ≠ i, K (x i, x j)

theorem pairAverage_eq_orderedPairs {n : ℕ} (K : E × E → ℝ) (x : Fin n → E) :
    pairAverage n K x = ((n : ℝ) * (n - 1 : ℕ))⁻¹ * ∑ p ∈ orderedPairs n, K (x p.1, x p.2) := by
  rw [pairAverage, sum_orderedPairs]

theorem pairAverage_memLp_two {n : ℕ} (X : Fin n → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    MemLp (fun x => pairAverage n K (fun i => X i x)) 2 ν := by
  simp only [pairAverage_eq_orderedPairs]
  exact (memLp_finsetSum _ fun p hp => kernel_pair_memLp X hind hX hK (Finset.mem_filter.mp hp).2).const_mul _

theorem pairAverage_integral {n : ℕ} (hn : 2 ≤ n) (X : Fin n → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ)) :
    (∫ x, pairAverage n K (fun i => X i x) ∂ν) = ∫ z, K z ∂μ.prod μ := by
  simp only [pairAverage_eq_orderedPairs]
  rw [integral_const_mul, integral_finsetSum]
  · have he : (∑ p ∈ orderedPairs n, ∫ x, K (X p.1 x, X p.2 x) ∂ν) =
        ∑ _p ∈ orderedPairs n, ∫ z, K z ∂μ.prod μ :=
      Finset.sum_congr rfl fun p hp => kernel_pair_integral X hind hX hmK (Finset.mem_filter.mp hp).2
    rw [he, Finset.sum_const, orderedPairs_card, nsmul_eq_mul, Nat.cast_mul]
    have hN : (n : ℝ) * (n - 1 : ℕ) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast (by omega : n ≠ 0)) (by exact_mod_cast (by omega : n - 1 ≠ 0))
    exact inv_mul_cancel_left₀ hN _
  · exact fun p hp => (kernel_pair_memLp X hind hX hK (Finset.mem_filter.mp hp).2).integrable (by norm_num)

theorem pairAverage_centered_sq_le {n : ℕ} (hn : 2 ≤ n) (X : Fin n → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ))
    (hsym : ∀ x y, K (x, y) = K (y, x)) :
    (∫ x, (pairAverage n K (fun i => X i x) - ∫ z, K z ∂μ.prod μ) ^ 2 ∂ν) ≤
      4 / (n : ℝ) * (∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ) +
      2 / ((n : ℝ) * (n - 1 : ℕ)) * (∫ z, K z ^ 2 ∂μ.prod μ) := by
  rw [← pairAverage_integral hn X hind hX hmK hK,
    ← variance_eq_integral (pairAverage_memLp_two X hind hX hK).aemeasurable]
  let A := ∫ z, K z ^ 2 ∂μ.prod μ
  let B := ∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ
  have hA : 0 ≤ A := integral_nonneg fun _ => sq_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun _ => sq_nonneg _
  have hc : 0 ≤ (∫ z, K z ∂μ.prod μ) ^ 2 := sq_nonneg _
  have hcov {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) :
      covariance (fun x => K (X i x, X j x)) (fun x => K (X k x, X l x)) ν ≤
        overlapMajorant (i, j) (k, l) A B := by
    rw [covariance_eq_sub (kernel_pair_memLp X hind hX hK hij) (kernel_pair_memLp X hind hX hK hkl)]
    simp only [Pi.mul_apply, kernel_pair_integral X hind hX hmK hij,
      kernel_pair_integral X hind hX hmK hkl, ← pow_two]
    have hprod : (∫ x, K (X i x, X j x) * K (X k x, X l x) ∂ν) =
        if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then A
        else if i = k ∨ i = l ∨ j = k ∨ j = l then B else (∫ z, K z ∂μ.prod μ) ^ 2 := by
      by_cases hik : i = k
      · subst k; by_cases hjl : j = l
        · subst l; simpa only [true_and, true_or, ite_true, ← pow_two, A] using kernel_pair_integral X hind hX (hmK.pow_const 2) hij
        · simp only [true_and, hjl, Ne.symm hij, false_or, and_false, ite_false, true_or, ite_true]
          exact kernel_shared_product_integral X hind hX hmK hK hij hkl hjl
      · by_cases hil : i = l
        · subst l; by_cases hjk : j = k
          · subst k; simp only [and_true, or_true, ite_true]
            simpa only [hsym (X j _) (X i _), ← pow_two, A] using kernel_pair_integral X hind hX (hmK.pow_const 2) hij
          · simp only [hik, false_and, true_and, hjk, or_false, ite_false, true_or, false_or, ite_true]
            simpa only [hsym (X k _) (X i _)] using kernel_shared_product_integral X hind hX hmK hK hij hik hjk
        · by_cases hjk : j = k
          · subst k; simp only [hik, false_and, hil, false_or, true_or, ite_false, ite_true]
            simpa only [hsym (X i _) (X j _)] using kernel_shared_product_integral X hind hX hmK hK (Ne.symm hij) hkl hil
          · by_cases hjl : j = l
            · subst l; simp only [hik, false_and, hil, hjk, false_or, false_and, ite_false, or_true, ite_true]
              simpa only [hsym (X i _) (X j _), hsym (X k _) (X j _)] using
                kernel_shared_product_integral X hind hX hmK hK (Ne.symm hij) (Ne.symm hkl) hik
            · simp only [hik, hil, hjk, hjl, false_and, false_or, ite_false]
              have hd := (hind.indepFun_prodMk_prodMk (fun m => (hX m).measurable) i j k l hik hil hjk hjl).comp hmK hmK
              have he := hd.integral_fun_mul_eq_mul_integral
                (hmK.comp ((hX i).measurable.prodMk (hX j).measurable)).aestronglyMeasurable
                (hmK.comp ((hX k).measurable.prodMk (hX l).measurable)).aestronglyMeasurable
              simp only [Function.comp_def] at he
              rw [he, kernel_pair_integral X hind hX hmK hij, kernel_pair_integral X hind hX hmK hkl, pow_two]
    rw [hprod]; unfold overlapMajorant
    by_cases hik : i = k <;> by_cases hil : i = l <;> by_cases hjk : j = k <;> by_cases hjl : j = l <;>
      subst_vars <;>
      simp_all only [Prod.mk.injEq, Prod.swap, ne_eq, eq_comm, not_true_eq_false,
        true_and, and_true, or_true, true_or, false_and, and_false, false_or, or_false,
        ite_true, ite_false, zero_add, add_zero, mul_zero, mul_one, sub_self] <;> nlinarith
  let Y : (Fin n × Fin n) → Ω → ℝ := fun p x => K (X p.1 x, X p.2 x)
  have hY : ∀ p ∈ orderedPairs n, MemLp (Y p) 2 ν :=
    fun p hp => kernel_pair_memLp X hind hX hK (Finset.mem_filter.mp hp).2
  simp only [pairAverage_eq_orderedPairs]
  rw [variance_const_mul, variance_fun_sum' hY]
  have hsum : (∑ p ∈ orderedPairs n, ∑ q ∈ orderedPairs n, covariance (Y p) (Y q) ν) ≤
      (n : ℝ) * (n - 1 : ℕ) * (4 * (n - 1 : ℕ) * B + 2 * A) := by
    calc
      _ ≤ ∑ p ∈ orderedPairs n, ∑ q ∈ orderedPairs n, overlapMajorant p q A B :=
        Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq =>
          hcov (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
      _ = ∑ _p ∈ orderedPairs n, (4 * (n - 1 : ℕ) * B + 2 * A) := Finset.sum_congr rfl fun p hp => by
        have hps : p.swap ∈ orderedPairs n := by
          simpa only [orderedPairs, Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap, ne_comm] using hp
        have h1 {r : Fin n × Fin n} (hr : r ∈ orderedPairs n) :
            (∑ q ∈ orderedPairs n, if q = r then (1 : ℝ) else 0) = 1 := by simp [hr]
        simp only [overlapMajorant, Finset.sum_add_distrib, ← Finset.mul_sum,
          orderedPairs_first_count, orderedPairs_second_count, h1 hp, h1 hps]
        ring
      _ = _ := by simp only [Finset.sum_const, orderedPairs_card, nsmul_eq_mul, Nat.cast_mul]
  refine (mul_le_mul_of_nonneg_left hsum (sq_nonneg _)).trans_eq ?_
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hm0 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : n - 1 ≠ 0)
  dsimp [A, B]; field_simp

theorem pairAverage_measurable (n : ℕ) {K : E × E → ℝ} (hmK : Measurable K) :
    Measurable (pairAverage n K) :=
  (Finset.measurable_fun_sum _ fun i _ => Finset.measurable_fun_sum _ fun j _ =>
    hmK.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))).const_mul _

end KernelEstimates
end UStatistic
end NearlyMinimax.PairUStatistic

-- ============================================================================
-- 2. Conditional Sampling Law & Observation Moments (`NearlyMinimax`)
-- ============================================================================

namespace NearlyMinimax
section ConditionalAndObservationMoments
set_option backward.isDefEq.respectTransparency false

def finiteProductKernel {ι α β : Type*} [Fintype ι] [MeasurableSpace α] [MeasurableSpace β]
    (κ : ι → Kernel α β) [∀ i, IsMarkovKernel (κ i)] : Kernel (ι → α) (ι → β) where
  toFun x := Measure.pi fun i => κ i (x i)
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    induction s, hs using MeasurableSpace.induction_on_inter generateFrom_pi.symm isPiSystem_pi with
    | empty => simp only [measure_empty]; exact measurable_const
    | basic s hs =>
      obtain ⟨t, ht, rfl⟩ := hs; simp_rw [Measure.pi_pi]
      exact Finset.measurable_fun_prod Finset.univ fun i _ =>
        (Kernel.measurable_coe (κ i) (ht i (mem_univ i))).comp (measurable_pi_apply i)
    | compl s hs ih => simp_rw [measure_compl hs (measure_ne_top _ _), measure_univ]; exact measurable_const.sub ih
    | iUnion f hd hf ih => simp_rw [measure_iUnion hd hf]; exact Measurable.tsum ih
    | x_4 => infer_instance

instance finiteProductKernel_markov {ι α β : Type*} [Fintype ι] [MeasurableSpace α] [MeasurableSpace β]
    (κ : ι → Kernel α β) [∀ i, IsMarkovKernel (κ i)] : IsMarkovKernel (finiteProductKernel κ) :=
  ⟨fun x => inferInstanceAs (IsProbabilityMeasure (Measure.pi fun i => κ i (x i)))⟩

def pairVectors {ι α β : Type*} (z : (ι → α) × (ι → β)) : ι → α × β := fun i => (z.1 i, z.2 i)

private lemma pairVectors_measurable {ι α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (pairVectors (ι := ι) (α := α) (β := β)) :=
  Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)

private lemma pi_compProd_eq_map_pairVectors {ι α β : Type*} [Fintype ι] [MeasurableSpace α] [MeasurableSpace β]
    (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (κ : ι → Kernel α β) [∀ i, IsMarkovKernel (κ i)] :
    Measure.pi (fun i => (μ i).compProd (κ i)) =
      ((Measure.pi μ).compProd (finiteProductKernel κ)).map pairVectors := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply pairVectors_measurable (MeasurableSet.univ_pi hs),
    Measure.compProd_apply (pairVectors_measurable (MeasurableSet.univ_pi hs))]
  simp_rw [show ∀ x : ι → α, Prod.mk x ⁻¹' (pairVectors ⁻¹' Set.univ.pi s) =
      Set.univ.pi fun i => Prod.mk (x i) ⁻¹' s i from fun x => by ext; simp [pairVectors, Set.mem_pi],
    show ∀ x, finiteProductKernel κ x = Measure.pi fun i => κ i (x i) from fun _ => rfl, Measure.pi_pi]
  have hprod (f : ι → α → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
      (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ a, f i a ∂μ i := by
    rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ (fun i (x : ι → α) => f i (x i))
      (iIndepFun_pi fun i => (hf i).aemeasurable) fun i => (hf i).comp (measurable_pi_apply i)]
    exact Finset.prod_congr rfl fun i _ =>
      (lintegral_map' (hf i).aemeasurable (measurable_pi_apply i).aemeasurable).symm.trans
        (by rw [(measurePreserving_eval μ i).map_eq])
  rw [hprod (fun i a => κ i a (Prod.mk a ⁻¹' s i)) fun i => Kernel.measurable_kernel_prodMk_left (hs i)]
  simp_rw [Measure.compProd_apply (hs _)]

def designVectorLaw {d : ℕ} (θ : RegressionParameter d) (n : ℕ) :
    Measure (Fin n → Covariate d) := Measure.pi fun _ => designLaw θ

def conditionalErrorLaw {d n : ℕ} (θ : RegressionParameter d)
    (x : Fin n → Covariate d) : Measure (Fin n → ℝ) := Measure.pi fun i => θ.errors (x i)

def conditionalErrorKernel {d : ℕ} (θ : RegressionParameter d) (n : ℕ) :
    Kernel (Fin n → Covariate d) (Fin n → ℝ) := finiteProductKernel fun _ => θ.errors

instance conditionalErrorKernel_markov {d : ℕ} (θ : RegressionParameter d) (n : ℕ) :
    IsMarkovKernel (conditionalErrorKernel θ n) := by unfold conditionalErrorKernel; infer_instance

instance conditionalErrorLaw_probability {d n : ℕ} (θ : RegressionParameter d)
    (x : Fin n → Covariate d) : IsProbabilityMeasure (conditionalErrorLaw θ x) := by
  unfold conditionalErrorLaw; infer_instance

def samplesFromDesignErrors {d n : ℕ} (θ : RegressionParameter d)
    (z : (Fin n → Covariate d) × (Fin n → ℝ)) : Fin n → Observation d :=
  fun i => (z.1 i, θ.regression (z.1 i) + z.2 i)

private lemma samplesFromDesignErrors_measurable {d n : ℕ} (θ : RegressionParameter d)
    (hf : Measurable θ.regression) : Measurable (samplesFromDesignErrors (n := n) θ) :=
  Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((hf.comp ((measurable_pi_apply i).comp measurable_fst)).add ((measurable_pi_apply i).comp measurable_snd))

private lemma sampleLaw_eq_conditional_map {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (n : ℕ) :
    sampleLaw θ n =
      ((designVectorLaw θ n).compProd (conditionalErrorKernel θ n)).map (samplesFromDesignErrors θ) := by
  let := designLaw_isProbability C θ hθ
  have hm : Measurable fun z : Covariate d × ℝ => (z.1, θ.regression z.1 + z.2) :=
    measurable_fst.prodMk ((hθ.2.1.comp measurable_fst).add measurable_snd)
  have hv : Measurable fun z : Fin n → Covariate d × ℝ => fun i => ((z i).1, θ.regression (z i).1 + (z i).2) :=
    Measurable.of_eval fun i => hm.comp (measurable_pi_apply i)
  unfold sampleLaw observationLaw
  rw [← Measure.pi_map_pi fun _ => hm.aemeasurable,
    pi_compProd_eq_map_pairVectors (ι := Fin n) (fun _ => designLaw θ) (fun _ => θ.errors),
    Measure.map_map hv pairVectors_measurable]
  rfl

theorem meanSquaredRisk_conditioning {d n : ℕ} (C : ModelConstants d)
    (T : Estimator d n) (θ : RegressionParameter d) (hθ : Admissible C θ) :
    meanSquaredRisk T θ =
      ∫⁻ x, ∫⁻ u, ENNReal.ofReal ((T.val (samplesFromDesignErrors θ (x, u)) - θ.variance) ^ 2)
        ∂conditionalErrorLaw θ x ∂designVectorLaw θ n := by
  let := designLaw_isProbability C θ hθ
  let : IsProbabilityMeasure (designVectorLaw θ n) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin n => designLaw θ))
  have hg : Measurable fun z : Fin n → Observation d => ENNReal.ofReal ((T.val z - θ.variance) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((T.property.sub measurable_const).pow_const 2)
  have hm := samplesFromDesignErrors_measurable (n := n) θ hθ.2.1
  have hgm : Measurable fun z : (Fin n → Covariate d) × (Fin n → ℝ) =>
      ENNReal.ofReal ((T.val (samplesFromDesignErrors θ z) - θ.variance) ^ 2) := hg.comp hm
  unfold meanSquaredRisk
  rw [sampleLaw_eq_conditional_map C θ hθ, lintegral_map' hg.aemeasurable hm.aemeasurable,
    Measure.lintegral_compProd hgm]
  rfl

theorem sampleLaw_integral_conditioning {d n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (g : (Fin n → Observation d) → E) (hg : Integrable g (sampleLaw θ n)) :
    (∫ z, g z ∂sampleLaw θ n) =
      ∫ x, ∫ u, g (samplesFromDesignErrors θ (x, u)) ∂conditionalErrorLaw θ x ∂designVectorLaw θ n := by
  let := designLaw_isProbability C θ hθ
  let : IsProbabilityMeasure (designVectorLaw θ n) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin n => designLaw θ))
  have hm := samplesFromDesignErrors_measurable (n := n) θ hθ.2.1
  have hmap : Integrable g (((designVectorLaw θ n).compProd (conditionalErrorKernel θ n)).map (samplesFromDesignErrors θ)) := by
    rwa [← sampleLaw_eq_conditional_map C θ hθ]
  have hcomp : Integrable (fun z => g (samplesFromDesignErrors θ z)) ((designVectorLaw θ n).compProd (conditionalErrorKernel θ n)) := by
    simpa only [Function.comp_def] using hmap.comp_measurable hm
  rw [sampleLaw_eq_conditional_map C θ hθ, integral_map hm.aemeasurable hmap.aestronglyMeasurable,
    Measure.integral_compProd hcomp]
  rfl

theorem designLaw_cube_ae {d : ℕ} (θ : RegressionParameter d) :
    ∀ᵐ x ∂designLaw θ, x ∈ unitCube d := by
  have hu : MeasurableSet (unitCube d) := by
    rw [show unitCube d = Set.univ.pi fun _ : Fin d => Set.Icc (0 : ℝ) 1 by
      ext; simp only [unitCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_Icc]]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  exact (ae_restrict_mem hu).filter_mono
    (withDensity_absolutelyContinuous (cubeVolume d) fun x => ENNReal.ofReal (θ.density x)).ae_le

theorem admissible_conditional_error_facts {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (n : ℕ) :
    ∀ᵐ x ∂designVectorLaw θ n,
      (∀ i, x i ∈ unitCube d) ∧
      (∀ i, MemLp (fun u : Fin n → ℝ => u i) 4 (conditionalErrorLaw θ x)) ∧
      iIndepFun (fun i (u : Fin n → ℝ) => u i) (conditionalErrorLaw θ x) ∧
      (∀ i, (∫ u, u i ∂conditionalErrorLaw θ x) = 0) ∧
      (∀ i, (∫ u, (u i) ^ 2 ∂conditionalErrorLaw θ x) = θ.variance) ∧
      (∀ i, (∫ u, (u i) ^ 4 ∂conditionalErrorLaw θ x) ≤ C.fourthBound) := by
  let := designLaw_isProbability C θ hθ
  have hgood := eventually_all.mpr fun i : Fin n =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => designLaw θ) (i := i)).eventually
      ((designLaw_cube_ae θ).and hθ.2.2.2.2.2.2.2)
  have hcoord (x : Fin n → Covariate d) (i : Fin n) (g : ℝ → ℝ) (hg : Measurable g) :
      (∫ u, g (u i) ∂conditionalErrorLaw θ x) = ∫ a, g a ∂θ.errors (x i) := by
    have h := integral_map (μ := Measure.pi fun j => θ.errors (x j))
      (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable
    rwa [(measurePreserving_eval (fun j => θ.errors (x j)) i).map_eq, eq_comm] at h
  filter_upwards [hgood] with x hx
  refine ⟨fun i => (hx i).1, fun i => ?_,
    iIndepFun_pi (μ := fun i => θ.errors (x i)) (X := fun _ => id) fun _ => aemeasurable_id,
    fun i => by rw [hcoord x i (fun u => u) measurable_id]; exact (hx i).2.2.2.2.1,
    fun i => by rw [hcoord x i (· ^ 2) (by fun_prop)]; exact (hx i).2.2.2.2.2.1,
    fun i => by rw [hcoord x i (· ^ 4) (by fun_prop)]; exact (hx i).2.2.2.2.2.2⟩
  have hm4 : MemLp (fun u : ℝ => u) 4 (θ.errors (x i)) := by
    refine (integrable_norm_rpow_iff (f := fun u : ℝ => u) (p := 4) aestronglyMeasurable_id (by norm_num) (by simp)).mp ?_
    convert (hx i).2.2.2.1 using 1; funext u
    norm_num only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
    calc |u| ^ (4 : ℝ) = |u| ^ (4 : ℕ) := Real.rpow_natCast _ _
         _ = u ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  simpa only [Function.comp_def, Function.eval, conditionalErrorLaw] using
    hm4.comp_measurePreserving (measurePreserving_eval (fun j => θ.errors (x j)) i)

-- Observation moments

def responseSecondBound {d : ℕ} (C : ModelConstants d) : ℝ := C.holderBound ^ 2 + C.varianceUpper
def responseFourthBound {d : ℕ} (C : ModelConstants d) : ℝ := 8 * (C.holderBound ^ 4 + C.fourthBound)

theorem responseSecondBound_pos {d : ℕ} (C : ModelConstants d) : 0 < responseSecondBound C := by
  have := C.varianceLower_pos.trans C.variance_interval; unfold responseSecondBound; positivity

theorem responseFourthBound_pos {d : ℕ} (C : ModelConstants d) : 0 < responseFourthBound C := by
  have := lt_of_le_of_lt (sq_nonneg _) C.fourth_margin; unfold responseFourthBound; positivity

theorem observationLaw_integral_conditioning {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (g : Observation d → E) (hg : Integrable g (observationLaw θ)) :
    (∫ z, g z ∂observationLaw θ) =
      ∫ x, ∫ u, g (x, θ.regression x + u) ∂θ.errors x ∂designLaw θ := by
  let := designLaw_isProbability C θ hθ
  have hm : Measurable fun z : Covariate d × ℝ => (z.1, θ.regression z.1 + z.2) :=
    measurable_fst.prodMk ((hθ.2.1.comp measurable_fst).add measurable_snd)
  have hcomp := hg.comp_measurable hm
  unfold observationLaw at hg ⊢
  rw [integral_map hm.aemeasurable hg.aestronglyMeasurable]
  simpa only [Function.comp_def] using Measure.integral_compProd hcomp

private lemma admissible_conditional_response_second {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    ∀ᵐ x ∂designLaw θ,
      Integrable (fun u : ℝ => (θ.regression x + u) ^ 2) (θ.errors x) ∧
      (∫ u : ℝ, (θ.regression x + u) ^ 2 ∂θ.errors x) = θ.regression x ^ 2 + θ.variance ∧
      (∫ u : ℝ, (θ.regression x + u) ^ 2 ∂θ.errors x) ≤ responseSecondBound C := by
  filter_upwards [designLaw_cube_ae θ, hθ.2.2.2.2.2.2.2] with x hx hm
  have h2 : MemLp (fun u : ℝ => u) 2 (θ.errors x) := (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hm.2.1
  have heq := response_second_moment_of_centered_error h2 hm.2.2.2.1 hm.2.2.2.2.1 (θ.regression x)
  refine ⟨((memLp_const (θ.regression x)).add h2).integrable_sq, heq, ?_⟩
  rw [heq]
  have hf := pow_le_pow_left₀ (abs_nonneg _) (admissible_regression_value_bound C θ hθ x hx) 2
  rw [sq_abs] at hf
  exact add_le_add hf hθ.2.2.2.2.2.2.1

private lemma observationLaw_localized_even_lintegral_le {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (m : ℕ) (B : ℝ)
    (hcond : ∀ᵐ x ∂designLaw θ, Integrable (fun u : ℝ => (θ.regression x + u) ^ (2 * m)) (θ.errors x) ∧
      (∫ u : ℝ, (θ.regression x + u) ^ (2 * m) ∂θ.errors x) ≤ B)
    (A : Set (Covariate d)) (hA : MeasurableSet A) :
    (∫⁻ z, ENNReal.ofReal ((Prod.fst ⁻¹' A).indicator (fun z : Observation d => z.2 ^ (2 * m)) z)
      ∂observationLaw θ) ≤ ENNReal.ofReal B * designLaw θ A := by
  let := designLaw_isProbability C θ hθ
  have hm : Measurable fun z : Covariate d × ℝ => (z.1, θ.regression z.1 + z.2) :=
    measurable_fst.prodMk ((hθ.2.1.comp measurable_fst).add measurable_snd)
  let g : Observation d → ℝ≥0∞ := fun z => A.indicator (fun _ => 1) z.1 * ENNReal.ofReal (z.2 ^ (2 * m))
  have hg : Measurable g :=
    ((measurable_const.indicator hA).comp measurable_fst).mul (ENNReal.measurable_ofReal.comp (measurable_snd.pow_const _))
  rw [show (fun z : Observation d => ENNReal.ofReal ((Prod.fst ⁻¹' A).indicator (fun z : Observation d => z.2 ^ (2 * m)) z)) = g from
    funext fun z => by by_cases hz : z.1 ∈ A <;> simp [g, hz]]
  have hgm : Measurable fun z : Covariate d × ℝ => g (z.1, θ.regression z.1 + z.2) := hg.comp hm
  unfold observationLaw
  rw [lintegral_map' hg.aemeasurable hm.aemeasurable, Measure.lintegral_compProd hgm]
  refine (lintegral_mono_ae ?_).trans_eq
    (by rw [lintegral_mul_const _ (measurable_const.indicator hA), lintegral_indicator_const hA, one_mul, mul_comm])
  filter_upwards [hcond] with x hx
  change (∫⁻ u, A.indicator (fun _ => (1 : ℝ≥0∞)) x * ENNReal.ofReal ((θ.regression x + u) ^ (2 * m)) ∂θ.errors x) ≤ _
  rw [lintegral_const_mul _ (by fun_prop)]
  gcongr
  rw [← ofReal_integral_eq_lintegral_ofReal hx.1 (Eventually.of_forall fun u => by dsimp; rw [pow_mul]; positivity)]
  exact ENNReal.ofReal_mono hx.2

private lemma admissible_conditional_response_fourth {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    ∀ᵐ x ∂designLaw θ,
      Integrable (fun u : ℝ => (θ.regression x + u) ^ 4) (θ.errors x) ∧
      (∫ u : ℝ, (θ.regression x + u) ^ 4 ∂θ.errors x) ≤ responseFourthBound C := by
  filter_upwards [designLaw_cube_ae θ, hθ.2.2.2.2.2.2.2] with x hx hm
  let f := θ.regression x
  have hp (u : ℝ) : (f + u) ^ 4 ≤ 8 * (f ^ 4 + u ^ 4) := by
    have h := (show Even (4 : ℕ) by decide).add_pow_le (a := f) (b := u); norm_num at h; exact h
  have hd : Integrable (fun u => 8 * (f ^ 4 + u ^ 4)) (θ.errors x) :=
    ((integrable_const (f ^ 4)).add hm.2.2.1).const_mul 8
  have hi : Integrable (fun u => (f + u) ^ 4) (θ.errors x) :=
    hd.mono' ((measurable_const.add measurable_id).pow_const 4).aestronglyMeasurable
      (Eventually.of_forall fun u => by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hp u)
  refine ⟨hi, ?_⟩
  have hmono := integral_mono hi hd hp
  rw [integral_const_mul, integral_add (integrable_const _) hm.2.2.1, integral_const] at hmono
  simp at hmono
  have hf4 : f ^ 4 ≤ C.holderBound ^ 4 := by
    simpa only [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ f ^ 4)] using
      pow_le_pow_left₀ (abs_nonneg f) (admissible_regression_value_bound C θ hθ x hx) 4
  unfold responseFourthBound; linarith [hm.2.2.2.2.2]

theorem observationLaw_fst_measurePreserving {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    MeasurePreserving (Prod.fst : Observation d → Covariate d) (observationLaw θ) (designLaw θ) := by
  let := designLaw_isProbability C θ hθ
  refine ⟨measurable_fst, ?_⟩
  have hm : Measurable fun z : Covariate d × ℝ => (z.1, θ.regression z.1 + z.2) :=
    measurable_fst.prodMk ((hθ.2.1.comp measurable_fst).add measurable_snd)
  unfold observationLaw
  rw [Measure.map_map measurable_fst hm]
  exact Measure.fst_compProd (designLaw θ) θ.errors

theorem observationLaw_response_fourth_integrable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    Integrable (fun z : Observation d => z.2 ^ 4) (observationLaw θ) := by
  let := designLaw_isProbability C θ hθ
  refine ⟨(measurable_snd.pow_const 4).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, show (fun z : Observation d => ‖z.2 ^ 4‖ₑ) = fun z => ENNReal.ofReal (z.2 ^ 4) from
    funext fun _ => Real.enorm_of_nonneg (by positivity)]
  have hh := observationLaw_localized_even_lintegral_le C θ hθ 2 (responseFourthBound C)
    (admissible_conditional_response_fourth C θ hθ) Set.univ MeasurableSet.univ
  simp only [Set.preimage_univ, Set.indicator_univ, measure_univ, mul_one] at hh
  exact lt_of_le_of_lt hh ENNReal.ofReal_lt_top

theorem observationLaw_response_memLp_two {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    MemLp (Prod.snd : Observation d → ℝ) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  have hm4 : MemLp (Prod.snd : Observation d → ℝ) 4 (observationLaw θ) := by
    refine (integrable_norm_rpow_iff (f := Prod.snd) (p := 4) measurable_snd.aestronglyMeasurable (by norm_num) (by simp)).mp ?_
    convert observationLaw_response_fourth_integrable C θ hθ using 1; funext z
    norm_num only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
    calc |z.2| ^ (4 : ℝ) = |z.2| ^ (4 : ℕ) := Real.rpow_natCast _ _
         _ = z.2 ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  exact hm4.mono_exponent (by norm_num)

private lemma observationLaw_localized_second_integral_le {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (A : Set (Covariate d)) (hA : MeasurableSet A) :
    (∫ z, (Prod.fst ⁻¹' A).indicator (fun z : Observation d => z.2 ^ 2) z ∂observationLaw θ) ≤
      responseSecondBound C * (designLaw θ).real A := by
  let := designLaw_isProbability C θ hθ
  have hb := responseSecondBound_pos C
  have hh := observationLaw_localized_even_lintegral_le C θ hθ 1 (responseSecondBound C)
    ((admissible_conditional_response_second C θ hθ).mono fun _ h => ⟨h.1, h.2.2⟩) A hA
  simp only [Nat.mul_one] at hh
  rw [← ofReal_integral_eq_lintegral_ofReal
      ((observationLaw_response_memLp_two C θ hθ).integrable_sq.indicator (measurable_fst hA))
      (Eventually.of_forall fun _ => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _),
    show ENNReal.ofReal (responseSecondBound C) * designLaw θ A =
      ENNReal.ofReal (responseSecondBound C * (designLaw θ).real A) by
      rw [ENNReal.ofReal_mul hb.le, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

theorem observationLaw_localized_fourth_integral_le {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (A : Set (Covariate d)) (hA : MeasurableSet A) :
    (∫ z, (Prod.fst ⁻¹' A).indicator (fun z : Observation d => z.2 ^ 4) z ∂observationLaw θ) ≤
      responseFourthBound C * (designLaw θ).real A := by
  let := designLaw_isProbability C θ hθ
  have hb := responseFourthBound_pos C
  have hh := observationLaw_localized_even_lintegral_le C θ hθ 2 (responseFourthBound C)
    (admissible_conditional_response_fourth C θ hθ) A hA
  rw [← ofReal_integral_eq_lintegral_ofReal
      ((observationLaw_response_fourth_integrable C θ hθ).indicator (measurable_fst hA))
      (Eventually.of_forall fun _ => Set.indicator_nonneg (fun _ _ => by positivity) _),
    show ENNReal.ofReal (responseFourthBound C) * designLaw θ A =
      ENNReal.ofReal (responseFourthBound C * (designLaw θ).real A) by
      rw [ENNReal.ofReal_mul hb.le, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

theorem observationLaw_localized_response_energy_le {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (A : Set (Covariate d)) (hA : MeasurableSet A) :
    (∫ z, (Prod.fst ⁻¹' A).indicator (fun z : Observation d => (1 + |z.2|) ^ 2) z ∂observationLaw θ) ≤
      (2 * (1 + responseSecondBound C)) * (designLaw θ).real A := by
  let := observationLaw_isProbability C θ hθ
  have hs : MemLp (fun z : Observation d => |z.2|) 2 (observationLaw θ) := by
    simpa only [Real.norm_eq_abs] using (observationLaw_response_memLp_two C θ hθ).norm
  have hi0 : Integrable (fun z : Observation d => (1 + |z.2|) ^ 2) (observationLaw θ) :=
    ((memLp_const (1 : ℝ)).add hs).integrable_sq
  have hd0 : Integrable (fun z : Observation d => 2 * (1 + z.2 ^ 2)) (observationLaw θ) :=
    ((integrable_const (1 : ℝ)).add (observationLaw_response_memLp_two C θ hθ).integrable_sq).const_mul 2
  have hb := integral_mono (hi0.indicator (measurable_fst hA)) (hd0.indicator (measurable_fst hA))
    fun z => Set.indicator_le_indicator (by nlinarith [sq_nonneg (1 - |z.2|), sq_abs z.2])
  rw [show (fun z : Observation d => (Prod.fst ⁻¹' A).indicator (fun z => 2 * (1 + z.2 ^ 2)) z) =
      fun z => 2 * ((Prod.fst ⁻¹' A).indicator (fun _ => (1 : ℝ)) z +
        (Prod.fst ⁻¹' A).indicator (fun z : Observation d => z.2 ^ 2) z) from
      funext fun z => by by_cases hz : z.1 ∈ A <;> simp [hz],
    integral_const_mul, integral_add ((integrable_const (1 : ℝ)).indicator (measurable_fst hA))
      ((observationLaw_response_memLp_two C θ hθ).integrable_sq.indicator (measurable_fst hA)),
    integral_indicator_const (1 : ℝ) (measurable_fst hA)] at hb
  simp only [smul_eq_mul, mul_one,
    (observationLaw_fst_measurePreserving C θ hθ).measureReal_preimage hA.nullMeasurableSet] at hb
  nlinarith [observationLaw_localized_second_integral_le C θ hθ A hA]

end ConditionalAndObservationMoments

-- ============================================================================
-- 3. Regular Grid Geometry, Hölder-Taylor Bridge, and Partition Collision
-- ============================================================================

section GridAndHolderBridge
open scoped ContDiff

def regularGridIndex (k : ℕ) (hk : 0 < k) (x : ℝ) : Fin k :=
  ⟨min ⌊(k : ℝ) * x⌋₊ (k - 1), (min_le_right _ _).trans_lt (by omega)⟩

def regularGridCell {d : ℕ} (k : ℕ) (hk : 0 < k) (x : Covariate d) : Fin d → Fin k :=
  fun i => regularGridIndex k hk (x i)

def regularGridCorner {d : ℕ} (k : ℕ) (c : Fin d → Fin k) : Covariate d :=
  fun i => (c i : ℝ) / k

private lemma regular_grid_index_corner_le (k : ℕ) (hk : 0 < k) (x : ℝ) (hx : 0 ≤ x) :
    (regularGridIndex k hk x : ℝ) / k ≤ x := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hfloor := Nat.floor_le (mul_nonneg hkr.le hx)
  have hmin : ((min ⌊(k : ℝ) * x⌋₊ (k - 1) : ℕ) : ℝ) ≤ ⌊(k : ℝ) * x⌋₊ := by exact_mod_cast min_le_left _ _
  exact (div_le_iff₀ hkr).mpr (by change ((min _ _ : ℕ) : ℝ) ≤ x * k; nlinarith)

theorem regular_grid_corner_mem_cube {d : ℕ} (k : ℕ) (hk : 0 < k)
    (c : Fin d → Fin k) : regularGridCorner k c ∈ unitCube d := fun i => by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  exact ⟨div_nonneg (Nat.cast_nonneg _) hkr.le,
    (div_le_iff₀ hkr).mpr (by simpa only [one_mul] using (show ((c i).val : ℝ) < k by exact_mod_cast (c i).isLt).le)⟩

theorem regular_grid_cell_radius {d : ℕ} (k : ℕ) (hk : 0 < k)
    (x : Covariate d) (hx : x ∈ unitCube d) (i : Fin d) :
    |x i - regularGridCorner k (regularGridCell k hk x) i| ≤ 1 / k := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  let m := ⌊(k : ℝ) * x i⌋₊
  rw [regularGridCorner, regularGridCell, abs_of_nonneg (sub_nonneg.mpr (regular_grid_index_corner_le k hk (x i) (hx i).1)),
    show x i - (regularGridIndex k hk (x i) : ℝ) / k = (x i * k - (regularGridIndex k hk (x i) : ℝ)) / k by field_simp]
  refine (div_le_div_iff_of_pos_right hkr).mpr ?_
  change x i * k - ((min m (k - 1) : ℕ) : ℝ) ≤ 1
  by_cases hm : m ≤ k - 1
  · rw [min_eq_left hm]; nlinarith [Nat.lt_floor_add_one ((k : ℝ) * x i)]
  · rw [min_eq_right (by omega), Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    nlinarith [mul_le_mul_of_nonneg_right (hx i).2 hkr.le]

theorem regular_grid_cell_measurable {d : ℕ} (k : ℕ) (hk : 0 < k) :
    Measurable (regularGridCell (d := d) k hk) :=
  measurable_pi_iff.mpr fun i =>
    ((measurable_of_countable fun m : ℕ => (⟨min m (k - 1), (min_le_right _ _).trans_lt (by omega)⟩ : Fin k)).comp
      ((measurable_const.mul measurable_id).nat_floor)).comp (measurable_pi_apply i)

-- Hölder-Taylor transport

def euclideanCoordinates (d : ℕ) : EuclideanSpace ℝ (Fin d) ≃L[ℝ] Covariate d :=
  PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin d => ℝ

def euclideanPoint {d : ℕ} (x : Covariate d) : EuclideanSpace ℝ (Fin d) :=
  (euclideanCoordinates d).symm x

def euclideanExtension {d : ℕ} (F : Covariate d → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  F ∘ euclideanCoordinates d

@[simp] private lemma euclideanCoordinates_apply {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    euclideanCoordinates d x i = x i := rfl

@[simp] private lemma euclideanPoint_apply {d : ℕ} (x : Covariate d) (i : Fin d) :
    euclideanPoint x i = x i := rfl

@[simp] private lemma euclideanCoordinates_point {d : ℕ} (x : Covariate d) :
    euclideanCoordinates d (euclideanPoint x) = x := (euclideanCoordinates d).apply_symm_apply x

private lemma euclideanCoordinates_norm {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    euclideanNorm (euclideanCoordinates d x) = ‖x‖ := by
  rw [euclideanNorm, EuclideanSpace.norm_eq]; simp only [euclideanCoordinates_apply, Real.norm_eq_abs, sq_abs]

private lemma euclideanPoint_norm {d : ℕ} (x : Covariate d) : ‖euclideanPoint x‖ = euclideanNorm x := by
  rw [← euclideanCoordinates_norm, euclideanCoordinates_point]

private lemma euclideanExtension_mem_holderBall {d : ℕ} (C : ModelConstants d)
    (F : Covariate d → ℝ) (hf : ContDiffOn ℝ C.order F C.domain)
    (hNorm : holderNorm C.domain F C.order C.alpha ≤ ENNReal.ofReal C.holderBound) :
    euclideanExtension F ∈ RoughRegime.Model.holderBall C.smoothness (2 * C.holderBound) := by
  have horder : RoughRegime.Model.holderOrder C.smoothness = C.order := C.order_eq.symm
  have halpha : RoughRegime.Model.holderExponent C.smoothness = C.alpha := by
    simp only [RoughRegime.Model.holderExponent, horder, ModelConstants.alpha]
  have hcoord {q : ℕ} (hq : q ≤ C.order) (σ : Fin q → Fin d) (x : EuclideanSpace ℝ (Fin d))
      (hx : x ∈ RoughRegime.Model.cube d) :
      RoughRegime.Model.coordinateDerivative (euclideanExtension F) q σ x =
        iteratedFDeriv ℝ q F (euclideanCoordinates d x) (fun j => Pi.single (σ j) 1) := by
    have hqf : ContDiffOn ℝ q F C.domain := hf.of_le (by exact_mod_cast hq)
    have hat : ContDiffAt ℝ q (euclideanExtension F) x :=
      (hqf.comp_continuousLinearMap (euclideanCoordinates d).toContinuousLinearMap).contDiffAt
        ((C.domain_open.preimage (euclideanCoordinates d).continuous).mem_nhds (C.cube_subset hx))
    rw [RoughRegime.Model.coordinateDerivative_eq_iteratedFDeriv _ q σ x hx hat]
    have he := (euclideanCoordinates d).iteratedFDerivWithin_comp_right F uniqueDiffOn_univ (x := x) (mem_univ _) q
    simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at he
    rw [show euclideanExtension F = F ∘ euclideanCoordinates d from rfl, he]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearEquiv.coe_coe]
    congr 1
  have hsup : RoughRegime.Model.derivativeSup (euclideanExtension F)
      (RoughRegime.Model.holderOrder C.smoothness) ≤ ENNReal.ofReal C.holderBound := by
    unfold RoughRegime.Model.derivativeSup; rw [horder]
    refine iSup_le fun q => iSup_le fun hq => iSup_le fun σ => iSup_le fun x => iSup_le fun hx => ?_
    rw [hcoord hq σ x hx]
    exact ENNReal.ofReal_le_ofReal (ordered_coordinate_bound C.domain C.domain_open F C.order C.alpha
      C.holderBound C.holderBound_pos.le hf hNorm q hq σ _ (C.cube_subset hx))
  have hsem : RoughRegime.Model.holderSeminorm (euclideanExtension F) C.smoothness ≤
      ENNReal.ofReal C.holderBound := by
    unfold RoughRegime.Model.holderSeminorm; rw [horder, halpha]
    refine iSup_le fun σ => iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => iSup_le fun hxy =>
      ENNReal.ofReal_le_ofReal ?_
    have hmod : |iteratedFDeriv ℝ C.order F (euclideanCoordinates d x) (fun j => Pi.single (σ j) 1) -
        iteratedFDeriv ℝ C.order F (euclideanCoordinates d y) (fun j => Pi.single (σ j) 1)| ≤
        C.holderBound * euclideanNorm (euclideanCoordinates d x - euclideanCoordinates d y) ^ C.alpha :=
      ordered_coordinate_modulus C.domain C.domain_open F C.order C.alpha
        C.holderBound C.holderBound_pos.le hf hNorm σ _ _ (C.cube_subset hx) (C.cube_subset hy)
    rw [hcoord le_rfl σ x hx, hcoord le_rfl σ y hy]
    rw [← map_sub, euclideanCoordinates_norm] at hmod
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _)).2 hmod
  change RoughRegime.Model.holderNorm (euclideanExtension F) C.smoothness ≤ _
  unfold RoughRegime.Model.holderNorm
  rw [if_pos ⟨C.smoothness_pos, by
    rw [horder]
    exact (hf.comp_continuousLinearMap (euclideanCoordinates d).toContinuousLinearMap).mono fun _ hx => C.cube_subset hx⟩]
  exact (add_le_add hsup hsem).trans_eq
    (by rw [← ENNReal.ofReal_add C.holderBound_pos.le C.holderBound_pos.le]; congr 1; ring)

def modelTaylorPolynomial {d : ℕ} (C : ModelConstants d) (F : Covariate d → ℝ)
    (x : Covariate d) : MvPolynomial (Fin d) ℝ :=
  RoughRegime.Model.holderTaylorPolynomial (euclideanExtension F) C.order (euclideanPoint x)

def taylorErrorFactor {d : ℕ} (C : ModelConstants d) : ℝ :=
  (2 * (d : ℝ) ^ C.order / C.order.factorial) * (Real.sqrt (d : ℝ)) ^ C.smoothness

theorem taylorErrorFactor_pos {d : ℕ} (C : ModelConstants d) : 0 < taylorErrorFactor C := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast C.dimension_pos
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hd
  unfold taylorErrorFactor
  exact mul_pos (div_pos (mul_pos (by norm_num) (pow_pos hd _)) (by exact_mod_cast Nat.factorial_pos _))
    (Real.rpow_pos_of_pos hs _)

theorem admissible_regression_taylor {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (x : Covariate d) (hx : x ∈ unitCube d) :
    ∃ P : MvPolynomial (Fin d) ℝ, P.totalDegree ≤ C.order ∧
      ∀ y ∈ unitCube d, |θ.regression y - MvPolynomial.eval y P| ≤
        ((d : ℝ) ^ C.order * (2 * C.holderBound) / C.order.factorial) *
          euclideanNorm (y - x) ^ C.smoothness := by
  rcases hθ with ⟨_, _, _, _, ⟨F, hcube, hreg, hNorm⟩, _, _, _⟩
  refine ⟨modelTaylorPolynomial C F x, RoughRegime.Model.holderTaylorPolynomial_degree _ _ _, fun y hy => ?_⟩
  have herr := RoughRegime.Model.holderTaylorPolynomial_error (euclideanExtension F) C.smoothness (2 * C.holderBound)
    (mul_nonneg (by norm_num) C.holderBound_pos.le) (euclideanExtension_mem_holderBall C F hreg hNorm)
    (euclideanPoint x) (euclideanPoint y) hx hy
  rw [show RoughRegime.Model.holderOrder C.smoothness = C.order from C.order_eq.symm,
    show euclideanPoint y - euclideanPoint x = euclideanPoint (y - x) from
      ((euclideanCoordinates d).symm.map_sub y x).symm, euclideanPoint_norm] at herr
  simpa only [euclideanExtension, Function.comp_apply, euclideanCoordinates_point,
    euclideanPoint_apply, modelTaylorPolynomial, hcube y hy] using herr

theorem admissible_regression_taylor_cell {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (x : Covariate d) (hx : x ∈ unitCube d) (h : ℝ) (hh : 0 ≤ h) :
    ∃ P : MvPolynomial (Fin d) ℝ, P.totalDegree ≤ C.order ∧
      ∀ y ∈ unitCube d, (∀ i, |y i - x i| ≤ h) →
        |θ.regression y - MvPolynomial.eval y P| ≤
          taylorErrorFactor C * C.holderBound * h ^ C.smoothness := by
  obtain ⟨P, hdeg, herr⟩ := admissible_regression_taylor C θ hθ x hx
  refine ⟨P, hdeg, fun y hy hxy => (herr y hy).trans ?_⟩
  have hp := Real.rpow_le_rpow (by unfold euclideanNorm; positivity)
    (euclideanNorm_le_coordinate_radius (y - x) h hh hxy) C.smoothness_pos.le
  have hcoef : 0 ≤ (d : ℝ) ^ C.order * (2 * C.holderBound) / C.order.factorial :=
    div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg d) _) (mul_nonneg (by norm_num) C.holderBound_pos.le))
      (Nat.cast_nonneg _)
  refine (mul_le_mul_of_nonneg_left hp hcoef).trans_eq ?_
  rw [Real.mul_rpow (Real.sqrt_nonneg _) hh]; unfold taylorErrorFactor; ring

-- Pair window geometry

def elementarySmoothness {d : ℕ} (C : ModelConstants d) : ℝ := min C.smoothness 1

theorem regular_grid_cell_corner_le {d : ℕ} (k : ℕ) (hk : 0 < k)
    (x : Covariate d) (hx : x ∈ unitCube d) (i : Fin d) :
    regularGridCorner k (regularGridCell k hk x) i ≤ x i :=
  regular_grid_index_corner_le k hk (x i) (hx i).1

theorem regular_grid_same_cell_radius {d : ℕ} (k : ℕ) (hk : 0 < k)
    (x y : Covariate d) (hx : x ∈ unitCube d) (hy : y ∈ unitCube d)
    (hcell : regularGridCell k hk x = regularGridCell k hk y) (i : Fin d) :
    |x i - y i| ≤ 1 / k := by
  have hx' := regular_grid_cell_radius k hk x hx i
  have hy' := regular_grid_cell_radius k hk y hy i
  have hxlo := regular_grid_cell_corner_le k hk x hx i
  have hylo := regular_grid_cell_corner_le k hk y hy i
  rw [hcell] at hx' hxlo
  exact abs_le.2 ⟨by linarith [(abs_le.mp hy').2], by linarith [(abs_le.mp hx').2]⟩

private lemma regular_grid_same_cell_regression_difference {d : ℕ}
    (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
    (k : ℕ) (hk : 0 < k) (x y : Covariate d) (hx : x ∈ unitCube d) (hy : y ∈ unitCube d)
    (hcell : regularGridCell k hk x = regularGridCell k hk y) :
    |θ.regression x - θ.regression y| ≤
      (2 * ((d : ℝ) + 1) * C.holderBound) * (Real.sqrt (d : ℝ) * (1 / k)) ^ elementarySmoothness C := by
  have hmod : |θ.regression x - θ.regression y| ≤
      (2 * ((d : ℝ) + 1) * C.holderBound) * euclideanNorm (x - y) ^ elementarySmoothness C := by
    rcases hθ with ⟨_, _, _, _, ⟨F, hcube, hreg, hNorm⟩, _, _, _⟩
    have hm := RoughRegime.Model.holderBall_spatial_modulus (euclideanExtension F)
      C.smoothness (2 * C.holderBound) (mul_nonneg (by norm_num) C.holderBound_pos.le)
      (euclideanExtension_mem_holderBall C F hreg hNorm) (euclideanPoint x) (euclideanPoint y) hx hy
    rw [show euclideanPoint x - euclideanPoint y = euclideanPoint (x - y) from
      ((euclideanCoordinates d).symm.map_sub x y).symm, euclideanPoint_norm] at hm
    simp only [euclideanExtension, Function.comp_apply, euclideanCoordinates_point, hcube x hx, hcube y hy] at hm
    unfold elementarySmoothness; convert hm using 1 <;> ring
  exact hmod.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by unfold euclideanNorm; positivity)
      (euclideanNorm_le_coordinate_radius (x - y) (1 / k) (by positivity)
        (regular_grid_same_cell_radius k hk x y hx hy hcell))
      (lt_min C.smoothness_pos (by norm_num)).le)
    (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) C.holderBound_pos.le))

def regularGridProbability {d : ℕ} (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    (c : Fin d → Fin k) : ℝ :=
  (designLaw θ).real ((regularGridCell k hk) ⁻¹' {c})

private lemma regularGridProbability_sum {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    ∑ c, regularGridProbability θ k hk c = 1 := by
  let := designLaw_isProbability C θ hθ
  simpa [regularGridProbability] using sum_measureReal_preimage_singleton (μ := designLaw θ)
    (Finset.univ : Finset (Fin d → Fin k))
    fun c _ => (measurableSet_singleton c).preimage (regular_grid_cell_measurable k hk)

private lemma admissible_designLaw_le_cubeVolume {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    designLaw θ ≤ ENNReal.ofReal C.densityUpper • cubeVolume d := by
  unfold designLaw; rw [← withDensity_const]; apply withDensity_mono
  filter_upwards [hθ.2.2.1] with _ hx; exact ENNReal.ofReal_le_ofReal hx.2

theorem regular_grid_fiber_volume_le {d : ℕ} (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k) :
    cubeVolume d ((regularGridCell k hk) ⁻¹' {c}) ≤ ENNReal.ofReal (1 / (k : ℝ)) ^ d := by
  rw [cubeVolume, Measure.restrict_apply ((measurableSet_singleton c).preimage (regular_grid_cell_measurable k hk))]
  let a : Covariate d := fun i => regularGridCorner k c i
  let b : Covariate d := fun i => regularGridCorner k c i + 1 / k
  refine (measure_mono (t := Icc a b) fun x hx => ⟨fun i => ?_, fun i => ?_⟩).trans_eq ?_
  · simpa only [show regularGridCell k hk x = c from hx.1] using regular_grid_cell_corner_le k hk x hx.2 i
  · have hi := (abs_le.mp (by simpa only [show regularGridCell k hk x = c from hx.1] using
      regular_grid_cell_radius k hk x hx.2 i)).2
    dsimp [b]; linarith
  · rw [Real.volume_Icc_pi]; simp_rw [show ∀ i, b i - a i = 1 / (k : ℝ) from fun _ => by dsimp [a, b]; ring]; simp

theorem regularGridProbability_cap {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k) :
    regularGridProbability θ k hk c ≤ C.densityUpper / (k : ℝ) ^ d := by
  let := designLaw_isProbability C θ hθ
  have hdom := Measure.le_iff.1 (admissible_designLaw_le_cubeVolume C θ hθ)
    ((regularGridCell k hk) ⁻¹' {c}) ((measurableSet_singleton c).preimage (regular_grid_cell_measurable k hk))
  rw [Measure.smul_apply, smul_eq_mul] at hdom
  have hcap : (designLaw θ) ((regularGridCell k hk) ⁻¹' {c}) ≤
      ENNReal.ofReal C.densityUpper * ENNReal.ofReal (1 / (k : ℝ)) ^ d := by
    apply hdom.trans; gcongr; exact regular_grid_fiber_volume_le k hk c
  have hu : 0 ≤ C.densityUpper := by linarith [C.one_lt_densityUpper]
  refine (ENNReal.toReal_mono (by finiteness) hcap).trans_eq ?_
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hu,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / k), div_pow, one_pow]
  ring

end GridAndHolderBridge

-- ============================================================================
-- 4. Partition Moments, Window Scores, Stabilized Ratio, and Pair Operators
-- ============================================================================

section PartitionAndPairScores
set_option backward.isDefEq.respectTransparency false

section Partition
attribute [local instance] Classical.propDecidable
variable {X B : Type*} [MeasurableSpace X] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] [MeasurableEq B]
  (μ : Measure X) [IsProbabilityMeasure μ] (label : X → B) (hlabel : Measurable label)
include hlabel

private lemma finite_label_integral (g : B → ℝ) :
    (∫ x, g (label x) ∂μ) = ∑ c, μ.real (label ⁻¹' {c}) * g c := by
  rw [← integral_map hlabel.aemeasurable (measurable_of_countable g).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  exact Finset.sum_congr rfl fun c _ => by rw [measureReal_def, Measure.map_apply hlabel (measurableSet_singleton c)]; rfl

def sameLabelKernel (z : X × X) : ℝ := if label z.1 = label z.2 then 1 else 0

theorem sameLabelKernel_measurable : Measurable (sameLabelKernel label) :=
  Measurable.ite (measurableSet_eq_fun (hlabel.comp measurable_fst) (hlabel.comp measurable_snd))
    measurable_const measurable_const

theorem sameLabelKernel_memLp : MemLp (sameLabelKernel label) 2 (μ.prod μ) :=
  MemLp.of_bound (sameLabelKernel_measurable label hlabel).aestronglyMeasurable 1
    (Eventually.of_forall fun _ => by unfold sameLabelKernel; split_ifs <;> norm_num)

theorem sameLabelKernel_symmetric (z : X × X) :
    sameLabelKernel label z.swap = sameLabelKernel label z := by
  simp only [sameLabelKernel, Prod.fst_swap, Prod.snd_swap, eq_comm]

private lemma sameLabelKernel_row (x : X) :
    (∫ y, sameLabelKernel label (x, y) ∂μ) = μ.real (label ⁻¹' {label x}) := by
  rw [show (fun y => sameLabelKernel label (x, y)) = (label ⁻¹' {label x}).indicator fun _ => (1 : ℝ) from
    funext fun _ => by simp [sameLabelKernel, Set.indicator, eq_comm],
    integral_indicator ((measurableSet_singleton _).preimage hlabel)]
  simp

theorem sameLabelKernel_integral :
    (∫ z, sameLabelKernel label z ∂μ.prod μ) = ∑ c, μ.real (label ⁻¹' {c}) ^ 2 := by
  rw [integral_prod _ ((sameLabelKernel_memLp μ label hlabel).integrable (by norm_num))]
  simp_rw [sameLabelKernel_row μ label hlabel]
  rw [finite_label_integral μ label hlabel fun c => μ.real (label ⁻¹' {c})]
  simp only [pow_two]

theorem sameLabelKernel_square_integral :
    (∫ z, (sameLabelKernel label z) ^ 2 ∂μ.prod μ) = ∑ c, μ.real (label ⁻¹' {c}) ^ 2 := by
  rw [show (fun z => (sameLabelKernel label z) ^ 2) = sameLabelKernel label from
    funext fun _ => by unfold sameLabelKernel; split_ifs <;> norm_num]
  exact sameLabelKernel_integral μ label hlabel

theorem sameLabelKernel_row_square_integral :
    (∫ x, (∫ y, sameLabelKernel label (x, y) ∂μ) ^ 2 ∂μ) = ∑ c, μ.real (label ⁻¹' {c}) ^ 3 := by
  simp_rw [sameLabelKernel_row μ label hlabel]
  rw [finite_label_integral μ label hlabel fun c => μ.real (label ⁻¹' {c}) ^ 2]
  exact Finset.sum_congr rfl fun _ _ => by ring

def labelLocalizedKernel (g : X → ℝ) (z : X × X) : ℝ :=
  if label z.1 = label z.2 then g z.2 else 0

theorem labelLocalizedKernel_integrable (g : X → ℝ) (hg : Integrable g μ) :
    Integrable (labelLocalizedKernel label g) (μ.prod μ) := by
  rw [show labelLocalizedKernel label g = {z : X × X | label z.1 = label z.2}.indicator fun z => g z.2 from
    funext fun _ => by simp [labelLocalizedKernel, Set.indicator_apply]]
  exact (hg.comp_snd μ).indicator (measurableSet_eq_fun (hlabel.comp measurable_fst) (hlabel.comp measurable_snd))

theorem labelLocalizedKernel_integral_le (g : X → ℝ) (hg : Integrable g μ)
    (M : ℝ) (hloc : ∀ c : B, (∫ x, (label ⁻¹' {c}).indicator g x ∂μ) ≤ M * μ.real (label ⁻¹' {c})) :
    (∫ z, labelLocalizedKernel label g z ∂μ.prod μ) ≤ M * ∑ c : B, μ.real (label ⁻¹' {c}) ^ 2 := by
  have hrow (x : X) : (∫ y, labelLocalizedKernel label g (x, y) ∂μ) = ∫ y, (label ⁻¹' {label x}).indicator g y ∂μ :=
    congrArg (integral μ) (funext fun _ => by simp [labelLocalizedKernel, Set.indicator_apply, eq_comm])
  have hi := (labelLocalizedKernel_integrable μ label hlabel g hg).integral_prod_left
  simp_rw [hrow] at hi
  have hpm : Integrable (fun x => μ.real (label ⁻¹' {label x})) μ :=
    (MemLp.of_bound ((measurable_of_countable fun c : B => μ.real (label ⁻¹' {c})).comp hlabel).aestronglyMeasurable
      1 (p := 1) (Eventually.of_forall fun _ => by
        dsimp only [Function.comp_def]; rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)).integrable (by norm_num)
  rw [integral_prod _ (labelLocalizedKernel_integrable μ label hlabel g hg)]
  simp_rw [hrow]
  refine (integral_mono hi (hpm.const_mul M) fun x => hloc (label x)).trans_eq ?_
  rw [integral_const_mul, finite_label_integral μ label hlabel fun c => μ.real (label ⁻¹' {c})]
  simp only [pow_two]

def pairWindowScore (r : X → ℝ) (V : ℝ) (z : X × X) : ℝ :=
  if label z.1 = label z.2 then (r z.1 - r z.2) ^ 2 / 2 - V else 0

theorem pairWindowScore_measurable (r : X → ℝ) (hr : Measurable r) (V : ℝ) :
    Measurable (pairWindowScore label r V) :=
  Measurable.ite (measurableSet_eq_fun (hlabel.comp measurable_fst) (hlabel.comp measurable_snd))
    ((((hr.comp measurable_fst).sub (hr.comp measurable_snd)).pow_const 2 |>.div_const 2).sub measurable_const)
    measurable_const

omit hlabel in
theorem pairWindowScore_symmetric (r : X → ℝ) (V : ℝ) (x y : X) :
    pairWindowScore label r V (x, y) = pairWindowScore label r V (y, x) := by
  unfold pairWindowScore; simp only [Prod.fst, Prod.snd, eq_comm]; split_ifs <;> ring

omit hlabel in
private lemma pairWindowScore_abs_le (r : X → ℝ) (V : ℝ) (z : X × X) :
    |pairWindowScore label r V z| ≤ r z.1 ^ 2 + r z.2 ^ 2 + |V| := by
  unfold pairWindowScore; split_ifs
  · refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity : 0 ≤ (r z.1 - r z.2) ^ 2 / 2)]
    nlinarith [sq_nonneg (r z.1 + r z.2)]
  · simp only [abs_zero]; positivity

omit hlabel in
private lemma pairWindowScore_sq_le (r : X → ℝ) (V : ℝ) (z : X × X) :
    pairWindowScore label r V z ^ 2 ≤ 4 * (r z.1 ^ 4 + r z.2 ^ 4) + 2 * V ^ 2 := by
  unfold pairWindowScore; split_ifs
  · have h1 := add_sq_le (a := (r z.1 - r z.2) ^ 2 / 2) (b := -V)
    have h2 := (show Even (4 : ℕ) by decide).add_pow_le (a := r z.1) (b := -r z.2)
    norm_num at h2; nlinarith
  · simp only [zero_pow (by decide : (2 : ℕ) ≠ 0)]; positivity

private lemma pairWindowScore_memLp (r : X → ℝ) (hr : Measurable r) (V : ℝ)
    (h4 : Integrable (fun x => r x ^ 4) μ) : MemLp (pairWindowScore label r V) 2 (μ.prod μ) :=
  (memLp_two_iff_integrable_sq (pairWindowScore_measurable label hlabel r hr V).aestronglyMeasurable).mpr <|
    ((((h4.comp_fst μ).add (h4.comp_snd μ)).const_mul 4).add (integrable_const _)).mono'
      ((pairWindowScore_measurable label hlabel r hr V).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact pairWindowScore_sq_le label r V z)

private lemma pairWindowScore_energy_le (r : X → ℝ) (hr : Measurable r) (V M4 : ℝ)
    (h4 : Integrable (fun x => r x ^ 4) μ)
    (hloc : ∀ c : B, (∫ x, (label ⁻¹' {c}).indicator (fun x => r x ^ 4) x ∂μ) ≤ M4 * μ.real (label ⁻¹' {c})) :
    (∫ z, pairWindowScore label r V z ^ 2 ∂μ.prod μ) ≤
      (8 * M4 + 2 * V ^ 2) * ∑ c : B, μ.real (label ⁻¹' {c}) ^ 2 := by
  let L := labelLocalizedKernel label fun x => r x ^ 4
  have hiL := labelLocalizedKernel_integrable μ label hlabel _ h4
  have hiD := (sameLabelKernel_memLp μ label hlabel).integrable (by norm_num)
  have hd : Integrable (fun z : X × X => 4 * (L z + L z.swap) + 2 * V ^ 2 * sameLabelKernel label z) (μ.prod μ) :=
    ((hiL.add hiL.swap).const_mul 4).add (hiD.const_mul _)
  have hb := integral_mono (pairWindowScore_memLp μ label hlabel r hr V h4).integrable_sq hd fun z => by
      by_cases h : label z.1 = label z.2
      · have hb0 := pairWindowScore_sq_le label r V z
        simp only [pairWindowScore, L, labelLocalizedKernel, sameLabelKernel, Prod.fst_swap, Prod.snd_swap,
          if_pos h, if_pos h.symm] at hb0 ⊢
        nlinarith
      · simp [pairWindowScore, L, labelLocalizedKernel, sameLabelKernel, h, Ne.symm h]
  rw [integral_add (f := fun z : X × X => 4 * (L z + L z.swap)) (g := fun z => 2 * V ^ 2 * sameLabelKernel label z)
      ((hiL.add hiL.swap).const_mul 4) (hiD.const_mul _),
    integral_const_mul, integral_add (f := L) (g := fun z => L z.swap) hiL hiL.swap,
    integral_prod_swap L, integral_const_mul, sameLabelKernel_integral μ label hlabel] at hb
  have hL := labelLocalizedKernel_integral_le μ label hlabel _ h4 M4 hloc
  dsimp [L] at hb; nlinarith

private lemma pairWindowScore_row_energy_le (r : X → ℝ) (hr : Measurable r)
    (V M2 M4 cap : ℝ) (hM2 : 0 ≤ M2) (hcap : 0 ≤ cap)
    (h2 : Integrable (fun x => r x ^ 2) μ) (h4 : Integrable (fun x => r x ^ 4) μ)
    (hglobal : (∫ x, r x ^ 4 ∂μ) ≤ M4)
    (hloc : ∀ c : B, (∫ x, (label ⁻¹' {c}).indicator (fun x => r x ^ 2) x ∂μ) ≤ M2 * μ.real (label ⁻¹' {c}))
    (hmass : ∀ c : B, μ.real (label ⁻¹' {c}) ≤ cap) :
    (∫ x, (∫ y, pairWindowScore label r V (x, y) ∂μ) ^ 2 ∂μ) ≤
      2 * cap ^ 2 * (M4 + (|V| + M2) ^ 2) := by
  have hi := PairUStatistic.rowIntegral_sq_integrable (pairWindowScore_memLp μ label hlabel r hr V h4)
  have hd : Integrable (fun x => 2 * cap ^ 2 * (r x ^ 4 + (|V| + M2) ^ 2)) μ :=
    (h4.add (integrable_const _)).const_mul _
  have hb := integral_mono hi hd fun x => by
    let A := label ⁻¹' {label x}
    have hA : MeasurableSet A := (measurableSet_singleton _).preimage hlabel
    let e : X → ℝ := A.indicator fun y => r x ^ 2 + r y ^ 2 + |V|
    have hiE : Integrable e μ := (((integrable_const (r x ^ 2)).add h2).add (integrable_const |V|)).indicator hA
    have hpt (y : X) : ‖pairWindowScore label r V (x, y)‖ ≤ e y := by
      by_cases he : label x = label y
      · simpa only [Real.norm_eq_abs, e, A, Set.indicator_of_mem (show y ∈ A from he.symm)] using pairWindowScore_abs_le label r V (x, y)
      · simp [pairWindowScore, e, A, Set.indicator_apply, he, Ne.symm he]
    have hiS : Integrable (fun y => pairWindowScore label r V (x, y)) μ :=
      hiE.mono' ((pairWindowScore_measurable label hlabel r hr V).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (Eventually.of_forall hpt)
    have hrow : |∫ y, pairWindowScore label r V (x, y) ∂μ| ≤ μ.real A * (r x ^ 2 + |V| + M2) := by
      have h1 := (Real.norm_eq_abs _).symm.le.trans ((norm_integral_le_integral_norm _).trans (integral_mono hiS.norm hiE hpt))
      rw [show (∫ y, e y ∂μ) = μ.real A * (r x ^ 2 + |V|) + ∫ y, A.indicator (fun y => r y ^ 2) y ∂μ by
        dsimp [e]; rw [integral_indicator hA, show (fun y => r x ^ 2 + r y ^ 2 + |V|) = fun y => (r x ^ 2 + |V|) + r y ^ 2 from funext fun _ => by ring,
          integral_add (integrable_const _) h2.restrict, integral_const, ← integral_indicator hA]
        simp only [measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul]] at h1
      nlinarith [hloc (label x)]
    calc
      (∫ y, pairWindowScore label r V (x, y) ∂μ) ^ 2 = |∫ y, pairWindowScore label r V (x, y) ∂μ| ^ 2 := (sq_abs _).symm
      _ ≤ (μ.real A * (r x ^ 2 + (|V| + M2))) ^ 2 := by
          simpa only [add_assoc] using pow_le_pow_left₀ (abs_nonneg _) hrow 2
      _ = μ.real A ^ 2 * (r x ^ 2 + (|V| + M2)) ^ 2 := by ring
      _ ≤ cap ^ 2 * (r x ^ 2 + (|V| + M2)) ^ 2 := by
          have : 0 ≤ μ.real A := measureReal_nonneg; have := hmass (label x); gcongr
      _ ≤ cap ^ 2 * (2 * ((r x ^ 2) ^ 2 + (|V| + M2) ^ 2)) := mul_le_mul_of_nonneg_left add_sq_le (sq_nonneg cap)
      _ = _ := by ring
  rw [integral_const_mul, integral_add h4 (integrable_const _), integral_const] at hb
  simp at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add hglobal le_rfl) (by positivity))

private lemma pairWindowScore_integral (r : X → ℝ) (hr : Measurable r) (V : ℝ) (hr2 : MemLp r 2 μ) :
    (∫ z, pairWindowScore label r V z ∂μ.prod μ) =
      ∑ c : B, (μ.real (label ⁻¹' {c}) * (∫ x, (label ⁻¹' {c}).indicator (fun x => r x ^ 2) x ∂μ) -
        (∫ x, (label ⁻¹' {c}).indicator r x ∂μ) ^ 2 - V * μ.real (label ⁻¹' {c}) ^ 2) := by
  let L := labelLocalizedKernel label fun x => r x ^ 2
  let Q := fun z : X × X => sameLabelKernel label z * r z.1 * r z.2
  have hiL := labelLocalizedKernel_integrable μ label hlabel _ hr2.integrable_sq
  have hQeq (z : X × X) : Q z = ∑ c : B, (label ⁻¹' {c}).indicator r z.1 * (label ⁻¹' {c}).indicator r z.2 := by
    dsimp [Q]; rw [Finset.sum_eq_single (label z.1)]
    · by_cases he : label z.1 = label z.2
      · simp [sameLabelKernel, Set.indicator_apply, he]
      · simp [sameLabelKernel, Set.indicator_apply, he, Ne.symm he]
    · intro c _ hne; simp [Set.indicator_apply, Ne.symm hne]
    · simp
  have hiQ : Integrable Q (μ.prod μ) := by
    rw [show Q = fun z : X × X => ∑ c : B, (label ⁻¹' {c}).indicator r z.1 * (label ⁻¹' {c}).indicator r z.2 from funext hQeq]
    exact integrable_finsetSum _ fun c _ =>
      ((hr2.integrable (by norm_num)).indicator ((measurableSet_singleton _).preimage hlabel)).mul_prod
        ((hr2.integrable (by norm_num)).indicator ((measurableSet_singleton _).preimage hlabel))
  have hiD := (sameLabelKernel_memLp μ label hlabel).integrable (by norm_num)
  rw [show pairWindowScore label r V = fun z : X × X => (L z + L z.swap) / 2 - Q z - V * sameLabelKernel label z from
      funext fun z => by
        dsimp [pairWindowScore, L, Q, labelLocalizedKernel, sameLabelKernel]
        by_cases he : label z.1 = label z.2
        · simp only [if_pos he, if_pos he.symm, one_mul]; ring
        · simp [he, Ne.symm he],
    integral_sub (f := fun z : X × X => (L z + L z.swap) / 2 - Q z) (g := fun z => V * sameLabelKernel label z)
      (((hiL.add hiL.swap).div_const 2).sub hiQ) (hiD.const_mul V),
    integral_sub (f := fun z : X × X => (L z + L z.swap) / 2) (g := Q) ((hiL.add hiL.swap).div_const 2) hiQ,
    integral_div, integral_add (f := L) (g := fun z => L z.swap) hiL hiL.swap,
    integral_prod_swap L, integral_const_mul]
  have hL : (∫ z, L z ∂μ.prod μ) = ∑ c : B, μ.real (label ⁻¹' {c}) * ∫ x, (label ⁻¹' {c}).indicator (fun x => r x ^ 2) x ∂μ := by
    rw [integral_prod _ hiL]
    simp_rw [show ∀ x, (∫ y, labelLocalizedKernel label (fun x => r x ^ 2) (x, y) ∂μ) =
        ∫ y, (label ⁻¹' {label x}).indicator (fun x => r x ^ 2) y ∂μ from
      fun x => congrArg (integral μ) (funext fun _ => by simp [labelLocalizedKernel, Set.indicator_apply, eq_comm])]
    exact finite_label_integral μ label hlabel fun c => ∫ y, (label ⁻¹' {c}).indicator (fun x => r x ^ 2) y ∂μ
  have hQ : (∫ z, Q z ∂μ.prod μ) = ∑ c : B, (∫ x, (label ⁻¹' {c}).indicator r x ∂μ) ^ 2 := by
    rw [show Q = fun z : X × X => ∑ c : B, (label ⁻¹' {c}).indicator r z.1 * (label ⁻¹' {c}).indicator r z.2 from funext hQeq]
    rw [integral_finsetSum _ fun c _ =>
      ((hr2.integrable (by norm_num)).indicator ((measurableSet_singleton _).preimage hlabel)).mul_prod
        ((hr2.integrable (by norm_num)).indicator ((measurableSet_singleton _).preimage hlabel))]
    exact Finset.sum_congr rfl fun _ _ => by rw [integral_prod_mul]; ring
  rw [hL, hQ, sameLabelKernel_integral μ label hlabel, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end Partition

-- Regular grid collision mass & window model

def regularGridCollisionMass {d : ℕ} (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k) : ℝ :=
  ∑ c, regularGridProbability θ k hk c ^ 2

theorem regularGridCollisionMass_lower {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    1 / (k : ℝ) ^ d ≤ regularGridCollisionMass θ k hk := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d → Fin k))) (f := regularGridProbability θ k hk)
  simp only [regularGridProbability_sum C θ hθ k hk, one_pow, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow] at h
  exact (div_le_iff₀ (pow_pos (by exact_mod_cast hk : (0 : ℝ) < k) d)).2
    (by simpa only [mul_comm, regularGridCollisionMass] using h)

theorem regularGridCollisionMass_upper {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    regularGridCollisionMass θ k hk ≤ C.densityUpper / (k : ℝ) ^ d := by
  refine (Finset.sum_le_sum (g := fun c => (C.densityUpper / (k : ℝ) ^ d) * regularGridProbability θ k hk c) fun c _ => ?_).trans_eq
    (by rw [← Finset.mul_sum, regularGridProbability_sum C θ hθ k hk, mul_one])
  rw [sq]; exact mul_le_mul_of_nonneg_right (regularGridProbability_cap C θ hθ k hk c) measureReal_nonneg

theorem regularGridCollisionRowEnergy_upper {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    (∑ c, regularGridProbability θ k hk c ^ 3) ≤ (C.densityUpper / (k : ℝ) ^ d) ^ 2 := by
  let cap := C.densityUpper / (k : ℝ) ^ d
  have hcap : 0 ≤ cap := div_nonneg (by linarith [C.one_lt_densityUpper]) (pow_nonneg (Nat.cast_nonneg k) d)
  calc
    _ ≤ cap * regularGridCollisionMass θ k hk := by
      rw [regularGridCollisionMass, Finset.mul_sum]
      exact Finset.sum_le_sum fun c _ => by
        nlinarith [mul_le_mul_of_nonneg_right (regularGridProbability_cap C θ hθ k hk c) (sq_nonneg (regularGridProbability θ k hk c))]
    _ ≤ cap * cap := mul_le_mul_of_nonneg_left (regularGridCollisionMass_upper C θ hθ k hk) hcap
    _ = _ := sq cap |>.symm

def regularObservationLabel {d : ℕ} (k : ℕ) (hk : 0 < k) :
    Observation d → (Fin d → Fin k) := fun z => regularGridCell k hk z.1

theorem regularObservationLabel_measurable {d : ℕ} (k : ℕ) (hk : 0 < k) :
    Measurable (regularObservationLabel (d := d) k hk) :=
  (regular_grid_cell_measurable k hk).comp measurable_fst

theorem regularObservationLabel_fiber {d : ℕ} (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k) :
    (regularObservationLabel (d := d) k hk) ⁻¹' {c} =
      Prod.fst ⁻¹' ((regularGridCell k hk) ⁻¹' {c}) := rfl

theorem regularObservationLabel_mass {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k) :
    (observationLaw θ).real ((regularObservationLabel k hk) ⁻¹' {c}) = regularGridProbability θ k hk c :=
  (observationLaw_fst_measurePreserving C θ hθ).measureReal_preimage
    ((measurableSet_singleton c).preimage (regular_grid_cell_measurable k hk)).nullMeasurableSet

def regularPairScore {d : ℕ} (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k) :
    Observation d × Observation d → ℝ :=
  pairWindowScore (regularObservationLabel k hk) Prod.snd θ.variance

theorem regularPairScore_memLp {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    MemLp (regularPairScore θ k hk) 2 ((observationLaw θ).prod (observationLaw θ)) := by
  let := observationLaw_isProbability C θ hθ
  exact pairWindowScore_memLp (observationLaw θ) _ (regularObservationLabel_measurable k hk)
    Prod.snd measurable_snd θ.variance (observationLaw_response_fourth_integrable C θ hθ)

theorem regularPairScore_kernel_energy_le {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    (∫ z, regularPairScore θ k hk z ^ 2 ∂(observationLaw θ).prod (observationLaw θ)) ≤
      (8 * responseFourthBound C + 2 * θ.variance ^ 2) * regularGridCollisionMass θ k hk := by
  let := observationLaw_isProbability C θ hθ
  simpa only [regularObservationLabel_mass C θ hθ k hk, regularPairScore, regularGridCollisionMass] using
    pairWindowScore_energy_le (observationLaw θ) _ (regularObservationLabel_measurable k hk)
      Prod.snd measurable_snd θ.variance (responseFourthBound C)
      (observationLaw_response_fourth_integrable C θ hθ) fun c => by
        rw [regularObservationLabel_mass C θ hθ k hk c, regularObservationLabel_fiber k hk c]
        exact observationLaw_localized_fourth_integral_le C θ hθ _
          ((measurableSet_singleton _).preimage (regular_grid_cell_measurable k hk))

theorem regularPairScore_row_energy_le {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    (∫ x, (∫ y, regularPairScore θ k hk (x, y) ∂observationLaw θ) ^ 2 ∂observationLaw θ) ≤
      2 * (C.densityUpper / (k : ℝ) ^ d) ^ 2 *
        (responseFourthBound C + (|θ.variance| + responseSecondBound C) ^ 2) := by
  let := observationLaw_isProbability C θ hθ
  let := designLaw_isProbability C θ hθ
  have hρ : 0 < C.densityUpper := zero_lt_one.trans C.one_lt_densityUpper
  exact pairWindowScore_row_energy_le (observationLaw θ) _ (regularObservationLabel_measurable k hk)
    Prod.snd measurable_snd θ.variance (responseSecondBound C) (responseFourthBound C)
    (C.densityUpper / (k : ℝ) ^ d) (responseSecondBound_pos C).le (by positivity)
    (observationLaw_response_memLp_two C θ hθ).integrable_sq
    (observationLaw_response_fourth_integrable C θ hθ)
    (by simpa using observationLaw_localized_fourth_integral_le C θ hθ Set.univ MeasurableSet.univ)
    (fun c => by
      rw [regularObservationLabel_mass C θ hθ k hk c, regularObservationLabel_fiber k hk c]
      exact observationLaw_localized_second_integral_le C θ hθ _
        ((measurableSet_singleton _).preimage (regular_grid_cell_measurable k hk)))
    fun c => by rw [regularObservationLabel_mass C θ hθ k hk c]; exact regularGridProbability_cap C θ hθ k hk c

private lemma regularPairScore_mean_eq_signal {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    (∫ z, regularPairScore θ k hk z ∂(observationLaw θ).prod (observationLaw θ)) =
      ∫ z, pairWindowScore (regularObservationLabel k hk) (fun z : Observation d => θ.regression z.1) 0 z
        ∂(observationLaw θ).prod (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  let := designLaw_isProbability C θ hθ
  have hreg_obs : MemLp (fun z : Observation d => θ.regression z.1) 2 (observationLaw θ) :=
    MemLp.of_bound (hθ.2.1.comp measurable_fst).aestronglyMeasurable C.holderBound
      (((observationLaw_fst_measurePreserving C θ hθ).quasiMeasurePreserving.ae (designLaw_cube_ae θ)).mono
        fun z hz => by simpa only [Real.norm_eq_abs] using admissible_regression_value_bound C θ hθ z.1 hz)
  have hreg_des : MemLp θ.regression 2 (designLaw θ) :=
    MemLp.of_bound hθ.2.1.aestronglyMeasurable C.holderBound
      ((designLaw_cube_ae θ).mono fun x hx => by simpa only [Real.norm_eq_abs] using admissible_regression_value_bound C θ hθ x hx)
  have hcov (g : Covariate d → ℝ) (hg : Measurable g) :
      (∫ z, g z.1 ∂observationLaw θ) = ∫ x, g x ∂designLaw θ := by
    have hh := integral_map (μ := observationLaw θ) measurable_fst.aemeasurable hg.aestronglyMeasurable
    rwa [(observationLaw_fst_measurePreserving C θ hθ).map_eq, eq_comm] at hh
  rw [regularPairScore,
    pairWindowScore_integral (observationLaw θ) _ (regularObservationLabel_measurable k hk)
      Prod.snd measurable_snd θ.variance (observationLaw_response_memLp_two C θ hθ),
    pairWindowScore_integral (observationLaw θ) _ (regularObservationLabel_measurable k hk)
      (fun z : Observation d => θ.regression z.1) (hθ.2.1.comp measurable_fst) 0 hreg_obs]
  refine Finset.sum_congr rfl fun c _ => ?_
  let A := (regularGridCell k hk) ⁻¹' {c}
  have hA : MeasurableSet A := (measurableSet_singleton _).preimage (regular_grid_cell_measurable k hk)
  have h1 : (∫ z, (Prod.fst ⁻¹' A).indicator (Prod.snd : Observation d → ℝ) z ∂observationLaw θ) =
      ∫ z, (Prod.fst ⁻¹' A).indicator (fun z : Observation d => θ.regression z.1) z ∂observationLaw θ := by
    rw [observationLaw_integral_conditioning C θ hθ _
        (((observationLaw_response_memLp_two C θ hθ).integrable (by norm_num)).indicator (measurable_fst hA)),
      show (fun z : Observation d => (Prod.fst ⁻¹' A).indicator (fun z => θ.regression z.1) z) =
        fun z => A.indicator θ.regression z.1 from funext fun z => by by_cases hz : z.1 ∈ A <;> simp [Set.indicator, hz],
      hcov _ (hθ.2.1.indicator hA)]
    refine integral_congr_ae (hθ.2.2.2.2.2.2.2.mono fun x hx => ?_)
    by_cases hxa : x ∈ A
    · simp [hxa, integral_add (integrable_const _) hx.1, hx.2.2.2.1]
    · simp [hxa]
  have h2 : (∫ z, (Prod.fst ⁻¹' A).indicator (fun z : Observation d => z.2 ^ 2) z ∂observationLaw θ) =
      (∫ z, (Prod.fst ⁻¹' A).indicator (fun z : Observation d => θ.regression z.1 ^ 2) z ∂observationLaw θ) +
        θ.variance * (designLaw θ).real A := by
    rw [observationLaw_integral_conditioning C θ hθ _
        ((observationLaw_response_memLp_two C θ hθ).integrable_sq.indicator (measurable_fst hA)),
      show (∫ x, ∫ u, (Prod.fst ⁻¹' A).indicator (fun z : Observation d => z.2 ^ 2) (x, θ.regression x + u) ∂θ.errors x ∂designLaw θ) =
        ∫ x, A.indicator (fun x => θ.regression x ^ 2 + θ.variance) x ∂designLaw θ from
        integral_congr_ae ((admissible_conditional_response_second C θ hθ).mono fun x hx => by
          by_cases hxa : x ∈ A
          · simpa [hxa] using hx.2.1
          · simp [hxa]),
      show (fun z : Observation d => (Prod.fst ⁻¹' A).indicator (fun z => θ.regression z.1 ^ 2) z) =
        fun z => A.indicator (fun x => θ.regression x ^ 2) z.1 from
        funext fun z => by by_cases hz : z.1 ∈ A <;> simp [Set.indicator, hz],
      hcov _ ((hθ.2.1.pow_const 2).indicator hA), integral_indicator hA, integral_indicator hA,
      integral_add hreg_des.integrable_sq.restrict (integrable_const θ.variance), integral_const]
    simp only [measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul]; ring
  rw [regularObservationLabel_mass C θ hθ k hk c, regularObservationLabel_fiber k hk c, h1, h2]
  dsimp [A, regularGridProbability]; ring

def regularGridOscillation {d : ℕ} (C : ModelConstants d) (k : ℕ) : ℝ :=
  (2 * ((d : ℝ) + 1) * C.holderBound) * (Real.sqrt d * (1 / (k : ℝ))) ^ elementarySmoothness C

theorem regularPairScore_mean_nonneg {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    0 ≤ ∫ z, regularPairScore θ k hk z ∂(observationLaw θ).prod (observationLaw θ) := by
  rw [regularPairScore_mean_eq_signal C θ hθ k hk]
  exact integral_nonneg fun _ => by unfold pairWindowScore; split_ifs <;> simp only [sub_zero] <;> positivity

theorem regularPairScore_mean_le {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    (∫ z, regularPairScore θ k hk z ∂(observationLaw θ).prod (observationLaw θ)) ≤
      (regularGridOscillation C k ^ 2 / 2) * regularGridCollisionMass θ k hk := by
  let := observationLaw_isProbability C θ hθ
  have hcube := (observationLaw_fst_measurePreserving C θ hθ).quasiMeasurePreserving.ae (designLaw_cube_ae θ)
  rw [regularPairScore_mean_eq_signal C θ hθ k hk]
  let R := fun z : Observation d => θ.regression z.1
  have hR2 : Integrable (fun z => R z ^ 2) (observationLaw θ) :=
    (MemLp.of_bound (hθ.2.1.comp measurable_fst).aestronglyMeasurable C.holderBound
      (hcube.mono fun z hz => by simpa only [Real.norm_eq_abs, Function.comp_def, R] using admissible_regression_value_bound C θ hθ z.1 hz)).integrable_sq
  have hd : Integrable (fun z : Observation d × Observation d => R z.1 ^ 2 + R z.2 ^ 2)
      ((observationLaw θ).prod (observationLaw θ)) := (hR2.comp_fst _).add (hR2.comp_snd _)
  have hsig : Integrable (pairWindowScore (regularObservationLabel k hk) R 0) ((observationLaw θ).prod (observationLaw θ)) :=
    hd.mono'
      (pairWindowScore_measurable _ (regularObservationLabel_measurable k hk) R (hθ.2.1.comp measurable_fst) 0).aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa only [abs_zero, add_zero, Real.norm_eq_abs] using pairWindowScore_abs_le (regularObservationLabel k hk) R 0 z)
  have hD := (sameLabelKernel_memLp (observationLaw θ) _ (regularObservationLabel_measurable k hk)).integrable (by norm_num)
  have hb := integral_mono_ae hsig (hD.const_mul (regularGridOscillation C k ^ 2 / 2)) <| by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hcube, Measure.quasiMeasurePreserving_snd.ae hcube] with z hz1 hz2
    classical
    by_cases he : regularObservationLabel k hk z.1 = regularObservationLabel k hk z.2
    · have hs := pow_le_pow_left₀ (abs_nonneg _)
        (regular_grid_same_cell_regression_difference C θ hθ k hk z.1.1 z.2.1 hz1 hz2 he) 2
      simp only [sq_abs] at hs
      simp only [pairWindowScore, sameLabelKernel, if_pos he, sub_zero, mul_one, R]
      exact div_le_div_of_nonneg_right hs (by norm_num)
    · simp [pairWindowScore, sameLabelKernel, he]
  rw [integral_const_mul, sameLabelKernel_integral (observationLaw θ) _ (regularObservationLabel_measurable k hk)] at hb
  simpa only [regularObservationLabel_mass C θ hθ k hk, regularGridCollisionMass] using hb

-- Stabilized ratio risk

def stabilizedRatio {Ω : Type*} (lo hi a : ℝ) (N D : Ω → ℝ) (x : Ω) : ℝ :=
  clip lo hi (N x / max (D x) a)

theorem stabilizedRatio_measurable {Ω : Type*} [MeasurableSpace Ω]
    (lo hi a : ℝ) {N D : Ω → ℝ} (hN : Measurable N) (hD : Measurable D) :
    Measurable (stabilizedRatio lo hi a N D) :=
  (clip_lipschitz lo hi).continuous.measurable.comp (hN.div (hD.max measurable_const))

theorem stabilizedRatio_error_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {lo hi a V : ℝ} {N D : Ω → ℝ}
    (hN : Measurable N) (hD : Measurable D) (hlo : lo ≤ V) (hhi : V ≤ hi) :
    MemLp (fun x => stabilizedRatio lo hi a N D x - V) 2 μ :=
  MemLp.of_bound ((stabilizedRatio_measurable lo hi a hN hD).sub measurable_const).aestronglyMeasurable (hi - lo)
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, stabilizedRatio] using clip_error_le_diameter hlo hhi (x := N x / max (D x) a))

theorem stabilized_ratio_mse_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {lo hi a V ED : ℝ} {N D : Ω → ℝ}
    (hN : Measurable N) (hD : Measurable D)
    (hS : MemLp (fun x => N x - V * D x) 2 μ) (hD2 : MemLp D 2 μ)
    (ha : 0 < a) (hlo : lo ≤ V) (hhi : V ≤ hi) (hV : 0 ≤ V) (hED : 2 * a ≤ ED) :
    (∫ x, (stabilizedRatio lo hi a N D x - V) ^ 2 ∂μ) ≤
      (2 / a ^ 2) * ((∫ x, (N x - V * D x) ^ 2 ∂μ) + hi ^ 2 * (∫ x, (D x - ED) ^ 2 ∂μ)) := by
  have hDc : MemLp (fun x => D x - ED) 2 μ := hD2.sub (memLp_const ED)
  have hiR : Integrable (fun x => (2 / a ^ 2) * ((N x - V * D x) ^ 2 + hi ^ 2 * (D x - ED) ^ 2)) μ :=
    (hS.integrable_sq.add (hDc.integrable_sq.const_mul _)).const_mul _
  have hb := integral_mono (stabilizedRatio_error_memLp μ (a := a) hN hD hlo hhi).integrable_sq hiR fun x => by
    have hs := pow_le_pow_left₀ (abs_nonneg _) (stabilized_ratio_error ha hlo hhi hV hED (N := N x) (D := D x)) 2
    rw [sq_abs] at hs
    refine hs.trans ?_
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_left add_sq_le (sq_nonneg _)).trans_eq
      (by rw [sq_abs, mul_pow, sq_abs]; ring)
  rwa [integral_const_mul,
    integral_add (f := fun x => (N x - V * D x) ^ 2) (g := fun x => hi ^ 2 * (D x - ED) ^ 2)
      hS.integrable_sq (hDc.integrable_sq.const_mul _),
    integral_const_mul] at hb

theorem stabilized_ratio_lintegral_mse_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {lo hi a V ED : ℝ} {N D : Ω → ℝ}
    (hN : Measurable N) (hD : Measurable D)
    (hS : MemLp (fun x => N x - V * D x) 2 μ) (hD2 : MemLp D 2 μ)
    (ha : 0 < a) (hlo : lo ≤ V) (hhi : V ≤ hi) (hV : 0 ≤ V) (hED : 2 * a ≤ ED) :
    (∫⁻ x, ENNReal.ofReal ((stabilizedRatio lo hi a N D x - V) ^ 2) ∂μ) ≤
      ENNReal.ofReal ((2 / a ^ 2) * ((∫ x, (N x - V * D x) ^ 2 ∂μ) + hi ^ 2 * (∫ x, (D x - ED) ^ 2 ∂μ))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (stabilizedRatio_error_memLp μ (a := a) hN hD hlo hhi).integrable_sq
    (Eventually.of_forall fun _ => sq_nonneg _)]
  exact ENNReal.ofReal_mono (stabilized_ratio_mse_le μ hN hD hS hD2 ha hlo hhi hV hED)

-- Bounded pair mean operators

section PairOperators
set_option synthInstance.maxHeartbeats 200000

abbrev PairVector := EuclideanSpace ℝ (Fin 3)

def pairResponseVector (y y' : ℝ) : PairVector := WithLp.toLp 2 ![y', y, 1]
def pairCoordinateVector (i : Fin 3) : PairVector := WithLp.toLp 2 (Pi.single i 1)

def pairNoiseOperator : PairVector →L[ℝ] PairVector :=
  InnerProductSpace.rankOne ℝ (pairCoordinateVector 0) (pairCoordinateVector 0) +
    InnerProductSpace.rankOne ℝ (pairCoordinateVector 1) (pairCoordinateVector 1)

def pairScoreOperator (V y y' : ℝ) : PairVector →L[ℝ] PairVector :=
  InnerProductSpace.rankOne ℝ (pairResponseVector y y') (pairResponseVector y y') - V • pairNoiseOperator

private lemma pairResponseVector_norm_sq (y y' : ℝ) :
    ‖pairResponseVector y y'‖ ^ 2 = y' ^ 2 + y ^ 2 + 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]; simp [pairResponseVector, Fin.sum_univ_succ, add_assoc]

theorem pairNoiseOperator_norm_le : ‖pairNoiseOperator‖ ≤ 2 := by
  have hc (i : Fin 3) : ‖pairCoordinateVector i‖ = 1 := by
    have hs : ‖pairCoordinateVector i‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]; simp [pairCoordinateVector, Pi.single_apply, Finset.sum_ite_eq']
    nlinarith [norm_nonneg (pairCoordinateVector i)]
  have h := norm_add_le
    (InnerProductSpace.rankOne ℝ (pairCoordinateVector 0) (pairCoordinateVector 0))
    (InnerProductSpace.rankOne ℝ (pairCoordinateVector 1) (pairCoordinateVector 1))
  norm_num only [InnerProductSpace.norm_rankOne, hc, one_mul] at h
  exact h

theorem pairScoreOperator_norm_sq_le (V y y' : ℝ) :
    ‖pairScoreOperator V y y'‖ ^ 2 ≤ 6 * (y ^ 4 + y' ^ 4 + 1) + 8 * V ^ 2 := by
  have hn : ‖pairScoreOperator V y y'‖ ≤ ‖pairResponseVector y y'‖ ^ 2 + 2 * |V| := by
    refine (norm_sub_le _ _).trans ?_
    simp only [InnerProductSpace.norm_rankOne, norm_smul, Real.norm_eq_abs]
    have hp := mul_le_mul_of_nonneg_left pairNoiseOperator_norm_le (abs_nonneg V)
    change _ ≤ _; nlinarith
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hr : ‖pairResponseVector y y'‖ ^ 4 ≤ 3 * (y ^ 4 + y' ^ 4 + 1) := by
    rw [show ‖pairResponseVector y y'‖ ^ 4 = (‖pairResponseVector y y'‖ ^ 2) ^ 2 by ring, pairResponseVector_norm_sq]
    nlinarith [sq_nonneg (y ^ 2 - y' ^ 2), sq_nonneg (y ^ 2 - 1), sq_nonneg (y' ^ 2 - 1)]
  nlinarith [sq_abs V, sq_nonneg (‖pairResponseVector y y'‖ ^ 2 - 2 * |V|)]

private lemma pairResponseVector_continuous : Continuous fun z : ℝ × ℝ => pairResponseVector z.1 z.2 :=
  (PiLp.continuous_toLp 2 fun _ : Fin 3 => ℝ).comp (continuous_pi fun i => by fin_cases i <;> simp [pairResponseVector] <;> fun_prop)

theorem pairScoreOperator_continuous (V : ℝ) :
    Continuous fun z : ℝ × ℝ => pairScoreOperator V z.1 z.2 :=
  (((InnerProductSpace.rankOne ℝ).continuous.comp pairResponseVector_continuous).clm_apply
    pairResponseVector_continuous).sub continuous_const

theorem pairResponseVector_inner (a : PairVector) (y y' : ℝ) :
    ⟪a, pairResponseVector y y'⟫ = a 0 * y' + a 1 * y + a 2 := by
  simp [PiLp.inner_apply, pairResponseVector, RCLike.inner_apply, Fin.sum_univ_succ]; ring

theorem pairNoiseOperator_inner (a b : PairVector) :
    ⟪a, pairNoiseOperator b⟫ = a 0 * b 0 + a 1 * b 1 := by
  simp only [pairNoiseOperator, ContinuousLinearMap.add_apply, inner_add_right,
    InnerProductSpace.inner_right_rankOne_apply]
  simp [pairCoordinateVector, PiLp.inner_apply, RCLike.inner_apply]

theorem pairScoreOperator_inner_polynomial (V y y' : ℝ) (a b : PairVector) :
    ⟪a, pairScoreOperator V y y' b⟫ =
      (a 0 * b 0) * y' ^ 2 + (a 1 * b 1) * y ^ 2 +
      (a 0 * b 1 + a 1 * b 0) * (y * y') +
      (a 0 * b 2 + a 2 * b 0) * y' +
      (a 1 * b 2 + a 2 * b 1) * y + a 2 * b 2 -
      V * (a 0 * b 0 + a 1 * b 1) := by
  simp only [pairScoreOperator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    inner_sub_right, inner_smul_right, InnerProductSpace.inner_right_rankOne_apply,
    pairResponseVector_inner, pairNoiseOperator_inner]
  rw [real_inner_comm b (pairResponseVector y y'), pairResponseVector_inner]; ring

def regularPairDesignMeasure {d : ℕ} (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k) :
    Measure (Covariate d × Covariate d) :=
  ENNReal.ofReal ((k : ℝ) ^ d) • ((designLaw θ).prod (designLaw θ)).restrict
    {z | regularGridCell k hk z.1 = regularGridCell k hk z.2}

theorem regularPairDesignMeasure_isFinite {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    IsFiniteMeasure (regularPairDesignMeasure θ k hk) := by
  let := designLaw_isProbability C θ hθ
  exact (((designLaw θ).prod (designLaw θ)).restrict _).smul_finite ENNReal.ofReal_ne_top

theorem regularPairDesignMeasure_integral {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Covariate d × Covariate d → E) :
    (∫ z, f z ∂regularPairDesignMeasure θ k hk) =
      (k : ℝ) ^ d • ∫ z, sameLabelKernel (regularGridCell k hk) z • f z ∂(designLaw θ).prod (designLaw θ) := by
  let := designLaw_isProbability C θ hθ
  have hlabel := regular_grid_cell_measurable (d := d) k hk
  have hC : MeasurableSet {z : Covariate d × Covariate d | regularGridCell k hk z.1 = regularGridCell k hk z.2} :=
    measurableSet_eq_fun (hlabel.comp measurable_fst) (hlabel.comp measurable_snd)
  rw [regularPairDesignMeasure, integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg (Nat.cast_nonneg k) d),
    show (fun z => sameLabelKernel (regularGridCell k hk) z • f z) =
      {z | regularGridCell k hk z.1 = regularGridCell k hk z.2}.indicator f from
      funext fun z => by classical by_cases hz : regularGridCell k hk z.1 = regularGridCell k hk z.2 <;> simp [sameLabelKernel, hz],
    integral_indicator hC]

theorem regularPairDesignMeasure_mass_bounds {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    1 ≤ (regularPairDesignMeasure θ k hk).real univ ∧
      (regularPairDesignMeasure θ k hk).real univ ≤ C.densityUpper := by
  let := designLaw_isProbability C θ hθ
  have hi := regularPairDesignMeasure_integral C θ hθ k hk fun _ => (1 : ℝ)
  simp only [integral_const, smul_eq_mul, mul_one,
    sameLabelKernel_integral (designLaw θ) (regularGridCell k hk) (regular_grid_cell_measurable k hk)] at hi
  rw [hi, show (∑ c, (designLaw θ).real (regularGridCell k hk ⁻¹' {c}) ^ 2) = regularGridCollisionMass θ k hk from rfl]
  have hkp : 0 < (k : ℝ) ^ d := pow_pos (by exact_mod_cast hk) d
  exact ⟨by simpa [hkp.ne', mul_div_cancel₀] using mul_le_mul_of_nonneg_left (regularGridCollisionMass_lower C θ hθ k hk) hkp.le,
    by simpa [hkp.ne', mul_comm, mul_div_cancel₀] using mul_le_mul_of_nonneg_left (regularGridCollisionMass_upper C θ hθ k hk) hkp.le⟩

theorem regularPairDesignMeasure_fst_cube_le {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    (regularPairDesignMeasure θ k hk).map Prod.fst ≤ ENNReal.ofReal (C.densityUpper ^ 2) • cubeVolume d := by
  let := designLaw_isProbability C θ hθ
  have hkp : 0 < (k : ℝ) ^ d := pow_pos (by exact_mod_cast hk) d
  have hp : 0 ≤ C.densityUpper := by linarith [C.one_lt_densityUpper]
  have hlabel := regular_grid_cell_measurable (d := d) k hk
  have hC : MeasurableSet {z : Covariate d × Covariate d | regularGridCell k hk z.1 = regularGridCell k hk z.2} :=
    measurableSet_eq_fun (hlabel.comp measurable_fst) (hlabel.comp measurable_snd)
  have hfst : (regularPairDesignMeasure θ k hk).map Prod.fst ≤ ENNReal.ofReal C.densityUpper • designLaw θ := by
    refine Measure.le_iff.2 fun A hA => ?_
    rw [Measure.map_apply measurable_fst hA, regularPairDesignMeasure, Measure.smul_apply,
      Measure.restrict_apply (measurable_fst hA), Measure.prod_apply ((measurable_fst hA).inter hC), Measure.smul_apply]
    let cap := C.densityUpper / (k : ℝ) ^ d
    have hi : (∫⁻ x, designLaw θ (Prod.mk x ⁻¹' (Prod.fst ⁻¹' A ∩ {z | regularGridCell k hk z.1 = regularGridCell k hk z.2})) ∂designLaw θ) ≤
        ENNReal.ofReal cap * designLaw θ A := by
      refine (lintegral_mono fun x => ?_).trans_eq (lintegral_indicator_const hA _)
      change designLaw θ (Prod.mk x ⁻¹' _) ≤ _
      by_cases hx : x ∈ A
      · rw [show Prod.mk x ⁻¹' (Prod.fst ⁻¹' A ∩ {z | regularGridCell k hk z.1 = regularGridCell k hk z.2}) =
          regularGridCell k hk ⁻¹' {regularGridCell k hk x} by ext y; simp [hx, eq_comm], Set.indicator_of_mem hx]
        simpa only [regularGridProbability, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
          ENNReal.ofReal_le_ofReal (regularGridProbability_cap C θ hθ k hk (regularGridCell k hk x))
      · rw [show Prod.mk x ⁻¹' (Prod.fst ⁻¹' A ∩ {z | regularGridCell k hk z.1 = regularGridCell k hk z.2}) = ∅ by
          ext y; simp [hx], measure_empty, Set.indicator_of_notMem hx]
    calc ENNReal.ofReal ((k : ℝ) ^ d) • _
      _ ≤ ENNReal.ofReal ((k : ℝ) ^ d) * (ENNReal.ofReal cap * designLaw θ A) := by
          change ENNReal.ofReal ((k : ℝ) ^ d) * _ ≤ _; gcongr
      _ = ENNReal.ofReal C.densityUpper • designLaw θ A := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hkp.le, show (k : ℝ) ^ d * cap = C.densityUpper from mul_div_cancel₀ _ hkp.ne', smul_eq_mul]
  calc (regularPairDesignMeasure θ k hk).map Prod.fst
    _ ≤ ENNReal.ofReal C.densityUpper • designLaw θ := hfst
    _ ≤ ENNReal.ofReal C.densityUpper • (ENNReal.ofReal C.densityUpper • cubeVolume d) := by
        gcongr; exact admissible_designLaw_le_cubeVolume C θ hθ
    _ = _ := by rw [smul_smul, ← ENNReal.ofReal_mul hp, ← pow_two]

def boundedRegression {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (x : Covariate d) : ℝ := clip (-C.holderBound) C.holderBound (θ.regression x)

def boundedPairRegressionOperator {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (w : Covariate d × Covariate d) : PairVector →L[ℝ] PairVector :=
  InnerProductSpace.rankOne ℝ
    (pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2))
    (pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2))

theorem boundedPairRegressionOperator_norm_le {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (w : Covariate d × Covariate d) :
    ‖boundedPairRegressionOperator C θ w‖ ≤ 2 * C.holderBound ^ 2 + 1 := by
  rw [boundedPairRegressionOperator, InnerProductSpace.norm_rankOne, ← pow_two, pairResponseVector_norm_sq]
  have hb (x : Covariate d) : |boundedRegression C θ x| ≤ C.holderBound :=
    abs_le.2 (clip_mem_Icc (x := θ.regression x) (by linarith [C.holderBound_pos]))
  have h1 := pow_le_pow_left₀ (abs_nonneg _) (hb w.1) 2
  have h2 := pow_le_pow_left₀ (abs_nonneg _) (hb w.2) 2
  simp only [sq_abs] at h1 h2; linarith

theorem boundedPairRegressionOperator_symmetric {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (w : Covariate d × Covariate d) (a b : PairVector) :
    ⟪a, boundedPairRegressionOperator C θ w b⟫ = ⟪boundedPairRegressionOperator C θ w a, b⟫ := by
  simp only [boundedPairRegressionOperator, InnerProductSpace.rankOne_apply,
    inner_smul_right, inner_smul_left, real_inner_comm, starRingEnd_apply, star_trivial]; ring

theorem boundedPairRegressionOperator_measurable_apply {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    Measurable fun z : (Covariate d × Covariate d) × PairVector =>
      boundedPairRegressionOperator C θ z.1 z.2 := by
  have hbm : Measurable (boundedRegression C θ) := (clip_lipschitz _ _).continuous.measurable.comp hθ.2.1
  have hv : Measurable fun w : Covariate d × Covariate d =>
      pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2) :=
    pairResponseVector_continuous.measurable.comp ((hbm.comp measurable_fst).prodMk (hbm.comp measurable_snd))
  simp only [boundedPairRegressionOperator, InnerProductSpace.rankOne_apply]
  exact (show Continuous fun z : ℝ × PairVector => z.1 • z.2 from continuous_fst.smul continuous_snd).measurable.comp
    (((hv.comp measurable_fst).inner measurable_snd).prodMk (hv.comp measurable_fst))

theorem regularPairDesignMeasure_cube_ae {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    ∀ᵐ w ∂regularPairDesignMeasure θ k hk, w.1 ∈ unitCube d ∧ w.2 ∈ unitCube d := by
  let := designLaw_isProbability C θ hθ
  refine (Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict).ae_le ?_
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := designLaw θ) (ν := designLaw θ)).ae (designLaw_cube_ae θ),
    (Measure.quasiMeasurePreserving_snd (μ := designLaw θ) (ν := designLaw θ)).ae (designLaw_cube_ae θ)] with _ hx hy
  exact ⟨hx, hy⟩

theorem boundedPairRegressionOperator_eq_ae {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    boundedPairRegressionOperator C θ =ᵐ[regularPairDesignMeasure θ k hk]
      fun w => InnerProductSpace.rankOne ℝ (pairResponseVector (θ.regression w.1) (θ.regression w.2))
        (pairResponseVector (θ.regression w.1) (θ.regression w.2)) := by
  have heq_cube {x : Covariate d} (hx : x ∈ unitCube d) : boundedRegression C θ x = θ.regression x := by
    have h := abs_le.mp (admissible_regression_value_bound C θ hθ x hx); exact clip_target h.1 h.2
  filter_upwards [regularPairDesignMeasure_cube_ae C θ hθ k hk] with w hw
  simp only [boundedPairRegressionOperator, heq_cube hw.1, heq_cube hw.2]

end PairOperators
end PartitionAndPairScores
end NearlyMinimax
