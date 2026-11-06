module
public import Mathlib
public import NearlyMinimax.FinitePartitionMoments
public import NearlyMinimax.ObservationMoments
@[expose] public section
noncomputable section
section
section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace NearlyMinimax.PairUStatistic
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {i j k : ι}
def orderedPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2)
theorem sum_orderedPairs  (f : Fin n × Fin n → ℝ) :
    (∑ p ∈ orderedPairs n, f p) = ∑ i, ∑ j with j ≠ i, f (i, j) := by
  simp only [orderedPairs, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [ne_comm]
theorem orderedPairs_card (n : ℕ) : (orderedPairs n).card = n * (n - 1) := by
  have hfilter (i : Fin n) :
      Finset.univ.filter (fun j : Fin n => j ≠ i) = Finset.univ.erase i := by
    ext j
    simp
  have he := sum_orderedPairs (n := n) (fun _ => ↑1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at he
  simp only [hfilter, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, nsmul_eq_mul] at he
  exact_mod_cast he
theorem orderedPairs_first_count  (i : Fin n) :
    (∑ p ∈ orderedPairs n, if p.1 = i then (1 : ℝ) else 0) = (n - 1 : ℕ) := by
  rw [sum_orderedPairs, Finset.sum_eq_single i]
  · have hfilter :
        Finset.univ.filter (fun k : Fin n => k ≠ i) = Finset.univ.erase i := by
      ext k
      simp
    simp only [hfilter, ite_true]
    simp
  · intro j _ hji
    simp [hji]
  · simp
theorem sum_orderedPairs_swap  (f : Fin n × Fin n → ℝ) :
    (∑ p ∈ orderedPairs n, f p.swap) = ∑ p ∈ orderedPairs n, f p := by
  apply Finset.sum_bij (fun p _ => p.swap)
  · intro p hp
    simpa only [orderedPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.swap, ne_comm] using hp
  · intro a _ b _ hab
    exact Prod.swap_injective hab
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    simpa only [orderedPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.swap, ne_comm] using hb
  · intro p _
    rfl
theorem orderedPairs_single_count  {p : Fin n × Fin n}
    (hp : p ∈ orderedPairs n) :
    (∑ q ∈ orderedPairs n, if q = p then (1 : ℝ) else 0) = 1 := by
  simp [hp]
def overlapMajorant  (p q : Fin n × Fin n) (A B : ℝ) : ℝ :=
  B * ((if q.1 = p.1 then 1 else 0) + (if q.2 = p.1 then 1 else 0) +
    (if q.1 = p.2 then 1 else 0) + (if q.2 = p.2 then 1 else 0)) +
  A * ((if q = p then 1 else 0) + (if q = p.swap then 1 else 0))
theorem overlap_majorant_sum  {p : Fin n × Fin n}
    (hp : p ∈ orderedPairs n) (A B : ℝ) :
    (∑ q ∈ orderedPairs n, overlapMajorant p q A B) =
      4 * (n - 1 : ℕ) * B + 2 * A := by
  have hps : p.swap ∈ orderedPairs n := by
    simpa only [orderedPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.swap, ne_comm] using hp
  have h_orderedPairs_second_count (i : Fin n) : (∑ p ∈ orderedPairs n, if p.2 = i then (1 : ℝ) else 0) = (n - 1 : ℕ) := (sum_orderedPairs_swap (fun p : Fin n × Fin n => if p.1 = i then (1 : ℝ) else 0)).trans
    (orderedPairs_first_count i)
  simp only [overlapMajorant, Finset.sum_add_distrib, ← Finset.mul_sum,
    orderedPairs_first_count, h_orderedPairs_second_count,
    orderedPairs_single_count hp, orderedPairs_single_count hps]
  ring
variable {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
variable {ν : Measure Ω} {μ : Measure E} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
theorem integral_comp_measurePreserving (f : Ω → E)
    (hf : MeasurePreserving f ν μ) (g : E → ℝ) (hg : Measurable g) :
    (∫ x, g (f x) ∂ν) = ∫ y, g y ∂μ := by
  rw [← hf.map_eq]
  exact (integral_map hf.aemeasurable hg.aestronglyMeasurable).symm
theorem pair_measurePreserving (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {i j : ι} (hij : i ≠ j) :
    MeasurePreserving (fun x => (X i x, X j x)) ν (μ.prod μ) := by
  refine ⟨(hX i).measurable.prodMk (hX j).measurable, ?_⟩
  rw [(hind.indepFun hij).map_prod_eq_prod_map_map (hX i).aemeasurable
    (hX j).aemeasurable, (hX i).map_eq, (hX j).map_eq]
theorem kernel_pair_memLp (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ))
    {i j : ι} (hij : i ≠ j) : MemLp (fun x => K (X i x, X j x)) 2 ν :=
  hK.comp_measurePreserving (pair_measurePreserving X hind hX hij)
theorem kernel_pair_integral (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hK : Measurable K) {i j : ι} (hij : i ≠ j) :
    (∫ x, K (X i x, X j x) ∂ν) = ∫ z, K z ∂μ.prod μ :=
  integral_comp_measurePreserving _ (pair_measurePreserving X hind hX hij) K hK
theorem shared_product_integrable {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    Integrable (fun z : (E × E) × E => K z.1 * K (z.1.1, z.2))
      ((μ.prod μ).prod μ) := (hK.comp_measurePreserving measurePreserving_fst).integrable_mul (hK.comp_measurePreserving (measurePreserving_fst.prod (MeasurePreserving.id μ)))
def rowIntegral (K : E × E → ℝ) (x : E) : ℝ := ∫ y, K (x, y) ∂μ
theorem row_product_integrable {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    Integrable (fun z : E × E => K z * rowIntegral (μ := μ) K z.1) (μ.prod μ) := by
  simpa only [integral_const_mul, rowIntegral] using ((shared_product_integrable hK).integral_prod_left)
theorem rowIntegral_sq_integrable {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    Integrable (fun x => rowIntegral (μ := μ) K x ^ 2) μ := by
  simpa only [integral_mul_const, rowIntegral, pow_two] using ((row_product_integrable hK).integral_prod_left)
theorem kernel_shared_product_integral (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ))
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∫ x, K (X i x, X j x) * K (X i x, X k x) ∂ν) =
      ∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ := by
  have hg  :=
    (hmK.comp measurable_fst).mul (hmK.comp (measurable_fst.fst.prodMk measurable_snd))
  have h_triple_measurePreserving : MeasurePreserving (fun x => ((X i x, X j x), X k x)) ν ((μ.prod μ).prod μ) := by
    refine ⟨((hX i).measurable.prodMk (hX j).measurable).prodMk (hX k).measurable, ?_⟩
    rw [(hind.indepFun_prodMk (fun i => (hX i).measurable) i j k hik hjk).map_prod_eq_prod_map_map
        ((hX i).aemeasurable.prodMk (hX j).aemeasurable) (hX k).aemeasurable,
      (pair_measurePreserving X hind hX hij).map_eq, (hX k).map_eq]
  have h_shared_product_integral : (∫ z : (E × E) × E, K z.1 * K (z.1.1, z.2) ∂(μ.prod μ).prod μ) =
      ∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ := by
    rw [integral_prod _ (shared_product_integrable hK)]
    simp only [integral_const_mul]
    change (∫ z : E × E, K z * rowIntegral (μ := μ) K z.1 ∂μ.prod μ) = _
    rw [integral_prod _ (row_product_integrable hK)]
    simp only [integral_mul_const, rowIntegral, pow_two]
  exact (integral_comp_measurePreserving _
    h_triple_measurePreserving _ hg).trans
    h_shared_product_integral
def pairAverage (n : ℕ) (K : E × E → ℝ) (x : Fin n → E) : ℝ :=
  ((n : ℝ) * (n - 1 : ℕ))⁻¹ * ∑ i, ∑ j with j ≠ i, K (x i, x j)
theorem kernel_pair_covariance_le [DecidableEq ι] (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ))
    (hsym : ∀ x y, K (x, y) = K (y, x))
    {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) :
    covariance (fun x => K (X i x, X j x)) (fun x => K (X k x, X l x)) ν ≤
      (∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ) *
        ((if k = i then 1 else 0) + (if l = i then 1 else 0) +
          (if k = j then 1 else 0) + (if l = j then 1 else 0)) +
      (∫ z, K z ^ 2 ∂μ.prod μ) *
        ((if (k, l) = (i, j) then 1 else 0) + (if (k, l) = (j, i) then 1 else 0)) := by
  have h_kernel_pair_sq_integral  := kernel_pair_integral X hind hX (hmK.pow_const 2) hij
  have : 0 ≤ ∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have : 0 ≤ (∫ z, K z ∂μ.prod μ) ^ 2 := sq_nonneg _
  rw [covariance_eq_sub (kernel_pair_memLp X hind hX hK hij)
    (kernel_pair_memLp X hind hX hK hkl)]
  simp only [Pi.mul_apply]
  have h_kernel_pair_product_classification : (∫ x, K (X i x, X j x) * K (X k x, X l x) ∂ν) =
      if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then ∫ z, K z ^ 2 ∂μ.prod μ
      else if i = k ∨ i = l ∨ j = k ∨ j = l then
        ∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ else (∫ z, K z ∂μ.prod μ) ^ 2 := by
    by_cases hik : i = k
    · subst k
      by_cases hjl : j = l
      · subst l
        simpa only [true_and, true_or, or_true, ite_true, pow_two] using
          h_kernel_pair_sq_integral
      · have hji  := Ne.symm hij
        simp only [hjl, and_false, hji, false_or, ite_false, true_or, ite_true]
        exact kernel_shared_product_integral X hind hX hmK hK hij hkl hjl
    · by_cases hil : i = l
      · subst l
        by_cases hjk : j = k
        · subst k
          have he : (fun x => K (X i x, X j x) * K (X j x, X i x)) =
              (fun x => K (X i x, X j x) ^ 2) := by
            funext x
            rw [hsym (X j x) (X i x), pow_two]
          rw [he]
          simp only [and_true, or_true, ite_true]
          exact h_kernel_pair_sq_integral
        · have  := hkl
          simp only [hik, false_and, true_and, hjk, or_false, ite_false, true_or,
            false_or, ite_true]
          have he : (fun x => K (X i x, X j x) * K (X k x, X i x)) =
              (fun x => K (X i x, X j x) * K (X i x, X k x)) := by
            funext x
            rw [hsym (X k x) (X i x)]
          rw [he]
          exact kernel_shared_product_integral X hind hX hmK hK hij hik hjk
      · by_cases hjk : j = k
        · subst k
          have he : (fun x => K (X i x, X j x) * K (X j x, X l x)) =
              (fun x => K (X j x, X i x) * K (X j x, X l x)) := by
            funext x
            rw [hsym (X i x) (X j x)]
          rw [he]
          simp only [hik, false_and, hil, false_or, true_or, ite_false, ite_true]
          exact kernel_shared_product_integral X hind hX hmK hK (Ne.symm hij) hkl hil
        · by_cases hjl : j = l
          · subst l
            have he : (fun x => K (X i x, X j x) * K (X k x, X j x)) =
                (fun x => K (X j x, X i x) * K (X j x, X k x)) := by
              funext x
              rw [hsym (X i x) (X j x), hsym (X k x) (X j x)]
            rw [he]
            simp only [hik, false_and, hil, hjk, false_or, false_and, ite_false,
              or_true, ite_true]
            exact kernel_shared_product_integral X hind hX hmK hK (Ne.symm hij)
              (Ne.symm hkl) hik
          · simp only [hik, hil, hjk, hjl, false_and, false_or, ite_false]
            have hd := (hind.indepFun_prodMk_prodMk (fun i => (hX i).measurable)
              i j k l hik hil hjk hjl).comp hmK hmK
            have he := hd.integral_fun_mul_eq_mul_integral
              (hmK.comp ((hX i).measurable.prodMk (hX j).measurable)).aestronglyMeasurable
              (hmK.comp ((hX k).measurable.prodMk (hX l).measurable)).aestronglyMeasurable
            simp only [Function.comp_def] at he
            rw [he, kernel_pair_integral X hind hX hmK hij, kernel_pair_integral X hind hX hmK hkl,
              pow_two]
  rw [kernel_pair_integral X hind hX hmK hij, kernel_pair_integral X hind hX hmK hkl,
    ← pow_two, h_kernel_pair_product_classification]
  by_cases hik : i = k <;> by_cases hil : i = l <;>
    by_cases hjk : j = k <;> by_cases hjl : j = l <;>
    subst_vars <;>
    simp_all only [Prod.mk.injEq, ne_eq, eq_comm, not_true_eq_false, and_true, or_true, and_false, or_false, ite_true, ite_false, zero_add, add_zero, mul_zero, mul_one, sub_self] <;> nlinarith
theorem pairAverage_eq_orderedPairs {n : ℕ} (K : E × E → ℝ) (x : Fin n → E) :
    pairAverage n K x =
      ((n : ℝ) * (n - 1 : ℕ))⁻¹ * ∑ p ∈ orderedPairs n, K (x p.1, x p.2) := by
  rw [pairAverage, sum_orderedPairs]
theorem pairAverage_memLp_two  (X : Fin n → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    MemLp (fun x => pairAverage n K (fun i => X i x)) 2 ν := by
  simp only [pairAverage_eq_orderedPairs]
  apply MemLp.const_mul
  apply memLp_finsetSum
  intro p hp
  exact kernel_pair_memLp X hind hX hK (Finset.mem_filter.mp hp).2
theorem pairAverage_integral  (hn : 2 ≤ n) (X : Fin n → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ)) :
    (∫ x, pairAverage n K (fun i => X i x) ∂ν) = ∫ z, K z ∂μ.prod μ := by
  simp only [pairAverage_eq_orderedPairs]
  rw [integral_const_mul, integral_finsetSum]
  · have he : (∑ p ∈ orderedPairs n, ∫ x, K (X p.1 x, X p.2 x) ∂ν) =
        ∑ _p ∈ orderedPairs n, ∫ z, K z ∂μ.prod μ := by
      apply Finset.sum_congr rfl
      intro p hp
      exact kernel_pair_integral X hind hX hmK (Finset.mem_filter.mp hp).2
    rw [he, Finset.sum_const, orderedPairs_card, nsmul_eq_mul, Nat.cast_mul]
    have : 0 < n := by omega
    have : 0 < n - 1 := by omega
    exact inv_mul_cancel_left₀ (by positivity) _
  · intro p hp
    exact (kernel_pair_memLp X hind hX hK (Finset.mem_filter.mp hp).2).integrable (by norm_num)
theorem pairAverage_centered_sq_le  (hn : 2 ≤ n) (X : Fin n → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ))
    (hsym : ∀ x y, K (x, y) = K (y, x)) :
    (∫ x, (pairAverage n K (fun i => X i x) - ∫ z, K z ∂μ.prod μ) ^ 2 ∂ν) ≤
      4 / ↑n * (∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ) +
      2 / (↑n * (n - 1 : ℕ)) * (∫ z, K z ^ 2 ∂μ.prod μ) := by
  have h_pairAverage_variance_le : variance (fun x => pairAverage n K (fun i => X i x)) ν ≤
      4 / ↑n * (∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ) +
      2 / (↑n * (n - 1 : ℕ)) * (∫ z, K z ^ 2 ∂μ.prod μ) := by
    let A := ∫ z, K z ^ 2 ∂μ.prod μ
    let B := ∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ
    let Y : (Fin n × Fin n) → Ω → ℝ := fun p x => K (X p.1 x, X p.2 x)
    have hsum : (∑ p ∈ orderedPairs n, ∑ q ∈ orderedPairs n,
        covariance (Y p) (Y q) ν) ≤
        ↑n * (n - 1 : ℕ) * (4 * (n - 1 : ℕ) * B + 2 * A) := by
      calc
        _ ≤ ∑ p ∈ orderedPairs n, ∑ q ∈ orderedPairs n,
            overlapMajorant p q A B := by
          apply Finset.sum_le_sum
          intro p hp
          apply Finset.sum_le_sum
          intro q hq
          simpa only [Y, overlapMajorant, A, B, Prod.mk.eta, Prod.swap] using
            kernel_pair_covariance_le X hind hX hmK hK hsym
              (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
        _ = ∑ _p ∈ orderedPairs n, (4 * (n - 1 : ℕ) * B + 2 * A) := by
          exact Finset.sum_congr rfl (fun p hp => overlap_majorant_sum hp A B)
        _ = _ := by
          simp only [Finset.sum_const, orderedPairs_card, nsmul_eq_mul, Nat.cast_mul]
    simp only [pairAverage_eq_orderedPairs]
    rw [variance_const_mul, variance_fun_sum' (by intro p hp; exact kernel_pair_memLp X hind hX hK (Finset.mem_filter.mp hp).2)]
    calc
      _ ≤ (((n : ℝ) * (n - 1 : ℕ))⁻¹) ^ 2 *
          (↑n * (n - 1 : ℕ) * (4 * (n - 1 : ℕ) * B + 2 * A)) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = _ := by
        have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
        have : ((n - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : n - 1 ≠ 0)
        field_simp
        <;> ring
  have hv := h_pairAverage_variance_le
  rw [variance_eq_integral (pairAverage_memLp_two X hind hX hK).aemeasurable,
    pairAverage_integral hn X hind hX hmK hK] at hv
  exact hv
theorem pairAverage_measurable (n : ℕ) {K : E × E → ℝ} (hmK : Measurable K) :
    Measurable (pairAverage n K) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact hmK.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
end NearlyMinimax.PairUStatistic
end
open MeasureTheory Set Filter
open scoped BigOperators
namespace NearlyMinimax
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
section Partition
variable {X B : Type*} [MeasurableSpace X] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] [MeasurableEq B]
  (μ : Measure X) [IsProbabilityMeasure μ] (label : X → B) (hlabel : Measurable label)
include hlabel
def labelLocalizedKernel (g : X → ℝ) (z : X × X) : ℝ :=
  if label z.1 = label z.2 then g z.2 else 0
theorem labelLocalizedKernel_integrable (g ) (hg : Integrable g μ) :
    Integrable (labelLocalizedKernel label g) (μ.prod μ) := by
  have he : labelLocalizedKernel label g =
      {z : X × X | label z.1 = label z.2}.indicator (fun z => g z.2) := by
    funext z
    simp [labelLocalizedKernel, Set.indicator_apply]
  rw [he]
  exact (hg.comp_snd μ).indicator
    (measurableSet_eq_fun (hlabel.comp measurable_fst) (hlabel.comp measurable_snd))
omit hlabel in
theorem labelLocalizedKernel_row (g x) :
    (∫ y, labelLocalizedKernel label g (x, y) ∂μ) =
      ∫ y, (label ⁻¹' {label x}).indicator g y ∂μ := by
  congr 1
  funext y
  simp [labelLocalizedKernel, Set.indicator_apply, eq_comm]
theorem labelLocalizedKernel_integral_le (g ) (hg : Integrable g μ)
    (M ) (hloc : ∀ c : B,
      (∫ x, (label ⁻¹' {c}).indicator g x ∂μ) ≤ M * μ.real (label ⁻¹' {c})) :
    (∫ z, labelLocalizedKernel label g z ∂μ.prod μ) ≤
      M * ∑ c : B, μ.real (label ⁻¹' {c}) ^ 2 := by
  rw [integral_prod _ (labelLocalizedKernel_integrable μ label hlabel g hg)]
  simp_rw [labelLocalizedKernel_row μ label g]
  have hi := (labelLocalizedKernel_integrable μ label hlabel g hg).integral_prod_left
  simp_rw [labelLocalizedKernel_row μ label g] at hi
  calc
    _ ≤ ∫ x, M * μ.real (label ⁻¹' {label x}) ∂μ := by
      have h_partition_mass_integrable : Integrable (fun x => μ.real (label ⁻¹' {label x})) μ := by
        have hm : Measurable (fun x => μ.real (label ⁻¹' {label x})) :=
          (measurable_of_countable (fun c => μ.real (label ⁻¹' {c}))).comp hlabel
        apply (MemLp.of_bound hm.aestronglyMeasurable 1 (p := 1) ?_).integrable (by norm_num)
        filter_upwards [] with x
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact measureReal_le_one
      apply integral_mono hi (h_partition_mass_integrable.const_mul M)
      exact fun x => hloc (label x)
    _ = _ := by
      rw [integral_const_mul,
        finite_label_integral μ label hlabel (fun c => μ.real (label ⁻¹' {c}))]
      simp only [pow_two]
omit hlabel in
theorem sameLabelKernel_mul_eq_sum (r z) :
    sameLabelKernel label z * r z.1 * r z.2 =
      ∑ c : B, (label ⁻¹' {c}).indicator r z.1 * (label ⁻¹' {c}).indicator r z.2 := by
  rw [Finset.sum_eq_single (label z.1)]
  · by_cases he : label z.1 = label z.2
    · simp [sameLabelKernel, he]
    · simp [sameLabelKernel, he, Ne.symm he]
  · intro c hc hne
    simp [Set.indicator_apply, Ne.symm hne]
  · simp
def pairWindowScore (r : X → ℝ) (V : ℝ) (z : X × X) : ℝ :=
  if label z.1 = label z.2 then (r z.1 - r z.2) ^ 2 / 2 - V else 0
theorem pairWindowScore_measurable (r ) (hr : Measurable r) (V ) :
    Measurable (pairWindowScore label r V) := by
  exact Measurable.ite
    (measurableSet_eq_fun (hlabel.comp measurable_fst) (hlabel.comp measurable_snd))
    ((((hr.comp measurable_fst).sub (hr.comp measurable_snd)).pow_const 2
      |>.div_const 2).sub measurable_const) measurable_const
omit hlabel in
theorem pairWindowScore_symmetric (r V x y) :
    pairWindowScore label r V (x, y) = pairWindowScore label r V (y, x) := by
  unfold pairWindowScore
  simp only [Prod.fst, Prod.snd, eq_comm]
  split_ifs <;> ring
omit hlabel in
theorem pairWindowScore_abs_le (r V z) :
    |pairWindowScore label r V z| ≤ r z.1 ^ 2 + r z.2 ^ 2 + |V| := by
  unfold pairWindowScore
  split_ifs with h
  · calc
      _ ≤ |(r z.1 - r z.2) ^ 2 / 2| + |V| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_of_nonneg (by positivity : 0 ≤ (r z.1 - r z.2) ^ 2 / 2)]
        nlinarith [sq_nonneg (r z.1 + r z.2)]
  · simp only [abs_zero]
    positivity
omit hlabel in
theorem pairWindowScore_sq_le (r V z) :
    pairWindowScore label r V z ^ 2 ≤
      4 * (r z.1 ^ 4 + r z.2 ^ 4) + 2 * V ^ 2 := by
  unfold pairWindowScore
  split_ifs with h
  · have := add_sq_le (a := (r z.1 - r z.2) ^ 2 / 2) (b := -V)
    have h2 := (show Even 4 by decide).add_pow_le
      (a := r z.1) (b := -r z.2)
    norm_num at h2
    nlinarith
  · simp only [zero_pow (by decide : 2 ≠ 0)]
    positivity
theorem pairWindowScore_memLp (r ) (hr : Measurable r) (V )
    (h4 : Integrable (fun x => r x ^ 4) μ) :
    MemLp (pairWindowScore label r V) 2 (μ.prod μ) := by
  apply (memLp_two_iff_integrable_sq
    (pairWindowScore_measurable label hlabel r hr V).aestronglyMeasurable).mpr
  apply ((((h4.comp_fst μ).add (h4.comp_snd μ)).const_mul 4).add (integrable_const _)).mono'
    ((pairWindowScore_measurable label hlabel r hr V).pow_const 2).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pairWindowScore_sq_le label r V z
theorem pairWindowScore_energy_le (r ) (hr : Measurable r) (V M4 )
    (h4 : Integrable (fun x => r x ^ 4) μ)
    (hloc : ∀ c : B, (∫ x, (label ⁻¹' {c}).indicator (fun x => r x ^ 4) x ∂μ) ≤
      M4 * μ.real (label ⁻¹' {c})) :
    (∫ z, pairWindowScore label r V z ^ 2 ∂μ.prod μ) ≤
      (8 * M4 + 2 * V ^ 2) * ∑ c : B, μ.real (label ⁻¹' {c}) ^ 2 := by
  let L := labelLocalizedKernel label (fun x => r x ^ 4)
  have hiL : Integrable L (μ.prod μ) :=
    labelLocalizedKernel_integrable μ label hlabel _ h4
  have hiD := (sameLabelKernel_memLp μ label hlabel).integrable (by norm_num)
  have hd : Integrable (fun z => 4 * (L z + L z.swap) +
      2 * V ^ 2 * sameLabelKernel label z) (μ.prod μ) :=
    ((hiL.add hiL.swap).const_mul 4).add (hiD.const_mul _)
  have h_pairWindowScore_local_sq_le (z : X × X) : pairWindowScore label r V z ^ 2 ≤
      4 * (labelLocalizedKernel label (fun x => r x ^ 4) z +
        labelLocalizedKernel label (fun x => r x ^ 4) z.swap) +
      2 * V ^ 2 * sameLabelKernel label z := by
    by_cases h : label z.1 = label z.2
    · have hb := pairWindowScore_sq_le label r V z
      simp only [pairWindowScore, labelLocalizedKernel, sameLabelKernel,
        Prod.fst_swap, Prod.snd_swap, if_pos h, if_pos h.symm] at hb ⊢
      nlinarith
    · simp [pairWindowScore, labelLocalizedKernel, sameLabelKernel, h, Ne.symm h]
  have hb := integral_mono (pairWindowScore_memLp μ label hlabel r hr V h4).integrable_sq
    hd h_pairWindowScore_local_sq_le
  rw [integral_add
      (f := fun z => 4 * (L z + L z.swap))
      (g := fun z => 2 * V ^ 2 * sameLabelKernel label z)
      ((hiL.add hiL.swap).const_mul 4) (hiD.const_mul _),
    integral_const_mul, integral_add (f := L) (g := fun z => L z.swap) hiL hiL.swap,
    integral_prod_swap L, integral_const_mul, sameLabelKernel_integral μ label hlabel] at hb
  have := labelLocalizedKernel_integral_le μ label hlabel _ h4 M4 hloc
  dsimp [L] at hb
  nlinarith
theorem pairWindowScore_row_energy_le (r ) (hr : Measurable r)
    (V M2 M4 cap ) (hM2 : 0 ≤ M2) (hcap : 0 ≤ cap)
    (h2 : Integrable (fun x => r x ^ 2) μ)
    (h4 : Integrable (fun x => r x ^ 4) μ)
    (hglobal : (∫ x, r x ^ 4 ∂μ) ≤ M4)
    (hloc : ∀ c : B, (∫ x, (label ⁻¹' {c}).indicator (fun x => r x ^ 2) x ∂μ) ≤
      M2 * μ.real (label ⁻¹' {c}))
    (hmass : ∀ c : B, μ.real (label ⁻¹' {c}) ≤ cap) :
    (∫ x, (∫ y, pairWindowScore label r V (x, y) ∂μ) ^ 2 ∂μ) ≤
      2 * cap ^ 2 * (M4 + (|V| + M2) ^ 2) := by
  have hi := PairUStatistic.rowIntegral_sq_integrable
    (pairWindowScore_memLp μ label hlabel r hr V h4)
  have hd : Integrable (fun x => 2 * cap ^ 2 * (r x ^ 4 + (|V| + M2) ^ 2)) μ :=
    (h4.add (integrable_const _)).const_mul _
  have hp : ∀ x, (∫ y, pairWindowScore label r V (x, y) ∂μ) ^ 2 ≤
      2 * cap ^ 2 * (r x ^ 4 + (|V| + M2) ^ 2) := by
    intro x
    let p := μ.real (label ⁻¹' {label x})
    have : 0 ≤ p := measureReal_nonneg
    have : p ≤ cap := hmass (label x)
    have h_pairWindowScore_row_abs_le : |∫ y, pairWindowScore label r V (x, y) ∂μ| ≤
        μ.real (label ⁻¹' {label x}) * (r x ^ 2 + |V| + M2) := by
      let A := label ⁻¹' {label x}
      have hA : MeasurableSet A := (measurableSet_singleton _).preimage hlabel
      let e : X → ℝ := fun y => A.indicator (fun y => r x ^ 2 + r y ^ 2 + |V|) y
      have hiE : Integrable e μ :=
        (((integrable_const (r x ^ 2)).add h2).add (integrable_const |V|)).indicator hA
      have hpoint : ∀ y, ‖pairWindowScore label r V (x, y)‖ ≤ e y := by
        intro y
        by_cases he : label x = label y
        · simpa only [Real.norm_eq_abs, e, A, Set.indicator_of_mem
            (show y ∈ A from he.symm)] using pairWindowScore_abs_le label r V (x, y)
        · simp [pairWindowScore, e, A, Set.indicator_apply, he, Ne.symm he]
      have hiS : Integrable (fun y => pairWindowScore label r V (x, y)) μ := by
        apply hiE.mono' ((pairWindowScore_measurable label hlabel r hr V).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        exact Eventually.of_forall hpoint
      have hb : |∫ y, pairWindowScore label r V (x, y) ∂μ| ≤ ∫ y, e y ∂μ := by
        calc
          _ = ‖∫ y, pairWindowScore label r V (x, y) ∂μ‖ := (Real.norm_eq_abs _).symm
          _ ≤ ∫ y, ‖pairWindowScore label r V (x, y)‖ ∂μ := norm_integral_le_integral_norm _
          _ ≤ _ := integral_mono hiS.norm hiE hpoint
      have heq : (∫ y, e y ∂μ) = μ.real A * (r x ^ 2 + |V|) +
          ∫ y, A.indicator (fun y => r y ^ 2) y ∂μ := by
        dsimp [e]
        rw [integral_indicator hA]
        have he : (fun y => r x ^ 2 + r y ^ 2 + |V|) =
            (fun y => (r x ^ 2 + |V|) + r y ^ 2) := by funext y; ring
        rw [he, integral_add (integrable_const _) h2.restrict,
          integral_const, ← integral_indicator hA]
        simp only [measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul]
      rw [heq] at hb
      have := hloc (label x)
      dsimp [A] at hb
      nlinarith
    have hb := h_pairWindowScore_row_abs_le
    have : 0 ≤ |V| + M2 := add_nonneg (abs_nonneg _) hM2
    calc
      _ = |∫ y, pairWindowScore label r V (x, y) ∂μ| ^ 2 := (sq_abs _).symm
      _ ≤ (p * (r x ^ 2 + |V| + M2)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = p ^ 2 * (r x ^ 2 + (|V| + M2)) ^ 2 := by ring
      _ ≤ cap ^ 2 * (r x ^ 2 + (|V| + M2)) ^ 2 := by gcongr
      _ ≤ cap ^ 2 * (2 * ((r x ^ 2) ^ 2 + (|V| + M2) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left add_sq_le (sq_nonneg cap)
      _ = _ := by ring
  have hb := integral_mono hi hd hp
  rw [integral_const_mul, integral_add h4 (integrable_const _), integral_const] at hb
  simp at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add hglobal le_rfl) (by positivity))
theorem pairWindowScore_integral (r ) (hr : Measurable r) (V )
    (hr2 : MemLp r 2 μ) :
    (∫ z, pairWindowScore label r V z ∂μ.prod μ) =
      ∑ c : B, (μ.real (label ⁻¹' {c}) *
        (∫ x, (label ⁻¹' {c}).indicator (fun x => r x ^ 2) x ∂μ) -
        (∫ x, (label ⁻¹' {c}).indicator r x ∂μ) ^ 2 -
        V * μ.real (label ⁻¹' {c}) ^ 2) := by
  let L := labelLocalizedKernel label (fun x => r x ^ 2)
  let Q := fun z => sameLabelKernel label z * r z.1 * r z.2
  have hiL  :=
    labelLocalizedKernel_integrable μ label hlabel _ hr2.integrable_sq
  have h_sameLabelKernel_mul_integrable : Integrable (fun z => sameLabelKernel label z * r z.1 * r z.2) (μ.prod μ) := by
    have hr  := hr2.integrable (by norm_num)
    simp_rw [sameLabelKernel_mul_eq_sum label r]
    apply integrable_finsetSum
    intro c hc
    exact (hr.indicator ((measurableSet_singleton _).preimage hlabel)).mul_prod
      (hr.indicator ((measurableSet_singleton _).preimage hlabel))
  have hiQ  :=
    h_sameLabelKernel_mul_integrable
  have heq : pairWindowScore label r V =
      (fun z => (L z + L z.swap) / 2 - Q z - V * sameLabelKernel label z) := by
    funext z
    dsimp [pairWindowScore, L, Q, labelLocalizedKernel, sameLabelKernel]
    by_cases he : label z.1 = label z.2
    · simp only [ite_eq_left he, ite_eq_left he.symm, one_mul]
      ring
    · simp [he, Ne.symm he]
  rw [heq, integral_sub
      (f := fun z => (L z + L z.swap) / 2 - Q z)
      (g := fun z => V * sameLabelKernel label z)
      (((hiL.add hiL.swap).div_const 2).sub hiQ) (((sameLabelKernel_memLp μ label hlabel).integrable (by norm_num)).const_mul V),
    integral_sub (f := fun z => (L z + L z.swap) / 2) (g := Q)
      ((hiL.add hiL.swap).div_const 2) hiQ,
    integral_div, integral_add (f := L) (g := fun z => L z.swap) hiL hiL.swap,
    integral_prod_swap L, integral_const_mul]
  have h_sameLabelKernel_mul_integral : (∫ z, sameLabelKernel label z * r z.1 * r z.2 ∂μ.prod μ) =
      ∑ c : B, (∫ x, (label ⁻¹' {c}).indicator r x ∂μ) ^ 2 := by
    have hr  := hr2.integrable (by norm_num)
    simp_rw [sameLabelKernel_mul_eq_sum label r]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro c hc
      rw [integral_prod_mul]
      ring
    · intro c hc
      exact (hr.indicator ((measurableSet_singleton _).preimage hlabel)).mul_prod
        (hr.indicator ((measurableSet_singleton _).preimage hlabel))
  have h_labelLocalizedKernel_integral (g) (hg : Integrable g μ) : (∫ z, labelLocalizedKernel label g z ∂μ.prod μ) =
      ∑ c : B, μ.real (label ⁻¹' {c}) *
        (∫ x, (label ⁻¹' {c}).indicator g x ∂μ) := by
    rw [integral_prod _ (labelLocalizedKernel_integrable μ label hlabel g hg)]
    simp_rw [labelLocalizedKernel_row μ label g]
    exact finite_label_integral μ label hlabel
      (fun c => ∫ x, (label ⁻¹' {c}).indicator g x ∂μ)
  rw [h_labelLocalizedKernel_integral _ hr2.integrable_sq,
    h_sameLabelKernel_mul_integral,
    sameLabelKernel_integral μ label hlabel, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring
end Partition
end NearlyMinimax
end
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
def regularObservationLabel  (k ) (hk : 0 < k) :
    Observation d → (Fin d → Fin k) := fun z => regularGridCell k hk z.1
theorem regularObservationLabel_measurable  (k hk) :
    Measurable (regularObservationLabel (d := d) k hk) :=
  (regular_grid_cell_measurable k hk).comp measurable_fst
theorem regularObservationLabel_fiber  (k hk c) :
    (regularObservationLabel (d := d) k hk) ⁻¹' {c} =
      Prod.fst ⁻¹' ((regularGridCell k hk) ⁻¹' {c}) := rfl
theorem regularObservationLabel_mass {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k)
    (c : Fin d → Fin k) :
    (observationLaw θ).real ((regularObservationLabel k hk) ⁻¹' {c}) =
      regularGridProbability θ k hk c := by
  exact (observationLaw_fst_measurePreserving C θ hθ).measureReal_preimage
    ((measurableSet_singleton c).preimage (regular_grid_cell_measurable k hk)).nullMeasurableSet
def regularPairScore  (θ : RegressionParameter d) (k ) (hk : 0 < k) :
    Observation d × Observation d → ℝ :=
  pairWindowScore (regularObservationLabel k hk) Prod.snd θ.variance
theorem regularPairScore_memLp  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k hk) :
    MemLp (regularPairScore θ k hk) 2 ((observationLaw θ).prod (observationLaw θ)) := by
  let := observationLaw_isProbability C θ hθ
  exact pairWindowScore_memLp (observationLaw θ) _
    (regularObservationLabel_measurable k hk) Prod.snd measurable_snd θ.variance
    (observationLaw_response_fourth_integrable C θ hθ)
theorem observationLaw_regression_memLp_two  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    MemLp (fun z => θ.regression z.1) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  apply MemLp.of_bound (hθ.2.1.comp measurable_fst).aestronglyMeasurable C.holderBound
  filter_upwards [(observationLaw_fst_measurePreserving C θ hθ).quasiMeasurePreserving.ae
    (designLaw_cube_ae θ)] with z hz
  simpa only [Real.norm_eq_abs, Function.comp_def] using
    admissible_regression_value_bound C θ hθ z.1 hz
def regularGridOscillation  (C : ModelConstants d) (k : ℕ) : ℝ :=
  2 * (d + 1) * C.holderBound *
    (Real.sqrt d * (1 / k)) ^ elementarySmoothness C
end NearlyMinimax
