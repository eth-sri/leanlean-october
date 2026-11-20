module

public import NearlyMinimax.LiftL2


@[expose] public section

/-! Raw multilinear kernel moment bounds under genuine independent L²
observations. Increasing lift order requires no higher response moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace NearlyMinimax.KernelMomentBounds

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

variable {p k : ℕ} {X : Ω → Fin p → ℝ} (hm : Measurable X) (hL2 : ∀ a, MemLp (fun ω => X ω a) 2 μ)

theorem pi_norm_sq_le_sum_sq (v : Fin p → ℝ) : ‖v‖ ^ 2 ≤ ∑ a, (v a) ^ 2 := by
  have hn : ‖v‖ ≤ Real.sqrt (∑ a, (v a) ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro a
    simpa only [Real.norm_eq_abs, Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt (Finset.single_le_sum (fun a _ => sq_nonneg (v a)) (Finset.mem_univ a))
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt (by positivity))

include hm hL2 in
/-- Coordinatewise L² gives genuine vector L² and a sharp dimension-free
comparison with the sum of coordinate energies. -/
theorem vector_memLp_two : MemLp X 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (integrable_finsetSum Finset.univ (fun a _ => (hL2 a).integrable_sq)).mono' (hm.norm.pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pi_norm_sq_le_sum_sq (X ω)

include hm hL2 in
theorem vector_second_le_sum_coordinates :
    (∫ ω, ‖X ω‖ ^ 2 ∂μ) ≤ ∑ a, ∫ ω, X ω a ^ 2 ∂μ := by
  have h := integral_mono ((vector_memLp_two hm hL2).norm.integrable_sq) (integrable_finsetSum Finset.univ (fun a _ => (hL2 a).integrable_sq)) (fun ω => pi_norm_sq_le_sum_sq (X ω))
  rwa [integral_finsetSum _ (fun a _ => (hL2 a).integrable_sq)] at h

/-- Independence makes the raw order-k kernel energy at most its squared
operator norm times the k-th power of a single-observation energy cap. -/
theorem multilinear_second_le
    (H : ContinuousMultilinearMap ℝ (fun _ => Fin p → ℝ) ℝ)
    {X : Fin k → Ω → Fin p → ℝ} (hind : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (hL2 : ∀ i a, MemLp (fun ω => X i ω a) 2 μ)
    {E : ℝ} (hE : 0 ≤ E) (henergy : ∀ i, (∫ ω, ‖X i ω‖ ^ 2 ∂μ) ≤ E) :
    (∫ ω, H (fun i => X i ω) ^ 2 ∂μ) ≤ ‖H‖ ^ 2 * E ^ k := by
  classical
  have hnorm i := (vector_memLp_two (hm i) (hL2 i)).norm
  have hind' : iIndepFun (fun i ω => ‖X i ω‖ ^ 2) μ :=
    hind.comp _ (fun _ => measurable_norm.pow_const 2)
  have hmeas' i  := (hm i).norm.pow_const 2
  have hcomp : (∫ ω, H (fun i => X i ω) ^ 2 ∂μ) ≤
      ‖H‖ ^ 2 * ∫ ω, ∏ i, ‖X i ω‖ ^ 2 ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono ((LiftL2.multilinear_kernel_memLp_two H.toMultilinearMap (Function.Embedding.refl (Fin k)) hind hm hL2).integrable_sq) ((LiftL2.independent_finset_product_integrable hind' hmeas' (fun i => (hnorm i).integrable_sq) Finset.univ).const_mul _)
    intro ω
    change H (fun i => X i ω) ^ 2 ≤ _
    simpa only [Real.norm_eq_abs, sq_abs, mul_pow, Finset.prod_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (H.le_opNorm _) 2
  rw [(hind'.integral_fun_prod_eq_prod_integral (fun i => (hmeas' i).aestronglyMeasurable))] at hcomp
  apply hcomp.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    _ ≤ _ := Finset.prod_le_prod₀
      (fun i _ => by positivity) (fun i _ => henergy i)
    _ = _ := by simp

/-- A factorial derivative cap produces the precise factorial power series
used in the pilot budget, proved from actual independent feature moments. -/
theorem factorial_kernel_budget
    {H : ContinuousMultilinearMap ℝ (fun _ => Fin p → ℝ) ℝ}
    {X : Fin k → Ω → Fin p → ℝ} (hind : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (hL2 : ∀ i a, MemLp (fun ω => X i ω a) 2 μ)
    {E a c Λ : ℝ} (hE : 0 ≤ E) (ha : 0 ≤ a) (hc : 0 ≤ c) (hΛ : 0 < Λ)
    (henergy : ∀ i, (∫ ω, ‖X i ω‖ ^ 2 ∂μ) ≤ E)
    (hderiv : ‖H‖ ≤ a * k.factorial * c ^ k) :
    ((k.factorial * Λ ^ k)⁻¹) * (∫ ω, H (fun i => X i ω) ^ 2 ∂μ) ≤
      a ^ 2 * k.factorial * (c ^ 2 * E / Λ) ^ k := by
  have h := mul_le_mul_of_nonneg_left
    ((multilinear_second_le H hind hm hL2 hE henergy).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hderiv 2) (pow_nonneg hE k)))
    (show 0 ≤ (k.factorial * Λ ^ k)⁻¹ by positivity)
  apply h.trans_eq
  simp [div_pow, mul_pow, pow_mul, Nat.mul_comm]
  field_simp <;> ring

end NearlyMinimax.KernelMomentBounds
