module

public import RequestProject.FiniteRankCompletion

/-!
# Hilbert–Schmidt operators are compact

Generic Hilbert-space facts used for the regularizing remainders of Section 6 (Lemmas 6.3 and
6.7): if `T : H → K` is bounded and `∑ᵢ ‖T bᵢ‖² < ∞` for a Hilbert basis `(bᵢ)` of `H`, then
`‖T‖ ≤ (∑ᵢ ‖T bᵢ‖²)^{1/2}` (`norm_le_sqrt_tsum_norm_sq`) and `T` is compact
(`isCompactOperator_of_summable_norm_sq`), being the operator-norm limit of the finite-rank
truncations `x ↦ ∑_{i ∈ F} ⟨bᵢ, x⟩ T bᵢ`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Filter Topology
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

section
variable (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K)

section
include b T

/-- Expansion of `T x` along a Hilbert basis. -/
lemma hasSum_apply_hilbertBasis x :
    HasSum (fun i => ⟪b i, x⟫_𝕜 • T (b i)) (T x) := by
  have := (b.hasSum_repr x).mapL T
  simpa [b.repr_apply_apply] using this

/-- Cauchy–Schwarz bound for the part of the expansion of `T x` over a set `s` of indices. -/
lemma norm_tsum_subtype_le (s : Set ι)
    (hT : Summable fun i => ‖T (b i)‖ ^ 2) x :
    ‖∑' i : s, ⟪b i, x⟫_𝕜 • T (b i)‖ ≤ Real.sqrt (∑' i : s, ‖T (b i)‖ ^ 2) * ‖x‖ := by
  set f : s → ℝ := fun i => ‖⟪b i, x⟫_𝕜‖
  set g : s → ℝ := fun i => ‖T (b i)‖
  have hbessel  :=
    b.orthonormal.inner_products_summable x
  have hf2 : Summable fun i : s => f i ^ (2 : ℝ) := by
    simpa [Function.comp_def] using hbessel.subtype (· ∈ s)
  have hg2 : Summable fun i : s => g i ^ (2 : ℝ) := by
    simpa [Function.comp_def] using hT.subtype (· ∈ s)
  have hfg := Real.summable_mul_of_Lp_Lq_of_nonneg Real.HolderConjugate.two_two
    (fun i => norm_nonneg _) (fun i => norm_nonneg _) hf2 hg2
  have hle := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (fun i => norm_nonneg _) (fun i => norm_nonneg _) hf2 hg2
  have hsumf : ∑' i : s, f i ^ (2 : ℝ) ≤ ‖x‖ ^ 2 := by
    have h1 : ∑' i : s, f i ^ (2 : ℝ) ≤ ∑' i : ι, ‖⟪b i, x⟫_𝕜‖ ^ 2 := by
      simp  
      exact hbessel.tsum_subtype_le _ s (fun i => by positivity)
    exact h1.trans (b.orthonormal.tsum_inner_products_le x)
  have hnorm : Summable fun i : s => ‖⟪b i, x⟫_𝕜 • T (b i)‖ := by
    simpa [norm_smul] using hfg
  calc ‖∑' i : s, ⟪b i, x⟫_𝕜 • T (b i)‖ ≤ ∑' i : s, ‖⟪b i, x⟫_𝕜 • T (b i)‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ = ∑' i : s, f i * g i := by simp [norm_smul, f, g]
    _ ≤ (∑' i : s, f i ^ 2) ^ (1 / 2) * (∑' i : s, g i ^ 2) ^ (1 / 2) :=
        hle
    _ ≤ (‖x‖ ^ 2) ^ (1 / (2 : ℝ)) * (∑' i : s, g i ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
        gcongr
    _ = Real.sqrt (∑' i : s, ‖T (b i)‖ ^ 2) * ‖x‖ := by
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg x), mul_comm]
        simp [g]

/-- **Hilbert–Schmidt bound.** `‖T‖ ≤ (∑ᵢ ‖T bᵢ‖²)^{1/2}` for a Hilbert basis `(bᵢ)`. -/
theorem norm_le_sqrt_tsum_norm_sq
    (hT : Summable fun i => ‖T (b i)‖ ^ 2) :
    ‖T‖ ≤ Real.sqrt (∑' i, ‖T (b i)‖ ^ 2) := by
  refine T.opNorm_le_bound (Real.sqrt_nonneg _) fun x => ?_
  have h := norm_tsum_subtype_le b T Set.univ hT x
  have e1 : ∑' i : (Set.univ : Set ι), ⟪b i, x⟫_𝕜 • T (b i) = T x := by
    rw [tsum_univ (f := fun i => ⟪b i, x⟫_𝕜 • T (b i))]
    exact (hasSum_apply_hilbertBasis b T x).tsum_eq
  have e2  :=
    tsum_univ (f := fun i => ‖T (b i)‖ ^ 2)
  rwa [e1, e2] at h

end


/-- The finite-rank truncation `x ↦ ∑_{i ∈ F} ⟨bᵢ, x⟩ T bᵢ`. -/
def hsTrunc (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K) F  :=
  ∑ i ∈ F, (innerSL 𝕜 (b i)).smulRight (T (b i))

section
include b T

lemma hsTrunc_apply F x :
    hsTrunc b T F x = ∑ i ∈ F, ⟪b i, x⟫_𝕜 • T (b i) := by
  simp_all [hsTrunc]

lemma isCompactOperator_hsTrunc F :
    IsCompactOperator (hsTrunc b T F) := by
  classical
  unfold hsTrunc
  induction F using Finset.induction_on with
  | empty => simpa using isCompactOperator_zero
  | insert j F hj ih =>
    rw [Finset.sum_insert hj]
    refine IsCompactOperator.add (f := ⇑((innerSL 𝕜 (b j)).smulRight (T (b j)))) ?_ ih
    have hle : LinearMap.range (((innerSL 𝕜 (b j)).smulRight (T (b j)) : H →L[𝕜] K) :
        H →ₗ[𝕜] K) ≤ 𝕜 ∙ T (b j) := by
      rintro _ ⟨x, rfl⟩
      measurability
    haveI  := Submodule.finiteDimensional_of_le hle
    exact isCompactOperator_of_finiteDimensional_range _

lemma norm_sub_hsTrunc_le
    (hT : Summable fun i => ‖T (b i)‖ ^ 2) F :
    ‖T - hsTrunc b T F‖ ≤ Real.sqrt (∑' i : {i // i ∉ F}, ‖T (b i)‖ ^ 2) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  have hs := hasSum_apply_hilbertBasis b T x
  have hsplit := hs.summable.sum_add_tsum_compl (s := F)
  rw [hs.tsum_eq] at hsplit
  have : (T - hsTrunc b T F) x = ∑' i : {i // i ∉ F}, ⟪b i, x⟫_𝕜 • T (b i) := by
    rw [ContinuousLinearMap.sub_apply, hsTrunc_apply, ← hsplit]
    simp  
    rfl
  rw [this]
  solve_by_elim (maxDepth := 5) [norm_tsum_subtype_le]

end


end


/-- **Hilbert–Schmidt operators are compact.** If `∑ᵢ ‖T bᵢ‖² < ∞` for a Hilbert basis
`(bᵢ)` of `H`, then `T` is a compact operator. -/
theorem isCompactOperator_of_summable_norm_sq [CompleteSpace K] (b : HilbertBasis ι 𝕜 H)
    (T : H →L[𝕜] K) (hT : Summable fun i => ‖T (b i)‖ ^ 2) : IsCompactOperator T := by
  have hlim : Tendsto ((hsTrunc b T)) atTop (𝓝 T) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 := tendsto_tsum_compl_atTop_zero (fun i => ‖T (b i)‖ ^ 2)
    have h1 : Tendsto (fun F : Finset ι => Real.sqrt (∑' i : {i // i ∉ F}, ‖T (b i)‖ ^ 2))
        atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp h0
    refine squeeze_zero (fun F => norm_nonneg _) (fun F => ?_) h1
    rw [norm_sub_rev]
    exact norm_sub_hsTrunc_le b T hT F
  have hmem  :=
    (isCompactOperator_hsTrunc b T)
  exact isClosed_setOf_isCompactOperator.mem_of_tendsto hlim (Eventually.of_forall hmem)

end PolyaNeumann
