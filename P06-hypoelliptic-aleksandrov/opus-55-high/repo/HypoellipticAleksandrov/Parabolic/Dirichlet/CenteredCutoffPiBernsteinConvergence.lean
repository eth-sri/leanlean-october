module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.PiBernsteinApproximation
public import HypoellipticAleksandrov.Parabolic.Dirichlet.CommonCompactIntegralSq
public import HypoellipticAleksandrov.Parabolic.Dirichlet.FiniteSeparatedBernsteinAssembly
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Centered cutoff Bernstein convergence

This module converts uniform product-Bernstein approximation on a centered cube into squared
integral convergence for a fixed compactly supported spatial cutoff.
-/

@[expose] public section

open Filter Function MeasureTheory Set Topology
open scoped BigOperators Topology unitInterval

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem piBernsteinApproximation_norm_tendsto_zero
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : C(Fin d → I, E)) :
    Tendsto (fun n : ℕ => ‖piBernsteinApproximation n F - F‖) atTop (nhds 0) := tendsto_iff_norm_sub_tendsto_zero.mp (piBernsteinApproximation_uniform F)

private def centeredUnitPoint {d : ℕ} (R : ℝ) (hR : 0 < R)
    (y : PDE.Vec d) (hy : y ∈ Icc (fun _ => -R) (fun _ => R)) : Fin d → I :=
  fun i => ⟨((y i / R) + 1) / 2, by
    have hlo : -1 ≤ y i / R := by
      rw [le_div_iff₀ hR]
      aesop
    have hhi : y i / R ≤ 1 := by
      rw [div_le_one hR]
      aesop
    grind⟩

private def centeredContinuousField {d : ℕ}
    (Kt : TopologicalSpace.Compacts ℝ) (R : ℝ)
    (f : TimeVelocity d → ℝ) (hf : Continuous f) :
    C(Fin d → I, C(Kt, ℝ)) :=
  ContinuousMap.curry ⟨fun p => f (p.2, fun i => R * (2 * (p.1 i : ℝ) - 1)), by
    fun_prop⟩

private theorem cutoffPiBernsteinApproximation_eq_centeredContinuousField
    {d n : ℕ} (Kt : TopologicalSpace.Compacts ℝ)
    (R : ℝ) (hR : 0 < R) (χ : PDE.Vec d → ℝ)
    (f : TimeVelocity d → ℝ) (hf : Continuous f)
    (τ : ℝ) (hτ : τ ∈ (Kt : Set ℝ))
    (y : PDE.Vec d) (hy : y ∈ Icc (fun _ => -R) (fun _ => R)) :
    cutoffPiBernsteinApproximation (n := n) R χ f (τ, y) =
      χ y * piBernsteinApproximation n (centeredContinuousField Kt R f hf)
        (centeredUnitPoint R hR y hy) ⟨τ, hτ⟩ := by
  unfold cutoffPiBernsteinApproximation piBernsteinApproximation
  simp only [ContinuousMap.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp [piBernsteinBasis]
  congr 2

/-- Centered cutoff product-Bernstein approximations converge in squared integral. -/
theorem tendsto_integral_sq_cutoffPiBernsteinApproximation
    {d : ℕ} {μ : Measure (TimeVelocity d)} [IsFiniteMeasureOnCompacts μ]
    (Kt : TopologicalSpace.Compacts ℝ) (Ksp : Set (PDE.Vec d))
    (χ : PDE.Vec d → ℝ) (hχcont : Continuous χ)
    (hχcompact : IsCompact (tsupport χ))
    (hχone : Set.EqOn χ 1 Ksp)
    (R : ℝ) (hR : 0 < R)
    (hcube : tsupport χ ⊆ Set.Icc (fun _ => -R) (fun _ => R))
    (f : TimeVelocity d → ℝ) (hfcont : Continuous f)
    (hfsupport : tsupport f ⊆ (Kt : Set ℝ) ×ˢ Ksp) :
    Tendsto
      (fun n => ∫ z,
        (cutoffPiBernsteinApproximation (n := n) R χ f z - f z) ^ 2 ∂μ)
      atTop (nhds 0) := by
  let F := centeredContinuousField Kt R f hfcont
  let e  := fun n => ‖piBernsteinApproximation n F - F‖
  have he0 : Tendsto e atTop (nhds 0) := by
    simpa only [e] using piBernsteinApproximation_norm_tendsto_zero F
  obtain ⟨M, hM⟩ := hχcompact.exists_bound_of_continuousOn hχcont.continuousOn
  let C := max 1 M
  have hC0 : 0 ≤ C := le_trans zero_le_one (le_max_left _ _)
  have hχC {y : PDE.Vec d} (hy : y ∈ tsupport χ) : |χ y| ≤ C := (hM y hy).trans (le_max_right _ _)
  let g  := fun n z =>
    cutoffPiBernsteinApproximation (n := n) R χ f z - f z
  have hzero (z : TimeVelocity d) (hτ : z.1 ∉ (Kt : Set ℝ)) :
      ∀ n, g n z = 0 := by
    have hfzero (y : PDE.Vec d) : f (z.1, y) = 0 := by
      by_contra hn
      have hz : (z.1, y) ∈ tsupport f := subset_closure hn
      grind
    simp [g, cutoffPiBernsteinApproximation, hfzero]
  have hbound (n : ℕ) (z : TimeVelocity d) : |g n z| ≤ C * e n := by
    by_cases hτ : z.1 ∈ (Kt : Set ℝ)
    · by_cases hχ : χ z.2 = 0
      · have hfzero : f z = 0 := by
          by_contra hn
          have hz := hfsupport (subset_closure hn)
          aesop
        simp only [g, cutoffPiBernsteinApproximation, hχ, zero_mul, hfzero, sub_zero,
          abs_zero]
        positivity
      · have hyts : z.2 ∈ tsupport χ := subset_closure hχ
        have heq : χ z.2 * f z = f z := by
          by_cases hfz : f z = 0
          · grind
          · have hone : χ z.2 = 1 := by
              simpa using hχone (hfsupport (subset_closure hfz)).2
            simp_all
        dsimp only [g]
        rw [cutoffPiBernsteinApproximation_eq_centeredContinuousField
          Kt R hR χ f hfcont z.1 hτ z.2 (hcube hyts), ← heq, ← mul_sub, abs_mul]
        apply mul_le_mul (hχC hyts) ?_ (abs_nonneg _) hC0
        have hFz : F (centeredUnitPoint R hR z.2 (hcube hyts)) ⟨z.1, hτ⟩ = f z := by
          dsimp [F, centeredContinuousField, centeredUnitPoint]
          field_simp [hR.ne']
          ring
        rw [← hFz, ← ContinuousMap.sub_apply, ← ContinuousMap.sub_apply, ← Real.norm_eq_abs]
        exact (ContinuousMap.norm_coe_le_norm
          _
          _).trans
          (ContinuousMap.norm_coe_le_norm _
            _)
    · rw [hzero z hτ n, abs_zero]
      positivity
  let K : TopologicalSpace.Compacts (TimeVelocity d) :=
    Kt ×ˢ ⟨tsupport χ, hχcompact⟩
  refine tendsto_integral_sq_of_common_compact_uniform_bound K g
    K.isCompact.measurableSet ?_ ?_ (fun n => C * e n) ?_ ?_
  · intro n
    apply Continuous.aestronglyMeasurable
    apply Continuous.sub
    · unfold cutoffPiBernsteinApproximation
      fun_prop
    omega
  · intro n z hz
    by_contra hn
    rcases not_and_or.mp hn with hτ | hy
    · simp_all
    · have hχz : χ z.2 = 0 := image_eq_zero_of_notMem_tsupport hy
      have hfz : f z = 0 := by
        by_contra hfne
        have hone : χ z.2 = 1 := by
          simpa using hχone (hfsupport (subset_closure hfne)).2
        simp_all
      exact hz (by simp [g, cutoffPiBernsteinApproximation, hχz, hfz])
  · simpa only [mul_zero] using tendsto_const_nhds.mul he0
  omega

end HypoellipticAleksandrov.Parabolic.Dirichlet
