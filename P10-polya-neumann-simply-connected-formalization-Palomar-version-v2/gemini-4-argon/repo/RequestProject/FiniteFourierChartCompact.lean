module

public import RequestProject.FiniteFourierChartRemainder
public import RequestProject.FiniteRankCompletion
public import RequestProject.NormalizedPeriodicRegular

/-! Compact principal compression in the actual finite Fourier chart. -/

@[expose] public section
noncomputable section
namespace PolyaNeumann
open ContinuousLinearMap
open scoped InnerProductSpace ContDiff
local notation "H₁" => nonpositiveFourierSubspaceᗮ

private theorem chart_rankOne_compact
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (v : Y) (u : X) :
    IsCompactOperator (InnerProductSpace.rankOne ℂ v u) := by
  exact (isCompactOperator_of_finiteDimensional_range
    (ContinuousLinearMap.toSpanSingleton ℂ v)).comp_clm (innerSL ℂ u)

private theorem chart_compact_sum
    {ι X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (s : Finset ι) (T : ι → X →L[ℂ] Y)
    (hT : ∀ i ∈ s, IsCompactOperator (T i)) :
    IsCompactOperator (∑ i ∈ s, T i : X →L[ℂ] Y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isCompactOperator_zero : IsCompactOperator (0 : X →L[ℂ] Y))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hT i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))

theorem localConformal_finiteFourierChart_regular_compression
    {R C : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    hFs
    (hb : Bornology.IsBounded (F '' Metric.ball 0 1))
    hL
    (hhol : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hinj : Set.InjOn F (Metric.ball 0 1))
    (hC : ∀ z ∈ Metric.ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : e = F)
    (hsource : Metric.closedBall 0 1 ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target)
    {E₀ E : ℝ} (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1ComplementForm (F '' Metric.ball (0 : ℂ) 1) E₀ E))
    W
    hbase
    {d : ℕ} (u : Fin d → H₁) v :
    ∃ D : H₁ →L[ℂ] H₁, IsCompactOperator D ∧
      adjoint (finiteFourierChart u v) ∘L
        normalizedPeriodicRegularOperator (localConformalDiskHalfTrace hR F hFs hL)
          E₀ E W hbase ∘L finiteFourierChart u v =
        (4 : ℂ) • ContinuousLinearMap.id ℂ H₁ + D := by
  let P := normalizedPeriodicRegularOperator (localConformalDiskHalfTrace hR F hFs hL)
    E₀ E W hbase
  let D := adjoint (finiteFourierChart u v) ∘L P ∘L finiteFourierChart u v -
    (4 : ℂ) • ContinuousLinearMap.id ℂ H₁
  refine ⟨D, show IsCompactOperator (adjoint (finiteFourierChart u v) ∘L P ∘L finiteFourierChart u v - (4 : ℂ) • ContinuousLinearMap.id ℂ H₁) by
    have heq : adjoint (finiteFourierChart u v) ∘L P ∘L finiteFourierChart u v -
        (4 : ℂ) • ContinuousLinearMap.id ℂ H₁ =
        adjoint (finiteFourierChart u v) ∘L (P - (4 : ℂ) • posProj) ∘L
          finiteFourierChart u v +
        (4 : ℂ) • (adjoint (finiteFourierChart u v) ∘L posProj ∘L
          finiteFourierChart u v - ContinuousLinearMap.id ℂ H₁) := by
      simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
        ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_sub]
      abel
    rw [heq]
    exact (((localConformal_normalizedPeriodicRegular_sub_four_posProj_compact hR F hFs hb hL hhol hinj hC e he hsource hes hE₀ hunit W hbase).comp_clm (finiteFourierChart u v)).clm_comp
      (adjoint (finiteFourierChart u v))).add
      ((show IsCompactOperator (adjoint (finiteFourierChart u v) ∘L posProj ∘L finiteFourierChart u v - ContinuousLinearMap.id ℂ H₁) by
        rw [show adjoint (finiteFourierChart u v) ∘L posProj ∘L finiteFourierChart u v - ContinuousLinearMap.id ℂ H₁ = adjoint (finiteFourierChart u v) ∘L posProj ∘L (finiteFourierChart u v - Submodule.subtypeL H₁) + (adjoint (finiteFourierChart u v) - adjoint (Submodule.subtypeL H₁)) ∘L posProj ∘L Submodule.subtypeL H₁ by
          simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
            (show adjoint (Submodule.subtypeL H₁) ∘L posProj ∘L Submodule.subtypeL H₁ = ContinuousLinearMap.id ℂ H₁ by
              apply ContinuousLinearMap.ext
              intro z
              simp [Submodule.adjoint_subtypeL, Submodule.subtypeL_apply]
              rw [← nonpositive_orthogonal_starProjection,
                Submodule.starProjection_mem_subspace_eq_self]
              exact Submodule.orthogonalProjection_mem_subspace_eq_self z)]
          abel]
        exact (((show IsCompactOperator (finiteFourierChart u v - Submodule.subtypeL H₁) by
          simp [finiteFourierChart]
          exact chart_compact_sum Finset.univ _ (fun i _ => chart_rankOne_compact (v i) (u i))).clm_comp posProj).clm_comp
          (adjoint (finiteFourierChart u v))).add
          (((show IsCompactOperator (adjoint (finiteFourierChart u v) - adjoint (Submodule.subtypeL H₁)) by
            simp [finiteFourierChart]
            exact chart_compact_sum Finset.univ _ (fun i _ => chart_rankOne_compact (u i) (v i))).comp_clm posProj).comp_clm
            (Submodule.subtypeL H₁))).smul 4), ?_⟩
  change adjoint (finiteFourierChart u v) ∘L P ∘L finiteFourierChart u v = _
  dsimp only [D]
  abel

end PolyaNeumann
end
