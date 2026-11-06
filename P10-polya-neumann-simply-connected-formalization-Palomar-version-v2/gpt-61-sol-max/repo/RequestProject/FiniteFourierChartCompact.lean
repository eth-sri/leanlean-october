module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.FiniteFourierChartRemainder
public import RequestProject.FiniteRankCompletion
public import RequestProject.NormalizedPeriodicRegular

/-! Compact principal compression in the actual finite Fourier chart. -/

@[expose] public section

open scoped ContDiff
noncomputable section
namespace PolyaNeumann
open ContinuousLinearMap
local notation "H₁" => nonpositiveFourierSubspaceᗮ

private theorem chart_rankOne_compact
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (v : Y) (u : X) :
    IsCompactOperator (InnerProductSpace.rankOne ℂ v u) := (isCompactOperator_of_finiteDimensional_range
    (ContinuousLinearMap.toSpanSingleton ℂ v)).comp_clm (innerSL ℂ u)

private theorem chart_compact_sum
    {ι X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    s (T : ι → X →L[ℂ] Y)
    (hT : ∀ i ∈ s, IsCompactOperator (T i)) :
    IsCompactOperator (∑ i ∈ s, T i : X →L[ℂ] Y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCompactOperator_zero
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hT i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))

section
variable {d } (u : Fin d → H₁) (v : Fin d → L2Z)
include d u v

theorem finiteFourierChart_sub_subtype_compact :
    IsCompactOperator (finiteFourierChart u v - Submodule.subtypeL H₁) := by
  simp_all [finiteFourierChart, chart_compact_sum, chart_rankOne_compact]

theorem finiteFourierChart_adjoint_sub_projection_compact :
    IsCompactOperator (adjoint (finiteFourierChart u v) - adjoint (Submodule.subtypeL H₁)) := by
  simp  [finiteFourierChart]
  simp_all [chart_compact_sum, chart_rankOne_compact]

end


private theorem chart_subtype_positive_compression :
    adjoint (Submodule.subtypeL H₁) ∘L posProj ∘L Submodule.subtypeL H₁ =
      ContinuousLinearMap.id ℂ H₁ := by
  apply ContinuousLinearMap.ext
  intro z
  simp  [Submodule.adjoint_subtypeL]
  rw [← nonpositive_orthogonal_starProjection,
    Submodule.starProjection_mem_subspace_eq_self]
  simp_all

section
variable {d } (u : Fin d → H₁) (v : Fin d → L2Z)
local notation "finiteFourierChartFixed" => finiteFourierChart u v

include d u v

theorem finiteFourierChart_positive_compression_sub_one_compact :
    IsCompactOperator (adjoint finiteFourierChartFixed ∘L posProj ∘L
      finiteFourierChartFixed - ContinuousLinearMap.id ℂ H₁) := by
  have heq : adjoint finiteFourierChartFixed ∘L posProj ∘L finiteFourierChartFixed -
      ContinuousLinearMap.id ℂ H₁ =
      adjoint finiteFourierChartFixed ∘L posProj ∘L
        (finiteFourierChartFixed - Submodule.subtypeL H₁) +
      (adjoint finiteFourierChartFixed - adjoint (Submodule.subtypeL H₁)) ∘L
        posProj ∘L Submodule.subtypeL H₁ := by
    simp_all [chart_subtype_positive_compression]
  rw [heq]
  exact (((finiteFourierChart_sub_subtype_compact u v).clm_comp posProj).clm_comp
    (adjoint finiteFourierChartFixed)).add
    (((finiteFourierChart_adjoint_sub_projection_compact u v).comp_clm posProj).comp_clm
      (Submodule.subtypeL H₁))

theorem finiteFourierChart_regular_compression_sub_four_compact (P : L2Z →L[ℂ] L2Z)
    (hP : IsCompactOperator (P - (4 : ℂ) • posProj)) :
    IsCompactOperator (adjoint finiteFourierChartFixed ∘L P ∘L finiteFourierChartFixed -
      (4 : ℂ) • ContinuousLinearMap.id ℂ H₁) := by
  have heq : adjoint finiteFourierChartFixed ∘L P ∘L finiteFourierChartFixed -
      (4 : ℂ) • ContinuousLinearMap.id ℂ H₁ =
      adjoint finiteFourierChartFixed ∘L (P - (4 : ℂ) • posProj) ∘L
        finiteFourierChartFixed +
      (4 : ℂ) • (adjoint finiteFourierChartFixed ∘L posProj ∘L
        finiteFourierChartFixed - ContinuousLinearMap.id ℂ H₁) := by
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_sub]
    abel
  rw [heq]
  exact ((hP.comp_clm finiteFourierChartFixed).clm_comp
    (adjoint finiteFourierChartFixed)).add
    ((finiteFourierChart_positive_compression_sub_one_compact u v).smul 4)

end


theorem localConformal_finiteFourierChart_regular_compression
    {R C : ℝ} (hR : 1 < R) (F : PlaneMap)
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : Set.InjOn F unitDisk)
    (hC : DiskInverseJacobianBound F C)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F)
    (hsource : closedUnitDisk ⊆ e.source)
    (hes : RealSmoothOn e.symm e.target)
    {E₀ E : ℝ} (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1ComplementForm (F '' unitDisk) E₀ E))
    (W : ℝ → ComplexEnd Ell2)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2)
    {d : ℕ} (u : Fin d → H₁) (v : Fin d → L2Z) :
    ∃ D : H₁ →L[ℂ] H₁, IsCompactOperator D ∧
      adjoint (finiteFourierChart u v) ∘L
        normalizedPeriodicRegularOperator (localConformalDiskHalfTrace hR F hFs hL)
          E₀ E W hbase ∘L finiteFourierChart u v =
        (4 : ℂ) • ContinuousLinearMap.id ℂ H₁ + D := by
  let P := normalizedPeriodicRegularOperator (localConformalDiskHalfTrace hR F hFs hL)
    E₀ E W hbase
  let D := adjoint (finiteFourierChart u v) ∘L P ∘L finiteFourierChart u v -
    (4 : ℂ) • ContinuousLinearMap.id ℂ H₁
  have hP  :=
    localConformal_normalizedPeriodicRegular_sub_four_posProj_compact
      hR F hFs hb hL hhol hinj hC e he hsource hes hE₀ hunit W hbase
  refine ⟨D, finiteFourierChart_regular_compression_sub_four_compact u v P hP, ?_⟩
  dsimp only [D]
  abel

end PolyaNeumann