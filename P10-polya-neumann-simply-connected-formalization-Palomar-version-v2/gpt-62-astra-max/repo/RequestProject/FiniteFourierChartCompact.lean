module

public import RequestProject.DiskCoordinates

public import RequestProject.FiniteFourierChartRemainder
public import RequestProject.FiniteRankCompletion
public import RequestProject.NormalizedPeriodicRegular
public import RequestProject.PlanarNotation

/-! Compact principal compression in the actual finite Fourier chart. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped ContDiff

namespace PolyaNeumann
open ContinuousLinearMap
open scoped InnerProductSpace
local notation "H₁" => nonpositiveFourierSubspaceᗮ

private theorem chart_rankOne_compact
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (v : Y) (u : X) :
    IsCompactOperator (InnerProductSpace.rankOne ℂ v u) := (isCompactOperator_of_finiteDimensional_range
    (ContinuousLinearMap.toSpanSingleton ℂ v)).comp_clm (innerSL ℂ u)

private theorem chart_compact_sum
    {ι X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (s : Finset ι) (T : ι → X →L[ℂ] Y)
    (hT : ∀ i ∈ s, IsCompactOperator (T i)) :
    IsCompactOperator (∑ i ∈ s, T i : X →L[ℂ] Y) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact isCompactOperator_zero
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hT i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))

theorem finiteFourierChart_sub_subtype_compact {d : ℕ}
    (u : Fin d → H₁) (v : Fin d → L2Z) :
    IsCompactOperator (finiteFourierChart u v - Submodule.subtypeL H₁) := by
  simp [finiteFourierChart, add_sub_cancel_left]
  exact chart_compact_sum Finset.univ _ (fun i _ => chart_rankOne_compact (v i) (u i))

theorem finiteFourierChart_adjoint_sub_projection_compact {d : ℕ}
    (u : Fin d → H₁) (v : Fin d → L2Z) :
    IsCompactOperator (adjoint (finiteFourierChart u v) - adjoint (Submodule.subtypeL H₁)) := by
  simp [finiteFourierChart]
  exact chart_compact_sum Finset.univ _ (fun i _ => chart_rankOne_compact (u i) (v i))

private theorem chart_subtype_positive_compression :
    adjoint (Submodule.subtypeL H₁) ∘L posProj ∘L Submodule.subtypeL H₁ =
      ContinuousLinearMap.id ℂ H₁ := by
  apply ContinuousLinearMap.ext
  intro z
  simp [Submodule.adjoint_subtypeL]
  rw [← nonpositive_orthogonal_starProjection,
    Submodule.starProjection_mem_subspace_eq_self]
  exact Submodule.orthogonalProjection_mem_subspace_eq_self z

theorem finiteFourierChart_positive_compression_sub_one_compact {d : ℕ}
    (u : Fin d → H₁) (v : Fin d → L2Z) :
    IsCompactOperator (adjoint (finiteFourierChart u v) ∘L posProj ∘L
      finiteFourierChart u v - ContinuousLinearMap.id ℂ H₁) := by
  have heq : adjoint (finiteFourierChart u v) ∘L posProj ∘L finiteFourierChart u v -
      ContinuousLinearMap.id ℂ H₁ =
      adjoint (finiteFourierChart u v) ∘L posProj ∘L
        (finiteFourierChart u v - Submodule.subtypeL H₁) +
      (adjoint (finiteFourierChart u v) - adjoint (Submodule.subtypeL H₁)) ∘L
        posProj ∘L Submodule.subtypeL H₁ := by
    simp [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp, chart_subtype_positive_compression]
  rw [heq]
  exact (((finiteFourierChart_sub_subtype_compact u v).clm_comp posProj).clm_comp
    (adjoint (finiteFourierChart u v))).add
    (((finiteFourierChart_adjoint_sub_projection_compact u v).comp_clm posProj).comp_clm
      (Submodule.subtypeL H₁))

theorem finiteFourierChart_regular_compression_sub_four_compact {d : ℕ}
    (u : Fin d → H₁) (v : Fin d → L2Z) (P : FourierOp)
    (hP : IsCompactOperator (P - (4 : ℂ) • posProj)) :
    IsCompactOperator (adjoint (finiteFourierChart u v) ∘L P ∘L finiteFourierChart u v -
      (4 : ℂ) • ContinuousLinearMap.id ℂ H₁) := by
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
  exact ((hP.comp_clm (finiteFourierChart u v)).clm_comp
    (adjoint (finiteFourierChart u v))).add
    ((finiteFourierChart_positive_compression_sub_one_compact u v).smul 4)

theorem localConformal_finiteFourierChart_regular_compression (Φ : ConformalDiskMap)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = Φ.map) (hsource : closedDisk ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target) {E₀ E : ℝ} (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1ComplementForm Φ.domain E₀ E)) (W : TransportPath)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2) {d : ℕ} (u : Fin d → H₁)
    (v : Fin d → L2Z) :
    ∃ D : H₁ →L[ℂ] H₁, IsCompactOperator D ∧
      adjoint (finiteFourierChart u v) ∘L
        normalizedPeriodicRegularOperator (Φ.pulledBackHalfTrace Φ.lipschitzDomain)
          E₀ E W hbase ∘L finiteFourierChart u v =
        (4 : ℂ) • ContinuousLinearMap.id ℂ H₁ + D := by
  let P := normalizedPeriodicRegularOperator (Φ.pulledBackHalfTrace Φ.lipschitzDomain)
    E₀ E W hbase
  let D := adjoint (finiteFourierChart u v) ∘L P ∘L finiteFourierChart u v -
    (4 : ℂ) • ContinuousLinearMap.id ℂ H₁
  have hP  :=
    localConformal_normalizedPeriodicRegular_sub_four_posProj_compact
      Φ e he hsource hes hE₀ hunit W hbase
  refine ⟨D, finiteFourierChart_regular_compression_sub_four_compact u v P hP, ?_⟩
  change adjoint (finiteFourierChart u v) ∘L P ∘L finiteFourierChart u v =
    (4 : ℂ) • ContinuousLinearMap.id ℂ H₁ + D
  simp [D]

end PolyaNeumann
end
