module
public import MathCollab.Density.Stronger.Atkinson.FiniteWeightVariation
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCutoffVariation
public import MathCollab.Density.Stronger.Atkinson.ZetaBandSecondDerivatives
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFirstDerivative
public import MathCollab.Density.Stronger.Atkinson.FresnelEvaluation
public import MathCollab.Density.Stronger.Atkinson.ContinuousKernelPrimitive
public import MathCollab.Density.Stronger.Atkinson.IntervalSecondDerivativeBounds
public import MathCollab.Density.Stronger.Atkinson.SecondDerivativeComposition
public import MathCollab.Density.Stronger.PointMean.HorizontalEdges
public import MathCollab.Density.Stronger.Fourth.SquareTail
public import Mathlib
public import TaoTrudgianYang2025.PositiveSlopeChartFibers

@[expose] public section

/-!
# Exact chart partition of the original retained stationary set

The mesh is fixed by sigma, before F, N, T or the source endpoints.
The actual stationary integers have positive slopes, belong to this
finite grid, and form contiguous natural-number blocks in each cell.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

def modelPhaseSlopeMesh (σ : ℝ) : ℝ := (2 : ℝ)^(-σ)/8

theorem modelPhaseSlopeMesh_pos (σ : ℝ) : 0 < modelPhaseSlopeMesh σ := by
  unfold modelPhaseSlopeMesh
  positivity

theorem modelPhaseSharpStationarySet_grid_window
    {F : ℝ → ℝ} {σ δ T N : ℝ} {a b : ℕ} {q : ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hpos : δ ≤ min ((2 : ℝ)^(-σ)/2) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hq : q ∈ modelPhaseSharpStationarySet F T N a b) :
    (q : ℝ)*N/T ∈ Icc (4*modelPhaseSlopeMesh σ) 2 := by
  have he : 4*modelPhaseSlopeMesh σ = 2^(-σ)/2 := by
    unfold modelPhaseSlopeMesh
    ring
  rw [he]
  exact (modelPhaseSlopeRange_positive_window hσ hpos hF (modelPhaseSharpStationarySet_critical_geometry hσ hδ hF hT hN ha hb hq).1)

theorem modelPhaseSharpStationarySet_positive
    {F : ℝ → ℝ} {σ δ T N : ℝ} {a b : ℕ} {q : ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hpos : δ ≤ min ((2 : ℝ)^(-σ)/2) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hq : q ∈ modelPhaseSharpStationarySet F T N a b) :
    0 < q := by
  have hd := modelPhaseSlopeMesh_pos σ
  exact_mod_cast ((mul_pos_iff_of_pos_right hN).mp ((div_pos_iff_of_pos_right hT).mp (lt_of_lt_of_le (by positivity) ((modelPhaseSharpStationarySet_grid_window hσ hδ hpos hF hT hN ha hb hq).1))))

theorem modelPhaseSharpStationarySet_chart_partition
    {F : ℝ → ℝ} {σ δ T N : ℝ} {a b : ℕ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hpos : δ ≤ min ((2 : ℝ)^(-σ)/2) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (f : ℤ → ℂ) :
    ∑ j ∈ positiveSlopeChartIndices (modelPhaseSlopeMesh σ),
      ∑ q ∈ positiveSlopeChartFiber (modelPhaseSharpStationarySet F T N a b)
        (modelPhaseSlopeMesh σ) N T j, f q =
      ∑ q ∈ modelPhaseSharpStationarySet F T N a b, f q := by
  apply sum_positiveSlopeChartFibers (modelPhaseSlopeMesh_pos σ)
  intro q hq
  exact modelPhaseSharpStationarySet_grid_window hσ hδ hpos hF hT hN ha hb hq

theorem modelPhaseSharpStationarySet_chart_coordinate
    {F : ℝ → ℝ} {σ δ T N : ℝ} {a b j : ℕ} {q : ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hpos : δ ≤ min ((2 : ℝ)^(-σ)/2) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hq : q ∈ positiveSlopeChartFiber (modelPhaseSharpStationarySet F T N a b)
      (modelPhaseSlopeMesh σ) N T j) :
    ((q : ℝ)*N/T)/positiveSlopeChartScale (modelPhaseSlopeMesh σ) j ∈ Ioo (1 : ℝ) 2 := by
  have hmem := mem_positiveSlopeChartFiber.mp hq
  have hv := modelPhaseSharpStationarySet_grid_window hσ hδ hpos hF hT hN ha hb hmem.1
  have hd := modelPhaseSlopeMesh_pos σ
  have hj : j ∈ positiveSlopeChartIndices (modelPhaseSlopeMesh σ) := by
    rw [← hmem.2]
    exact positiveSlopeChartIndex_mem hd hv
  exact positiveSlopeChart_coordinate hd (Finset.mem_Icc.mp hj).1
    ((positiveSlopeChartIndex_eq_iff hd ((by positivity : 0 ≤ 4*modelPhaseSlopeMesh σ).trans hv.1) j).mp hmem.2)

theorem modelPhaseSharpStationarySet_chart_natural_interval
    {F : ℝ → ℝ} {σ δ T N : ℝ} {a b j : ℕ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hpos : δ ≤ min ((2 : ℝ)^(-σ)/2) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hne : (positiveSlopeChartFiber (modelPhaseSharpStationarySet F T N a b)
      (modelPhaseSlopeMesh σ) N T j).Nonempty) :
    ∃ c L : ℕ, positiveSlopeChartFiber (modelPhaseSharpStationarySet F T N a b)
      (modelPhaseSlopeMesh σ) N T j =
        (Finset.Icc c (c+L)).image (fun n : ℕ => (n : ℤ)) := by
  classical
  have hlong : (a : ℝ)/N+4*(Real.sqrt T)⁻¹ < (b : ℝ)/N := by
    by_contra h
    simp only [(modelPhaseSharpStationarySet_of_short (F := F) (le_of_not_gt h)),positiveSlopeChartFiber,Finset.filter_empty,Finset.not_nonempty_empty] at hne
  have hnonneg : ∀ q ∈ positiveSlopeChartFiber (modelPhaseSharpStationarySet F T N a b)
      (modelPhaseSlopeMesh σ) N T j, 0 ≤ q := by
    intro q hq
    exact (modelPhaseSharpStationarySet_positive hσ hδ hpos hF hT hN ha hb
      (mem_positiveSlopeChartFiber.mp hq).1).le
  rw [modelPhaseSharpStationarySet_of_long hlong] at hne hnonneg ⊢
  exact positiveSlopeChartFiber_Ioo_natural_interval
    (modelPhaseSlopeMesh_pos σ) hN hT hne hnonneg

end TaoTrudgianYang2025
