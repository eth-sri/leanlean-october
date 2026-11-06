module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

open scoped Manifold ContDiff

namespace DedekindZetaZeroFree









section LieData

variable (G : Type*) [Group G] [TopologicalSpace G]
variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [ChartedSpace V G] [LieGroup (𝓘(ℝ, V)) ∞ G]
variable (B : Type*) [Fintype B]

structure HilbertLieExponentialData where
  basis : Module.Basis B ℝ V
  exponential : V → G
  exponential_zero : exponential 0 = 1
  exponential_add_ray : ∀ (X : V) (s t : ℝ),
    exponential ((s + t) • X) = exponential (s • X) * exponential (t • X)
  exponential_smooth : ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, V)) ∞ exponential
  exponentialChart : PartialDiffeomorph (𝓘(ℝ, V)) (𝓘(ℝ, V)) V G ∞
  zero_mem_source : (0 : V) ∈ exponentialChart.toPartialEquiv.source
  chart_eq_exponential : ∀ X ∈ exponentialChart.toPartialEquiv.source,
    exponentialChart X = exponential X
  adjoint : G → V ≃ₗ[ℝ] V
  adjoint_smooth : ∀ a b : B,
    ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, ℝ)) ∞
      (fun g : G => basis.equivFun (adjoint g (basis b)) a)
  exponential_conjugation : ∀ (g : G) (X : V),
    g * exponential X * g⁻¹ = exponential (adjoint g X)

end LieData

section Representation

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [ChartedSpace V G] [LieGroup (𝓘(ℝ, V)) ∞ G]
variable {B : Type*} [Fintype B]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]








end Representation

end DedekindZetaZeroFree
