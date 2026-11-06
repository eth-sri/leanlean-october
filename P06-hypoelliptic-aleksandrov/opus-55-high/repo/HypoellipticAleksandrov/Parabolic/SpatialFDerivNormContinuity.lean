module

public import HypoellipticAleksandrov.Parabolic.SpatialFDerivNorm
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open scoped BigOperators Matrix.Norms.Elementwise

variable {d : ℕ} {K : Set (TimeVelocity d)}

/-- Smoothness on a neighborhood makes the spatial derivative norm of a
scalar field continuous on the carrier. -/
theorem IsSmoothOnNeighborhood.continuousOn_spatialScalarFDerivEuclideanNorm
    
    {f : TimeVelocity d → ℝ}
    (hf : IsSmoothOnNeighborhood f K) :
    ContinuousOn (spatialScalarFDerivEuclideanNorm f) K := by
  rcases hf with ⟨V, hVopen, hKV, hV⟩
  apply (Real.continuous_sqrt.comp_continuousOn ?_).mono hKV
  apply continuousOn_finset_sum
  intro k _hk
  exact ((hV.continuousOn_fderiv_of_isOpen hVopen (by simp)).clm_apply
    continuousOn_const).pow 2

/-- Smoothness on a neighborhood makes the spatial derivative Frobenius norm
of a vector field continuous on the carrier. -/
theorem IsSmoothOnNeighborhood.continuousOn_spatialVectorFDerivFrobeniusNorm
    
    {f : TimeVelocity d → PDE.Vec d}
    (hf : IsSmoothOnNeighborhood f K) :
    ContinuousOn (spatialVectorFDerivFrobeniusNorm f) K := by
  rcases hf with ⟨V, hVopen, hKV, hV⟩
  apply (Real.continuous_sqrt.comp_continuousOn ?_).mono hKV
  apply continuousOn_finset_sum
  intro j _hj
  apply continuousOn_finset_sum
  intro k _hk
  have hfj : ContDiffOn ℝ _ (fun z : TimeVelocity d => f z j) V :=
    (contDiffOn_apply ℝ ℝ j Set.univ).comp hV fun _ _ => Set.mem_univ _
  exact ((hfj.continuousOn_fderiv_of_isOpen hVopen (by simp)).clm_apply
    continuousOn_const).pow 2

/-- Smoothness on a neighborhood makes the spatial derivative Frobenius norm
of a matrix field continuous on the carrier. -/
theorem IsSmoothOnNeighborhood.continuousOn_spatialMatrixFDerivFrobeniusNorm
    
    {f : TimeVelocity d → PDE.Mat d}
    (hf : IsSmoothOnNeighborhood f K) :
    ContinuousOn (spatialMatrixFDerivFrobeniusNorm f) K := by
  rcases hf with ⟨V, hVopen, hKV, hV⟩
  apply (Real.continuous_sqrt.comp_continuousOn ?_).mono hKV
  apply continuousOn_finset_sum
  intro i _hi
  apply continuousOn_finset_sum
  intro j _hj
  apply continuousOn_finset_sum
  intro k _hk
  have hfi : ContDiffOn ℝ _ (fun z : TimeVelocity d => f z i) V :=
    (contDiffOn_apply ℝ _ i Set.univ).comp hV fun _ _ => Set.mem_univ _
  have hfij : ContDiffOn ℝ _ (fun z : TimeVelocity d => f z i j) V :=
    (contDiffOn_apply ℝ ℝ j Set.univ).comp hfi fun _ _ => Set.mem_univ _
  exact ((hfij.continuousOn_fderiv_of_isOpen hVopen (by simp)).clm_apply
    continuousOn_const).pow 2

end HypoellipticAleksandrov.Parabolic
