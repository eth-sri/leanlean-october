module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import PDEFoundation.Ambient.Basis

/-!
# Spatial Fréchet-derivative coordinate norms

This module defines the Euclidean and Frobenius norms of spatial-coordinate
Fréchet derivatives on the native time--velocity carrier.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open scoped BigOperators

variable {d : ℕ}

/-- Euclidean norm of the spatial-coordinate Fréchet derivative of a scalar field. -/
def spatialScalarFDerivEuclideanNorm
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (z : TimeVelocity d) : ℝ :=
  Real.sqrt (∑ k : Fin d,
    ((fderiv ℝ f z) (0, PDE.basisVec k)) ^ 2)

/-- Frobenius norm of the spatial-coordinate Fréchet derivative of a vector field. -/
def spatialVectorFDerivFrobeniusNorm
    (f : TimeVelocity d → PDE.Vec d) (z : TimeVelocity d) : ℝ :=
  Real.sqrt (∑ j : Fin d, ∑ k : Fin d,
    ((fderiv ℝ (fun w  => f w j) z)
      (0, PDE.basisVec k)) ^ 2)

/-- Frobenius norm of the spatial-coordinate Fréchet derivative of a matrix field. -/
def spatialMatrixFDerivFrobeniusNorm
    (f : TimeVelocity d → PDE.Mat d) (z : TimeVelocity d) : ℝ :=
  Real.sqrt (∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d,
    ((fderiv ℝ (fun w  => f w i j) z)
      (0, PDE.basisVec k)) ^ 2)

/-- Each scalar spatial derivative coordinate is bounded by its Euclidean norm. -/
theorem abs_spatialScalarFDeriv_le
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (z : TimeVelocity d) (k : Fin d) :
    |(fderiv ℝ f z) (0, PDE.basisVec k)| ≤
      spatialScalarFDerivEuclideanNorm f z := by
  unfold spatialScalarFDerivEuclideanNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum

    (fun i _ => sq_nonneg ((fderiv ℝ f z) (0, PDE.basisVec i)))
    (Finset.mem_univ k)

/-- Each vector spatial derivative coordinate is bounded by its Frobenius norm. -/
theorem abs_spatialVectorFDeriv_le
    (f : TimeVelocity d → PDE.Vec d) (z : TimeVelocity d) (j k : Fin d) :
    |(fderiv ℝ (fun w  => f w j) z)
        (0, PDE.basisVec k)| ≤
      spatialVectorFDerivFrobeniusNorm f z := (id
  (Real.abs_le_sqrt
    (Trans.trans
      (Finset.single_le_sum (fun k' x => sq_nonneg ((fderiv ℝ (fun w => f w j) z) (0, PDE.basisVec k')))
        (Finset.mem_univ k))
      (Finset.single_le_sum
        (fun j' x => Finset.sum_nonneg fun k' x => sq_nonneg ((fderiv ℝ (fun w => f w j') z) (0, PDE.basisVec k')))
        (Finset.mem_univ j)))))

/-- Each matrix spatial derivative coordinate is bounded by its Frobenius norm. -/
theorem abs_spatialMatrixFDeriv_le
    (f : TimeVelocity d → PDE.Mat d) (z : TimeVelocity d) (i j k : Fin d) :
    |(fderiv ℝ (fun w  => f w i j) z)
        (0, PDE.basisVec k)| ≤
      spatialMatrixFDerivFrobeniusNorm f z := (id
  (Real.abs_le_sqrt
    (Trans.trans
      (Trans.trans
        (Finset.single_le_sum (fun k' x => sq_nonneg ((fderiv ℝ (fun w => f w i j) z) (0, PDE.basisVec k')))
          (Finset.mem_univ k))
        (Finset.single_le_sum
          (fun j' x => Finset.sum_nonneg fun k' x => sq_nonneg ((fderiv ℝ (fun w => f w i j') z) (0, PDE.basisVec k')))
          (Finset.mem_univ j)))
      (Finset.single_le_sum
        (fun i' x =>
          Finset.sum_nonneg fun j' x =>
            Finset.sum_nonneg fun k' x => sq_nonneg ((fderiv ℝ (fun w => f w i' j') z) (0, PDE.basisVec k')))
        (Finset.mem_univ i)))))

end HypoellipticAleksandrov.Parabolic
