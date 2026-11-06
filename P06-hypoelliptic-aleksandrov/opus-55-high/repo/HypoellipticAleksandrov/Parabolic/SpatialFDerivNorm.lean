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

/-- Euclidean norm of the spatial-coordinate Fréchet derivative of a scalar field. -/
def spatialScalarFDerivEuclideanNorm {d : ℕ}
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d) : ℝ :=
  Real.sqrt (∑ k : Fin d,
    ((fderiv ℝ f z) (0, PDE.basisVec k)) ^ 2)

/-- Frobenius norm of the spatial-coordinate Fréchet derivative of a vector field. -/
def spatialVectorFDerivFrobeniusNorm {d : ℕ}
    (f : TimeVelocity d → PDE.Vec d) (z : TimeVelocity d) : ℝ :=
  Real.sqrt (∑ j : Fin d, ∑ k : Fin d,
    ((fderiv ℝ (fun w : TimeVelocity d => f w j) z)
      (0, PDE.basisVec k)) ^ 2)

/-- Frobenius norm of the spatial-coordinate Fréchet derivative of a matrix field. -/
def spatialMatrixFDerivFrobeniusNorm {d : ℕ}
    (f : TimeVelocity d → PDE.Mat d) (z : TimeVelocity d) : ℝ :=
  Real.sqrt (∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d,
    ((fderiv ℝ (fun w : TimeVelocity d => f w i j) z)
      (0, PDE.basisVec k)) ^ 2)

variable {d : ℕ}

/-- Each scalar spatial derivative coordinate is bounded by its Euclidean norm. -/
theorem abs_spatialScalarFDeriv_le 
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d) (k : Fin d) :
    |(fderiv ℝ f z) (0, PDE.basisVec k)| ≤
      spatialScalarFDerivEuclideanNorm f z := by
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun i : Fin d => ((fderiv ℝ f z) _) ^ 2)
    (fun i _ => sq_nonneg ((fderiv ℝ f z) (0, PDE.basisVec i)))
    (Finset.mem_univ k)

/-- Each vector spatial derivative coordinate is bounded by its Frobenius norm. -/
theorem abs_spatialVectorFDeriv_le 
    (f : TimeVelocity d → PDE.Vec d) (z : TimeVelocity d) (j k : Fin d) :
    |(fderiv ℝ (fun w : TimeVelocity d => f w j) z)
        (0, PDE.basisVec k)| ≤
      spatialVectorFDerivFrobeniusNorm f z := by
  apply Real.abs_le_sqrt
  calc
    ((fderiv ℝ _ z) _) ^ 2 ≤
        ∑ k' : Fin d,
          ((fderiv ℝ _ z)
            _) ^ 2 := Finset.single_le_sum (s := Finset.univ)
        (f := fun k' : Fin d =>
          ((fderiv ℝ _ z)
            _) ^ 2)
        (fun k' _ => sq_nonneg ((fderiv ℝ _ z)
          (0, PDE.basisVec k')))
        (Finset.mem_univ k)
    _ ≤ ∑ j' : Fin d, ∑ k' : Fin d,
        ((fderiv ℝ (fun w : TimeVelocity d => f w j') z)
          _) ^ 2 := Finset.single_le_sum (s := Finset.univ)
        (f := fun j' : Fin d => ∑ k' : Fin d,
          ((fderiv ℝ _ z)
            _) ^ 2)
        (fun j' _ => Finset.sum_nonneg fun k' _ =>
          sq_nonneg ((fderiv ℝ (fun w : TimeVelocity d => f w j') z)
            (0, PDE.basisVec k')))
        (Finset.mem_univ j)

/-- Each matrix spatial derivative coordinate is bounded by its Frobenius norm. -/
theorem abs_spatialMatrixFDeriv_le 
    (f : TimeVelocity d → PDE.Mat d) (z : TimeVelocity d) (i j k : Fin d) :
    |(fderiv ℝ (fun w : TimeVelocity d => f w i j) z)
        (0, PDE.basisVec k)| ≤
      spatialMatrixFDerivFrobeniusNorm f z := by
  apply Real.abs_le_sqrt
  calc
    ((fderiv ℝ _ z) _) ^ 2 ≤
        ∑ k' : Fin d,
          ((fderiv ℝ _ z)
            _) ^ 2 := Finset.single_le_sum (s := Finset.univ)
        (f := fun k' : Fin d =>
          ((fderiv ℝ _ z)
            _) ^ 2)
        (fun k' _ => sq_nonneg ((fderiv ℝ _ z)
          (0, PDE.basisVec k')))
        (Finset.mem_univ k)
    _ ≤ ∑ j' : Fin d, ∑ k' : Fin d,
        ((fderiv ℝ (fun w : TimeVelocity d => f w i j') z)
          _) ^ 2 := Finset.single_le_sum (s := Finset.univ)
        (f := fun j' : Fin d => ∑ k' : Fin d,
          ((fderiv ℝ _ z)
            _) ^ 2)
        (fun j' _ => Finset.sum_nonneg fun k' _ =>
          sq_nonneg ((fderiv ℝ (fun w : TimeVelocity d => f w i j') z)
            (0, PDE.basisVec k')))
        (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin d, ∑ j' : Fin d, ∑ k' : Fin d,
        ((fderiv ℝ _ z)
          _) ^ 2 := Finset.single_le_sum (s := Finset.univ)
        (f := fun i' : Fin d => ∑ j' : Fin d, ∑ k' : Fin d,
          ((fderiv ℝ _ z)
            _) ^ 2)
        (fun i' _ => Finset.sum_nonneg fun j' _ =>
          Finset.sum_nonneg fun k' _ =>
            sq_nonneg ((fderiv ℝ (fun w : TimeVelocity d => f w i' j') z)
              (0, PDE.basisVec k')))
        (Finset.mem_univ i)

end HypoellipticAleksandrov.Parabolic
