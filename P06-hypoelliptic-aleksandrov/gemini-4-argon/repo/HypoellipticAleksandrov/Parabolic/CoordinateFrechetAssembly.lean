module

public import HypoellipticAleksandrov.Parabolic.MollifiedJetUniformCauchy

/-!
# Coordinate assembly of Fréchet derivatives

This file reconstructs continuous linear and bilinear maps from their values
on the canonical time--velocity basis and identifies the assembled coordinate
derivatives with the first and second Fréchet derivatives.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open Filter
open scoped Topology BigOperators

noncomputable section

/- Assemble the values on the canonical time--velocity basis into a
continuous linear map. -/
def coordinateContinuousLinearMap
    {d } {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : TimeVelocityCoord d → F) :
    TimeVelocity d →L[ℝ] F :=
  (ContinuousLinearMap.fst ℝ ℝ (PDE.Vec d)).smulRight
      (a (timeCoord d)) +
    ∑ i : Fin d,
      (((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.snd ℝ ℝ (PDE.Vec d))).smulRight
          (a (velocityCoord i)))

theorem coordinateContinuousLinearMap_eq
    {d } {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : TimeVelocity d →L[ℝ] F) :
    coordinateContinuousLinearMap
      (fun c => L (timeVelocityBasis c)) = L := by
  apply ContinuousLinearMap.ext
  intro z
  calc
    coordinateContinuousLinearMap (fun c => L (timeVelocityBasis c)) z =
        z.1 • L (timeVelocityBasis (timeCoord d)) +
          ∑ i : Fin d, z.2 i • L (timeVelocityBasis (velocityCoord i)) := by
      simp [coordinateContinuousLinearMap]
    _ = L (z.1 • timeVelocityBasis (timeCoord d) +
          ∑ i : Fin d, z.2 i • timeVelocityBasis (velocityCoord i)) := by
      rw [map_add, map_smul]
      simp only [map_sum, map_smul]
    _ = L z := by
      congr 1
      have hv : (∑ i : Fin d, z.2 i • timeVelocityBasis (velocityCoord i)) =
          ((0, z.2) : TimeVelocity d) := by
        rw [show (∑ i : Fin d, z.2 i • timeVelocityBasis (velocityCoord i)) =
            (0, ∑ i : Fin d, z.2 i • PDE.basisVec i) by
          apply Prod.ext
          · simp [timeVelocityBasis, velocityCoord, Prod.fst_sum]
          · simp [timeVelocityBasis, velocityCoord, Prod.snd_sum]]
        rw [PDE.sum_smul_basisVec]
      rw [hv]
      simp [timeVelocityBasis, timeCoord]

/- Assemble scalar values on ordered pairs of canonical coordinates. -/
def coordinateBilinearOperator
    {d } (a : TimeVelocityCoord d → TimeVelocityCoord d → ℝ) :
    TimeVelocity d →L[ℝ] (TimeVelocity d →L[ℝ] ℝ) :=
  coordinateContinuousLinearMap
    (fun c => coordinateContinuousLinearMap (a c))

theorem coordinateContinuousLinearMap_coordinateIteratedFDeriv_one_eq_fderiv
    {d } (f : TimeVelocity d → ℝ) (z )
    (hf : ContDiffAt ℝ 1 f z) :
    coordinateContinuousLinearMap
      (fun c => TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single c 1) f z) = fderiv ℝ f z := by
  rw [← coordinateContinuousLinearMap_eq (fderiv ℝ f z)]
  congr 1
  funext c
  have h := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
      (0 : TimeVelocityMultiIndex d) c f z (by
        convert hf using 1
        simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
          TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order])
  rw [show TimeVelocityMultiIndex.coordinateIteratedFDeriv
      (0 : TimeVelocityMultiIndex d) f = f by
    funext y
    exact TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero f y] at h
  simpa only [zero_add] using h

