module

public import HypoellipticAleksandrov.Parabolic.MollifiedJetUniformCauchy
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Coordinate assembly of Fréchet derivatives

This file reconstructs continuous linear and bilinear maps from their values
on the canonical time--velocity basis and identifies the assembled coordinate
derivatives with the first and second Fréchet derivatives.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic


open scoped BigOperators

noncomputable section

/-- Assemble the values on the canonical time--velocity basis into a
continuous linear map. -/
def coordinateContinuousLinearMap
    {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : TimeVelocityCoord d → F) :
    TimeVelocity d →L[ℝ] F :=
  (ContinuousLinearMap.fst ℝ ℝ (PDE.Vec d)).smulRight
      (a (timeCoord d)) +
    ∑ i : Fin d,
      (((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.snd ℝ ℝ (PDE.Vec d))).smulRight
          (a (velocityCoord i)))

variable {d : ℕ}

variable {F : Type*}

@[simp] theorem coordinateContinuousLinearMap_apply_timeVelocityBasis

    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : TimeVelocityCoord d → F) (c : TimeVelocityCoord d) :
    coordinateContinuousLinearMap a (timeVelocityBasis c) = a c := by
  cases c with
  | inl c =>
      cases c
      simp [coordinateContinuousLinearMap, timeVelocityBasis, timeCoord]
  | inr i =>
      simp [coordinateContinuousLinearMap, timeVelocityBasis, velocityCoord, PDE.basisVec]

theorem coordinateContinuousLinearMap_eq

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

variable (a : TimeVelocityCoord d → TimeVelocityCoord d → ℝ)

/-- Assemble scalar values on ordered pairs of canonical coordinates. -/
def coordinateBilinearOperator
      :
    TimeVelocity d →L[ℝ] (TimeVelocity d →L[ℝ] ℝ) :=
  coordinateContinuousLinearMap
    (fun c => coordinateContinuousLinearMap (a c))



variable (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (z : TimeVelocity d)

theorem coordinateContinuousLinearMap_coordinateIteratedFDeriv_one_eq_fderiv

    (hf : ContDiffAt ℝ 1 f z) :
    coordinateContinuousLinearMap
      (fun c => TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single c 1) f z) = fderiv ℝ f z := by
  rw [← coordinateContinuousLinearMap_eq (fderiv ℝ f z)]
  congr 1
  funext c
  have h := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
      (0 : TimeVelocityMultiIndex d) c f z (by
        simp_all [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order])
  rw [show TimeVelocityMultiIndex.coordinateIteratedFDeriv
      (0 : TimeVelocityMultiIndex d) f = f by
    funext y
    exact TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero f y] at h
  simpa only [zero_add] using h

theorem coordinateBilinearOperator_coordinateIteratedFDeriv_two_eq

    (hf : ContDiff ℝ PDE.smoothOrder f) :
    coordinateBilinearOperator
      (fun c e => TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single c 1 + Pi.single e 1) f z) =
      fderiv ℝ ((fderiv ℝ f)) z := by
  let H := fderiv ℝ ((fderiv ℝ f)) z

  have hentry (c e : TimeVelocityCoord d) :
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
          (Pi.single c 1 + Pi.single e 1) f z =
        H (timeVelocityBasis c) (timeVelocityBasis e) := by
    rw [add_comm]
    rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at]
    · have hfirst : ((TimeVelocityMultiIndex.coordinateIteratedFDeriv (Pi.single e 1) f)) =
          (fun y => fderiv ℝ f y (timeVelocityBasis e)) := by
        funext y
        have h := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
            (0 : TimeVelocityMultiIndex d) e f y
              (by
                convert (contDiff_infty.mp hf 1).contDiffAt using 1
                simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
                  TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order])
        rw [show TimeVelocityMultiIndex.coordinateIteratedFDeriv
            (0 : TimeVelocityMultiIndex d) f = f by
          funext x
          exact TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero f x] at h
        simpa only [zero_add] using h
      change (fderiv ℝ ((TimeVelocityMultiIndex.coordinateIteratedFDeriv (Pi.single e 1) f)) z) (timeVelocityBasis c) = _
      rw [hfirst, fderiv_clm_apply
        (((contDiff_infty_iff_fderiv.mp hf).2).differentiable (by simp) z)
        (differentiableAt_const (c := timeVelocityBasis e))]
      simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
        ContinuousLinearMap.flip_apply]
      rfl
    · exact hf.contDiffAt.of_le (by simp)
  calc
    coordinateBilinearOperator
        (fun c e => TimeVelocityMultiIndex.coordinateIteratedFDeriv
          (Pi.single c 1 + Pi.single e 1) f z) =
        coordinateBilinearOperator
          (fun c e => H (timeVelocityBasis c) (timeVelocityBasis e)) := by
      congr 1
      funext c e
      exact hentry c e
    _ = coordinateContinuousLinearMap
        (fun c => H (timeVelocityBasis c)) := by
      unfold coordinateBilinearOperator
      congr 1
      funext c
      exact coordinateContinuousLinearMap_eq
        (H (timeVelocityBasis c))
    _ = H := coordinateContinuousLinearMap_eq H
