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

@[simp] theorem coordinateContinuousLinearMap_apply_timeVelocityBasis
     {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : TimeVelocityCoord d → F) (c : TimeVelocityCoord d) :
    coordinateContinuousLinearMap a (timeVelocityBasis c) = a c := by
  cases c with
  | inl c =>
      cases c
      simp [coordinateContinuousLinearMap, timeVelocityBasis, timeCoord]
  | inr i =>
      simp [coordinateContinuousLinearMap, timeVelocityBasis, velocityCoord]

theorem coordinateContinuousLinearMap_eq
     {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : TimeVelocity d →L[ℝ] F) :
    coordinateContinuousLinearMap
      (fun c => L (timeVelocityBasis c)) = L := by
  apply ContinuousLinearMap.ext
  intro z
  calc
    coordinateContinuousLinearMap _ z =
        z.1 • L (timeVelocityBasis (timeCoord d)) +
          ∑ i : Fin d, z.2 i • L (timeVelocityBasis (velocityCoord i)) := by
      simp [coordinateContinuousLinearMap]
    _ = L (z.1 • timeVelocityBasis (timeCoord d) +
          ∑ i : Fin d, z.2 i • timeVelocityBasis (velocityCoord i)) := by
      rw [map_add]
      simp only [map_sum, map_smul]
    _ = L z := by
      have hv : (∑ i : Fin d, z.2 i • timeVelocityBasis (velocityCoord i)) =
          ((0, z.2)) := by
        rw [show (∑ i : Fin d, z.2 i • timeVelocityBasis (velocityCoord i)) =
            (0, ∑ i : Fin d, z.2 i • PDE.basisVec i) by
          apply Prod.ext
          · simp [timeVelocityBasis, velocityCoord, Prod.fst_sum]
          · simp [timeVelocityBasis, velocityCoord, Prod.snd_sum]]
        aesop
      simp_all

/-- Assemble scalar values on ordered pairs of canonical coordinates. -/
def coordinateBilinearOperator
    {d : ℕ} (a : TimeVelocityCoord d → TimeVelocityCoord d → ℝ) :
    TimeVelocity d →L[ℝ] (TimeVelocity d →L[ℝ] ℝ) :=
  coordinateContinuousLinearMap
    (fun c => coordinateContinuousLinearMap (a c))

variable {d : ℕ} (f : TimeVelocity d → ℝ) (z : TimeVelocity d)

@[simp] theorem coordinateBilinearOperator_apply_timeVelocityBasis
     (a : TimeVelocityCoord d → TimeVelocityCoord d → ℝ)
    (c e : TimeVelocityCoord d) :
    coordinateBilinearOperator a (timeVelocityBasis c)
      (timeVelocityBasis e) = a c e := by
  simp [coordinateBilinearOperator]

theorem coordinateContinuousLinearMap_coordinateIteratedFDeriv_one_eq_fderiv
    
    (hf : ContDiffAt ℝ 1 f z) :
    coordinateContinuousLinearMap
      (fun c => TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single c 1) f z) = fderiv ℝ f z := by
  rw [← coordinateContinuousLinearMap_eq (fderiv ℝ f z)]
  congr 1
  funext c
  have h := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
      (0) c f z (by
        convert hf using 1
        simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
          TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order])
  rw [show TimeVelocityMultiIndex.coordinateIteratedFDeriv
      (0 : TimeVelocityMultiIndex d) f = f by
    aesop] at h
  simp_all

theorem coordinateBilinearOperator_coordinateIteratedFDeriv_two_eq
    
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    coordinateBilinearOperator
      (fun c e => TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single c 1 + Pi.single e 1) f z) =
      fderiv ℝ (fun y => fderiv ℝ f y) z := by
  let H := fderiv ℝ (fun y => fderiv ℝ f y) z
  have hgrad : ContDiff ℝ _ (fderiv ℝ f) :=
    (contDiff_infty_iff_fderiv.mp hf).2
  have hentry (c e : TimeVelocityCoord d) :
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
          (Pi.single c 1 + Pi.single e 1) f z =
        H (timeVelocityBasis c) (timeVelocityBasis e) := by
    rw [add_comm, TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at]
    · have hfirst : (fun y =>
          TimeVelocityMultiIndex.coordinateIteratedFDeriv
            (Pi.single e 1) f y) =
          (fun y => fderiv ℝ f y (timeVelocityBasis e)) := by
        funext y
        have h := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
            (0) e f y
              (by
                convert (contDiff_infty.mp hf 1).contDiffAt using 1
                simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
                  TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order])
        rw [show TimeVelocityMultiIndex.coordinateIteratedFDeriv
            (0 : TimeVelocityMultiIndex d) f = f by
          aesop] at h
        simp_all
      change (fderiv ℝ (fun y =>
        TimeVelocityMultiIndex.coordinateIteratedFDeriv
          _ f y) z) _ = _
      rw [hfirst, fderiv_clm_apply
        (hgrad.differentiable (by simp) z)
        (differentiableAt_const (c := timeVelocityBasis e))]
      aesop
    · exact hf.contDiffAt.of_le (by simp)
  calc
    coordinateBilinearOperator
        _ =
        coordinateBilinearOperator
          (fun c e => H _ _) := by
      congr 1
      funext c e
      exact hentry c e
    _ = coordinateContinuousLinearMap
        _ := by
      unfold coordinateBilinearOperator
      congr 1
      funext c
      exact coordinateContinuousLinearMap_eq
        _
    _ = H := coordinateContinuousLinearMap_eq H
