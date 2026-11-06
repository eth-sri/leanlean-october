module

public import HypoellipticAleksandrov.Parabolic.Jacobian
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Jacobian

open private HypoellipticAleksandrov.Parabolic.trace_mul_nonneg_of_posDef_posSemidef from HypoellipticAleksandrov.Parabolic.Jacobian
section
open private HypoellipticAleksandrov.Parabolic.timeFirstCoordinateMatrix_parabolicNormalMapDerivative_raw from HypoellipticAleksandrov.Parabolic.Jacobian
private alias _sharedProof_238_0 := HypoellipticAleksandrov.Parabolic.timeFirstCoordinateMatrix_parabolicNormalMapDerivative_raw
end
section
open private HypoellipticAleksandrov.Parabolic.abs_det_normalBlock_eq from HypoellipticAleksandrov.Parabolic.Jacobian
private alias _sharedProof_200_0 := HypoellipticAleksandrov.Parabolic.abs_det_normalBlock_eq
end
section
open private HypoellipticAleksandrov.Parabolic.normalRowOperation_mul_normalBlock from HypoellipticAleksandrov.Parabolic.Jacobian
private alias _sharedProof_81_0 := HypoellipticAleksandrov.Parabolic.normalRowOperation_mul_normalBlock
end
section
open private HypoellipticAleksandrov.Parabolic.timeFirstCoordinates_symm_velocity from HypoellipticAleksandrov.Parabolic.Jacobian
private alias _sharedProof_59_0 := HypoellipticAleksandrov.Parabolic.timeFirstCoordinates_symm_velocity
end


/-!
# Local parabolic normal-map Jacobian

This module localizes the pointwise normal-map differential and determinant
calculation from `Parabolic.Jacobian` to a `ContDiffAt ℝ 2` hypothesis.  It
uses no geometric, contact-set, or global regularity assumption.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open scoped BigOperators MatrixOrder
open Matrix

variable {d : ℕ} {u : HypoellipticAleksandrov.Parabolic.ScalarField d}

private theorem differentiableAt_velocityGradient_of_contDiffAt
     {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 u z) :
    DifferentiableAt ℝ (velocityGradient u) z := by
  rw [differentiableAt_pi]
  intro i
  change DifferentiableAt ℝ
    (fun x  ↦ fderiv ℝ u x (0, Pi.single i 1)) z
  exact ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
    (by norm_num)

variable {y₀ : PDE.Vec d}

/-- A `C²` germ supplies the displayed Fréchet derivative of its parabolic
normal map at its base point. -/
theorem parabolicNormalMap_hasFDerivAt_of_contDiffAt

    {z : TimeVelocity d} (hu : ContDiffAt ℝ 2 u z) :
    HasFDerivAt (parabolicNormalMap u y₀)
      (parabolicNormalMapDerivative u y₀ z) z := by
  let Du := fderiv ℝ u z
  let Dg := fderiv ℝ (velocityGradient u) z
  let velocityCoordinate  := fun i ↦
    (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ ℝ (PDE.Vec d))

  have hg'  :=
    (differentiableAt_velocityGradient_of_contDiffAt hu).hasFDerivAt

  change HasFDerivAt
    (fun x => (u x - PDE.vecDot (velocityGradient u x) (x.2 - y₀),
      velocityGradient u x)) _ z
  simpa only [parabolicNormalMapDerivative, Du, Dg,
    velocityCoordinate, Pi.sub_apply] using (((hu.differentiableAt (by norm_num)).hasFDerivAt).sub (by
        change HasFDerivAt
          (fun x  ↦ ∑ i, velocityGradient u x i * (x.2 i - y₀ i)) _ z
        refine HasFDerivAt.fun_sum fun i _hi ↦ ?_
        have hgi : HasFDerivAt (fun x  ↦ velocityGradient u x i)
            ((ContinuousLinearMap.proj i).comp Dg) z := by
          simpa only [Dg, Function.comp_def, ContinuousLinearMap.proj_apply] using
            ((ContinuousLinearMap.proj i).hasFDerivAt.comp z hg')

        simpa using hgi.fun_mul (show _ by
            simpa [velocityCoordinate] using
              (((ContinuousLinearMap.proj i).comp
                (ContinuousLinearMap.snd ℝ ℝ (PDE.Vec d))).hasFDerivAt.sub_const (y₀ i))))).prodMk hg'

/-- A `C²` germ supplies the displayed Fréchet derivative within every set. -/
theorem parabolicNormalMap_hasFDerivWithinAt_of_contDiffAt

    {s : HypoellipticAleksandrov.Parabolic.Region d} {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 u z) :
    HasFDerivWithinAt (parabolicNormalMap u y₀)
      (parabolicNormalMapDerivative u y₀ z) s z :=
  (parabolicNormalMap_hasFDerivAt_of_contDiffAt hu).hasFDerivWithinAt

/-! ## Private time-first coordinate calculation -/

private def timeFirstCoordinates (d : ℕ) :
    TimeVelocity d ≃L[ℝ] ((Fin 1 ⊕ Fin d) → ℝ) :=
  ((ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℝ)).prodCongr
      (ContinuousLinearEquiv.refl ℝ (PDE.Vec d))).symm.trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 1) (Fin d)
      (fun _ ↦ ℝ)).symm

variable {d : ℕ} (L : TimeVelocity d →L[ℝ] TimeVelocity d)

private def timeFirstCoordinateConjugate  :
    ((Fin 1 ⊕ Fin d) → ℝ) →L[ℝ] ((Fin 1 ⊕ Fin d) → ℝ) :=
  (timeFirstCoordinates d).toContinuousLinearMap.comp
    (L.comp (timeFirstCoordinates d).symm.toContinuousLinearMap)

private def timeFirstCoordinateMatrix   :=
  LinearMap.toMatrix' (timeFirstCoordinateConjugate L).toLinearMap

private theorem det_timeFirstCoordinateMatrix  :
    (timeFirstCoordinateMatrix L).det = L.det := by
  calc
    (timeFirstCoordinateMatrix L).det = (timeFirstCoordinateConjugate L).det := by
      simp [timeFirstCoordinateMatrix]
    _ = L.det :=
      LinearMap.det_conj L.toLinearMap _

private theorem det_timeFirstCoordinateMatrix_eq_det_coordinateMatrix  :
    (timeFirstCoordinateMatrix L).det = (coordinateMatrix L).det := by
  rw [det_timeFirstCoordinateMatrix, det_coordinateMatrix]

/-! ## Private determinant-one row operation -/

private def scalarBlock (a : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ ↦ a

variable {d : ℕ}



private def colBlock  (q : PDE.Vec d) :
    Matrix (Fin d) (Fin 1) ℝ := fun i _ ↦ q i

private def rawVelocityJacobian  (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (z : TimeVelocity d) :
    PDE.Mat d :=
  fun i j ↦ fderiv ℝ (velocityGradient u) z (0, Pi.single j 1) i

private def rowMulMatrix  (r : PDE.Vec d) (H : PDE.Mat d) :
    Matrix (Fin 1) (Fin d) ℝ :=
  fun _ j ↦ ∑ i, r i * H i j

private def normalBlock  (a : ℝ) (q r : PDE.Vec d) (H : PDE.Mat d)  :=
  Matrix.fromBlocks (scalarBlock (a - PDE.vecDot r q)) (-(rowMulMatrix r H))
    (colBlock q) H








variable (a : ℝ) (q r : PDE.Vec d) (H : PDE.Mat d)



private theorem abs_det_normalBlock_eq
    (ha : 0 ≤ a) (hH : (-H).PosSemidef) :
    |(normalBlock a q r H).det| = a * (-H).det := (_sharedProof_200_0 a q r H ha hH)


/-! ## Private coordinate bridge for the local derivative -/

variable (x : TimeVelocity d)












variable {u : HypoellipticAleksandrov.Parabolic.ScalarField d}

section
variable (z : TimeVelocity d) (hu : ContDiffAt ℝ 2 u z)

include hu
private theorem rawVelocityJacobian_apply_eq_of_contDiffAt
     (i j : Fin d) :
    rawVelocityJacobian u z i j =
      fderiv ℝ (fderiv ℝ u) z (0, Pi.single j 1) (0, Pi.single i 1) := by
  let sharedTerm_4d37339fab := ((hu.fderiv_right (m := 1) (by norm_num)))
  let H := fderiv ℝ (fderiv ℝ u) z
  let ei : TimeVelocity d := ((0 ), Pi.single i (1 ))

  have hcomponent :
      fderiv ℝ (fun x  ↦ fderiv ℝ u x ei) z = H.flip ei := by


    simpa [H] using ((sharedTerm_4d37339fab.differentiableAt (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const ei z)).fderiv

  change
    (fderiv ℝ (fun x  ↦ fun k : Fin d ↦
      fderiv ℝ u x (0, Pi.single k 1)) z) (0, Pi.single j 1) i = _
  rw [fderiv_pi (by
      intro k
      exact (sharedTerm_4d37339fab.clm_apply contDiffAt_const).differentiableAt
        (by norm_num))]
  simp only [ContinuousLinearMap.pi_apply]
  rw [show fderiv ℝ (fun x  ↦ fderiv ℝ u x (0, Pi.single i 1)) z =
      H.flip (0, Pi.single i 1) by assumption]
  rfl

private theorem rawVelocityJacobian_eq_velocityHessian_of_contDiffAt
      :
    rawVelocityJacobian u z = velocityHessian u z := by
  ext i j
  calc
    rawVelocityJacobian u z i j =
        fderiv ℝ (fderiv ℝ u) z (0, Pi.single j 1) (0, Pi.single i 1) :=
      rawVelocityJacobian_apply_eq_of_contDiffAt z hu i j
    _ = fderiv ℝ (fderiv ℝ u) z (0, Pi.single i 1) (0, Pi.single j 1) :=
      (hu.isSymmSndFDerivAt (by norm_num)).eq
        ((0 ), Pi.single j 1) ((0 ), Pi.single i 1)
    _ = velocityHessian u z i j := rfl
end


private theorem timeFirstCoordinateMatrix_parabolicNormalMapDerivative_raw
     (y₀ : PDE.Vec d) (z : TimeVelocity d) :
    timeFirstCoordinateMatrix (parabolicNormalMapDerivative u y₀ z) =
      normalBlock (timeDerivative u z)
        ((fderiv ℝ (velocityGradient u) z ((1 ), 0)))
        (z.2 - y₀) (rawVelocityJacobian u z) := (_sharedProof_238_0 y₀ z)


private theorem timeFirstCoordinateMatrix_parabolicNormalMapDerivative_of_contDiffAt
     (z : TimeVelocity d) (hu : ContDiffAt ℝ 2 u z)
    (y₀ : PDE.Vec d) :
    timeFirstCoordinateMatrix (parabolicNormalMapDerivative u y₀ z) =
      normalBlock (timeDerivative u z)
        ((fderiv ℝ (velocityGradient u) z ((1 ), 0)))
        (z.2 - y₀) (velocityHessian u z) := by
  rw [timeFirstCoordinateMatrix_parabolicNormalMapDerivative_raw,
    rawVelocityJacobian_eq_velocityHessian_of_contDiffAt z hu]

private theorem abs_det_fderiv_parabolicNormalMap_eq_of_contDiffAt
      {y₀ : PDE.Vec d} {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 u z)
    (ht : 0 ≤ timeDerivative u z) (hH : (-velocityHessian u z).PosSemidef) :
    |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| =
      timeDerivative u z * (-velocityHessian u z).det := by
  rw [(parabolicNormalMap_hasFDerivAt_of_contDiffAt hu).fderiv]
  rw [← det_coordinateMatrix]
  rw [← det_timeFirstCoordinateMatrix_eq_det_coordinateMatrix]
  rw [timeFirstCoordinateMatrix_parabolicNormalMapDerivative_of_contDiffAt z hu]
  exact abs_det_normalBlock_eq _ _ _ _ ht hH

/-! ## Determinant-weighted pointwise source bound -/




variable {u : HypoellipticAleksandrov.Parabolic.ScalarField d}

private theorem velocityHessian_isSymm_of_contDiffAt
      {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 u z) : (velocityHessian u z).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  simpa [velocityHessian] using
    (hu.isSymmSndFDerivAt (by norm_num)).eq
      ((0 ), Pi.single j 1) ((0 ), Pi.single i 1)

private theorem parabolicOperator_eq_timeDerivative_add_trace_neg_velocityHessian_of_contDiffAt
      (z : TimeVelocity d) (hu : ContDiffAt ℝ 2 u z)
    (A : CoefficientField d) :
    parabolicOperator A u z =
      timeDerivative u z +
        (coefficientAt A z * (-velocityHessian u z)).trace := by

  calc
    parabolicOperator A u z =
        timeDerivative u z - matrixContraction (coefficientAt A z) (velocityHessian u z) :=
      rfl
    _ = timeDerivative u z +
        matrixContraction (coefficientAt A z) (-velocityHessian u z) := by
      rw [matrixContraction_neg_right]
      ring
    _ = timeDerivative u z +
        (coefficientAt A z * (-velocityHessian u z)).trace := by
      rw [matrixContraction_eq_trace_mul_of_isSymm _ _ ((velocityHessian_isSymm_of_contDiffAt hu).neg)]

/-- At a locally `C²` point, the parabolic normal-map Jacobian is bounded by
the positive source part with the exact determinant weight. -/
theorem abs_det_fderiv_parabolicNormalMap_le_source_of_signs
     {A : CoefficientField d} {F u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    {y₀ : PDE.Vec d} {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 u z)
    (ht : 0 ≤ timeDerivative u z)
    (hH : (-velocityHessian u z).PosSemidef)
    (hA : (coefficientAt A z).PosDef)
    (hsub : parabolicOperator A u z ≤ F z) :
    |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| ≤
      (max (F z) 0) ^ (d + 1) /
        ((((d : ℝ) + 1) ^ (d + 1)) * (coefficientAt A z).det) := by
  let sharedTerm_e4d1428376 := ((timeDerivative u z + (coefficientAt A z * (-velocityHessian u z)).trace) / ((d : ℝ) + 1))
  let sharedTerm_371cdd4b83 := (timeDerivative u z + (coefficientAt A z * (-velocityHessian u z)).trace)
  let sharedTerm_ce9422247a := ((((d : ℝ) + 1) ^ (d + 1)) * (coefficientAt A z).det)
  let sharedTerm_7559fd3165 := (F z / ((d : ℝ) + 1))
  let sharedTerm_e33d1103bf := (timeDerivative u z * (-velocityHessian u z).det)
  have htrace  :=
    _root_.HypoellipticAleksandrov.Parabolic.trace_mul_nonneg_of_posDef_posSemidef _ _ hA hH
  have hoperator :
      parabolicOperator A u z =
        sharedTerm_371cdd4b83 :=
    parabolicOperator_eq_timeDerivative_add_trace_neg_velocityHessian_of_contDiffAt z hu A
  have hsource :
      sharedTerm_371cdd4b83 ≤ F z := by
    rw [← hoperator]
    exact hsub
  have hsum_nonneg :
      0 ≤ sharedTerm_371cdd4b83 :=
    add_nonneg ht htrace
  have hF  := hsum_nonneg.trans hsource
  have hdet_pos  := hA.det_pos
  have hmean := HypoellipticAleksandrov.det_mul_time_det_le_arith_mean_pow d
    _ _ _ hA hH ht

  have hden_pos : 0 < (d : ℝ) + 1 := by positivity


  calc
    |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| =
        sharedTerm_e33d1103bf :=
      abs_det_fderiv_parabolicNormalMap_eq_of_contDiffAt hu ht hH
    _ ≤ (sharedTerm_e4d1428376) ^
          (d + 1) / (coefficientAt A z).det := (show _ by
              rw [le_div_iff₀ hdet_pos]
              calc
                sharedTerm_e33d1103bf * (coefficientAt A z).det =
                    (coefficientAt A z).det * timeDerivative u z * (-velocityHessian u z).det := by
                  ring
                _ ≤ (sharedTerm_e4d1428376) ^
                    (d + 1) := hmean)
    _ ≤ (sharedTerm_7559fd3165) ^ (d + 1) / (coefficientAt A z).det :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (div_nonneg hsum_nonneg hden_pos.le) ((div_le_div_iff_of_pos_right hden_pos).mpr hsource) (d + 1)) hdet_pos.le
    _ = (F z) ^ (d + 1) /
        (sharedTerm_ce9422247a) := by
      rw [div_pow, div_div]
    _ = (max (F z) 0) ^ (d + 1) /
        (sharedTerm_ce9422247a) := by
      rw [max_eq_left hF]

end HypoellipticAleksandrov.Parabolic
