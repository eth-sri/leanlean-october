module

public import HypoellipticAleksandrov.Parabolic.Jacobian

/-!
# Local parabolic normal-map Jacobian

This module localizes the pointwise normal-map differential and determinant
calculation from `Parabolic.Jacobian` to a `ContDiffAt ℝ 2` hypothesis.  It
uses no geometric, contact-set, or global regularity assumption.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open scoped BigOperators MatrixOrder
open Matrix

variable {d : ℕ} (x : TimeVelocity d) (a : ℝ) (q r : PDE.Vec d) (H : PDE.Mat d) (L : TimeVelocity d →L[ℝ] TimeVelocity d) {u : TimeVelocity d → ℝ} {y₀ : PDE.Vec d} (z : TimeVelocity d)

private theorem differentiableAt_velocityGradient_of_contDiffAt
     {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 u z) :
    DifferentiableAt ℝ (velocityGradient u) z := by
  rw [differentiableAt_pi]
  intro i
  exact ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
    (by norm_num)

/-- A `C²` germ supplies the displayed Fréchet derivative of its parabolic
normal map at its base point. -/
theorem parabolicNormalMap_hasFDerivAt_of_contDiffAt
    
    {z : TimeVelocity d} (hu : ContDiffAt ℝ 2 u z) :
    HasFDerivAt (parabolicNormalMap u y₀)
      (parabolicNormalMapDerivative u y₀ z) z := by
  let Du := fderiv ℝ u z
  let Dg := fderiv ℝ (velocityGradient u) z
  let velocityCoordinate : Fin d → TimeVelocity d →L[ℝ] ℝ := fun i ↦
    (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ ℝ (PDE.Vec d))
  have hu' : HasFDerivAt u Du z :=
    (hu.differentiableAt (by norm_num)).hasFDerivAt
  have hg' : HasFDerivAt _ Dg z :=
    (differentiableAt_velocityGradient_of_contDiffAt hu).hasFDerivAt
  have hdot : HasFDerivAt
      (fun x : TimeVelocity d ↦ PDE.vecDot (velocityGradient u x) (x.2 - y₀))
      (∑ i, ((velocityGradient u z i) • velocityCoordinate i +
        (z.2 i - y₀ i) • ((ContinuousLinearMap.proj i).comp Dg))) z := by
    refine HasFDerivAt.fun_sum fun i _hi ↦ ?_
    have hgi : HasFDerivAt (fun x : TimeVelocity d ↦ velocityGradient u x i)
        ((ContinuousLinearMap.proj i).comp Dg) z := by
      simpa only [Dg, Function.comp_def, ContinuousLinearMap.proj_apply] using
        ((ContinuousLinearMap.proj i).hasFDerivAt.comp z hg')
    have hri : HasFDerivAt (fun x : TimeVelocity d ↦ x.2 i - y₀ i)
        (velocityCoordinate i) z := by
      simpa [velocityCoordinate] using
        (((ContinuousLinearMap.proj i).comp
          (ContinuousLinearMap.snd ℝ ℝ (PDE.Vec d))).hasFDerivAt.sub_const (y₀ i))
    simpa using hgi.fun_mul hri
  change HasFDerivAt
    (fun x => (u x - PDE.vecDot _ _,
      velocityGradient u x)) _ z
  simpa only [parabolicNormalMapDerivative, Du, Dg,
    velocityCoordinate, Pi.sub_apply] using (hu'.sub hdot).prodMk hg'

/-- A `C²` germ supplies the displayed Fréchet derivative within every set. -/
theorem parabolicNormalMap_hasFDerivWithinAt_of_contDiffAt
    
    {s : Set (TimeVelocity d)} {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 u z) :
    HasFDerivWithinAt (parabolicNormalMap u y₀)
      (parabolicNormalMapDerivative u y₀ z) s z :=
  (parabolicNormalMap_hasFDerivAt_of_contDiffAt hu).hasFDerivWithinAt

/-! ## Private time-first coordinate calculation -/






/-! ## Private determinant-one row operation -/












/-! ## Private coordinate bridge for the local derivative -/






private theorem rawVelocityJacobian_apply_eq_of_contDiffAt  (hu : ContDiffAt ℝ 2 u z) (i j : Fin d) :
    rawVelocityJacobian u z i j =
      fderiv ℝ (fderiv ℝ u) z (0, Pi.single j 1) (0, Pi.single i 1) := by
  let H := fderiv ℝ (fderiv ℝ u) z
  let ei : TimeVelocity d := ((0), Pi.single i (1))
  have hDu : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcomponent :
      fderiv ℝ (fun x : TimeVelocity d ↦ fderiv ℝ u x ei) z = H.flip ei := by
    have hconst : HasFDerivAt
        _
        (0 : TimeVelocity d →L[ℝ] TimeVelocity d) z :=
      hasFDerivAt_const ei z
    have happly := hDu.hasFDerivAt.clm_apply hconst
    simpa [H] using happly.fderiv
  have hcomponents : ∀ k : Fin d,
      DifferentiableAt ℝ (fun x : TimeVelocity d ↦ fderiv ℝ u x (0, Pi.single k 1)) z := by
    intro k
    exact ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  change
    (fderiv ℝ (fun x : TimeVelocity d ↦ fun k : Fin d ↦
      fderiv ℝ u x _) z) _ i = _
  rw [fderiv_pi hcomponents]
  simp only [ContinuousLinearMap.pi_apply]
  rw [show fderiv ℝ (fun x : TimeVelocity d ↦ fderiv ℝ u x (0, Pi.single i 1)) z =
      H.flip (0, Pi.single i 1) by simpa [ei] using hcomponent]
  rfl

private theorem rawVelocityJacobian_eq_velocityHessian_of_contDiffAt  (hu : ContDiffAt ℝ 2 u z) :
    rawVelocityJacobian u z = velocityHessian u z := by
  ext i j
  calc
    rawVelocityJacobian u z i j =
        fderiv ℝ (fderiv ℝ u) z _ _ :=
      rawVelocityJacobian_apply_eq_of_contDiffAt z hu i j
    _ = fderiv ℝ (fderiv ℝ u) z _ _ :=
      (hu.isSymmSndFDerivAt (by norm_num)).eq
        _ _
    _ = velocityHessian u z i j := rfl


private theorem timeFirstCoordinateMatrix_parabolicNormalMapDerivative_of_contDiffAt  (hu : ContDiffAt ℝ 2 u z)
    (y₀ : PDE.Vec d) :
    timeFirstCoordinateMatrix (parabolicNormalMapDerivative u y₀ z) =
      normalBlock (timeDerivative u z)
        (fun i ↦ fderiv ℝ (velocityGradient u) z ((1 : ℝ), 0) i)
        (z.2 - y₀) (velocityHessian u z) := by
  rw [timeFirstCoordinateMatrix_parabolicNormalMapDerivative_raw,
    rawVelocityJacobian_eq_velocityHessian_of_contDiffAt z hu]

private theorem abs_det_fderiv_parabolicNormalMap_eq_of_contDiffAt
     {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 u z)
    (ht : 0 ≤ timeDerivative u z) (hH : (-velocityHessian u z).PosSemidef) :
    |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| =
      timeDerivative u z * (-velocityHessian u z).det := by
  rw [(parabolicNormalMap_hasFDerivAt_of_contDiffAt hu).fderiv, ← det_coordinateMatrix]
  rw [← det_timeFirstCoordinateMatrix_eq_det_coordinateMatrix, timeFirstCoordinateMatrix_parabolicNormalMapDerivative_of_contDiffAt z hu]
  exact abs_det_normalBlock_eq _ _ _ _ ht hH

/-! ## Determinant-weighted pointwise source bound -/


private theorem velocityHessian_isSymm_of_contDiffAt
     {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 u z) : (velocityHessian u z).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  simpa [velocityHessian] using
    (hu.isSymmSndFDerivAt (by norm_num)).eq
      _ _

private theorem parabolicOperator_eq_timeDerivative_add_trace_neg_velocityHessian_of_contDiffAt
     (hu : ContDiffAt ℝ 2 u z)
    (A : CoefficientField d) :
    parabolicOperator A u z =
      timeDerivative u z +
        (coefficientAt A z * (-velocityHessian u z)).trace := by
  have hHsymm : (-velocityHessian u z).IsSymm :=
    (velocityHessian_isSymm_of_contDiffAt hu).neg
  calc
    parabolicOperator A u z =
        timeDerivative u z - matrixContraction _ _ :=
      rfl
    _ = timeDerivative u z +
        matrixContraction _ _ := by
      rw [matrixContraction_neg_right]
      ring
    _ = timeDerivative u z +
        (coefficientAt A z * (-velocityHessian u z)).trace := by
      rw [matrixContraction_eq_trace_mul_of_isSymm _ _ hHsymm]

/-- At a locally `C²` point, the parabolic normal-map Jacobian is bounded by
the positive source part with the exact determinant weight. -/
theorem abs_det_fderiv_parabolicNormalMap_le_source_of_signs
     {A : CoefficientField d} {F u : TimeVelocity d → ℝ}
    {y₀ : PDE.Vec d} {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 u z)
    (ht : 0 ≤ timeDerivative u z)
    (hH : (-velocityHessian u z).PosSemidef)
    (hA : (coefficientAt A z).PosDef)
    (hsub : parabolicOperator A u z ≤ F z) :
    |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| ≤
      (max (F z) 0) ^ (d + 1) /
        ((((d : ℝ) + 1) ^ (d + 1)) * (coefficientAt A z).det) := by
  have htrace  :=
    trace_mul_nonneg_of_posDef_posSemidef _ _ hA hH
  have hoperator  :=
    parabolicOperator_eq_timeDerivative_add_trace_neg_velocityHessian_of_contDiffAt z hu A
  have hsource :
      timeDerivative u z +
          (coefficientAt A z * (-velocityHessian u z)).trace ≤ F z := by
    rw [← hoperator]
    exact hsub
  have hsum_nonneg :
      0 ≤ timeDerivative u z +
        (coefficientAt A z * (-velocityHessian u z)).trace :=
    add_nonneg ht htrace
  have hF : 0 ≤ F z := hsum_nonneg.trans hsource
  have hdet_pos : 0 < (coefficientAt A z).det := hA.det_pos
  have hmean := HypoellipticAleksandrov.det_mul_time_det_le_arith_mean_pow d
    _ _ _ hA hH ht
  have hmatrix_div :
      timeDerivative u z * (-velocityHessian u z).det ≤
        ((timeDerivative u z +
            (coefficientAt A z * (-velocityHessian u z)).trace) / (d + 1)) ^
            (d + 1) / (coefficientAt A z).det := by
    rw [le_div_iff₀ hdet_pos]
    calc
      timeDerivative u z * (-velocityHessian u z).det * (coefficientAt A z).det =
          (coefficientAt A z).det * timeDerivative u z * (-velocityHessian u z).det := by
        ring
      _ ≤ ((timeDerivative u z +
          (coefficientAt A z * (-velocityHessian u z)).trace) / (d + 1)) ^
          (d + 1) := hmean
  have hden_pos : 0 < (d : ℝ) + 1 := by positivity
  have hquot :
      (timeDerivative u z +
          (coefficientAt A z * (-velocityHessian u z)).trace) / (d + 1) ≤
        F z / (d + 1) :=
    (div_le_div_iff_of_pos_right hden_pos).mpr hsource
  have hpow :
      ((timeDerivative u z +
          (coefficientAt A z * (-velocityHessian u z)).trace) / (d + 1)) ^ (d + 1) ≤
        (F z / (d + 1)) ^ (d + 1) :=
    pow_le_pow_left₀ (div_nonneg hsum_nonneg hden_pos.le) hquot _
  calc
    |((fderiv ℝ _ z).det)| =
        timeDerivative u z * (-velocityHessian u z).det :=
      abs_det_fderiv_parabolicNormalMap_eq_of_contDiffAt hu ht hH
    _ ≤ ((timeDerivative u z +
          (coefficientAt A z * (-velocityHessian u z)).trace) / (d + 1)) ^
          (d + 1) / (coefficientAt A z).det := hmatrix_div
    _ ≤ (F z / (d + 1)) ^ (d + 1) / (coefficientAt A z).det :=
      div_le_div_of_nonneg_right hpow hdet_pos.le
    _ = (F z) ^ (d + 1) /
        (((d + 1) ^ (d + 1)) * (coefficientAt A z).det) := by
      rw [div_pow, div_div]
    _ = (max _ 0) ^ (d + 1) /
        (((d + 1) ^ (d + 1)) * (coefficientAt A z).det) := by
      rw [max_eq_left hF]

end HypoellipticAleksandrov.Parabolic
