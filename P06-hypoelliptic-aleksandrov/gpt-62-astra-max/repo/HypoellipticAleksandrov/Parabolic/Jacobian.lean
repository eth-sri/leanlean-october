module

public import HypoellipticAleksandrov.Parabolic.ContactMap
public import HypoellipticAleksandrov.LinearAlgebra.DeterminantTrace
public import HypoellipticAleksandrov.Parabolic.Operator
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Parabolic normal-map Jacobian

This module differentiates the parabolic normal map in the product carrier
`TimeVelocity d`.  The `timeVelocityCoordinates` orders time last,
whereas the block calculation here uses a private time-first coordinate display.
Their determinant relation is proved through conjugation, not asserted by
definitional equality.  The raw velocity Jacobian keeps the mixed derivatives
in their genuine order until an explicit `C²` Schwarz bridge replaces it with
`velocityHessian`.

The resulting determinant identity needs only pointwise nonnegativity of the
time derivative and positive semidefiniteness of the negative velocity Hessian;
it has no contact-set premise.  The module also proves the exact pointwise
source bound used by the parabolic ABP argument.  The determinant calculation
uses a determinant-one row operation and therefore requires no Hessian inverse,
also when `d = 0`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open scoped BigOperators MatrixOrder
open Matrix

/-! ## The actual Fréchet derivative -/

section
variable {d : ℕ} {u : TimeVelocity d → ℝ} (hu : ContDiff ℝ 2 u) (y₀ : PDE.Vec d)
    (z : TimeVelocity d)

/-- The derivative candidate for the parabolic normal map. -/
def parabolicNormalMapDerivative (u : TimeVelocity d → ℝ) (y₀ : PDE.Vec d)
    (z : TimeVelocity d) : TimeVelocity d →L[ℝ] TimeVelocity d :=
  let Du := fderiv ℝ u z
  let Dg := fderiv ℝ (velocityGradient u) z
  let velocityCoordinate : Fin d → TimeVelocity d →L[ℝ] ℝ := fun i ↦
    (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ ℝ (PDE.Vec d))
  (Du - ∑ i, ((velocityGradient u z i) • velocityCoordinate i +
      (z.2 i - y₀ i) • ((ContinuousLinearMap.proj i).comp Dg))).prod Dg

include hu in
/-- A globally `C²` scalar function has the displayed Fréchet derivative of
the parabolic normal map. -/
theorem parabolicNormalMap_hasFDerivAt :
    HasFDerivAt (parabolicNormalMap u y₀)
      (parabolicNormalMapDerivative u y₀ z) z := by
  let Du := fderiv ℝ u z
  let Dg := fderiv ℝ (velocityGradient u) z
  let velocityCoordinate := fun i ↦
    (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ ℝ (PDE.Vec d))
  have hu' :=
    (hu.differentiable (by norm_num) z).hasFDerivAt
  have hg' :=
    (differentiable_velocityGradient hu z).hasFDerivAt
  have hdot : HasFDerivAt
      (fun x : TimeVelocity d ↦ PDE.vecDot (velocityGradient u x) (x.2 - y₀))
      (∑ i, ((velocityGradient u z i) • velocityCoordinate i +
        (z.2 i - y₀ i) • ((ContinuousLinearMap.proj i).comp Dg))) z := by
    refine HasFDerivAt.fun_sum fun i _hi ↦ ?_
    have hgi : HasFDerivAt (fun x : TimeVelocity d ↦ velocityGradient u x i)
        ((ContinuousLinearMap.proj i).comp Dg) z := by
      fun_prop
    fun_prop
  exact (hu'.sub hdot).prodMk hg'

include hu in
/-- The corresponding Fréchet derivative formula for the parabolic normal map. -/
theorem parabolicNormalMap_fderiv :
    fderiv ℝ (parabolicNormalMap u y₀) z = parabolicNormalMapDerivative u y₀ z :=
  (parabolicNormalMap_hasFDerivAt hu y₀ z).fderiv

end

/-! ## Private time-first coordinate calculation -/

/-- Product coordinates before the final `finAddFlip`: time is first. -/
private noncomputable def timeFirstCoordinates (d : ℕ) :
    TimeVelocity d ≃L[ℝ] ((Fin 1 ⊕ Fin d) → ℝ) :=
  ((ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℝ)).prodCongr
      (ContinuousLinearEquiv.refl ℝ (PDE.Vec d))).symm.trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 1) (Fin d)
      (fun _ ↦ ℝ)).symm

section
variable {d : ℕ} (L : TimeVelocity d →L[ℝ] TimeVelocity d)

/-- The time-first conjugate of a time--velocity endomorphism. -/
private def timeFirstCoordinateConjugate :
    ((Fin 1 ⊕ Fin d) → ℝ) →L[ℝ] ((Fin 1 ⊕ Fin d) → ℝ) :=
  (timeFirstCoordinates d).toContinuousLinearMap.comp
    (L.comp (timeFirstCoordinates d).symm.toContinuousLinearMap)

include L in
/-- The Pi-basis matrix of the private time-first conjugate. -/
private def timeFirstCoordinateMatrix :
    Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  LinearMap.toMatrix' (timeFirstCoordinateConjugate L).toLinearMap

private theorem det_timeFirstCoordinateMatrix :
    (timeFirstCoordinateMatrix L).det = L.det := by
  calc
    (timeFirstCoordinateMatrix L).det = (timeFirstCoordinateConjugate L).det := by
      simp [timeFirstCoordinateMatrix]
    _ = L.det :=
      LinearMap.det_conj L.toLinearMap (timeFirstCoordinates d).toLinearEquiv

/-- The time-first and time-last matrices have equal determinants.
This determinant bridge is deliberately not a definitional equality of matrices. -/
private theorem det_timeFirstCoordinateMatrix_eq_det_coordinateMatrix :
    (timeFirstCoordinateMatrix L).det = (coordinateMatrix L).det := by
  rw [det_timeFirstCoordinateMatrix, det_coordinateMatrix]

end

/-! ## Private determinant-one row operation -/

section
variable {d : ℕ} (a : ℝ) (q r : PDE.Vec d) (H : PDE.Mat d)

include a in
private def scalarBlock : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ ↦ a

private def rowBlock (r : PDE.Vec d) :
    Matrix (Fin 1) (Fin d) ℝ := fun _ i ↦ r i

private def colBlock (q : PDE.Vec d) :
    Matrix (Fin d) (Fin 1) ℝ := fun i _ ↦ q i

/-- The raw velocity Jacobian keeps input and output derivative coordinates in
their genuine order until the explicit Schwarz step below. -/
private def rawVelocityJacobian (u : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    PDE.Mat d :=
  fun i j ↦
    fderiv ℝ (velocityGradient u) z (0, Pi.single j 1) i

private def rowMulMatrix (r : PDE.Vec d) (H : PDE.Mat d) :
    Matrix (Fin 1) (Fin d) ℝ :=
  fun _ j ↦ ∑ i, r i * H i j

include a q r H in
private def normalBlock :
    Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  Matrix.fromBlocks (scalarBlock (a - PDE.vecDot r q)) (-(rowMulMatrix r H))
    (colBlock q) H

/-- Add `rᵀ` times the lower block row to the top block row. -/
private def normalRowOperation (r : PDE.Vec d) :
    Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  Matrix.fromBlocks 1 (rowBlock r) 0 1

private theorem normalRowOperation_mul_normalBlock :
    normalRowOperation r * normalBlock a q r H =
      Matrix.fromBlocks (scalarBlock a) 0 (colBlock q) H := by
  simp only [normalRowOperation, normalBlock, Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.zero_mul, zero_add]
  congr 1
  · ext ⟨⟩ ⟨⟩
    simp [scalarBlock, rowBlock, colBlock, Matrix.mul_apply, PDE.vecDot]
  · ext ⟨⟩ j
    simp [rowBlock, rowMulMatrix, Matrix.mul_apply]

private theorem det_normalRowOperation (r : PDE.Vec d) :
    (normalRowOperation r).det = 1 := by
  simp [normalRowOperation]

private theorem det_normalBlock :
    (normalBlock a q r H).det = a * H.det := by
  calc
    (normalBlock a q r H).det =
        (normalRowOperation r * normalBlock a q r H).det := by
      rw [Matrix.det_mul, det_normalRowOperation]
      ring
    _ = (Matrix.fromBlocks (scalarBlock a) 0 (colBlock q) H).det := by
      rw [normalRowOperation_mul_normalBlock]
    _ = a * H.det := by
      simp [scalarBlock]

private theorem abs_det_normalBlock_eq
    (ha : 0 ≤ a) (hH : (-H).PosSemidef) :
    |(normalBlock a q r H).det| = a * (-H).det := by
  have habs : |H.det| = (-H).det := by
    calc
      |H.det| = |(-H).det| := by rw [Matrix.det_neg, abs_mul]; simp
      _ = (-H).det := abs_of_nonneg (Matrix.PosSemidef.det_nonneg hH)
  rw [det_normalBlock, abs_mul, abs_of_nonneg ha, habs]

end

/-! ## Private coordinate bridge for the actual derivative -/

section
variable {d : ℕ} {u : TimeVelocity d → ℝ} (x : TimeVelocity d) (hu : ContDiff ℝ 2 u)
    (y₀ : PDE.Vec d) (z : TimeVelocity d)

private theorem timeFirstCoordinates_apply_time :
    timeFirstCoordinates d x (Sum.inl 0) = x.1 := by
  rfl

private theorem timeFirstCoordinates_apply_velocity (i : Fin d) :
    timeFirstCoordinates d x (Sum.inr i) = x.2 i := by
  rfl

private theorem timeFirstCoordinates_symm_time :
    (timeFirstCoordinates d).symm (Pi.single (Sum.inl 0) (1 : ℝ)) = ((1 : ℝ), 0) := by
  apply (timeFirstCoordinates d).injective
  rw [(timeFirstCoordinates d).apply_symm_apply]
  ext i
  rcases i with i | i
  · fin_cases i
    simp [timeFirstCoordinates_apply_time]
  · simp [timeFirstCoordinates_apply_velocity]

private theorem timeFirstCoordinates_symm_velocity (j : Fin d) :
    (timeFirstCoordinates d).symm (Pi.single (Sum.inr j) (1 : ℝ)) =
      ((0 : ℝ), Pi.single j 1) := by
  apply (timeFirstCoordinates d).injective
  rw [(timeFirstCoordinates d).apply_symm_apply]
  ext i
  rcases i with i | i
  · fin_cases i
    simp [timeFirstCoordinates_apply_time]
  · simp [timeFirstCoordinates_apply_velocity, Pi.single_apply]

private theorem timeFirstCoordinateMatrix_apply (L : TimeVelocity d →L[ℝ] TimeVelocity d)
    (i j : Fin 1 ⊕ Fin d) :
    timeFirstCoordinateMatrix L i j =
      timeFirstCoordinates d (L ((timeFirstCoordinates d).symm (Pi.single j 1))) i := by
  simp [timeFirstCoordinateMatrix, timeFirstCoordinateConjugate, LinearMap.toMatrix'_apply]

include hu in
private theorem rawVelocityJacobian_apply_eq (i j : Fin d) :
    rawVelocityJacobian u z i j =
      fderiv ℝ (fderiv ℝ u) z (0, Pi.single j 1) (0, Pi.single i 1) := by
  let H := fderiv ℝ (fderiv ℝ u) z
  let ei : TimeVelocity d := (0, Pi.single i 1)
  have hcomponent :
      fderiv ℝ (fun x : TimeVelocity d ↦ fderiv ℝ u x ei) z = H.flip ei := by
    have happly := ((hu.fderiv_right (m := 1) (by norm_num)).differentiable_one z).hasFDerivAt.clm_apply (hasFDerivAt_const ei z)
    simpa using happly.fderiv
  have hcomponents : ∀ k : Fin d,
      DifferentiableAt ℝ (fun x : TimeVelocity d ↦ fderiv ℝ u x (0, Pi.single k 1)) z := by
    fun_prop
  change
    (fderiv ℝ (fun x : TimeVelocity d ↦ fun k : Fin d ↦
      fderiv ℝ u x (0, Pi.single k 1)) z) (0, Pi.single j 1) i = _
  rw [fderiv_pi hcomponents]
  simp only [ContinuousLinearMap.pi_apply]
  rw [show fderiv ℝ (fun x : TimeVelocity d ↦ fderiv ℝ u x (0, Pi.single i 1)) z =
      H.flip (0, Pi.single i 1) by exact hcomponent]
  rfl

include hu in
private theorem rawVelocityJacobian_eq_velocityHessian :
    rawVelocityJacobian u z = velocityHessian u z := by
  ext i j
  calc
    rawVelocityJacobian u z i j =
        fderiv ℝ (fderiv ℝ u) z (0, Pi.single j 1) (0, Pi.single i 1) :=
      rawVelocityJacobian_apply_eq hu z i j
    _ = fderiv ℝ (fderiv ℝ u) z (0, Pi.single i 1) (0, Pi.single j 1) :=
      (hu.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq
        (0, Pi.single j 1) (0, Pi.single i 1)
    _ = velocityHessian u z i j := rfl

private theorem timeFirstCoordinateMatrix_parabolicNormalMapDerivative_raw :
    timeFirstCoordinateMatrix (parabolicNormalMapDerivative u y₀ z) =
      normalBlock (timeDerivative u z)
        (fun i ↦ fderiv ℝ (velocityGradient u) z ((1 : ℝ), 0) i)
        (z.2 - y₀) (rawVelocityJacobian u z) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i
    fin_cases j
    simp [timeFirstCoordinateMatrix_apply, timeFirstCoordinates_symm_time,
      timeFirstCoordinates_apply_time, parabolicNormalMapDerivative,
      normalBlock, scalarBlock, PDE.vecDot, timeDerivative]
  · fin_cases i
    simp [timeFirstCoordinateMatrix_apply, timeFirstCoordinates_symm_velocity,
      timeFirstCoordinates_apply_time, parabolicNormalMapDerivative,
      normalBlock, rowMulMatrix, rawVelocityJacobian, velocityGradient]
    rw [Finset.sum_add_distrib]
    have hsingle :
        (∑ x : Fin d, (fderiv ℝ u z) (0, Pi.single x 1) *
          (Pi.single j 1 : PDE.Vec d) x) =
          (fderiv ℝ u z) (0, Pi.single j 1) := by
      simp [Pi.single_apply]
    rw [hsingle]
    ring
  · fin_cases j
    simp [timeFirstCoordinateMatrix_apply, timeFirstCoordinates_symm_time,
      timeFirstCoordinates_apply_velocity, parabolicNormalMapDerivative,
      normalBlock, colBlock]
  · simp [timeFirstCoordinateMatrix_apply, timeFirstCoordinates_symm_velocity,
      timeFirstCoordinates_apply_velocity, parabolicNormalMapDerivative,
      normalBlock, rawVelocityJacobian]

include hu in
private theorem timeFirstCoordinateMatrix_parabolicNormalMapDerivative :
    timeFirstCoordinateMatrix (parabolicNormalMapDerivative u y₀ z) =
      normalBlock (timeDerivative u z)
        (fun i ↦ fderiv ℝ (velocityGradient u) z ((1 : ℝ), 0) i)
        (z.2 - y₀) (velocityHessian u z) := by
  rw [timeFirstCoordinateMatrix_parabolicNormalMapDerivative_raw,
    rawVelocityJacobian_eq_velocityHessian hu]

end

/-! ## Absolute determinant identity -/

/-- The absolute determinant of the Fréchet derivative of the parabolic normal
map equals the time derivative times the determinant of the negative velocity
Hessian, under the pointwise sign conditions and with no contact premise. -/
theorem abs_det_fderiv_parabolicNormalMap_eq {d : ℕ} {u : TimeVelocity d → ℝ}
    (hu : ContDiff ℝ 2 u) (y₀ : PDE.Vec d) (z : TimeVelocity d)
    (ht : 0 ≤ timeDerivative u z) (hH : (-velocityHessian u z).PosSemidef) :
    |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| =
      timeDerivative u z * (-velocityHessian u z).det := by
  rw [parabolicNormalMap_fderiv hu]
  rw [← det_coordinateMatrix]
  rw [← det_timeFirstCoordinateMatrix_eq_det_coordinateMatrix]
  rw [timeFirstCoordinateMatrix_parabolicNormalMapDerivative hu]
  exact abs_det_normalBlock_eq _ _ _ _ ht hH

/-! ## Determinant-weighted pointwise source bound -/

variable {d : ℕ}

/-- A positive-definite matrix paired with a positive-semidefinite matrix has
nonnegative product trace, without assuming the two matrices commute. -/
private theorem trace_mul_nonneg_of_posDef_posSemidef (A H : PDE.Mat d) (hA : A.PosDef) (hH : H.PosSemidef) :
    0 ≤ (A * H).trace := by
  let B := CFC.sqrt A * H * CFC.sqrt A
  have hB : B.PosSemidef := by
    have hsqrt : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
      (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq
    simpa only [B, hsqrt] using hH.conjTranspose_mul_mul_same (CFC.sqrt A)
  have htrace : B.trace = (A * H).trace := by
    calc
      B.trace = (H * CFC.sqrt A * CFC.sqrt A).trace := by
        exact (Matrix.trace_mul_cycle H (CFC.sqrt A) (CFC.sqrt A)).symm
      _ = (H * (CFC.sqrt A * CFC.sqrt A)).trace := by
        rw [Matrix.mul_assoc]
      _ = (H * A).trace := by
        rw [CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
      _ = (A * H).trace := Matrix.trace_mul_comm _ _
  rw [← htrace]
  exact hB.trace_nonneg

/-- The forward operator at a `C²` point is the time derivative plus the
trace contribution of the negative velocity Hessian. -/
private theorem parabolicOperator_eq_timeDerivative_add_trace_neg_velocityHessian {u : TimeVelocity d → ℝ} (hu : ContDiff ℝ 2 u)
    (A : CoefficientField d) (z : TimeVelocity d) :
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
      rw [matrixContraction_eq_trace_mul_of_isSymm _ _ ((velocityHessian_isSymm hu z).neg)]

/-- At a point of the parabolic sign set, the normal-map Jacobian is bounded
by the positive source part with the exact determinant weight. -/
theorem abs_det_fderiv_parabolicNormalMap_le_source {A : CoefficientField d} {f u : TimeVelocity d → ℝ}
    (hu : ContDiff ℝ 2 u) {T : ℝ} {y₀ : PDE.Vec d} {z : TimeVelocity d}
    (hz : z ∈ parabolicSignSet T y₀ u)
    (hA : (coefficientAt A z).PosDef)
    (hsub : parabolicOperator A u z ≤ f z) :
    |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| ≤
      (max (f z) 0) ^ (d + 1) /
        ((((d : ℝ) + 1) ^ (d + 1)) * (coefficientAt A z).det) := by
  rcases hz with ⟨_, _, htime, hH⟩
  have hsource :
      timeDerivative u z +
          (coefficientAt A z * (-velocityHessian u z)).trace ≤ f z := by
    rw [← (parabolicOperator_eq_timeDerivative_add_trace_neg_velocityHessian hu A z)]
    exact hsub
  have hsum_nonneg :=
    add_nonneg htime (trace_mul_nonneg_of_posDef_posSemidef _ _ hA hH)
  have hdet_pos := hA.det_pos
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
          (d + 1) := (HypoellipticAleksandrov.det_mul_time_det_le_arith_mean_pow d (coefficientAt A z) (-velocityHessian u z) (timeDerivative u z) hA hH htime)
  have hden_pos : 0 < (d : ℝ) + 1 := by positivity
  have hpow :=
    pow_le_pow_left₀ (div_nonneg hsum_nonneg hden_pos.le) ((div_le_div_iff_of_pos_right hden_pos).mpr hsource) (d + 1)
  calc
    |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| =
        timeDerivative u z * (-velocityHessian u z).det :=
      abs_det_fderiv_parabolicNormalMap_eq hu y₀ z htime hH
    _ ≤ ((timeDerivative u z +
          (coefficientAt A z * (-velocityHessian u z)).trace) / (d + 1)) ^
          (d + 1) / (coefficientAt A z).det := hmatrix_div
    _ ≤ (f z / (d + 1)) ^ (d + 1) / (coefficientAt A z).det :=
      div_le_div_of_nonneg_right hpow hdet_pos.le
    _ = (f z) ^ (d + 1) /
        (((d + 1) ^ (d + 1)) * (coefficientAt A z).det) := by
      rw [div_pow, div_div]
    _ = (max (f z) 0) ^ (d + 1) /
        (((d + 1) ^ (d + 1)) * (coefficientAt A z).det) := by
      rw [max_eq_left (hsum_nonneg.trans hsource)]

end HypoellipticAleksandrov.Parabolic
