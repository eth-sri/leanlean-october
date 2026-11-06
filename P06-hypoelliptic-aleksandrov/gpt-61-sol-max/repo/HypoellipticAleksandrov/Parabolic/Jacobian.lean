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

variable {d : ℕ}

/-- The derivative candidate for the parabolic normal map. -/
def parabolicNormalMapDerivative  (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (y₀ : PDE.Vec d)
    (z : TimeVelocity d) : TimeVelocity d →L[ℝ] TimeVelocity d :=
  let Du := fderiv ℝ u z
  let Dg := fderiv ℝ (velocityGradient u) z
  let velocityCoordinate : Fin d → TimeVelocity d →L[ℝ] ℝ := fun i ↦
    (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ ℝ (PDE.Vec d))
  (Du - ∑ i, ((velocityGradient u z i) • velocityCoordinate i +
      (z.2 i - y₀ i) • ((ContinuousLinearMap.proj i).comp Dg))).prod Dg

section
variable {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (hu : ContDiff ℝ 2 u) (y₀ : PDE.Vec d) (z : TimeVelocity d)

include hu
/-- A globally `C²` scalar function has the displayed Fréchet derivative of
the parabolic normal map. -/
theorem parabolicNormalMap_hasFDerivAt   :
    HasFDerivAt (parabolicNormalMap u y₀)
      (parabolicNormalMapDerivative u y₀ z) z := by
  let Du := fderiv ℝ u z
  let Dg := fderiv ℝ (velocityGradient u) z
  let velocityCoordinate  := fun i ↦
    (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ ℝ (PDE.Vec d))

  have hg'  :=
    (differentiable_velocityGradient hu z).hasFDerivAt

  change HasFDerivAt
    (fun x => (u x - PDE.vecDot (velocityGradient u x) (x.2 - y₀), velocityGradient u x))
    (parabolicNormalMapDerivative u y₀ z) z
  simpa [parabolicNormalMapDerivative, Du, Dg,
    velocityCoordinate, Function.comp_def] using (((hu.differentiable (by norm_num) z).hasFDerivAt).sub (by
        change HasFDerivAt
          (fun x  ↦ ∑ i, velocityGradient u x i * (x.2 i - y₀ i)) _ z
        refine HasFDerivAt.fun_sum fun i _hi ↦ ?_
        have hgi : HasFDerivAt (fun x  ↦ velocityGradient u x i)
            ((ContinuousLinearMap.proj i).comp Dg) z := by
          simpa [Dg, Function.comp_def] using ((ContinuousLinearMap.proj i).hasFDerivAt.comp z hg')

        simpa using hgi.fun_mul (show _ by
            simpa [velocityCoordinate] using
              (((ContinuousLinearMap.proj i).comp
                (ContinuousLinearMap.snd ℝ ℝ (PDE.Vec d))).hasFDerivAt.sub_const (y₀ i))))).prodMk hg'

/-- The corresponding Fréchet derivative formula for the parabolic normal map. -/
theorem parabolicNormalMap_fderiv   :
    fderiv ℝ (parabolicNormalMap u y₀) z = parabolicNormalMapDerivative u y₀ z :=
  (parabolicNormalMap_hasFDerivAt hu y₀ z).fderiv
end


/-! ## Private time-first coordinate calculation -/

/-- Product coordinates before the final `finAddFlip`: time is first. -/
private def timeFirstCoordinates (d : ℕ) :
    TimeVelocity d ≃L[ℝ] ((Fin 1 ⊕ Fin d) → ℝ) :=
  ((ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℝ)).prodCongr
      (ContinuousLinearEquiv.refl ℝ (PDE.Vec d))).symm.trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 1) (Fin d)
      (fun _ ↦ ℝ)).symm

variable {d : ℕ} (L : TimeVelocity d →L[ℝ] TimeVelocity d)

/-- The time-first conjugate of a time--velocity endomorphism. -/
private def timeFirstCoordinateConjugate  :
    ((Fin 1 ⊕ Fin d) → ℝ) →L[ℝ] ((Fin 1 ⊕ Fin d) → ℝ) :=
  (timeFirstCoordinates d).toContinuousLinearMap.comp
    (L.comp (timeFirstCoordinates d).symm.toContinuousLinearMap)

/-- The Pi-basis matrix of the private time-first conjugate. -/
private def timeFirstCoordinateMatrix   :=
  LinearMap.toMatrix' (timeFirstCoordinateConjugate L).toLinearMap

private theorem det_timeFirstCoordinateMatrix  :
    (timeFirstCoordinateMatrix L).det = L.det := by
  calc
    (timeFirstCoordinateMatrix L).det = (timeFirstCoordinateConjugate L).det := by
      simp [timeFirstCoordinateMatrix]
    _ = L.det :=
      LinearMap.det_conj L.toLinearMap _

/-- The time-first and time-last matrices have equal determinants.
This determinant bridge is deliberately not a definitional equality of matrices. -/
private theorem det_timeFirstCoordinateMatrix_eq_det_coordinateMatrix  :
    (timeFirstCoordinateMatrix L).det = (coordinateMatrix L).det := by
  rw [det_timeFirstCoordinateMatrix, det_coordinateMatrix]

/-! ## Private determinant-one row operation -/

private def scalarBlock (a : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ ↦ a

variable {d : ℕ}

private def rowBlock  (r : PDE.Vec d) :
    Matrix (Fin 1) (Fin d) ℝ := fun _ i ↦ r i

private def colBlock  (q : PDE.Vec d) :
    Matrix (Fin d) (Fin 1) ℝ := fun i _ ↦ q i

/-- The raw velocity Jacobian keeps input and output derivative coordinates in
their genuine order until the explicit Schwarz step below. -/
private def rawVelocityJacobian  (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (z : TimeVelocity d) :
    PDE.Mat d :=
  fun i j ↦
    fderiv ℝ (velocityGradient u) z (0, Pi.single j 1) i

private def rowMulMatrix  (r : PDE.Vec d) (H : PDE.Mat d) :
    Matrix (Fin 1) (Fin d) ℝ :=
  fun _ j ↦ ∑ i, r i * H i j

private def normalBlock  (a : ℝ) (q r : PDE.Vec d) (H : PDE.Mat d)  :=
  Matrix.fromBlocks (scalarBlock (a - PDE.vecDot r q)) (-(rowMulMatrix r H))
    (colBlock q) H

/-- Add `rᵀ` times the lower block row to the top block row. -/
private def normalRowOperation  (r : PDE.Vec d) :
    Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  Matrix.fromBlocks 1 (rowBlock r) 0 1

private theorem normalRowOperation_mul_normalBlock  (a : ℝ) (q r : PDE.Vec d)
    (H : PDE.Mat d) :
    normalRowOperation r * normalBlock a q r H =
      Matrix.fromBlocks (scalarBlock a) 0 (colBlock q) H := by
  simp only [normalRowOperation, normalBlock, Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.zero_mul, zero_add]
  congr 1
  · ext ⟨⟩ ⟨⟩
    simp [scalarBlock, rowBlock, colBlock, Matrix.mul_apply, PDE.vecDot]
  · ext ⟨⟩ j
    simp [rowBlock, rowMulMatrix, Matrix.mul_apply]

private theorem det_normalRowOperation  (r : PDE.Vec d) :
    (normalRowOperation r).det = 1 := by
  simp [normalRowOperation]

variable (a : ℝ) (q r : PDE.Vec d) (H : PDE.Mat d)

private theorem det_normalBlock   :
    (normalBlock a q r H).det = a * H.det := by
  calc
    (normalBlock a q r H).det =
        (normalRowOperation r * normalBlock a q r H).det := by
      rw [Matrix.det_mul, det_normalRowOperation]
      ring
    _ = (Matrix.fromBlocks (scalarBlock a) 0 (colBlock q) H).det := by
      rw [normalRowOperation_mul_normalBlock]
    _ = a * H.det := by
      simp [scalarBlock, Matrix.det_fromBlocks_zero₁₂]

private theorem abs_det_normalBlock_eq
    (ha : 0 ≤ a) (hH : (-H).PosSemidef) :
    |(normalBlock a q r H).det| = a * (-H).det := by

  have habs : |H.det| = (-H).det := by
    calc
      |H.det| = |(-H).det| := by rw [Matrix.det_neg, abs_mul]; simp
      _ = (-H).det := abs_of_nonneg (Matrix.PosSemidef.det_nonneg hH)
  rw [det_normalBlock, abs_mul, abs_of_nonneg ha, habs]

/-! ## Private coordinate bridge for the actual derivative -/

variable (x : TimeVelocity d)

private theorem timeFirstCoordinates_apply_time   :
    timeFirstCoordinates d x (Sum.inl 0) = x.1 := rfl

private theorem timeFirstCoordinates_apply_velocity   (i : Fin d) :
    timeFirstCoordinates d x (Sum.inr i) = x.2 i := rfl

private theorem timeFirstCoordinates_symm_time  :
    (timeFirstCoordinates d).symm (Pi.single (Sum.inl 0) (1 )) = ((1 : ℝ), 0) := rfl

private theorem timeFirstCoordinates_symm_velocity  (j : Fin d) :
    (timeFirstCoordinates d).symm (Pi.single (Sum.inr j) (1 )) =
      ((0 : ℝ), Pi.single j 1) := by
  apply (timeFirstCoordinates d).injective
  rw [(timeFirstCoordinates d).apply_symm_apply]
  ext i
  rcases i with i | i
  · rfl
  · simp [timeFirstCoordinates_apply_velocity, Pi.single_apply]

private theorem timeFirstCoordinateMatrix_apply  (L : TimeVelocity d →L[ℝ] TimeVelocity d)
    (i j : Fin 1 ⊕ Fin d) :
    timeFirstCoordinateMatrix L i j =
      timeFirstCoordinates d (L ((timeFirstCoordinates d).symm (Pi.single j 1))) i := rfl

variable {u : HypoellipticAleksandrov.Parabolic.ScalarField d}

section
variable (hu : ContDiff ℝ 2 u) (z : TimeVelocity d)

include hu
private theorem rawVelocityJacobian_apply_eq
     (i j : Fin d) :
    rawVelocityJacobian u z i j =
      fderiv ℝ (fderiv ℝ u) z (0, Pi.single j 1) (0, Pi.single i 1) := by
  let H := fderiv ℝ (fderiv ℝ u) z
  let ei : TimeVelocity d := ((0 ), Pi.single i (1 ))

  have hcomponent :
      fderiv ℝ (fun x  ↦ fderiv ℝ u x ei) z = H.flip ei := by


    simpa [H] using (((hu.fderiv_right (m := 1) (by norm_num)).differentiable_one z).hasFDerivAt.clm_apply (hasFDerivAt_const ei z)).fderiv

  change
    (fderiv ℝ (fun x  ↦ fun k : Fin d ↦
      fderiv ℝ u x (0, Pi.single k 1)) z) (0, Pi.single j 1) i = _
  rw [fderiv_pi (by
      intro k
      exact ((hu.contDiff_fderiv_apply (m := 1) (by norm_num)).comp
        (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num) z)]
  simp only [ContinuousLinearMap.pi_apply]
  rw [show fderiv ℝ (fun x  ↦ fderiv ℝ u x (0, Pi.single i 1)) z =
      H.flip (0, Pi.single i 1) by assumption]
  rfl

private theorem rawVelocityJacobian_eq_velocityHessian
     :
    rawVelocityJacobian u z = velocityHessian u z := by
  ext i j
  calc
    rawVelocityJacobian u z i j =
        fderiv ℝ (fderiv ℝ u) z (0, Pi.single j 1) (0, Pi.single i 1) :=
      rawVelocityJacobian_apply_eq hu z i j
    _ = fderiv ℝ (fderiv ℝ u) z (0, Pi.single i 1) (0, Pi.single j 1) :=
      (hu.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq
        ((0 ), Pi.single j 1) ((0 ), Pi.single i 1)
    _ = velocityHessian u z i j := rfl
end


private theorem timeFirstCoordinateMatrix_parabolicNormalMapDerivative_raw
     (y₀ : PDE.Vec d) (z : TimeVelocity d) :
    timeFirstCoordinateMatrix (parabolicNormalMapDerivative u y₀ z) =
      normalBlock (timeDerivative u z)
        ((fderiv ℝ (velocityGradient u) z ((1 ), 0)))
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
          (Pi.single j (1 ) : PDE.Vec d) x) =
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

section
variable (hu : ContDiff ℝ 2 u) (y₀ : PDE.Vec d) (z : TimeVelocity d)

include hu
private theorem timeFirstCoordinateMatrix_parabolicNormalMapDerivative
      :
    timeFirstCoordinateMatrix (parabolicNormalMapDerivative u y₀ z) =
      normalBlock (timeDerivative u z)
        ((fderiv ℝ (velocityGradient u) z ((1 ), 0)))
        (z.2 - y₀) (velocityHessian u z) := by
  rw [timeFirstCoordinateMatrix_parabolicNormalMapDerivative_raw,
    rawVelocityJacobian_eq_velocityHessian hu]

/-! ## Absolute determinant identity -/

/-- The absolute determinant of the Fréchet derivative of the parabolic normal
map equals the time derivative times the determinant of the negative velocity
Hessian, under the pointwise sign conditions and with no contact premise. -/
theorem abs_det_fderiv_parabolicNormalMap_eq

    (ht : 0 ≤ timeDerivative u z) (hH : (-velocityHessian u z).PosSemidef) :
    |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| =
      timeDerivative u z * (-velocityHessian u z).det := by
  rw [parabolicNormalMap_fderiv hu]
  rw [← det_coordinateMatrix]
  rw [← det_timeFirstCoordinateMatrix_eq_det_coordinateMatrix]
  rw [timeFirstCoordinateMatrix_parabolicNormalMapDerivative hu]
  exact abs_det_normalBlock_eq _ _ _ _ ht hH
end


/-! ## Determinant-weighted pointwise source bound -/

/-- A positive-definite matrix paired with a positive-semidefinite matrix has
nonnegative product trace, without assuming the two matrices commute. -/
private theorem trace_mul_nonneg_of_posDef_posSemidef
     (A H : PDE.Mat d) (hA : A.PosDef) (hH : H.PosSemidef) :
    0 ≤ (A * H).trace := by
  let B : PDE.Mat d := CFC.sqrt A * H * CFC.sqrt A

  have htrace : B.trace = (A * H).trace := by
    calc
      B.trace = (H * CFC.sqrt A * CFC.sqrt A).trace := (id (Eq.symm (trace_mul_cycle H (CFC.sqrt A) (CFC.sqrt A))))
      _ = (H * (CFC.sqrt A * CFC.sqrt A)).trace := by
        rw [Matrix.mul_assoc]
      _ = (H * A).trace := by
        rw [CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
      _ = (A * H).trace := Matrix.trace_mul_comm _ _
  rw [← htrace]
  exact (show B.PosSemidef by

      simpa only [B, (show (CFC.sqrt A)ᴴ = CFC.sqrt A from (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq)] using hH.conjTranspose_mul_mul_same (CFC.sqrt A)).trace_nonneg

/-- The forward operator at a `C²` point is the time derivative plus the
trace contribution of the negative velocity Hessian. -/
private theorem parabolicOperator_eq_timeDerivative_add_trace_neg_velocityHessian
     {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (hu : ContDiff ℝ 2 u)
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
theorem abs_det_fderiv_parabolicNormalMap_le_source
     {A : CoefficientField d} {f u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hu : ContDiff ℝ 2 u) {T : ℝ} {y₀ : PDE.Vec d} {z : TimeVelocity d}
    (hz : z ∈ parabolicSignSet T y₀ u)
    (hA : (coefficientAt A z).PosDef)
    (hsub : parabolicOperator A u z ≤ f z) :
    |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| ≤
      (max (f z) 0) ^ (d + 1) /
        ((((d : ℝ) + 1) ^ (d + 1)) * (coefficientAt A z).det) := by
  let sharedTerm_e20875691b := ((timeDerivative u z + (coefficientAt A z * (-velocityHessian u z)).trace) / ((d : ℝ) + 1))
  let sharedTerm_d39af155a6 := (timeDerivative u z + (coefficientAt A z * (-velocityHessian u z)).trace)
  let sharedTerm_f9dec4decf := ((((d : ℝ) + 1) ^ (d + 1)) * (coefficientAt A z).det)
  let sharedTerm_108418f6b2 := (f z / ((d : ℝ) + 1))
  let sharedTerm_7447840c0a := (timeDerivative u z * (-velocityHessian u z).det)
  rcases hz with ⟨_, _, htime, hH⟩
  have htrace  :=
    trace_mul_nonneg_of_posDef_posSemidef _ _ hA hH
  have hoperator :
      parabolicOperator A u z =
        sharedTerm_d39af155a6 :=
    parabolicOperator_eq_timeDerivative_add_trace_neg_velocityHessian hu A z
  have hsource :
      sharedTerm_d39af155a6 ≤ f z := by
    rw [← hoperator]
    exact hsub
  have hsum_nonneg :
      0 ≤ sharedTerm_d39af155a6 :=
    add_nonneg htime htrace
  have hf  := hsum_nonneg.trans hsource
  have hdet_pos  := hA.det_pos
  have hmean := HypoellipticAleksandrov.det_mul_time_det_le_arith_mean_pow d
    _ _ _ hA hH htime

  have hden_pos : 0 < (d : ℝ) + 1 := by positivity


  calc
    |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| =
        sharedTerm_7447840c0a :=
      abs_det_fderiv_parabolicNormalMap_eq hu y₀ z htime hH
    _ ≤ (sharedTerm_e20875691b) ^
          (d + 1) / (coefficientAt A z).det := (show _ by
              rw [le_div_iff₀ hdet_pos]
              calc
                sharedTerm_7447840c0a * (coefficientAt A z).det =
                    (coefficientAt A z).det * timeDerivative u z * (-velocityHessian u z).det := by
                  ring
                _ ≤ (sharedTerm_e20875691b) ^
                    (d + 1) := hmean)
    _ ≤ (sharedTerm_108418f6b2) ^ (d + 1) / (coefficientAt A z).det :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (div_nonneg hsum_nonneg hden_pos.le) ((div_le_div_iff_of_pos_right hden_pos).mpr hsource) (d + 1)) hdet_pos.le
    _ = (f z) ^ (d + 1) /
        (sharedTerm_f9dec4decf) := by
      rw [div_pow, div_div]
    _ = (max (f z) 0) ^ (d + 1) /
        (sharedTerm_f9dec4decf) := by
      rw [max_eq_left hf]

end HypoellipticAleksandrov.Parabolic
