module

public import HypoellipticAleksandrov.Parabolic.Jacobian
public import HypoellipticAleksandrov.Parabolic.MovingLensGeometry
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import HypoellipticAleksandrov.Parabolic.ContactMap
public import HypoellipticAleksandrov.Parabolic.MovingLensSign
public import HypoellipticAleksandrov.Parabolic.AreaFormula
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic
open Matrix
open scoped BigOperators MatrixOrder



/-- A `C²` germ supplies the displayed Fréchet derivative of its parabolic
normal map at its base point. -/
theorem parabolicNormalMap_hasFDerivAt_of_contDiffAt
    {d : ℕ} {u : TimeVelocity d → ℝ} {y₀ : PDE.Vec d}
    {z : TimeVelocity d} (hu : ContDiffAt ℝ 2 u z) :
    HasFDerivAt (parabolicNormalMap u y₀)
      (parabolicNormalMapDerivative u y₀ z) z  := by
  have differentiableAt_velocityGradient_of_contDiffAt :
      DifferentiableAt ℝ (velocityGradient u) z := by
    rw [differentiableAt_pi]
    intro i
    change DifferentiableAt ℝ
      (fun x : TimeVelocity d ↦ fderiv ℝ u x (0, Pi.single i 1)) z
    exact ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  let Du := fderiv ℝ u z
  let Dg := fderiv ℝ (velocityGradient u) z
  let velocityCoordinate : Fin d → TimeVelocity d →L[ℝ] ℝ := fun i ↦
    (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ ℝ (PDE.Vec d))
  have hu' :=
    (hu.differentiableAt (by norm_num)).hasFDerivAt
  have hg' :=
    (differentiableAt_velocityGradient_of_contDiffAt).hasFDerivAt
  have hdot : HasFDerivAt
      (fun x : TimeVelocity d ↦ PDE.vecDot (velocityGradient u x) (x.2 - y₀))
      (∑ i, ((velocityGradient u z i) • velocityCoordinate i +
        (z.2 i - y₀ i) • ((ContinuousLinearMap.proj i).comp Dg))) z := by
    change HasFDerivAt
      (fun x : TimeVelocity d ↦ ∑ i, velocityGradient u x i * (x.2 i - y₀ i)) _ z
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
    (fun x => (u x - PDE.vecDot (velocityGradient u x) (x.2 - y₀),
      velocityGradient u x)) _ z
  simpa [parabolicNormalMapDerivative, Du, Dg, velocityCoordinate] using (hu'.sub hdot).prodMk hg'


/-! ## Private time-first coordinate calculation -/

private noncomputable def timeFirstCoordinates (d : ℕ) :
    TimeVelocity d ≃L[ℝ] ((Fin 1 ⊕ Fin d) → ℝ) :=
  ((ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℝ)).prodCongr
      (ContinuousLinearEquiv.refl ℝ (PDE.Vec d))).symm.trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 1) (Fin d)
      (fun _ ↦ ℝ)).symm

private def timeFirstCoordinateConjugate {d : ℕ} (L : TimeVelocity d →L[ℝ] TimeVelocity d) :
    ((Fin 1 ⊕ Fin d) → ℝ) →L[ℝ] ((Fin 1 ⊕ Fin d) → ℝ) :=
  (timeFirstCoordinates d).toContinuousLinearMap.comp
    (L.comp (timeFirstCoordinates d).symm.toContinuousLinearMap)

private def timeFirstCoordinateMatrix {d : ℕ} (L : TimeVelocity d →L[ℝ] TimeVelocity d) :
    Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  LinearMap.toMatrix' (timeFirstCoordinateConjugate L).toLinearMap



/-! ## Private determinant-one row operation -/

private def scalarBlock (a : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ ↦ a

private def rowBlock {d : ℕ} (r : PDE.Vec d) :
    Matrix (Fin 1) (Fin d) ℝ := fun _ i ↦ r i

private def colBlock {d : ℕ} (q : PDE.Vec d) :
    Matrix (Fin d) (Fin 1) ℝ := fun i _ ↦ q i

private def rawVelocityJacobian {d : ℕ} (u : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    PDE.Mat d :=
  fun i j ↦ fderiv ℝ (velocityGradient u) z (0, Pi.single j 1) i

private def rowMulMatrix {d : ℕ} (r : PDE.Vec d) (H : PDE.Mat d) :
    Matrix (Fin 1) (Fin d) ℝ :=
  fun _ j ↦ ∑ i, r i * H i j

private def normalBlock {d : ℕ} (a : ℝ) (q r : PDE.Vec d) (H : PDE.Mat d) :
    Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  Matrix.fromBlocks (scalarBlock (a - PDE.vecDot r q)) (-(rowMulMatrix r H))
    (colBlock q) H

private def normalRowOperation {d : ℕ} (r : PDE.Vec d) :
    Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  Matrix.fromBlocks 1 (rowBlock r) 0 1

private theorem normalRowOperation_mul_normalBlock {d : ℕ} (a : ℝ) (q r : PDE.Vec d)
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


private theorem det_normalBlock {d : ℕ} (a : ℝ) (q r : PDE.Vec d) (H : PDE.Mat d) :
    (normalBlock a q r H).det = a * H.det  := by
  have det_normalRowOperation {d : ℕ} (r : PDE.Vec d) :
      (normalRowOperation r).det = 1 := by
    simp [normalRowOperation]
  calc
    (normalBlock a q r H).det =
        (normalRowOperation r * normalBlock a q r H).det := by
      rw [Matrix.det_mul, det_normalRowOperation]
      ring
    _ = (Matrix.fromBlocks (scalarBlock a) 0 (colBlock q) H).det := by
      rw [normalRowOperation_mul_normalBlock]
    _ = a * H.det := by
      simp [scalarBlock, Matrix.det_fromBlocks_zero₁₂]

private theorem abs_det_normalBlock_eq {d : ℕ} (a : ℝ) (q r : PDE.Vec d) (H : PDE.Mat d)
    (ha : 0 ≤ a) (hH : (-H).PosSemidef) :
    |(normalBlock a q r H).det| = a * (-H).det := by
  have habs : |H.det| = (-H).det := by
    calc
      |H.det| = |(-H).det| := by rw [Matrix.det_neg, abs_mul]; simp
      _ = (-H).det := abs_of_nonneg (Matrix.PosSemidef.det_nonneg hH)
  rw [det_normalBlock, abs_mul, abs_of_nonneg ha, habs]

/-! ## Private coordinate bridge for the local derivative -/





private theorem timeFirstCoordinateMatrix_apply {d : ℕ} (L : TimeVelocity d →L[ℝ] TimeVelocity d)
    (i j : Fin 1 ⊕ Fin d) :
    timeFirstCoordinateMatrix L i j =
      timeFirstCoordinates d (L ((timeFirstCoordinates d).symm (Pi.single j 1))) i := by
  simp [timeFirstCoordinateMatrix, timeFirstCoordinateConjugate,
    LinearMap.toMatrix'_apply, eq_comm]

private theorem rawVelocityJacobian_apply_eq_of_contDiffAt {d : ℕ} {u : TimeVelocity d → ℝ}
    (z : TimeVelocity d) (hu : ContDiffAt ℝ 2 u z) (i j : Fin d) :
    rawVelocityJacobian u z i j =
      fderiv ℝ (fderiv ℝ u) z (0, Pi.single j 1) (0, Pi.single i 1) := by
  let H := fderiv ℝ (fderiv ℝ u) z
  let ei : TimeVelocity d := (0, Pi.single i 1)
  have hDu :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcomponent :
      fderiv ℝ (fun x : TimeVelocity d ↦ fderiv ℝ u x ei) z = H.flip ei := by
    have hconst : HasFDerivAt
        (fun _ : TimeVelocity d ↦ ei)
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
      fderiv ℝ u x (0, Pi.single k 1)) z) (0, Pi.single j 1) i = _
  rw [fderiv_pi hcomponents]
  simp
  rw [show fderiv ℝ (fun x : TimeVelocity d ↦ fderiv ℝ u x (0, Pi.single i 1)) z =
      H.flip (0, Pi.single i 1) by simpa [ei] using hcomponent]
  rfl


private theorem timeFirstCoordinateMatrix_parabolicNormalMapDerivative_raw {d : ℕ}
    {u : TimeVelocity d → ℝ} (y₀ : PDE.Vec d) (z : TimeVelocity d) :
    timeFirstCoordinateMatrix (parabolicNormalMapDerivative u y₀ z) =
      normalBlock (timeDerivative u z)
        (fun i ↦ fderiv ℝ (velocityGradient u) z ((1 : ℝ), 0) i)
        (z.2 - y₀) (rawVelocityJacobian u z)     := by
  have timeFirstCoordinates_apply_velocity {d : ℕ} (x : TimeVelocity d) (i : Fin d) :
      timeFirstCoordinates d x (Sum.inr i) = x.2 i := by
    change x.2 i = x.2 i
    rfl
  have timeFirstCoordinates_apply_time {d : ℕ} (x : TimeVelocity d) :
      timeFirstCoordinates d x (Sum.inl 0) = x.1 := by
    change (fun _ : Fin 1 ↦ x.1) 0 = x.1
    rfl
  have timeFirstCoordinates_symm_velocity {d : ℕ} (j : Fin d) :
      (timeFirstCoordinates d).symm (Pi.single (Sum.inr j) 1) =
      (0, Pi.single j 1) := by
    apply (timeFirstCoordinates d).injective
    rw [(timeFirstCoordinates d).apply_symm_apply]
    ext i
    rcases i with i | i
    · fin_cases i
      simp [timeFirstCoordinates_apply_time]
    · simp [timeFirstCoordinates_apply_velocity, Pi.single_apply]
  have timeFirstCoordinates_symm_time :
      (timeFirstCoordinates d).symm (Pi.single (Sum.inl 0) 1) = (1, 0) := by
    apply (timeFirstCoordinates d).injective
    rw [(timeFirstCoordinates d).apply_symm_apply]
    ext i
    rcases i with i | i
    · fin_cases i
      simp [timeFirstCoordinates_apply_time]
    · simp [timeFirstCoordinates_apply_velocity]
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



/-! ## Determinant-weighted pointwise source bound -/

private theorem trace_mul_nonneg_of_posDef_posSemidef
    {d : ℕ} (A H : PDE.Mat d) (hA : A.PosDef) (hH : H.PosSemidef) :
    0 ≤ (A * H).trace := by
  let B := CFC.sqrt A * H * CFC.sqrt A
  have hB : B.PosSemidef := by
    have hsqrt : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
      (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq
    simpa only [B, hsqrt] using hH.conjTranspose_mul_mul_same (CFC.sqrt A)
  have htrace : B.trace = (A * H).trace := by
    calc
      B.trace = (H * CFC.sqrt A * CFC.sqrt A).trace := by
        dsimp only [B]
        exact (Matrix.trace_mul_cycle H (CFC.sqrt A) (CFC.sqrt A)).symm
      _ = (H * (CFC.sqrt A * CFC.sqrt A)).trace := by
        rw [Matrix.mul_assoc]
      _ = (H * A).trace := by
        rw [CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
      _ = (A * H).trace := Matrix.trace_mul_comm _ _
  rw [← htrace]
  exact hB.trace_nonneg



/-- At a locally `C²` point, the parabolic normal-map Jacobian is bounded by
the positive source part with the exact determinant weight. -/
theorem abs_det_fderiv_parabolicNormalMap_le_source_of_signs
    {d : ℕ} {A : CoefficientField d} {F u : TimeVelocity d → ℝ}
    {y₀ : PDE.Vec d} {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 u z)
    (ht : 0 ≤ timeDerivative u z)
    (hH : (-velocityHessian u z).PosSemidef)
    (hA : (coefficientAt A z).PosDef)
    (hsub : parabolicOperator A u z ≤ F z) :
    |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| ≤
      (max (F z) 0) ^ (d + 1) /
        ((((d : ℝ) + 1) ^ (d + 1)) * (coefficientAt A z).det)   := by
  have parabolicOperator_eq_timeDerivative_add_trace_neg_velocityHessian_of_contDiffAt :
      parabolicOperator A u z =
      timeDerivative u z +
        (coefficientAt A z * (-velocityHessian u z)).trace := by
    have velocityHessian_isSymm_of_contDiffAt :
        (velocityHessian u z).IsSymm := by
      refine Matrix.IsSymm.ext ?_
      intro i j
      simpa [velocityHessian] using
        (hu.isSymmSndFDerivAt (by norm_num)).eq
          (0, Pi.single j 1) (0, Pi.single i 1)
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
        rw [matrixContraction_eq_trace_mul_of_isSymm _ _ ((velocityHessian_isSymm_of_contDiffAt).neg)]
  have abs_det_fderiv_parabolicNormalMap_eq_of_contDiffAt {y₀ : PDE.Vec d} :
      |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| =
      timeDerivative u z * (-velocityHessian u z).det := by
    have timeFirstCoordinateMatrix_parabolicNormalMapDerivative_of_contDiffAt (y₀ : PDE.Vec d) :
        timeFirstCoordinateMatrix (parabolicNormalMapDerivative u y₀ z) =
        normalBlock (timeDerivative u z)
          (fun i ↦ fderiv ℝ (velocityGradient u) z (1, 0) i)
          (z.2 - y₀) (velocityHessian u z) := by
      have rawVelocityJacobian_eq_velocityHessian_of_contDiffAt :
          rawVelocityJacobian u z = velocityHessian u z := by
        ext i j
        calc
          rawVelocityJacobian u z i j =
              fderiv ℝ (fderiv ℝ u) z (0, Pi.single j 1) (0, Pi.single i 1) :=
            rawVelocityJacobian_apply_eq_of_contDiffAt z hu i j
          _ = fderiv ℝ (fderiv ℝ u) z (0, Pi.single i 1) (0, Pi.single j 1) :=
            (hu.isSymmSndFDerivAt (by norm_num)).eq
              (0, Pi.single j 1) (0, Pi.single i 1)
          _ = velocityHessian u z i j := rfl
      rw [timeFirstCoordinateMatrix_parabolicNormalMapDerivative_raw,
        rawVelocityJacobian_eq_velocityHessian_of_contDiffAt]
    have det_timeFirstCoordinateMatrix_eq_det_coordinateMatrix {d : ℕ} (L : TimeVelocity d →L[ℝ] TimeVelocity d) :
        (timeFirstCoordinateMatrix L).det = (coordinateMatrix L).det := by
      have det_timeFirstCoordinateMatrix {d : ℕ} (L : TimeVelocity d →L[ℝ] TimeVelocity d) :
          (timeFirstCoordinateMatrix L).det = L.det := by
        calc
          (timeFirstCoordinateMatrix L).det = (timeFirstCoordinateConjugate L).det := by
            simp [timeFirstCoordinateMatrix]
          _ = L.det :=
            LinearMap.det_conj L.toLinearMap (timeFirstCoordinates d).toLinearEquiv
      rw [det_timeFirstCoordinateMatrix, det_coordinateMatrix]
    rw [(parabolicNormalMap_hasFDerivAt_of_contDiffAt hu).fderiv]
    rw [← det_coordinateMatrix]
    rw [← det_timeFirstCoordinateMatrix_eq_det_coordinateMatrix]
    rw [timeFirstCoordinateMatrix_parabolicNormalMapDerivative_of_contDiffAt]
    exact abs_det_normalBlock_eq _ _ _ _ ht hH
  have hsource :
      timeDerivative u z +
          (coefficientAt A z * (-velocityHessian u z)).trace ≤ F z := by
    rw [← parabolicOperator_eq_timeDerivative_add_trace_neg_velocityHessian_of_contDiffAt]
    exact hsub
  have hsum_nonneg :=
    add_nonneg ht (trace_mul_nonneg_of_posDef_posSemidef _ _ hA hH)
  have hdet_pos := hA.det_pos
  have hmatrix_div :
      timeDerivative u z * (-velocityHessian u z).det ≤
        ((timeDerivative u z +
            (coefficientAt A z * (-velocityHessian u z)).trace) / ((d : ℝ) + 1)) ^
            (d + 1) / (coefficientAt A z).det := by
    rw [le_div_iff₀ hdet_pos]
    calc
      timeDerivative u z * (-velocityHessian u z).det * (coefficientAt A z).det =
          (coefficientAt A z).det * timeDerivative u z * (-velocityHessian u z).det := by
        ring
      _ ≤ ((timeDerivative u z +
          (coefficientAt A z * (-velocityHessian u z)).trace) / ((d : ℝ) + 1)) ^
          (d + 1) := (HypoellipticAleksandrov.det_mul_time_det_le_arith_mean_pow d (coefficientAt A z) (-velocityHessian u z) (timeDerivative u z) hA hH ht)
  have hden_pos : 0 < (d : ℝ) + 1 := by positivity
  have hpow :=
    pow_le_pow_left₀ (div_nonneg hsum_nonneg hden_pos.le) ((div_le_div_iff_of_pos_right hden_pos).mpr hsource) (d + 1)
  calc
    |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| =
        timeDerivative u z * (-velocityHessian u z).det :=
      abs_det_fderiv_parabolicNormalMap_eq_of_contDiffAt
    _ ≤ ((timeDerivative u z +
          (coefficientAt A z * (-velocityHessian u z)).trace) / ((d : ℝ) + 1)) ^
          (d + 1) / (coefficientAt A z).det := hmatrix_div
    _ ≤ (F z / ((d : ℝ) + 1)) ^ (d + 1) / (coefficientAt A z).det :=
      div_le_div_of_nonneg_right hpow hdet_pos.le
    _ = (F z) ^ (d + 1) /
        ((((d : ℝ) + 1) ^ (d + 1)) * (coefficientAt A z).det) := by
      rw [div_pow, div_div]
    _ = (max (F z) 0) ^ (d + 1) /
        ((((d : ℝ) + 1) ^ (d + 1)) * (coefficientAt A z).det) := by
      rw [max_eq_left (hsum_nonneg.trans hsource)]



/-- The time-preserving chart which normalizes moving-lens velocity displacement. -/
def movingLensChart {d : Nat} (xi eps : Real) (y : PDE.Vec d) :
    TimeVelocity d → TimeVelocity d :=
  fun z => (z.1,
    (Real.sqrt (movingLensDenominator xi eps z.1))⁻¹ •
      movingLensDisplacement y z)

/-- The inverse time-preserving chart from the normalized velocity coordinate. -/
def movingLensChartInv {d : Nat} (xi eps : Real) (y : PDE.Vec d) :
    TimeVelocity d → TimeVelocity d :=
  fun z => (z.1,
    z.1 • y + Real.sqrt (movingLensDenominator xi eps z.1) • z.2)

private theorem movingLensDisplacement_chartInv {d : Nat} (xi eps : Real)
    (y : PDE.Vec d) (z : TimeVelocity d) :
    movingLensDisplacement y (movingLensChartInv xi eps y z) =
      Real.sqrt (movingLensDenominator xi eps z.1) • z.2 := by
  ext i
  simp only [movingLensDisplacement, movingLensChartInv,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring



/-- Applying the inverse chart after the moving-lens chart recovers a nonnegative-time
point. -/
@[simp] theorem movingLensChartInv_apply_movingLensChart
    {d : Nat} {xi eps : Real} {y : PDE.Vec d} {z : TimeVelocity d}
    (hxi : 0 ≤ xi) (heps : 0 < eps) (hz : 0 ≤ z.1) :
    movingLensChartInv xi eps y (movingLensChart xi eps y z) = z := by
  have hsqrt :=
    Real.sqrt_pos.2 (movingLensDenominator_pos hxi heps hz)
  apply Prod.ext
  · rfl
  · ext i
    change (z.1 • y + Real.sqrt (movingLensDenominator xi eps z.1) •
        ((Real.sqrt (movingLensDenominator xi eps z.1))⁻¹ •
          (z.2 - z.1 • y))) i = z.2 i
    rw [smul_smul, mul_inv_cancel₀ hsqrt.ne', one_smul]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Applying the moving-lens chart after its inverse recovers a nonnegative-time
normalized point. -/
@[simp] theorem movingLensChart_apply_movingLensChartInv
    {d : Nat} {xi eps : Real} {y : PDE.Vec d} {z : TimeVelocity d}
    (hxi : 0 ≤ xi) (heps : 0 < eps) (hz : 0 ≤ z.1) :
    movingLensChart xi eps y (movingLensChartInv xi eps y z) = z := by
  have hsqrt :=
    Real.sqrt_pos.2 (movingLensDenominator_pos hxi heps hz)
  apply Prod.ext
  · rfl
  · ext i
    change ((Real.sqrt (movingLensDenominator xi eps z.1))⁻¹ •
        movingLensDisplacement y (movingLensChartInv xi eps y z)) i = z.2 i
    rw [movingLensDisplacement_chartInv, smul_smul, inv_mul_cancel₀ hsqrt.ne', one_smul]

/-- The chart maps the closed moving lens exactly onto the closed unit cylinder. -/
theorem movingLensChart_image_closed
    {d : Nat} {xi eps tau : Real} {y : PDE.Vec d}
    (hxi : 0 ≤ xi) (heps : 0 < eps) :
    movingLensChart xi eps y '' movingLensClosed xi eps tau y =
      closedParabolicCylinder tau (0 : PDE.Vec d)   := by
  have movingLensChartInv_displacement_sq {z : TimeVelocity d} (hz : 0 ≤ z.1) :
      PDE.vecNormSq (movingLensDisplacement y (movingLensChartInv xi eps y z)) =
      movingLensDenominator xi eps z.1 * PDE.vecNormSq z.2 := by
    have hden :=
      movingLensDenominator_pos hxi heps hz
    rw [movingLensDisplacement_chartInv, PDE.vecNormSq_smul, Real.sq_sqrt hden.le]
  have movingLensChart_velocity_sq {z : TimeVelocity d} (hz : 0 ≤ z.1) :
      PDE.vecNormSq (movingLensChart xi eps y z).2 =
      PDE.vecNormSq (movingLensDisplacement y z) /
        movingLensDenominator xi eps z.1 := by
    have hden :=
      movingLensDenominator_pos hxi heps hz
    change PDE.vecNormSq
        ((Real.sqrt (movingLensDenominator xi eps z.1))⁻¹ •
          movingLensDisplacement y z) =
      PDE.vecNormSq (movingLensDisplacement y z) /
        movingLensDenominator xi eps z.1
    rw [PDE.vecNormSq_smul, inv_pow, Real.sq_sqrt hden.le, div_eq_mul_inv]
    ring
  apply Set.Subset.antisymm
  · rintro q ⟨z, hz, rfl⟩
    rw [mem_closedParabolicCylinder_iff]
    refine ⟨hz.1, hz.2.1, ?_⟩
    have hden :=
      movingLensDenominator_pos hxi heps hz.1
    have hvelocity : PDE.vecNormSq (movingLensChart xi eps y z).2 ≤ 1 := by
      rw [movingLensChart_velocity_sq hz.1]
      exact (div_le_one₀ hden).mpr (by simpa using hz.2.2)
    simpa [PDE.euclideanClosedBall, PDE.euclideanSqDist] using hvelocity
  · intro q hq
    rw [mem_closedParabolicCylinder_iff] at hq
    refine ⟨movingLensChartInv xi eps y q, ?_, ?_⟩
    · refine ⟨hq.1, hq.2.1, ?_⟩
      have hvelocity : PDE.vecNormSq q.2 ≤ 1 := by
        simpa [PDE.euclideanClosedBall, PDE.euclideanSqDist] using hq.2.2
      change PDE.vecNormSq (movingLensDisplacement y (movingLensChartInv xi eps y q)) ≤
        movingLensDenominator xi eps q.1
      rw [movingLensChartInv_displacement_sq hq.1]
      simpa using mul_le_mul_of_nonneg_left hvelocity (movingLensDenominator_pos hxi heps hq.1).le
    · exact movingLensChart_apply_movingLensChartInv hxi heps hq.1



end HypoellipticAleksandrov.Parabolic

section



/-!
# Physical moving-lens first contact

This file records the direct, physical-coordinate first-contact coverage used
by the supplied-source moving-lens ABP argument.  The moving-lens chart is
used only to produce continuous paths inside the lens; no PDE quantity is
pulled back through it.
-/


namespace HypoellipticAleksandrov.Parabolic

noncomputable section

open Filter Set
open scoped Topology

/-- Concrete physical contact/area API for supplied-source lower-bound proof: sign set. -/
def movingLensSourceSignSet {d : ℕ} (xi eps tau : ℝ) (y : PDE.Vec d)
    (u : TimeVelocity d → ℝ) : Set (TimeVelocity d) :=
  {z | 0 < z.1 ∧ z.1 < tau ∧
    PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1 ∧
    0 < u z ∧ 0 ≤ timeDerivative u z ∧ (-velocityHessian u z).PosSemidef}

/-- Concrete physical contact/area API for supplied-source lower-bound proof: velocity footprint. -/
def movingLensVelocityFootprint (d : ℕ) (kappa : ℝ) : ℝ :=
  kappa + Real.sqrt d * kappa ^ (-3 : ℤ)

/-- Concrete physical contact/area API for supplied-source lower-bound proof: its wedge. -/
def movingLensSlopeInterceptWedge (d : ℕ) (R M : ℝ) : Set (TimeVelocity d) :=
  Set.Ioo (M / 2) (3 * M / 4) ×ˢ
    PDE.euclideanBall (0 : PDE.Vec d) (M / (4 * R))

private theorem movingLensSignXi_nonneg {kappa : ℝ} (hkappa : 0 < kappa) :
    0 ≤ movingLensSignXi kappa := by
  unfold movingLensSignXi
  positivity

private theorem movingLensDenominator_lt_kappa_sq
    {kappa eps tau t : ℝ} (hkappa : 0 < kappa)
    (heps_small : 2 * eps ^ 2 < kappa ^ 2) (ht : t ≤ tau)
    (htau_kappa : tau ≤ kappa⁻¹) :
    movingLensDenominator (movingLensSignXi kappa) eps t < kappa ^ 2 := by
  have hslope : movingLensSignXi kappa * t ≤ kappa ^ 2 / 2 := by
    calc
      movingLensSignXi kappa * t ≤ movingLensSignXi kappa * kappa⁻¹ :=
        mul_le_mul_of_nonneg_left (ht.trans htau_kappa) (movingLensSignXi_nonneg hkappa)
      _ = kappa ^ 2 / 2 := by
        unfold movingLensSignXi
        field_simp [hkappa.ne']
  unfold movingLensDenominator
  nlinarith

private theorem vecEuclideanNorm_le_of_sq_le
    {d : ℕ} {v : PDE.Vec d} {R : ℝ}
    (hR : 0 ≤ R) (h : PDE.vecNormSq v ≤ R ^ 2) :
    PDE.vecEuclideanNorm v ≤ R := by
  have hsq : PDE.vecEuclideanNorm v ^ 2 ≤ R ^ 2 := by
    simpa only [PDE.vecEuclideanNorm_sq] using h
  nlinarith

private theorem movingLensClosed_velocity_norm_lt_footprint
    {d : ℕ} {kappa tau eps : ℝ} {y : PDE.Vec d}
    (hkappa : 0 < kappa) (htau_kappa : tau ≤ kappa⁻¹)
    (heps_small : 2 * eps ^ 2 < kappa ^ 2)
    (hy : PDE.vecNormSq y ≤ (d : ℝ) * kappa ^ (-4 : ℤ))
    {z : TimeVelocity d}
    (hz : z ∈ movingLensClosed (movingLensSignXi kappa) eps tau y) :
    PDE.vecEuclideanNorm z.2 < movingLensVelocityFootprint d kappa := by
  rcases hz with ⟨hz0, hztau, hzspatial⟩
  have hdisp_sq :=
    hzspatial.trans_lt (movingLensDenominator_lt_kappa_sq hkappa heps_small hztau htau_kappa)
  have hdisp : PDE.vecEuclideanNorm (movingLensDisplacement y z) < kappa := by
    have hsq : PDE.vecEuclideanNorm (movingLensDisplacement y z) ^ 2 < kappa ^ 2 := by
      simpa only [PDE.vecEuclideanNorm_sq] using hdisp_sq
    nlinarith
  have hdnonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hrootnonneg : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hinv2nonneg : 0 ≤ kappa ^ (-2 : ℤ) := by positivity
  have hybound : PDE.vecEuclideanNorm y ≤ Real.sqrt d * kappa ^ (-2 : ℤ) := by
    apply vecEuclideanNorm_le_of_sq_le
    · positivity
    · have hsquare : (Real.sqrt d * kappa ^ (-2 : ℤ)) ^ 2 =
          (d : ℝ) * kappa ^ (-4 : ℤ) := by
        rw [mul_pow, Real.sq_sqrt hdnonneg]
        have hpow : (kappa ^ (-2 : ℤ)) ^ 2 = kappa ^ (-4 : ℤ) := by
          calc
            (kappa ^ (-2 : ℤ)) ^ 2 = kappa ^ ((-2 : ℤ) * 2) :=
              (zpow_mul kappa (-2) 2).symm
            _ = kappa ^ (-4 : ℤ) := by norm_num
        rw [hpow]
      rw [hsquare]
      exact hy
  have htime_norm : PDE.vecEuclideanNorm (z.1 • y) ≤
      Real.sqrt d * kappa ^ (-3 : ℤ) := by
    rw [PDE.vecEuclideanNorm_smul, abs_of_nonneg hz0]
    calc
      z.1 * PDE.vecEuclideanNorm y ≤ z.1 * (Real.sqrt d * kappa ^ (-2 : ℤ)) := (mul_le_mul_of_nonneg_left hybound hz0)
      _ ≤ kappa⁻¹ * (Real.sqrt d * kappa ^ (-2 : ℤ)) :=
        mul_le_mul_of_nonneg_right (hztau.trans htau_kappa) (by positivity)
      _ = Real.sqrt d * kappa ^ (-3 : ℤ) := by
        field_simp [hkappa.ne']
  have hsplit : z.2 = movingLensDisplacement y z + z.1 • y := by
    rw [movingLensDisplacement]
    exact (sub_add_cancel _ _).symm
  rw [hsplit]
  calc
    PDE.vecEuclideanNorm (movingLensDisplacement y z + z.1 • y) ≤
        PDE.vecEuclideanNorm (movingLensDisplacement y z) +
          PDE.vecEuclideanNorm (z.1 • y) :=
      PDE.vecEuclideanNorm_add_le _ _
    _ < kappa + Real.sqrt d * kappa ^ (-3 : ℤ) :=
      add_lt_add_of_lt_of_le hdisp htime_norm

private theorem affineVelocity_pos_on_movingLens
    {d : ℕ} {kappa tau eps M h : ℝ} {y p : PDE.Vec d}
    (hkappa : 0 < kappa) (htau_kappa : tau ≤ kappa⁻¹)
    (heps_small : 2 * eps ^ 2 < kappa ^ 2)
    (hy : PDE.vecNormSq y ≤ (d : ℝ) * kappa ^ (-4 : ℤ))
    (hM : 0 < M) (hh : M / 2 < h)
    (hp : p ∈ PDE.euclideanBall (0 : PDE.Vec d)
      (M / (4 * movingLensVelocityFootprint d kappa)))
    {z : TimeVelocity d}
    (hz : z ∈ movingLensClosed (movingLensSignXi kappa) eps tau y) :
    0 < affineVelocity 0 h p z.2 := by
  have hR : 0 < movingLensVelocityFootprint d kappa := by
    unfold movingLensVelocityFootprint
    positivity
  have hpNorm : PDE.vecEuclideanNorm p <
      M / (4 * movingLensVelocityFootprint d kappa) := by
    simpa using (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (x₀ := 0) (x := p)
      (R := M / (4 * movingLensVelocityFootprint d kappa)) (by positivity)).mp hp
  have hprod : PDE.vecEuclideanNorm p * PDE.vecEuclideanNorm z.2 < M / 4 := by
    calc
      PDE.vecEuclideanNorm p * PDE.vecEuclideanNorm z.2 ≤
          PDE.vecEuclideanNorm p * movingLensVelocityFootprint d kappa :=
        mul_le_mul_of_nonneg_left (movingLensClosed_velocity_norm_lt_footprint hkappa htau_kappa heps_small hy hz).le (PDE.vecEuclideanNorm_nonneg p)
      _ < (M / (4 * movingLensVelocityFootprint d kappa)) *
          movingLensVelocityFootprint d kappa :=
        mul_lt_mul_of_pos_right hpNorm hR
      _ = M / 4 := by field_simp [hR.ne']
  have hdot : -(M / 4) < PDE.vecDot p z.2 := by
    nlinarith [neg_abs_le (PDE.vecDot p z.2),
      (PDE.abs_vecDot_le_vecEuclideanNorm_mul p z.2).trans_lt hprod]
  rw [affineVelocity_apply]
  simp
  linarith

private theorem affineVelocity_lt_on_movingLens
    {d : ℕ} {kappa tau eps M h : ℝ} {y p : PDE.Vec d}
    (hkappa : 0 < kappa) (htau_kappa : tau ≤ kappa⁻¹)
    (heps_small : 2 * eps ^ 2 < kappa ^ 2)
    (hy : PDE.vecNormSq y ≤ (d : ℝ) * kappa ^ (-4 : ℤ))
    (hM : 0 < M) (hh : h < 3 * M / 4)
    (hp : p ∈ PDE.euclideanBall (0 : PDE.Vec d)
      (M / (4 * movingLensVelocityFootprint d kappa)))
    {z : TimeVelocity d}
    (hz : z ∈ movingLensClosed (movingLensSignXi kappa) eps tau y) :
    affineVelocity 0 h p z.2 < M := by
  have hR : 0 < movingLensVelocityFootprint d kappa := by
    unfold movingLensVelocityFootprint
    positivity
  have hpNorm : PDE.vecEuclideanNorm p <
      M / (4 * movingLensVelocityFootprint d kappa) := by
    simpa using (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (x₀ := 0) (x := p)
      (R := M / (4 * movingLensVelocityFootprint d kappa)) (by positivity)).mp hp
  have hprod : PDE.vecEuclideanNorm p * PDE.vecEuclideanNorm z.2 < M / 4 := by
    calc
      PDE.vecEuclideanNorm p * PDE.vecEuclideanNorm z.2 ≤
          PDE.vecEuclideanNorm p * movingLensVelocityFootprint d kappa :=
        mul_le_mul_of_nonneg_left (movingLensClosed_velocity_norm_lt_footprint hkappa htau_kappa heps_small hy hz).le (PDE.vecEuclideanNorm_nonneg p)
      _ < (M / (4 * movingLensVelocityFootprint d kappa)) *
          movingLensVelocityFootprint d kappa :=
        mul_lt_mul_of_pos_right hpNorm hR
      _ = M / 4 := by field_simp [hR.ne']
  have hdot : PDE.vecDot p z.2 < M / 4 :=
    lt_of_le_of_lt (le_abs_self _) ((PDE.abs_vecDot_le_vecEuclideanNorm_mul p z.2).trans_lt hprod)
  rw [affineVelocity_apply]
  simp
  linarith

private theorem movingLensChartInv_mem_closed
    {d : ℕ} {xi eps tau : ℝ} {y : PDE.Vec d}
    (hxi : 0 ≤ xi) (heps : 0 < eps) {q : TimeVelocity d}
    (hq : q ∈ closedParabolicCylinder tau (0 : PDE.Vec d)) :
    movingLensChartInv xi eps y q ∈ movingLensClosed xi eps tau y := by
  have hqImage : q ∈ movingLensChart xi eps y '' movingLensClosed xi eps tau y := by
    rw [movingLensChart_image_closed hxi heps]
    exact hq
  rcases hqImage with ⟨z, hz, hzq⟩
  have hEq : movingLensChartInv xi eps y q = z := by
    rw [← hzq]
    exact movingLensChartInv_apply_movingLensChart hxi heps hz.1
  rwa [hEq]

private theorem affineVelocity_line_deriv_at_zero
    {d : ℕ} (h : ℝ) (p v : PDE.Vec d) (i : Fin d) :
    HasDerivAt
      (fun r : ℝ => affineVelocity 0 h p
        (v + r • ((Pi.single i (1 : ℝ)) : PDE.Vec d)))
      (p i) 0 := by
  let e : PDE.Vec d := Pi.single i 1
  change HasDerivAt (fun r => affineVelocity 0 h p (v + r • e)) (p i) 0
  have hfun :
      (fun r => affineVelocity 0 h p (v + r • e)) =
        fun r => affineVelocity 0 h p v + r * p i := by
    classical
    funext r
    have hsingle : (∑ x : Fin d, p x * r * e x) = r * p i := by
      dsimp [e]
      rw [Fintype.sum_eq_single i]
      · simp
        ring
      · intro x hxi
        simp [hxi]
    unfold affineVelocity PDE.vecDot
    simp
    have hsplit :
        h + (∑ x, p x * (v x + r * e x)) =
          h + (∑ x, p x * v x) + (∑ x, p x * r * e x) := by
      calc
        h + (∑ x, p x * (v x + r * e x)) =
            h + (∑ x, (p x * v x + p x * r * e x)) := by
              congr 1
              apply Finset.sum_congr rfl
              intro x hx
              ring
        _ = h + (∑ x, p x * v x) + (∑ x, p x * r * e x) := by
              rw [Finset.sum_add_distrib]
              ring
    rw [hsplit, hsingle]
  rw [hfun]
  simpa using
    ((hasDerivAt_id' (𝕜 := ℝ) 0).mul_const (p i)).const_add
      (affineVelocity 0 h p v)

private theorem movingLensChart_path_mem_closed
    {d : ℕ} {xi eps tau : ℝ} {y : PDE.Vec d} {z : TimeVelocity d}
    (hxi : 0 ≤ xi) (heps : 0 < eps)
    (hz : z ∈ movingLensClosed xi eps tau y) {s : ℝ}
    (hs : s ∈ Set.Icc 0 z.1) :
    movingLensChartInv xi eps y (s, (movingLensChart xi eps y z).2) ∈
      movingLensClosed xi eps tau y := by
  have hzTrunc : z ∈ movingLensClosed xi eps z.1 y := ⟨hz.1, le_rfl, hz.2.2⟩
  have hzChart : movingLensChart xi eps y z ∈
      closedParabolicCylinder z.1 0 := by
    rw [← movingLensChart_image_closed hxi heps]
    exact ⟨z, hzTrunc, rfl⟩
  rw [mem_closedParabolicCylinder_iff] at hzChart
  have hpathTrunc : movingLensChartInv xi eps y
      (s, (movingLensChart xi eps y z).2) ∈ movingLensClosed xi eps z.1 y := by
    apply movingLensChartInv_mem_closed hxi heps
    rw [mem_closedParabolicCylinder_iff]
    exact ⟨hs.1, hs.2, hzChart.2.2⟩
  exact ⟨hpathTrunc.1, hpathTrunc.2.1.trans hz.2.1, hpathTrunc.2.2⟩

private theorem movingLensChart_path_initial_mem_causalBoundary
    {d : ℕ} {xi eps tau : ℝ} {y : PDE.Vec d} {z : TimeVelocity d}
    (hxi : 0 ≤ xi) (heps : 0 < eps)
    (hz : z ∈ movingLensClosed xi eps tau y) :
    movingLensChartInv xi eps y (0, (movingLensChart xi eps y z).2) ∈
      movingLensClosed xi eps tau y \ movingLensActive xi eps tau y := by
  refine ⟨movingLensChart_path_mem_closed hxi heps hz ⟨le_rfl, hz.1⟩, ?_⟩
  intro hactive
  exact (ne_of_gt hactive.1) (by simp [movingLensChartInv])

end

end HypoellipticAleksandrov.Parabolic
namespace HypoellipticAleksandrov.Parabolic

noncomputable section

open Filter Set
open scoped Topology

private theorem zero_between_of_continuousOn_of_neg_pos_local
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ c ∈ Set.Ioo a b, f c = 0 := by
  have hzero : 0 ∈ Set.Icc (f a) (f b) := ⟨hfa.le, hfb.le⟩
  rcases intermediate_value_Icc hab.le hf hzero with ⟨c, hc, hfc⟩
  refine ⟨c, ?_, hfc⟩
  constructor
  · by_contra hca
    have : c = a := le_antisymm (not_lt.mp hca) hc.1
    rw [this] at hfc
    linarith
  · by_contra hcb
    have : c = b := le_antisymm hc.2 (not_lt.mp hcb)
    rw [this] at hfc
    linarith



/-- Concrete physical contact/area API for supplied-source lower-bound proof: local coverage. -/
theorem movingLensSlopeInterceptWedge_subset_image_signSet_local
    (d : ℕ) (hd : 0 < d) (kappa tau eps : ℝ) (y : PDE.Vec d)
    (hkappa : 0 < kappa) (hkappa_one : kappa ≤ 1)
    (htau : 0 < tau) (htau_kappa : tau ≤ kappa⁻¹)
    (heps : 0 < eps) (heps_small : 2 * eps ^ 2 < kappa ^ 2)
    (hy : PDE.vecNormSq y ≤ (d : ℝ) * kappa ^ (-4 : ℤ))
    (u : TimeVelocity d → ℝ)
    (hucont : ContinuousOn u
      (movingLensClosed (movingLensSignXi kappa) eps tau y))
    (hulocal : ∀ z ∈ movingLensActive (movingLensSignXi kappa) eps tau y,
      ContDiffAt ℝ 2 u z)
    (hboundary : ∀ z ∈ movingLensClosed (movingLensSignXi kappa) eps tau y \
      movingLensActive (movingLensSignXi kappa) eps tau y, u z ≤ 0)
    (M : ℝ) (hM : 0 < M) (hMvalue : M = u (tau, tau • y)) :
    movingLensSlopeInterceptWedge d (movingLensVelocityFootprint d kappa) M ⊆
      parabolicNormalMap u 0 ''
        movingLensSourceSignSet (movingLensSignXi kappa) eps tau y u   := by
  have velocity_slice_hasDerivAt_of_contDiffAt_local {d : ℕ} {u : TimeVelocity d → ℝ} {z : TimeVelocity d} (hu : ContDiffAt ℝ 2 u z) (i : Fin d) :
      HasDerivAt
      (fun r : ℝ => u (z.1,
        z.2 + r • ((Pi.single i 1) : PDE.Vec d)))
      (velocityGradient u z i) 0 := by
    let e : PDE.Vec d := Pi.single i 1
    have hvline : HasDerivAt (fun r : ℝ => z.2 + r • e) e 0 := by
      simpa using
        ((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const e).const_add z.2
    have hline : HasDerivAt (fun r : ℝ => (z.1, z.2 + r • e))
        ((0, e) : TimeVelocity d) 0 :=
      (hasDerivAt_const (x := 0) (c := z.1)).prodMk hvline
    have huAt : HasFDerivAt u (fderiv ℝ u z)
        (z.1, z.2 + (0 : ℝ) • e) := by
      simpa using
        (hu.differentiableAt (by norm_num)).hasFDerivAt
    have hcomp := huAt.comp_hasDerivAt 0 hline
    simpa only [e, velocityGradient, Function.comp_def] using hcomp
  have time_slice_hasDerivAt_of_contDiffAt_local {u : TimeVelocity d → ℝ} {z : TimeVelocity d} (hu : ContDiffAt ℝ 2 u z) :
      HasDerivAt (fun t : ℝ => u (t, z.2)) (timeDerivative u z) z.1 := by
    have hline : HasDerivAt (fun t : ℝ => (t, z.2))
        ((1, 0) : TimeVelocity d) z.1 := by
      exact HasDerivAt.prodMk (hasDerivAt_id' (𝕜 := ℝ) z.1)
        (hasDerivAt_const (x := z.1) (c := z.2))
    simpa only [timeDerivative, Function.comp_def] using
      hu.differentiableAt (by norm_num) |>.hasFDerivAt.comp_hasDerivAt z.1 hline
  rintro ⟨h, p⟩ hpWedge
  rcases hpWedge with ⟨⟨hhLower, hhUpper⟩, hp⟩
  let xi : ℝ := movingLensSignXi kappa
  let ell : PDE.Vec d → ℝ := affineVelocity 0 h p
  let g : TimeVelocity d → ℝ := fun z => u z - ell z.2
  have hxi : 0 ≤ xi := by
    dsimp only [xi]
    exact movingLensSignXi_nonneg hkappa
  have hclosedCenter : (tau, tau • y) ∈ movingLensClosed xi eps tau y := by
    refine ⟨htau.le, le_rfl, ?_⟩
    rw [movingLensDisplacement, sub_self]
    simp [PDE.vecNormSq, PDE.vecDot]
    exact (movingLensDenominator_pos hxi heps htau.le).le
  have hellPos : ∀ z ∈ movingLensClosed xi eps tau y, 0 < ell z.2 := by
    intro z hz
    exact affineVelocity_pos_on_movingLens hkappa htau_kappa heps_small hy hM hhLower hp hz
  have hellLt : ∀ z ∈ movingLensClosed xi eps tau y, ell z.2 < M := by
    intro z hz
    exact affineVelocity_lt_on_movingLens hkappa htau_kappa heps_small hy hM hhUpper hp hz
  have hgCenter : 0 < g (tau, tau • y) := by
    change 0 < u (tau, tau • y) - ell (tau • y)
    rw [← hMvalue]
    exact sub_pos.mpr (hellLt _ hclosedCenter)
  have hgCont : ContinuousOn g (movingLensClosed xi eps tau y) := by
    have hellCont : Continuous (fun z : TimeVelocity d => ell z.2) := by
      unfold ell affineVelocity PDE.vecDot
      fun_prop
    exact hucont.sub hellCont.continuousOn
  let S : Set (TimeVelocity d) :=
    movingLensClosed xi eps tau y ∩ {z | 0 ≤ g z}
  have hcenterS : (tau, tau • y) ∈ S := ⟨hclosedCenter, hgCenter.le⟩
  have hSCompact : IsCompact S := by
    have hLensCompact : IsCompact (movingLensClosed xi eps tau y) :=
      isCompact_movingLensClosed hxi heps htau.le
    have hSClosed : IsClosed S := by
      dsimp only [S]
      change IsClosed
        (movingLensClosed xi eps tau y ∩ g ⁻¹' Set.Ici 0)
      exact hgCont.preimage_isClosed_of_isClosed hLensCompact.isClosed isClosed_Ici
    exact hLensCompact.of_isClosed_subset hSClosed inter_subset_left
  rcases hSCompact.exists_isMinOn ⟨(tau, tau • y), hcenterS⟩
      continuous_fst.continuousOn with ⟨zc, hzcS, hzcMin⟩
  have hzcClosed : zc ∈ movingLensClosed xi eps tau y := hzcS.1
  have hzcNonneg : 0 ≤ g zc := hzcS.2
  have htcPos : 0 < zc.1 := by
    by_contra hnot
    have hzero : zc.1 = 0 := le_antisymm (not_lt.mp hnot) hzcClosed.1
    let path : ℝ → TimeVelocity d := fun s =>
      movingLensChartInv xi eps y (s, (movingLensChart xi eps y zc).2)
    have hpathZero : path 0 ∈ movingLensClosed xi eps tau y \
        movingLensActive xi eps tau y := by
      dsimp only [path]
      exact movingLensChart_path_initial_mem_causalBoundary hxi heps hzcClosed
    have hpathEq : path 0 = zc := by
      dsimp only [path]
      have hEq : (0, (movingLensChart xi eps y zc).2) =
          movingLensChart xi eps y zc := by
        apply Prod.ext
        · simpa [movingLensChart] using hzero.symm
        · rfl
      rw [hEq]
      simpa using movingLensChartInv_apply_movingLensChart hxi heps hzcClosed.1
    have hneg : g (path 0) < 0 := by
      have hbd := hboundary _ hpathZero
      have hpz := hellPos _ (hpathZero.1)
      change u (path 0) - ell (path 0).2 < 0
      linarith
    rw [hpathEq] at hneg
    linarith
  have hgcZero : g zc = 0 := by
    apply le_antisymm ?_ hzcNonneg
    by_contra hnot
    have hgcPos : 0 < g zc := lt_of_not_ge hnot
    let path : ℝ → TimeVelocity d := fun s =>
      movingLensChartInv xi eps y (s, (movingLensChart xi eps y zc).2)
    have hpathCont : Continuous path := by
      dsimp only [path, movingLensChartInv]
      unfold movingLensDenominator
      fun_prop
    have hpathZero : path 0 ∈ movingLensClosed xi eps tau y \
        movingLensActive xi eps tau y := by
      dsimp only [path]
      exact movingLensChart_path_initial_mem_causalBoundary hxi heps hzcClosed
    have hgZero : g (path 0) < 0 := by
      have hbd := hboundary _ hpathZero
      have hpz := hellPos _ hpathZero.1
      change u (path 0) - ell (path 0).2 < 0
      linarith
    have hpathEnd : path zc.1 = zc := by
      dsimp only [path]
      exact movingLensChartInv_apply_movingLensChart hxi heps hzcClosed.1
    let f : ℝ → ℝ := fun s => g (path s)
    have hfCont : ContinuousOn f (Set.Icc 0 zc.1) := by
      have hcomp := hgCont.comp hpathCont.continuousOn (by
        intro s hs
        dsimp only [path]
        exact movingLensChart_path_mem_closed hxi heps hzcClosed hs)
      simpa only [f, Function.comp_def] using hcomp
    rcases zero_between_of_continuousOn_of_neg_pos_local htcPos hfCont
        (by simpa [f] using hgZero) (by simpa [f, hpathEnd] using hgcPos) with
      ⟨s, hs, hfs⟩
    have hsS : path s ∈ S := by
      refine ⟨?_, ?_⟩
      · dsimp only [path]
        exact movingLensChart_path_mem_closed hxi heps hzcClosed ⟨hs.1.le, hs.2.le⟩
      · simpa [f] using hfs.ge
    have hmin := hzcMin hsS
    change zc.1 ≤ s at hmin
    exact (not_lt_of_ge hmin) hs.2
  have htcLt : zc.1 < tau := by
    let zT : TimeVelocity d := (tau, tau • y)
    let path : ℝ → TimeVelocity d := fun s =>
      movingLensChartInv xi eps y (s, (movingLensChart xi eps y zT).2)
    have hpathCont : Continuous path := by
      dsimp only [path, movingLensChartInv]
      unfold movingLensDenominator
      fun_prop
    have hpathZero : path 0 ∈ movingLensClosed xi eps tau y \
        movingLensActive xi eps tau y := by
      dsimp only [path, zT]
      exact movingLensChart_path_initial_mem_causalBoundary hxi heps hclosedCenter
    have hgZero : g (path 0) < 0 := by
      have hbd := hboundary _ hpathZero
      have hpz := hellPos _ hpathZero.1
      change u (path 0) - ell (path 0).2 < 0
      linarith
    have hpathEnd : path tau = zT := by
      dsimp only [path]
      exact movingLensChartInv_apply_movingLensChart hxi heps hclosedCenter.1
    let f : ℝ → ℝ := fun s => g (path s)
    have hfCont : ContinuousOn f (Set.Icc 0 tau) := by
      have hcomp := hgCont.comp hpathCont.continuousOn (by
        intro s hs
        dsimp only [path, zT]
        exact movingLensChart_path_mem_closed hxi heps hclosedCenter hs)
      simpa only [f, Function.comp_def] using hcomp
    rcases zero_between_of_continuousOn_of_neg_pos_local htau hfCont
        (by simpa [f] using hgZero) (by simpa [f, hpathEnd, zT] using hgCenter) with
      ⟨s, hs, hfs⟩
    have hsS : path s ∈ S := by
      refine ⟨?_, ?_⟩
      · dsimp only [path, zT]
        exact movingLensChart_path_mem_closed hxi heps hclosedCenter ⟨hs.1.le, hs.2.le⟩
      · simpa [f] using hfs.ge
    have hmin := hzcMin hsS
    change zc.1 ≤ s at hmin
    exact hmin.trans_lt hs.2
  have hspatialNonpos : ∀ v : PDE.Vec d,
      (zc.1, v) ∈ movingLensClosed xi eps tau y → g (zc.1, v) ≤ 0 := by
    intro v hv
    by_contra hnot
    have hpos : 0 < g (zc.1, v) := lt_of_not_ge hnot
    let zv : TimeVelocity d := (zc.1, v)
    let path : ℝ → TimeVelocity d := fun s =>
      movingLensChartInv xi eps y (s, (movingLensChart xi eps y zv).2)
    have hpathCont : Continuous path := by
      dsimp only [path, movingLensChartInv]
      unfold movingLensDenominator
      fun_prop
    have hpathZero : path 0 ∈ movingLensClosed xi eps tau y \
        movingLensActive xi eps tau y := by
      dsimp only [path]
      exact movingLensChart_path_initial_mem_causalBoundary hxi heps hv
    have hgZero : g (path 0) < 0 := by
      have hbd := hboundary _ hpathZero
      have hpz := hellPos _ hpathZero.1
      change u (path 0) - ell (path 0).2 < 0
      linarith
    have hpathEnd : path zc.1 = zv := by
      dsimp only [path, zv]
      exact movingLensChartInv_apply_movingLensChart hxi heps hv.1
    let f : ℝ → ℝ := fun s => g (path s)
    have hfCont : ContinuousOn f (Set.Icc 0 zc.1) := by
      have hcomp := hgCont.comp hpathCont.continuousOn (by
        intro s hs
        dsimp only [path, zv]
        exact movingLensChart_path_mem_closed hxi heps hv hs)
      simpa only [f, Function.comp_def] using hcomp
    rcases zero_between_of_continuousOn_of_neg_pos_local htcPos hfCont
        (by simpa [f] using hgZero) (by simpa [f, hpathEnd, zv] using hpos) with
      ⟨s, hs, hfs⟩
    have hsS : path s ∈ S := by
      refine ⟨?_, ?_⟩
      · dsimp only [path, zv]
        exact movingLensChart_path_mem_closed hxi heps hv ⟨hs.1.le, hs.2.le⟩
      · simpa [f] using hfs.ge
    have hmin := hzcMin hsS
    change zc.1 ≤ s at hmin
    exact (not_lt_of_ge hmin) hs.2
  have hzcSpatial : PDE.vecNormSq (movingLensDisplacement y zc) <
      movingLensDenominator xi eps zc.1 := by
    by_contra hnot
    have heq : PDE.vecNormSq (movingLensDisplacement y zc) =
        movingLensDenominator xi eps zc.1 := le_antisymm hzcClosed.2.2 (not_lt.mp hnot)
    have hbd : u zc ≤ 0 := hboundary zc (by
      rw [mem_movingLensClosed_diff_active_iff]
      exact Or.inr ⟨hzcClosed.1, hzcClosed.2.1, heq⟩)
    have hpz := hellPos zc hzcClosed
    change u zc - ell zc.2 = 0 at hgcZero
    linarith
  have hzcActive : zc ∈ movingLensActive xi eps tau y :=
    ⟨htcPos, hzcClosed.2.1, hzcSpatial⟩
  have huz : ContDiffAt ℝ 2 u zc := hulocal zc hzcActive
  have huzcPos : 0 < u zc := by
    have hpz := hellPos zc hzcClosed
    change u zc - ell zc.2 = 0 at hgcZero
    linarith
  have hspatialLocalMax : IsLocalMax
      (fun v : PDE.Vec d => u (zc.1, v) - ell v) zc.2 := by
    rw [IsLocalMax]
    have hopen : {v : PDE.Vec d | PDE.vecNormSq
        (movingLensDisplacement y (zc.1, v)) < movingLensDenominator xi eps zc.1} ∈
        𝓝 zc.2 := by
      exact (isOpen_movingLensSpatialStrict xi eps y).preimage
        (continuous_const.prodMk continuous_id) |>.mem_nhds hzcSpatial
    filter_upwards [hopen] with v hv
    have hvClosed : (zc.1, v) ∈ movingLensClosed xi eps tau y :=
      ⟨htcPos.le, hzcClosed.2.1, hv.le⟩
    change g (zc.1, v) ≤ g zc
    rw [hgcZero]
    exact hspatialNonpos v hvClosed
  have hgrad : velocityGradient u zc = p := by
    ext i
    let q : PDE.Vec d := Pi.single i 1
    let line : ℝ → PDE.Vec d := fun r => zc.2 + r • q
    have hlineCont : ContinuousAt line 0 :=
      (((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const q).const_add zc.2).continuousAt
    have hmaxLine : IsLocalMax
        (fun r : ℝ => u (zc.1, line r) - ell (line r)) 0 := by
      have hmaxAtLine : IsLocalMax
          (fun v : PDE.Vec d => u (zc.1, v) - ell v) (line 0) := by
        simpa [line, q] using hspatialLocalMax
      exact hmaxAtLine.comp_continuous hlineCont
    have hderiv : HasDerivAt
        (fun r : ℝ => u (zc.1,
          zc.2 + r • ((Pi.single i 1) : PDE.Vec d)) -
          ell (zc.2 + r • ((Pi.single i 1) : PDE.Vec d)))
        (velocityGradient u zc i - p i) 0 :=
      (velocity_slice_hasDerivAt_of_contDiffAt_local huz i).sub
        (affineVelocity_line_deriv_at_zero h p zc.2 i)
    have hzero := hmaxLine.hasDerivAt_eq_zero (by simpa [line, q] using hderiv)
    exact sub_eq_zero.mp (by simpa using hzero)
  have hcontact : IsLocalMax
      (fun v : PDE.Vec d => u (zc.1, v) -
        (u zc + PDE.vecDot p (v - zc.2))) zc.2 := by
    have hrewrite :
        (fun v : PDE.Vec d => u (zc.1, v) - ell v) =
          fun v : PDE.Vec d => u (zc.1, v) -
            (u zc + PDE.vecDot p (v - zc.2)) := by
      funext v
      dsimp only [ell]
      simp [affineVelocity_apply]
      have hgcZero' := hgcZero
      dsimp only [g, ell] at hgcZero'
      change u zc - affineVelocity 0 h p zc.2 = 0 at hgcZero'
      simp [affineVelocity_apply] at hgcZero'
      unfold PDE.vecDot at hgcZero' ⊢
      have hsum : (∑ x, p x * v x) =
          (∑ x, p x * zc.2 x) + ∑ x, p x * (v - zc.2) x := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        simp
        ring
      rw [hsum]
      linarith
    rw [← hrewrite]
    exact hspatialLocalMax
  have hhess : (-velocityHessian u zc).PosSemidef :=
    neg_velocityHessian_posSemidef_of_spatial_localMax_affineContact_of_contDiffAt huz hcontact
  have htimeMax : IsLocalMaxOn
      (fun t : ℝ => u (t, zc.2) - ell zc.2) (Set.Iic zc.1) zc.1 := by
    rw [IsLocalMaxOn]
    have hpast := movingLensActive_mem_nhdsWithin_past hzcActive
    have hlineTendsto : Tendsto (fun t : ℝ => (t, zc.2))
        (𝓝[Set.Iic zc.1] zc.1) (𝓝[Set.Iic zc.1 ×ˢ Set.univ] zc) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨tendsto_nhdsWithin_of_tendsto_nhds
        ((continuous_id.prodMk continuous_const).continuousAt.tendsto), ?_⟩
      filter_upwards [eventually_mem_nhdsWithin] with t ht
      exact ⟨ht, mem_univ _⟩
    have hactiveEventually : ∀ᶠ t in 𝓝[Set.Iic zc.1] zc.1,
        (t, zc.2) ∈ movingLensActive xi eps tau y := hlineTendsto.eventually hpast
    filter_upwards [hactiveEventually, eventually_mem_nhdsWithin] with t ht hle
    have htime : g (t, zc.2) ≤ 0 := by
      by_contra hnot
      have hpos : 0 < g (t, zc.2) := lt_of_not_ge hnot
      have htS : (t, zc.2) ∈ S :=
        ⟨movingLensActive_subset_movingLensClosed xi eps tau y ht, hpos.le⟩
      have hmin := hzcMin htS
      change zc.1 ≤ t at hmin
      have hne : zc.1 ≠ t := by
        intro heq
        subst t
        linarith [hgcZero]
      have hlt : zc.1 < t := lt_of_le_of_ne hmin hne
      exact (not_lt_of_ge hle) hlt
    change u (t, zc.2) - ell zc.2 ≤ u zc - ell zc.2
    change g (t, zc.2) ≤ g zc
    rw [hgcZero]
    exact htime
  have htimeDeriv : HasDerivAt
      (fun t : ℝ => u (t, zc.2) - ell zc.2) (timeDerivative u zc) zc.1 :=
    (time_slice_hasDerivAt_of_contDiffAt_local huz).sub_const (ell zc.2)
  have hminusOne : (-1 : ℝ) ∈ posTangentConeAt (Set.Iic zc.1) zc.1 := by
    have hsegment : segment ℝ zc.1 (zc.1 - 1) ⊆ Set.Iic zc.1 := by
      intro s hs
      rw [segment_symm] at hs
      exact (segment_subset_Icc (sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1)) hs).2
    simpa using sub_mem_posTangentConeAt_of_segment_subset hsegment
  have htimeNonneg : 0 ≤ timeDerivative u zc := by
    have hnonpos := htimeMax.hasFDerivWithinAt_nonpos htimeDeriv.hasDerivWithinAt hminusOne
    have hneg : -timeDerivative u zc ≤ 0 := by simpa using hnonpos
    linarith
  refine ⟨zc, ?_, ?_⟩
  · exact ⟨htcPos, htcLt, hzcSpatial, huzcPos, htimeNonneg, hhess⟩
  · rw [parabolicNormalMap_apply]
    apply Prod.ext
    · change u zc - PDE.vecDot (velocityGradient u zc) (zc.2 - 0) = h
      simp
      rw [hgrad]
      dsimp only [g, ell] at hgcZero
      change u zc - affineVelocity 0 h p zc.2 = 0 at hgcZero
      simp [affineVelocity_apply] at hgcZero
      linarith
    · exact hgrad

end

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic


/-- Concrete physical contact/area API for supplied-source lower-bound proof: wedge-volume bound. -/
theorem movingLensSlopeInterceptWedge_volume_le_lintegral_abs_det_fderiv
    {d : Nat} {xi eps tau M R : Real} {y : PDE.Vec d}
    {u : TimeVelocity d -> Real}
    (hlocal : ∀ z ∈ movingLensActive xi eps tau y, ContDiffAt Real 2 u z)
    (hcoverage :
      movingLensSlopeInterceptWedge d R M ⊆
        parabolicNormalMap u 0 '' movingLensSourceSignSet xi eps tau y u) :
    MeasureTheory.MeasureSpace.volume (movingLensSlopeInterceptWedge d R M) ≤
      ∫⁻ z in movingLensSourceSignSet xi eps tau y u,
        ENNReal.ofReal |((fderiv Real (parabolicNormalMap u 0) z).det)|
          ∂MeasureTheory.MeasureSpace.volume   := by
  have parabolicNormalMap_hasFDerivWithinAt_of_contDiffAt {u : TimeVelocity d → ℝ} {y₀ : PDE.Vec d} {s : Set (TimeVelocity d)} {z : TimeVelocity d} (hu : ContDiffAt ℝ 2 u z) : HasFDerivWithinAt (parabolicNormalMap u y₀)
      (parabolicNormalMapDerivative u y₀ z) s z :=
    (parabolicNormalMap_hasFDerivAt_of_contDiffAt hu).hasFDerivWithinAt
  have movingLensSourceSignSet_areaFormulaData_of_localC2 :
      MeasurableSet (movingLensSourceSignSet xi eps tau y u) /\
      ∀ z ∈ movingLensSourceSignSet xi eps tau y u,
        HasFDerivWithinAt (parabolicNormalMap u 0)
          (parabolicNormalMapDerivative u 0 z)
          (movingLensSourceSignSet xi eps tau y u) z := by
    let O : Set (TimeVelocity d) := {z | 0 < z.1 /\ z.1 < tau /\
      PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1}
    have hO : IsOpen O := by
      rw [show O = {z | 0 < z.1 /\
          PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1} ∩
            {z | z.1 < tau} by
        ext z
        change (0 < z.1 /\ z.1 < tau /\
          PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1) ↔
          ((0 < z.1 /\
            PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1) /\
            z.1 < tau)
        constructor
        · rintro ⟨ht0, httau, hspatial⟩
          exact ⟨⟨ht0, hspatial⟩, httau⟩
        · rintro ⟨⟨ht0, hspatial⟩, httau⟩
          exact ⟨ht0, httau, hspatial⟩]
      exact (isOpen_movingLensPositiveSpatialStrict xi eps y).inter
        (isOpen_Iio.preimage continuous_fst)
    have hO_active : O ⊆ movingLensActive xi eps tau y := by
      rintro z ⟨hzpos, hzlt, hzspatial⟩
      exact ⟨hzpos, hzlt.le, hzspatial⟩
    have huO : ContDiffOn Real 2 u O := fun z hz =>
      (hlocal z (hO_active hz)).contDiffWithinAt
    have hDu : ContDiffOn Real 1 (fderiv Real u) O :=
      huO.fderiv_of_isOpen hO (by norm_num)
    have hD2u : ContDiffOn Real 0 (fderiv Real (fderiv Real u)) O :=
      hDu.fderiv_of_isOpen hO (by norm_num)
    have hucont : ContinuousOn u O := huO.continuousOn
    have htime : ContinuousOn (timeDerivative u) O := by
      unfold timeDerivative
      simpa using hDu.continuousOn.clm_apply continuousOn_const
    have hhess : ContinuousOn (velocityHessian u) O := by
      unfold velocityHessian
      apply continuousOn_pi.mpr
      intro i
      apply continuousOn_pi.mpr
      intro j
      simpa using hD2u.continuousOn.clm_apply continuousOn_const |>.clm_apply continuousOn_const
    have hpsdclosed : IsClosed {H : PDE.Mat d | H.PosSemidef} := by
      have hhermitian : IsClosed {H : PDE.Mat d | H.IsHermitian} := by
        have hset :
            {H : PDE.Mat d | H.IsHermitian} =
              ⋂ i : Fin d, ⋂ j : Fin d, {H : PDE.Mat d | H j i = H i j} := by
          ext H
          simp [Set.mem_iInter]
          constructor
          · intro h i j
            simpa using h.apply i j
          · intro h
            apply Matrix.IsHermitian.ext
            intro i j
            simpa using h i j
        rw [hset]
        refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
        exact isClosed_eq (continuous_id.matrix_elem j i) (continuous_id.matrix_elem i j)
      have hset :
          {H : PDE.Mat d | H.PosSemidef} =
            {H : PDE.Mat d | H.IsHermitian} ∩
              ⋂ q : PDE.Vec d, {H : PDE.Mat d | 0 ≤ dotProduct q (H.mulVec q)} := by
        ext H
        simp [Set.mem_iInter]
        simpa using (Matrix.posSemidef_iff_dotProduct_mulVec (M := H))
      rw [hset]
      refine hhermitian.inter (isClosed_iInter fun q => ?_)
      have hquad : Continuous (fun H : PDE.Mat d => dotProduct q (H.mulVec q)) :=
        continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
      exact isClosed_le continuous_const hquad
    have hpositive : MeasurableSet (O ∩ {z | 0 < u z}) :=
      (hucont.isOpen_inter_preimage hO isOpen_Ioi).measurableSet
    have hnonnegative : MeasurableSet (O ∩ {z | 0 ≤ timeDerivative u z}) := by
      rw [show O ∩ {z | 0 ≤ timeDerivative u z} =
          O \ (O ∩ (timeDerivative u) ⁻¹' Set.Iio 0) by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_preimage, Set.mem_setOf_eq,
          Set.mem_Iio]
        constructor
        · rintro ⟨hz, htimez⟩
          exact ⟨hz, fun hnegative => not_lt_of_ge htimez hnegative.2⟩
        · rintro ⟨hz, hnotnegative⟩
          exact ⟨hz, le_of_not_gt fun hnegative => hnotnegative ⟨hz, hnegative⟩⟩]
      exact hO.measurableSet.diff
        (htime.isOpen_inter_preimage hO isOpen_Iio).measurableSet
    have hpsd : MeasurableSet (O ∩ {z | (-velocityHessian u z).PosSemidef}) := by
      rw [show O ∩ {z | (-velocityHessian u z).PosSemidef} = O \ (O ∩
          (fun z => -velocityHessian u z) ⁻¹' {H : PDE.Mat d | H.PosSemidef}ᶜ) by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_preimage, Set.mem_setOf_eq,
          Set.mem_compl_iff]
        constructor
        · rintro ⟨hz, hzpsd⟩
          exact ⟨hz, fun hnotpsd => hnotpsd.2 hzpsd⟩
        · rintro ⟨hz, hnotpsd⟩
          exact ⟨hz, not_not.mp fun hzpsd => hnotpsd ⟨hz, hzpsd⟩⟩]
      exact hO.measurableSet.diff
        ((hhess.neg).isOpen_inter_preimage hO hpsdclosed.isOpen_compl).measurableSet
    have hmeas : MeasurableSet (movingLensSourceSignSet xi eps tau y u) := by
      rw [show movingLensSourceSignSet xi eps tau y u =
          (O ∩ {z | 0 < u z}) ∩ (O ∩ {z | 0 ≤ timeDerivative u z}) ∩
            (O ∩ {z | (-velocityHessian u z).PosSemidef}) by
        ext z
        change (0 < z.1 /\ z.1 < tau /\
          PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1 /\
          0 < u z /\ 0 ≤ timeDerivative u z /\ (-velocityHessian u z).PosSemidef) ↔
          ((z ∈ O /\ 0 < u z) /\ (z ∈ O /\ 0 ≤ timeDerivative u z)) /\
            (z ∈ O /\ (-velocityHessian u z).PosSemidef)
        constructor
        · rintro ⟨ht0, httau, hspatial, hpositivez, htimez, hpsdz⟩
          exact ⟨⟨⟨⟨ht0, httau, hspatial⟩, hpositivez⟩,
            ⟨⟨ht0, httau, hspatial⟩, htimez⟩⟩,
            ⟨⟨ht0, httau, hspatial⟩, hpsdz⟩⟩
        · rintro ⟨⟨⟨hOpositive, hpositivez⟩, ⟨hOtime, htimez⟩⟩, ⟨hOpsd, hpsdz⟩⟩
          exact ⟨hOpositive.1, hOpositive.2.1, hOpositive.2.2,
            hpositivez, htimez, hpsdz⟩]
      exact (hpositive.inter hnonnegative).inter hpsd
    refine ⟨hmeas, ?_⟩
    intro z hz
    exact parabolicNormalMap_hasFDerivWithinAt_of_contDiffAt
      (hlocal z (hO_active ⟨hz.1, hz.2.1, hz.2.2.1⟩))
  calc
    MeasureTheory.MeasureSpace.volume (movingLensSlopeInterceptWedge d R M) ≤
        MeasureTheory.MeasureSpace.volume
          (parabolicNormalMap u 0 '' movingLensSourceSignSet xi eps tau y u) :=
      MeasureTheory.measure_mono hcoverage
    _ ≤ ∫⁻ z in movingLensSourceSignSet xi eps tau y u,
        ENNReal.ofReal |((fderiv Real (parabolicNormalMap u 0) z).det)|
          ∂MeasureTheory.MeasureSpace.volume :=
      MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv
        MeasureTheory.MeasureSpace.volume
        (movingLensSourceSignSet_areaFormulaData_of_localC2).1
        (by
          intro z hz
          have hderiv := parabolicNormalMap_hasFDerivAt_of_contDiffAt (y₀ := 0)
            (hlocal z ⟨hz.1, hz.2.1.le, hz.2.2.1⟩)
          rw [hderiv.fderiv]
          exact hderiv.hasFDerivWithinAt)

/-- Concrete physical contact/area API for supplied-source lower-bound proof: wedge volume. -/
theorem volume_movingLensSlopeInterceptWedge
    {d : Nat} {R M : Real} (hR : 0 < R) (hM : 0 < M) :
    MeasureTheory.MeasureSpace.volume (movingLensSlopeInterceptWedge d R M) =
      ENNReal.ofReal (M / 4) *
        (ENNReal.ofReal ((M / (4 * R)) ^ d) *
          MeasureTheory.MeasureSpace.volume
            (PDE.euclideanBall (0 : PDE.Vec d) 1)) := by
  unfold movingLensSlopeInterceptWedge
  have hradius : 0 < M / (4 * R) := div_pos hM (mul_pos (by norm_num) hR)
  have hinterval : 3 * M / 4 - M / 2 = M / 4 := by ring
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
    Real.volume_Ioo, hinterval,
    PDE.volume_euclideanBall_eq_unit_mul_of_pos 0 hradius]

end HypoellipticAleksandrov.Parabolic
end

