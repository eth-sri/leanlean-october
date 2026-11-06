module

public import RequestProject.TwoPi
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Normed.Operator.Compact
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public import RequestProject.KernelIdentity
public import RequestProject.CorrectedKernelDomain
public import RequestProject.FractionalInterp
public import RequestProject.CorrectedKernelEnergy
public import RequestProject.PeriodicForm

/-!
# Fourier action of the corrected physical boundary kernel

The compact matrix in `CorrectedKernelSymm` is identified here with the actual
integral kernel of `i (T - T*) + O B O* - 2 D⁻¹`, initially on Fourier modes.
The factor `2π` comes from the normalized Fourier coefficients, whereas the
physical kernel is integrated with respect to ordinary coordinate measure.

These identities hold for the existing boundary coordinates; they do not
identify the harmonic Neumann map with `|D|⁻¹`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real MeasureTheory Set
open scoped ComplexConjugate InnerProductSpace


/-- The unnormalized coordinate Fourier mode `e^{inθ}`. -/
def kernelFourierMode (n : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp (n * Complex.I * θ)

lemma fourier_two_pi_eq_kernelFourierMode (n : ℤ) (θ : ℝ) :
    fourier n (θ : AddCircle (2 * π)) = kernelFourierMode n θ := by
  rw [fourier_coe_apply]
  unfold kernelFourierMode
  congr 1

  push_cast
  field_simp

/-- Acting on `e^{ins}` extracts the row's Fourier coefficient at `-n`.
No integrability hypothesis is needed for this scalar normalization identity. -/
lemma integral_kernelFourierMode_eq_coeff (r : ℝ → ℂ) (n : ℤ) :
    (∫ s in (0 : ℝ)..(2 * π), r s * kernelFourierMode n s) =
      (2 * π : ℂ) * fourierCoeffOn two_pi_pos r (-n) := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, neg_neg, Complex.real_smul, smul_eq_mul]

  push_cast
  have hnorm : (2 * π : ℂ) * (1 / (2 * π) : ℂ) = 1 := by field_simp
  rw [← mul_assoc, hnorm, one_mul]
  apply intervalIntegral.integral_congr
  intro s _
  have hmode : Complex.exp (2 * π * Complex.I * n * s / (2 * π)) =
      kernelFourierMode n s := by
    simpa only [fourier_coe_apply, Complex.ofReal_mul, Complex.ofReal_ofNat] using
      (fourier_two_pi_eq_kernelFourierMode n s)
  simp only [fourier_coe_apply, sub_zero, Complex.ofReal_mul, Complex.ofReal_ofNat]
  simpa only [hmode] using (mul_comm (r s) (kernelFourierMode n s))

/-- The physical integral operator's Fourier matrix is `2π` times the
double Fourier coefficient, with a reversed input frequency. -/
theorem fourierCoeffOn_kernel_mode_action (r : ℝ → ℝ → ℂ) (m n : ℤ) :
    fourierCoeffOn two_pi_pos
      (fun θ => ∫ s in (0 : ℝ)..(2 * π), r θ s * kernelFourierMode n s) m =
      (2 * π : ℂ) * fourierCoeffOn two_pi_pos
        (fun θ => fourierCoeffOn two_pi_pos (r θ) (-n)) m := by
  simp_rw [integral_kernelFourierMode_eq_coeff]
  exact fourierCoeffOn.const_mul _ _ _ _

/-- Probability Haar integration differs from ordinary coordinate integration
by the length of the parameter interval. -/
lemma two_pi_mul_integral_liftIco (f : ℝ → ℂ) :
    (2 * π : ℂ) * (∫ x : AddCircle (2 * π), AddCircle.liftIco (2 * π) 0 f x
      ∂(@AddCircle.haarAddCircle (2 * π) _)) =
      ∫ s in (0 : ℝ)..(2 * π), f s := by
  have hzero : fourierCoeff (AddCircle.liftIco (2 * π) 0 f) 0 =
      ∫ x : AddCircle (2 * π), AddCircle.liftIco (2 * π) 0 f x
        ∂(@AddCircle.haarAddCircle (2 * π) _) := by
    simp [fourierCoeff]
  rw [← hzero, fourierCoeff_liftIco_two_pi, fourierCoeffOn_eq_integral]
  simp only [neg_zero, fourier_zero, one_smul, sub_zero, Complex.real_smul]

  push_cast
  have hnorm : (2 * π : ℂ) * (1 / (2 * π) : ℂ) = 1 := by field_simp
  rw [← mul_assoc, hnorm, one_mul]

/-- The physical corrected Volterra operator, before subtraction of `2 D⁻¹`. -/
def correctedVolterraAction (W : ℝ → Ell2 →L[ℂ] Ell2) (g : ℝ → ℂ) (θ : ℝ) : ℂ :=
  Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) +
    observation W (cutBE W (observationAdj W g)) θ

lemma periodicP_eq_doubleTrace_add_correctedVolterraAction
    (W : ℝ → Ell2 →L[ℂ] Ell2) (n g : ℝ → ℂ) (θ : ℝ) :
    periodicP W n g θ = 2 * n θ + correctedVolterraAction W g θ := by
  simp only [periodicP, periodicA, correctedVolterraAction, cutBE]
  ring

/-- Decomposition of the actual corrected physical form. The supplied
trace remains the true Neumann-to-Dirichlet output when this identity is
applied to a solution; no harmonic principal-part identity is assumed. -/
theorem periodicP_eq_doubleTrace_add_kernel_integrals
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π)))
    (n : ℝ → ℂ) {g : ℝ → ℂ} (hg : Continuous g) {B : ℝ}
    (hgB : ∀ s, ‖g s‖ ≤ B) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    periodicP W n g θ = 2 * n θ +
      (∫ s in (0 : ℝ)..(2 * π), sawtoothKernel θ s * g s) +
      (∫ s in (0 : ℝ)..(2 * π), correctedKernel W θ s * g s) := by
  have hp := volterra_corrected_eq_integral hW hg.aestronglyMeasurable hgB hθ
  simp_rw [add_mul] at hp
  rw [intervalIntegral.integral_add (intervalIntegrable_sawtoothKernel_mul hg θ)
    (intervalIntegrable_correctedKernel_mul hW hg hgB hθ)] at hp
  rw [periodicP_eq_doubleTrace_add_correctedVolterraAction, correctedVolterraAction, hp]
  ring

/-! ### The actual integral action on arbitrary square-integrable inputs -/

section L2Action

variable {r : ℝ → ℝ → ℂ} {M : ℝ}
  (hmeas : ∀ θ, Measurable (r θ)) (hbd : ∀ θ s, ‖r θ s‖ ≤ M)

/-- The conjugated kernel row is an actual element of `L²(𝕋)`. -/
def conjKernelRow (θ : ℝ) : L2Circ :=
  kernelRow (k := fun θ s => conj (r θ s)) (M := M)
    (fun θ => Complex.continuous_conj.measurable.comp (hmeas θ))
    (fun θ s => by simpa only [RCLike.norm_conj] using hbd θ s) θ

lemma norm_conjKernelRow_le (θ : ℝ) : ‖conjKernelRow hmeas hbd θ‖ ≤ M :=
  norm_kernelRow_le _ _ θ

/-- Integral-kernel action on an arbitrary `L²` input. The inner product
uses probability Haar measure, so ordinary coordinate integration requires
the factor `2π`. -/
def kernelL2Action (g : L2Circ) (θ : ℝ) : ℂ :=
  (2 * π : ℂ) * ⟪conjKernelRow hmeas hbd θ, g⟫_ℂ

lemma norm_kernelL2Action_le (g : L2Circ) (θ : ℝ) :
    ‖kernelL2Action hmeas hbd g θ‖ ≤ 2 * π * M * ‖g‖ := by

  have hnorm : ‖(2 * π : ℂ)‖ = 2 * π := by
    rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
  rw [kernelL2Action, norm_mul, hnorm]
  calc
    _ ≤ (2 * π) * (‖conjKernelRow hmeas hbd θ‖ * ‖g‖) := by
      gcongr
      exact norm_inner_le_norm _ _
    _ ≤ (2 * π) * (M * ‖g‖) := by
      gcongr
      exact norm_conjKernelRow_le hmeas hbd θ
    _ = _ := by ring

/-- This action is a genuine integral against the input's `L²`
representative; its definition does not depend on choosing that representative. -/
theorem kernelL2Action_eq_haar_integral (g : L2Circ) (θ : ℝ) :
    kernelL2Action hmeas hbd g θ =
      (2 * π : ℂ) * ∫ x : AddCircle (2 * π), r θ (circRep x) * g x
        ∂(@AddCircle.haarAddCircle (2 * π) _) := by
  unfold kernelL2Action conjKernelRow kernelRow
  rw [MeasureTheory.L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp
    (memLp_liftIco_two_pi (M := M) (Complex.continuous_conj.measurable.comp (hmeas θ))
      (fun s => by simpa only [Function.comp_apply, RCLike.norm_conj] using hbd θ s))] with x hx
  simp only [liftIco_eq_comp, Function.comp_apply] at hx ⊢
  simp only [RCLike.inner_apply']
  rw [hx, starRingEnd_self_apply]

/-- On a bounded measurable coordinate function, the `L²` action agrees
with its ordinary physical interval integral. -/
theorem kernelL2Action_toLp {f : ℝ → ℂ} (hf : Measurable f) {B : ℝ}
    (hfB : ∀ s, ‖f s‖ ≤ B) (θ : ℝ) :
    kernelL2Action hmeas hbd ((memLp_liftIco_two_pi hf hfB).toLp _) θ =
      ∫ s in (0 : ℝ)..(2 * π), r θ s * f s := by
  rw [kernelL2Action_eq_haar_integral]
  have heq : (fun x : AddCircle (2 * π) =>
      r θ (circRep x) * ((memLp_liftIco_two_pi hf hfB).toLp _) x) =ᵐ[
        @AddCircle.haarAddCircle (2 * π) _]
      AddCircle.liftIco (2 * π) 0 (fun s => r θ s * f s) := by
    filter_upwards [MemLp.coeFn_toLp (memLp_liftIco_two_pi hf hfB)] with x hx
    rw [hx, liftIco_eq_comp, liftIco_eq_comp]
  rw [integral_congr_ae heq]
  have hzero : fourierCoeff (AddCircle.liftIco (2 * π) 0
      (fun s => r θ s * f s)) 0 =
      ∫ x : AddCircle (2 * π), AddCircle.liftIco (2 * π) 0
        (fun s => r θ s * f s) x ∂(@AddCircle.haarAddCircle (2 * π) _) := by
    simp [fourierCoeff]
  rw [← hzero, fourierCoeff_liftIco_two_pi, fourierCoeffOn_eq_integral]
  simp only [neg_zero, fourier_zero, one_smul, sub_zero, Complex.real_smul]

  push_cast
  have hnorm : (2 * π : ℂ) * (1 / (2 * π) : ℂ) = 1 := by field_simp
  rw [← mul_assoc, hnorm, one_mul]

/-- The actual `L²` action on a Fourier basis vector is the mode action
already identified with the physical coordinate integral. -/
theorem kernelL2Action_fourierBasis (n : ℤ) (θ : ℝ) :
    kernelL2Action hmeas hbd (fourierBasis (T := 2 * π) n) θ =
      ∫ s in (0 : ℝ)..(2 * π), r θ s * kernelFourierMode n s := by
  rw [integral_kernelFourierMode_eq_coeff]
  unfold kernelL2Action conjKernelRow
  rw [inner_kernelRow_fourierBasis, fourierCoeffOn_conj, starRingEnd_self_apply]

variable {K : NNReal}
  (hlip : ∀ θ θ' s, s ∈ Ico 0 (2 * π) → ‖r θ s - r θ' s‖ ≤ K * |θ - θ'|)

include hlip in
/-- Uniform Lipschitz rows give a continuous representative of the kernel
action even when the input is only square-integrable. -/
theorem lipschitzWith_kernelL2Action (g : L2Circ) :
    LipschitzWith (Real.toNNReal (2 * π * K * ‖g‖)) (kernelL2Action hmeas hbd g) := by
  refine LipschitzWith.of_dist_le_mul fun θ θ' => ?_
  rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  unfold kernelL2Action
  have hnorm : ‖(2 * π : ℂ)‖ = 2 * π := by
    rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
  rw [← mul_sub, ← inner_sub_left, norm_mul, hnorm]
  have hr : ‖conjKernelRow hmeas hbd θ - conjKernelRow hmeas hbd θ'‖ ≤
      K * |θ - θ'| := by
    apply norm_kernelRow_sub_le _ _ (fun x x' s hs => ?_) θ θ'
    simpa only [← map_sub, RCLike.norm_conj] using hlip x x' s hs
  calc
    _ ≤ (2 * π) *
      (‖conjKernelRow hmeas hbd θ - conjKernelRow hmeas hbd θ'‖ * ‖g‖) := by
      gcongr
      exact norm_inner_le_norm _ _
    _ ≤ (2 * π) * (K * |θ - θ'| * ‖g‖) := by
      gcongr
    _ = _ := by ring

include hlip in
lemma memLp_kernelL2Action (g : L2Circ) :
    MemLp (AddCircle.liftIco (2 * π) 0 (kernelL2Action hmeas hbd g)) 2
      (@AddCircle.haarAddCircle (2 * π) _) :=
  memLp_liftIco_two_pi (lipschitzWith_kernelL2Action hmeas hbd hlip g).continuous.measurable
    (norm_kernelL2Action_le hmeas hbd g)

/-- The physical bounded kernel operator on the actual circle `L²` space. -/
def kernelL2Lin : L2Circ →ₗ[ℂ] L2Circ where
  toFun g := (memLp_kernelL2Action hmeas hbd hlip g).toLp _
  map_add' g g' := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards with x
    simp [liftIco_eq_comp, kernelL2Action, inner_add_right, mul_add]
  map_smul' c g := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    filter_upwards with x
    simp [liftIco_eq_comp, kernelL2Action, inner_smul_right, mul_assoc, mul_comm, mul_left_comm]

lemma norm_kernelL2Lin_le (g : L2Circ) :
    ‖kernelL2Lin hmeas hbd hlip g‖ ≤ (2 * π * M) * ‖g‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbd 0 0)
  have h := Lp.norm_le_of_ae_bound (μ := (@AddCircle.haarAddCircle (2 * π) _)) (p := 2)
    (f := kernelL2Lin hmeas hbd hlip g) (C := 2 * π * M * ‖g‖) (by positivity) ?_
  · have h1 : measureUnivNNReal (@AddCircle.haarAddCircle (2 * π) _) = 1 := by
      simp [measureUnivNNReal]
    simpa [h1] using h
  · filter_upwards [MemLp.coeFn_toLp (memLp_kernelL2Action hmeas hbd hlip g)] with x hx
    change ‖((memLp_kernelL2Action hmeas hbd hlip g).toLp _) x‖ ≤ _
    rw [hx, liftIco_eq_comp]
    exact norm_kernelL2Action_le hmeas hbd g _

/-- The actual integral-kernel action as a bounded linear operator. -/
def kernelL2Op : L2Circ →L[ℂ] L2Circ :=
  (kernelL2Lin hmeas hbd hlip).mkContinuous _ (norm_kernelL2Lin_le hmeas hbd hlip)

/-- Matrix coefficients of the actual bounded `L²` operator. -/
theorem kernelL2Op_fourierMatrix (m n : ℤ) :
    (fourierBasis (T := 2 * π)).repr
        (kernelL2Op hmeas hbd hlip (fourierBasis (T := 2 * π) n)) m =
      (2 * π : ℂ) * fourierCoeffOn two_pi_pos
        (fun θ => fourierCoeffOn two_pi_pos (r θ) (-n)) m := by
  rw [fourierBasis_repr]
  change fourierCoeff ((memLp_kernelL2Action hmeas hbd hlip
    (fourierBasis (T := 2 * π) n)).toLp _) m = _
  rw [fourierCoeff_congr_ae (MemLp.coeFn_toLp
    (memLp_kernelL2Action hmeas hbd hlip (fourierBasis (T := 2 * π) n))),
    fourierCoeff_liftIco_two_pi]
  have hmode : kernelL2Action hmeas hbd (fourierBasis (T := 2 * π) n) =
      (fun θ => ∫ s in (0 : ℝ)..(2 * π), r θ s * kernelFourierMode n s) := by
    funext θ
    exact kernelL2Action_fourierBasis hmeas hbd n θ
  rw [hmode]
  exact fourierCoeffOn_kernel_mode_action r m n

/-- The Fourier matrix of the unnormalized integral operator. -/
def kernelIntegralMatrix (p : ℤ × ℤ) : ℂ :=
  (2 * π : ℂ) * fourierCoeffOn two_pi_pos
    (fun θ => fourierCoeffOn two_pi_pos (r θ) (-p.2)) p.1

/-- The mode identification extends to every actual `L²` input, by the
Hilbert-basis expansion and continuity of the physical operator. -/
theorem kernelL2Op_fourier_action
    (ha : Summable fun p => ‖kernelIntegralMatrix (r := r) p‖ ^ 2) (g : L2Circ) :
    ((fourierBasis (T := 2 * π)).repr (kernelL2Op hmeas hbd hlip g) : ℤ → ℂ) =
      (hsMatrixOp (kernelIntegralMatrix (r := r)) ha
        ((fourierBasis (T := 2 * π)).repr g) : ℤ → ℂ) := by
  funext m
  rw [hsMatrixOp_apply]
  have hs := (hasSum_apply_hilbertBasis (fourierBasis (T := 2 * π))
    (kernelL2Op hmeas hbd hlip) g).mapL
      (innerSL ℂ (fourierBasis (T := 2 * π) m))
  simp only [innerSL_apply_apply, inner_smul_right] at hs
  have ht : HasSum
      (fun n => kernelIntegralMatrix (r := r) (m, n) *
        (fourierBasis (T := 2 * π)).repr g n)
      ((fourierBasis (T := 2 * π)).repr (kernelL2Op hmeas hbd hlip g) m) := by
    convert hs using 1
    · funext n
      rw [← HilbertBasis.repr_apply_apply, ← HilbertBasis.repr_apply_apply,
        kernelL2Op_fourierMatrix hmeas hbd hlip]
      exact mul_comm _ _
    · simp only [HilbertBasis.repr_apply_apply]
  exact ht.tsum_eq.symm

end L2Action

/-! ### The normalization weights act on the actual kernel matrix -/

/-- The two half-order normalization weights cancel the weights in the
corrected remainder matrix, including at the zero mode. -/
lemma correctedRemainderMatrix_half_smoothing
    (W : ℝ → Ell2 →L[ℂ] Ell2) (m n : ℤ) :
    ((sobWeight m ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        correctedRemainderMatrix W 0 0 (m, n) *
        ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
      kernelIntegralMatrix (r := correctedKernel W) (m, n) := by
  have hcancel (j : ℤ) :
      ((sobWeight j ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((sobWeight j ^ (1 / 2 : ℝ) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (sobWeight_pos j)]
    norm_num
  have hfactor : correctedRemainderMatrix W 0 0 (m, n) =
      ((sobWeight m ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        kernelIntegralMatrix (r := correctedKernel W) (m, n) := by
    simp only [correctedRemainderMatrix, kernelIntegralMatrix, sobWeight,
      mul_zero, add_zero, sub_zero, Complex.ofReal_mul]
    push_cast
    ring
  rw [hfactor]
  calc
    _ = (((sobWeight m ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((sobWeight m ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
        (((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
        kernelIntegralMatrix (r := correctedKernel W) (m, n) := by ring
    _ = _ := by rw [hcancel, hcancel, one_mul, one_mul]

/-- The weighted Hilbert--Schmidt operator is the normalization of the
physical kernel operator: smoothing once on each side recovers its raw
Fourier matrix. Both summability hypotheses only construct the operators. -/
theorem correctedRemainderOp_half_smoothing
    (W : ℝ → Ell2 →L[ℂ] Ell2)
    (ha : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2)
    (hr : Summable fun p => ‖kernelIntegralMatrix (r := correctedKernel W) p‖ ^ 2)
    (f : L2Z) :
    sobolevSmoothing (1 / 2) (by norm_num)
        (hsMatrixOp (correctedRemainderMatrix W 0 0) ha
          (sobolevSmoothing (1 / 2) (by norm_num) f)) =
      hsMatrixOp (kernelIntegralMatrix (r := correctedKernel W)) hr f := by
  apply lp.ext
  funext m
  simp only [sobolevSmoothing, diagOp_apply, hsMatrixOp_apply]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  calc
    _ = (((sobWeight m ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          correctedRemainderMatrix W 0 0 (m, n) *
          ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * f n := by ring
    _ = _ := by rw [correctedRemainderMatrix_half_smoothing]

/-! ### Instantiation at the actual corrected boundary kernel -/

/-- The corrected physical boundary kernel acts on the actual circle `L²`
space. Its periodized extension agrees with the original kernel on the cut
square, by the already proved endpoint cancellation. -/
def correctedKernelL2Op
    {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) : L2Circ →L[ℂ] L2Circ :=
  kernelL2Op (measurable_ckPer hW) (norm_ckPer_le hK hW)
    (fun θ θ' s _ => ckPer_lip hK hW hc θ θ' s)

/-- The actual corrected boundary-kernel operator and its raw Fourier
matrix agree on every circle `L²` input, beyond individual modes. -/
theorem correctedKernelL2Op_fourier_action
    {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0)
    (hr : Summable fun p => ‖kernelIntegralMatrix (r := correctedKernel W) p‖ ^ 2)
    (g : L2Circ) :
    (fourierBasis (T := 2 * π)).repr (correctedKernelL2Op hK hW hc g) =
      hsMatrixOp (kernelIntegralMatrix (r := correctedKernel W)) hr
        ((fourierBasis (T := 2 * π)).repr g) := by
  have heq : kernelIntegralMatrix (r := ckPer W) =
      kernelIntegralMatrix (r := correctedKernel W) := by
    funext p
    have hcoeff := doubleCoeff_ckPer hK hW hc (-p.2, p.1)
    unfold doubleCoeff at hcoeff
    simp only [kernelIntegralMatrix, hcoeff]
  have hp : Summable fun p => ‖kernelIntegralMatrix (r := ckPer W) p‖ ^ 2 := by
    simpa only [heq] using hr
  apply lp.ext
  funext m
  have h := congrFun (kernelL2Op_fourier_action (measurable_ckPer hW)
    (norm_ckPer_le hK hW) (fun θ θ' s _ => ckPer_lip hK hW hc θ θ' s) hp g) m
  simpa only [correctedKernelL2Op, heq] using h

/-- On every bounded measurable coordinate input, the actual `L²`
operator's coefficients are those of the original physical kernel integral. -/
theorem correctedKernelL2Op_toLp_fourier
    {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0)
    {f : ℝ → ℂ} (hf : Measurable f) {B : ℝ} (hfB : ∀ s, ‖f s‖ ≤ B) (m : ℤ) :
    (fourierBasis (T := 2 * π)).repr
        (correctedKernelL2Op hK hW hc ((memLp_liftIco_two_pi hf hfB).toLp _)) m =
      fourierCoeffOn two_pi_pos
        (fun θ => ∫ s in (0 : ℝ)..(2 * π), correctedKernel W θ s * f s) m := by
  unfold correctedKernelL2Op
  rw [fourierBasis_repr]
  change fourierCoeff ((memLp_kernelL2Action (measurable_ckPer hW)
    (norm_ckPer_le hK hW) (fun θ θ' s _ => ckPer_lip hK hW hc θ θ' s)
      ((memLp_liftIco_two_pi hf hfB).toLp _)).toLp _) m = _
  rw [fourierCoeff_congr_ae (MemLp.coeFn_toLp
    (memLp_kernelL2Action (measurable_ckPer hW) (norm_ckPer_le hK hW)
      (fun θ θ' s _ => ckPer_lip hK hW hc θ θ' s)
        ((memLp_liftIco_two_pi hf hfB).toLp _))), fourierCoeff_liftIco_two_pi]
  have haction : kernelL2Action (measurable_ckPer hW) (norm_ckPer_le hK hW)
      ((memLp_liftIco_two_pi hf hfB).toLp _) =
      (fun θ => ∫ s in (0 : ℝ)..(2 * π), ckPer W θ s * f s) := by
    funext θ
    exact kernelL2Action_toLp (measurable_ckPer hW) (norm_ckPer_le hK hW) hf hfB θ
  rw [haction]
  refine congrFun (fourierCoeffOn_congr_ae two_pi_pos ?_) m
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le two_pi_pos.le] at hs
  change ckPer W θ s * f s = correctedKernel W θ s * f s
  rw [ckPer_eq hK hW hc (Ioc_subset_Icc_self hθ) hs]

end PolyaNeumann
