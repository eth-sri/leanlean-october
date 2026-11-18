module

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
public import RequestProject.CorrectedKernelSymm
public import RequestProject.BoundaryChart
public import RequestProject.ArcLength
public import RequestProject.SmoothDomain
public import RequestProject.ReconChordArc
public import RequestProject.FractionalInterp
public import RequestProject.CorrectedKernelEnergy
public import RequestProject.PeriodicForm
public import RequestProject.MatrixHS
public import RequestProject.NeumannProjectedWeak
public import RequestProject.NeumannNormalizedBoundary
public import RequestProject.LocalConformalBoundaryLoad
public import RequestProject.NeumannHerglotzBoundary
public import RequestProject.LocalConformalWeakModes
public import RequestProject.LocalConformalPrincipalFactorization

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PolyaNeumann

open Real MeasureTheory Set Metric Filter
open scoped ComplexConjugate InnerProductSpace

local instance factTwoPiPosKFA : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-! ### Self-adjointness of Hilbert-Schmidt & diagonal operators on `L2Z` -/

private theorem matrix_adjoint_coefficient (A : L2Z →L[ℂ] L2Z) (m n : ℤ) :
    ContinuousLinearMap.adjoint A (stdBasisZ n) m = conj (A (stdBasisZ m) n) := by
  have hl (b : L2Z) (k : ℤ) : ⟪stdBasisZ k, b⟫_ℂ = b k := by
    simp [stdBasisZ_apply, lp.inner_single_left, RCLike.inner_apply]
  have hr (b : L2Z) (k : ℤ) : ⟪b, stdBasisZ k⟫_ℂ = conj (b k) := by
    simp [stdBasisZ_apply, lp.inner_single_right, RCLike.inner_apply]
  rw [← hl, ContinuousLinearMap.adjoint_inner_right, hr]

private theorem matrix_operator_ext (A B : L2Z →L[ℂ] L2Z)
    (h : ∀ n, A (stdBasisZ n) = B (stdBasisZ n)) : A = B := by
  apply ContinuousLinearMap.ext_on ((Submodule.dense_iff_topologicalClosure_eq_top).2 stdBasisZ.dense_span)
  rintro _ ⟨n, rfl⟩; exact h n

theorem hsMatrixOp_isSelfAdjoint (a : ℤ × ℤ → ℂ)
    (ha : Summable fun p => ‖a p‖ ^ 2)
    (hs : ∀ m n, a (m, n) = conj (a (n, m))) :
    IsSelfAdjoint (hsMatrixOp a ha) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  refine matrix_operator_ext _ _ fun n => lp.ext <| funext fun m => ?_
  rw [matrix_adjoint_coefficient]; simp only [hsMatrixOp_stdBasisZ]; exact (hs m n).symm

theorem diagOp_isSelfAdjoint (w : ℤ → ℂ) (C : ℝ)
    (hw : ∀ n, ‖w n‖ ≤ C) (hs : ∀ n, conj (w n) = w n) :
    IsSelfAdjoint (diagOp w C hw) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  refine matrix_operator_ext _ _ fun n => lp.ext <| funext fun m => ?_
  rw [matrix_adjoint_coefficient]
  simp only [diagOp_apply, stdBasisZ_apply, lp.single_apply]
  by_cases hmn : m = n
  · subst m; simp [hs]
  · simp [hmn, Ne.symm hmn]

/-! ### Fourier action of bounded periodic integral kernels -/

def kernelFourierMode (n : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp (n * Complex.I * θ)

lemma fourier_two_pi_eq_kernelFourierMode (n : ℤ) (θ : ℝ) :
    fourier n (θ : AddCircle (2 * π)) = kernelFourierMode n θ := by
  rw [fourier_coe_apply]; unfold kernelFourierMode; congr 1
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  push_cast; field_simp

lemma integral_kernelFourierMode_eq_coeff (r : ℝ → ℂ) (n : ℤ) :
    (∫ s in (0 : ℝ)..(2 * π), r s * kernelFourierMode n s) =
      (2 * π : ℂ) * fourierCoeffOn two_pi_pos r (-n) := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, neg_neg, Complex.real_smul, smul_eq_mul]
  have hpi : (2 * π : ℂ) ≠ 0 := by exact_mod_cast two_pi_pos.ne'
  push_cast
  rw [← mul_assoc, show (2 * π : ℂ) * (1 / (2 * π) : ℂ) = 1 by field_simp, one_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have hmode : Complex.exp (2 * π * Complex.I * n * s / (2 * π)) = kernelFourierMode n s := by
    simpa only [fourier_coe_apply, Complex.ofReal_mul, Complex.ofReal_ofNat] using
      fourier_two_pi_eq_kernelFourierMode n s
  simp only [fourier_coe_apply, sub_zero, Complex.ofReal_mul, Complex.ofReal_ofNat]
  simpa only [hmode] using mul_comm (r s) (kernelFourierMode n s)

theorem fourierCoeffOn_kernel_mode_action (r : ℝ → ℝ → ℂ) (m n : ℤ) :
    fourierCoeffOn two_pi_pos
      (fun θ => ∫ s in (0 : ℝ)..(2 * π), r θ s * kernelFourierMode n s) m =
      (2 * π : ℂ) * fourierCoeffOn two_pi_pos
        (fun θ => fourierCoeffOn two_pi_pos (r θ) (-n)) m := by
  simp_rw [integral_kernelFourierMode_eq_coeff]
  exact fourierCoeffOn.const_mul _ _ _ _

lemma two_pi_mul_integral_liftIco (f : ℝ → ℂ) :
    (2 * π : ℂ) * (∫ x : AddCircle (2 * π), AddCircle.liftIco (2 * π) 0 f x
      ∂(@AddCircle.haarAddCircle (2 * π) _)) =
      ∫ s in (0 : ℝ)..(2 * π), f s := by
  have hzero : fourierCoeff (AddCircle.liftIco (2 * π) 0 f) 0 =
      ∫ x : AddCircle (2 * π), AddCircle.liftIco (2 * π) 0 f x
        ∂(@AddCircle.haarAddCircle (2 * π) _) := by simp [fourierCoeff]
  rw [← hzero, fourierCoeff_liftIco_two_pi, fourierCoeffOn_eq_integral]
  simp only [neg_zero, fourier_zero, one_smul, sub_zero, Complex.real_smul]
  have hpi : (2 * π : ℂ) ≠ 0 := by exact_mod_cast two_pi_pos.ne'
  push_cast
  rw [← mul_assoc, show (2 * π : ℂ) * (1 / (2 * π) : ℂ) = 1 by field_simp, one_mul]

def correctedVolterraAction (W : ℝ → Ell2 →L[ℂ] Ell2) (g : ℝ → ℂ) (θ : ℝ) : ℂ :=
  Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) +
    observation W (cutBE W (observationAdj W g)) θ

lemma periodicP_eq_doubleTrace_add_correctedVolterraAction
    (W : ℝ → Ell2 →L[ℂ] Ell2) (n g : ℝ → ℂ) (θ : ℝ) :
    periodicP W n g θ = 2 * n θ + correctedVolterraAction W g θ := by
  simp only [periodicP, periodicA, correctedVolterraAction, cutBE]; ring

section L2Action

variable {r : ℝ → ℝ → ℂ} {M : ℝ}
  (hmeas : ∀ θ, Measurable (r θ)) (hbd : ∀ θ s, ‖r θ s‖ ≤ M)

def conjKernelRow (θ : ℝ) : L2Circ :=
  kernelRow (k := fun θ s => conj (r θ s)) (M := M)
    (fun θ => Complex.continuous_conj.measurable.comp (hmeas θ))
    (fun θ s => by simpa only [RCLike.norm_conj] using hbd θ s) θ

def kernelL2Action (g : L2Circ) (θ : ℝ) : ℂ :=
  (2 * π : ℂ) * ⟪conjKernelRow hmeas hbd θ, g⟫_ℂ

lemma norm_kernelL2Action_le (g : L2Circ) (θ : ℝ) :
    ‖kernelL2Action hmeas hbd g θ‖ ≤ 2 * π * M * ‖g‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbd 0 0)
  have hnorm : ‖(2 * π : ℂ)‖ = 2 * π := by
    rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
  rw [kernelL2Action, norm_mul, hnorm]
  calc _ ≤ (2 * π) * (‖conjKernelRow hmeas hbd θ‖ * ‖g‖) := by gcongr; exact norm_inner_le_norm _ _
    _ ≤ (2 * π) * (M * ‖g‖) := by gcongr; exact norm_kernelRow_le _ _ θ
    _ = _ := by ring

theorem kernelL2Action_eq_haar_integral (g : L2Circ) (θ : ℝ) :
    kernelL2Action hmeas hbd g θ =
      (2 * π : ℂ) * ∫ x : AddCircle (2 * π), r θ (circRep x) * g x
        ∂(@AddCircle.haarAddCircle (2 * π) _) := by
  unfold kernelL2Action conjKernelRow kernelRow
  rw [MeasureTheory.L2.inner_def]; congr 1
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp
    (memLp_liftIco_two_pi (M := M) (Complex.continuous_conj.measurable.comp (hmeas θ))
      fun s => by simpa only [Function.comp_apply, RCLike.norm_conj] using hbd θ s)] with x hx
  simp only [liftIco_eq_comp, Function.comp_apply] at hx ⊢
  simp only [RCLike.inner_apply']
  rw [hx, starRingEnd_self_apply]

theorem kernelL2Action_fourierBasis (n : ℤ) (θ : ℝ) :
    kernelL2Action hmeas hbd (fourierBasis (T := 2 * π) n) θ =
      ∫ s in (0 : ℝ)..(2 * π), r θ s * kernelFourierMode n s := by
  rw [integral_kernelFourierMode_eq_coeff]
  unfold kernelL2Action conjKernelRow
  rw [inner_kernelRow_fourierBasis, fourierCoeffOn_conj, starRingEnd_self_apply]

variable {K : NNReal}
  (hlip : ∀ θ θ' s, s ∈ Ico 0 (2 * π) → ‖r θ s - r θ' s‖ ≤ K * |θ - θ'|)

include hlip in
theorem lipschitzWith_kernelL2Action (g : L2Circ) :
    LipschitzWith (Real.toNNReal (2 * π * K * ‖g‖)) (kernelL2Action hmeas hbd g) := by
  refine LipschitzWith.of_dist_le_mul fun θ θ' => ?_
  rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  unfold kernelL2Action
  have hnorm : ‖(2 * π : ℂ)‖ = 2 * π := by
    rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
  rw [← mul_sub, ← inner_sub_left, norm_mul, hnorm]
  have hr : ‖conjKernelRow hmeas hbd θ - conjKernelRow hmeas hbd θ'‖ ≤ K * |θ - θ'| :=
    norm_kernelRow_sub_le _ _ (fun x x' s hs => by simpa only [← map_sub, RCLike.norm_conj] using hlip x x' s hs) θ θ'
  calc _ ≤ (2 * π) * (‖conjKernelRow hmeas hbd θ - conjKernelRow hmeas hbd θ'‖ * ‖g‖) := by
          gcongr; exact norm_inner_le_norm _ _
    _ ≤ (2 * π) * (K * |θ - θ'| * ‖g‖) := by gcongr
    _ = _ := by ring

include hlip in
lemma memLp_kernelL2Action (g : L2Circ) :
    MemLp (AddCircle.liftIco (2 * π) 0 (kernelL2Action hmeas hbd g)) 2
      (@AddCircle.haarAddCircle (2 * π) _) :=
  memLp_liftIco_two_pi (lipschitzWith_kernelL2Action hmeas hbd hlip g).continuous.measurable
    (norm_kernelL2Action_le hmeas hbd g)

def kernelL2Lin : L2Circ →ₗ[ℂ] L2Circ where
  toFun g := (memLp_kernelL2Action hmeas hbd hlip g).toLp _
  map_add' g g' := by
    rw [← MemLp.toLp_add]; apply MemLp.toLp_congr
    filter_upwards with x; simp [liftIco_eq_comp, kernelL2Action, inner_add_right, mul_add]
  map_smul' c g := by
    rw [← MemLp.toLp_const_smul]; apply MemLp.toLp_congr
    filter_upwards with x; simp [liftIco_eq_comp, kernelL2Action, inner_smul_right, mul_assoc, mul_comm, mul_left_comm]

lemma norm_kernelL2Lin_le (g : L2Circ) :
    ‖kernelL2Lin hmeas hbd hlip g‖ ≤ (2 * π * M) * ‖g‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbd 0 0)
  have h := Lp.norm_le_of_ae_bound (μ := (@AddCircle.haarAddCircle (2 * π) _)) (p := 2)
    (f := kernelL2Lin hmeas hbd hlip g) (C := 2 * π * M * ‖g‖) (by positivity) ?_
  · have h1 : measureUnivNNReal (@AddCircle.haarAddCircle (2 * π) _) = 1 := by simp [measureUnivNNReal]
    simpa [h1] using h
  · filter_upwards [MemLp.coeFn_toLp (memLp_kernelL2Action hmeas hbd hlip g)] with x hx
    change ‖((memLp_kernelL2Action hmeas hbd hlip g).toLp _) x‖ ≤ _
    rw [hx, liftIco_eq_comp]
    exact norm_kernelL2Action_le hmeas hbd g _

def kernelL2Op : L2Circ →L[ℂ] L2Circ :=
  (kernelL2Lin hmeas hbd hlip).mkContinuous _ (norm_kernelL2Lin_le hmeas hbd hlip)

theorem kernelL2Op_fourierMatrix (m n : ℤ) :
    (fourierBasis (T := 2 * π)).repr
        (kernelL2Op hmeas hbd hlip (fourierBasis (T := 2 * π) n)) m =
      (2 * π : ℂ) * fourierCoeffOn two_pi_pos
        (fun θ => fourierCoeffOn two_pi_pos (r θ) (-n)) m := by
  rw [fourierBasis_repr]
  change fourierCoeff ((memLp_kernelL2Action hmeas hbd hlip (fourierBasis (T := 2 * π) n)).toLp _) m = _
  rw [fourierCoeff_congr_ae (MemLp.coeFn_toLp
    (memLp_kernelL2Action hmeas hbd hlip (fourierBasis (T := 2 * π) n))),
    fourierCoeff_liftIco_two_pi,
    show kernelL2Action hmeas hbd (fourierBasis (T := 2 * π) n) =
      fun θ => ∫ s in (0 : ℝ)..(2 * π), r θ s * kernelFourierMode n s from
      funext (kernelL2Action_fourierBasis hmeas hbd n)]
  exact fourierCoeffOn_kernel_mode_action r m n

def kernelIntegralMatrix (p : ℤ × ℤ) : ℂ :=
  (2 * π : ℂ) * fourierCoeffOn two_pi_pos
    (fun θ => fourierCoeffOn two_pi_pos (r θ) (-p.2)) p.1

theorem kernelL2Op_fourier_action
    (ha : Summable fun p => ‖kernelIntegralMatrix (r := r) p‖ ^ 2) (g : L2Circ) :
    ((fourierBasis (T := 2 * π)).repr (kernelL2Op hmeas hbd hlip g) : ℤ → ℂ) =
      (hsMatrixOp (kernelIntegralMatrix (r := r)) ha
        ((fourierBasis (T := 2 * π)).repr g) : ℤ → ℂ) := by
  funext m; rw [hsMatrixOp_apply]
  have hs := (hasSum_apply_hilbertBasis (fourierBasis (T := 2 * π))
    (kernelL2Op hmeas hbd hlip) g).mapL (innerSL ℂ (fourierBasis (T := 2 * π) m))
  simp only [innerSL_apply_apply, inner_smul_right] at hs
  have ht : HasSum (fun n => kernelIntegralMatrix (r := r) (m, n) * (fourierBasis (T := 2 * π)).repr g n)
      ((fourierBasis (T := 2 * π)).repr (kernelL2Op hmeas hbd hlip g) m) := by
    convert hs using 1
    · funext n
      rw [← HilbertBasis.repr_apply_apply, ← HilbertBasis.repr_apply_apply,
        kernelL2Op_fourierMatrix hmeas hbd hlip]
      exact mul_comm _ _
    · simp only [HilbertBasis.repr_apply_apply]
  exact ht.tsum_eq.symm

end L2Action

theorem correctedRemainderOp_half_smoothing
    (W : ℝ → Ell2 →L[ℂ] Ell2)
    (ha : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2)
    (hr : Summable fun p => ‖kernelIntegralMatrix (r := correctedKernel W) p‖ ^ 2)
    (f : L2Z) :
    sobolevSmoothing (1 / 2) (by norm_num)
        (hsMatrixOp (correctedRemainderMatrix W 0 0) ha
          (sobolevSmoothing (1 / 2) (by norm_num) f)) =
      hsMatrixOp (kernelIntegralMatrix (r := correctedKernel W)) hr f := by
  have hcancel (j : ℤ) :
      ((sobWeight j ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((sobWeight j ^ (1 / 2 : ℝ) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (sobWeight_pos j)]; norm_num
  apply lp.ext; funext m
  simp only [sobolevSmoothing, diagOp_apply, hsMatrixOp_apply]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hfactor : correctedRemainderMatrix W 0 0 (m, n) =
      ((sobWeight m ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        kernelIntegralMatrix (r := correctedKernel W) (m, n) := by
    simp only [correctedRemainderMatrix, kernelIntegralMatrix, sobWeight,
      mul_zero, add_zero, sub_zero, Complex.ofReal_mul]; push_cast; ring
  rw [hfactor]
  calc _ = (((sobWeight m ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((sobWeight m ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
          (((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
          kernelIntegralMatrix (r := correctedKernel W) (m, n) * f n := by ring
    _ = _ := by rw [hcancel, hcancel, one_mul, one_mul]

def correctedKernelL2Op
    {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) : L2Circ →L[ℂ] L2Circ :=
  kernelL2Op (measurable_ckPer hW) (norm_ckPer_le hK hW)
    (fun θ θ' s _ => ckPer_lip hK hW hc θ θ' s)

theorem correctedKernelL2Op_fourier_action
    {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0)
    (hr : Summable fun p => ‖kernelIntegralMatrix (r := correctedKernel W) p‖ ^ 2)
    (g : L2Circ) :
    (fourierBasis (T := 2 * π)).repr (correctedKernelL2Op hK hW hc g) =
      hsMatrixOp (kernelIntegralMatrix (r := correctedKernel W)) hr
        ((fourierBasis (T := 2 * π)).repr g) := by
  have heq : kernelIntegralMatrix (r := ckPer W) = kernelIntegralMatrix (r := correctedKernel W) :=
    funext fun p => by
      have hcoeff := doubleCoeff_ckPer hK hW hc (-p.2, p.1)
      unfold doubleCoeff at hcoeff; simp only [kernelIntegralMatrix, hcoeff]
  have hp : Summable fun p => ‖kernelIntegralMatrix (r := ckPer W) p‖ ^ 2 := by simpa only [heq] using hr
  refine lp.ext <| funext fun m => ?_
  simpa only [correctedKernelL2Op, heq] using
    congrFun (kernelL2Op_fourier_action (measurable_ckPer hW) (norm_ckPer_le hK hW)
      (fun θ θ' s _ => ckPer_lip hK hW hc θ θ' s) hp g) m

/-! ### Regular Neumann solution at reference & conformal Herglotz solution -/

theorem h1RegularResolvent_form_at_reference {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {E₀ : ℝ} (hE₀ : 0 ≤ E₀) (u : NeumannH1 Ω) :
    h1RegularResolvent Ω E₀ E₀ (h1HelmholtzForm Ω E₀ u) =
      (h1ResonantSpace Ω E₀)ᗮ.starProjection u := by
  let S := h1ResonantSpace Ω E₀
  let A := h1HelmholtzForm Ω E₀
  let B := h1ComplementForm Ω E₀ E₀
  let v : Sᗮ := Sᗮ.orthogonalProjection u
  have hAu : A u = A (v : NeumannH1 Ω) := by
    have h := congrArg A (S.starProjection_add_starProjection_orthogonal u)
    simp only [map_add, Submodule.starProjection_apply] at h
    have h0 : A (S.orthogonalProjection u : NeumannH1 Ω) = 0 := (S.orthogonalProjection u).property
    rw [h0, zero_add] at h
    exact h.symm
  have hproj : Sᗮ.orthogonalProjection (A u) = B v := by
    rw [hAu, ← h1ComplementForm_coe_eq hE₀ E₀ v]
    exact Sᗮ.orthogonalProjection_mem_subspace_eq_self (B v)
  change ((Ring.inverse B) (Sᗮ.orthogonalProjection (A u)) : NeumannH1 Ω) = (v : NeumannH1 Ω)
  rw [hproj]
  exact congrArg Subtype.val (by
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using
      congrArg (fun T : Sᗮ →L[ℂ] Sᗮ => T v) (Ring.inverse_mul_cancel B (h1ComplementForm_isUnit hb hL hE₀)))

theorem normalizedNeumannRegular_eq_trace_of_solution_at_reference {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z)
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {E₀ : ℝ} (hE₀ : 0 ≤ E₀) (b : L2Z) (u : NeumannH1 Ω)
    (hu : IsNormalizedNeumannSolution Q E₀ b u) :
    normalizedNeumannRegular Q E₀ E₀ b =
      Q u - Q ((h1ResonantSpace Ω E₀).starProjection u) := by
  change Q (h1RegularResolvent Ω E₀ E₀ (ContinuousLinearMap.adjoint Q b)) = _
  rw [← (isNormalizedNeumannSolution_iff Q E₀ b u).mp hu, h1RegularResolvent_form_at_reference hb hL hE₀ u]
  have hdecomp := congrArg Q ((h1ResonantSpace Ω E₀).starProjection_add_starProjection_orthogonal u)
  rw [map_add] at hdecomp
  exact eq_sub_of_add_eq' hdecomp

theorem localConformalHerglotz_isNormalizedNeumannSolution
    {R C : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))
    {E : ℝ} (hE : 0 ≤ E) {a : ℝ → ℂ} (ha : IsDirDensity a) :
    IsNormalizedNeumannSolution (localConformalDiskHalfTrace hR F hFs hL) E
      (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E)))
      (herglotzWaveH1 hb ha (Real.sqrt E)) :=
  isBoundaryNeumannSolution_isNormalizedNeumannSolution hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord _ _ (herglotzWaveH1_sqrt_isBoundaryNeumannSolution hb hL hγ ha hE)

/-! ### Forced harmonic modes & compactness of regular normalized NtD remainder -/

private def IsNormalizedNeumannForcedSolution {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (b : L2Z) (u q : NeumannH1 Ω) : Prop :=
  ∀ v : NeumannH1 Ω,
    (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i u⟫_ℂ) -
      ⟪h1Value Ω v, h1Value Ω q⟫_ℂ = ⟪Q v, b⟫_ℂ

private theorem normalize_forced_weak_mode {s t k a I b : ℂ}
    (hs : s ≠ 0) (hk : k ≠ 0) (h : s ^ 2 * k * a - I = t * s * b) :
    t * s * a - (t ^ 2 / k) * b = (t / (s * k)) * I := by
  rw [show I = s ^ 2 * k * a - t * s * b by linear_combination -h]
  field_simp [hs, hk]

private theorem forced_remainder_mode (n : ℤ) (hn : n ≠ 0)
    {t b d : ℂ} (h : t - normalizedInverseAbsSymbol n * b = d) :
    t - b = (sobWeight n : ℂ)⁻¹ *
      (normalizedInverseAbsSymbol n * b + (sobWeight n : ℂ) * d) := by
  let k : ℝ := |(n : ℝ)|
  have hk : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (Int.cast_ne_zero.mpr hn))
  have hs : (sobWeight n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sobWeight_pos n).ne'
  have hsk : (sobWeight n : ℂ) = (k : ℂ) + 1 := by
    exact_mod_cast (show sobWeight n = k + 1 by unfold sobWeight; dsimp [k]; ring)
  have hs' : (k : ℂ) + 1 ≠ 0 := hsk ▸ hs
  simp only [normalizedInverseAbsSymbol, if_neg hn] at h ⊢
  change t - ((sobWeight n / k : ℝ) : ℂ) * b = d at h
  change t - b = (sobWeight n : ℂ)⁻¹ * (((sobWeight n / k : ℝ) : ℂ) * b + (sobWeight n : ℂ) * d)
  calc t - b = ((sobWeight n / k : ℝ) : ℂ) * b - b + d := by linear_combination h
    _ = _ := by simp only [Complex.ofReal_div, hsk]; field_simp [hk, hs']; ring

section RegularPrincipal

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C K : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)

include hb hhol hinj hC e he hsource hes in
private theorem localConformal_forced_principal_mode_ne_zero
    (b : L2Z) (u q : NeumannH1 (F '' ball (0 : ℂ) 1))
    (hu : IsNormalizedNeumannForcedSolution (localConformalDiskHalfTrace hR F hFs hL) b u q)
    (n : ℤ) (hn : n ≠ 0) :
    localConformalDiskHalfTrace hR F hFs hL u n -
      (((sobWeight n / |(n : ℝ)| : ℝ) : ℂ)) * b n =
        diskMassForcingCoeff (localConformalMassForcing hR F hFs hL hK q) n := by
  have hs : (Real.sqrt (2 * π) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr two_pi_pos).ne'
  have hs2 : (Real.sqrt (2 * π) : ℂ) ^ 2 = (2 * π : ℂ) := by exact_mod_cast Real.sq_sqrt two_pi_pos.le
  cases n with
  | ofNat k =>
      cases k with
      | zero => exact (hn rfl).elim
      | succ m =>
          let kZ : ℤ := ((m + 1 : ℕ) : ℤ)
          obtain ⟨f, _, hp⟩ := exists_localConformal_physical_test hR F hFs hb hL hhol hinj hC
            e he hsource hes (contDiff_diskHolomorphicMode (m + 1))
          have hp' : localConformalH1Pullback hR F hFs hL (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) =
              diskHolomorphicH1Test (m + 1) := hp
          have hw := hu (smoothTraceH1 (F '' ball (0 : ℂ) 1) f)
          have htr : localConformalDiskHalfTrace hR F hFs hL (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) =
              ((Real.sqrt (sobWeight kZ) : ℂ) * (Real.sqrt (2 * π) : ℂ)) • stdBasisZ kZ := by
            change diskHalfTrace (localConformalH1Pullback hR F hFs hL _) = _
            rw [hp']; exact diskHalfTrace_holomorphicTest (m + 1)
          rw [← localConformalH1Pullback_gradient_inner hR F hFs hb hL hhol hinj hC _ u,
            localConformal_mass_pairing hR F hFs hb hL hhol hinj hC hK _ q,
            hp', disk_gradient_form_holomorphicTest, h1Value_diskHolomorphicH1Test,
            inner_diskHolomorphicArea_eq_integral, htr] at hw
          simp only [inner_smul_left, stdBasisZ_apply, lp.inner_single_left,
            RCLike.inner_apply', map_mul, Complex.conj_ofReal, map_one, one_mul] at hw
          have habs : |(kZ : ℝ)| = ((m + 1 : ℕ) : ℝ) := by
            dsimp [kZ]; push_cast; rw [abs_of_nonneg (by positivity)]
          have hweight : sobWeight kZ = ((m + 2 : ℕ) : ℝ) := by
            simp only [sobWeight, habs]; push_cast; ring
          have hk : (((m + 1 : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
          have ht2 : (Real.sqrt ((m + 2 : ℕ) : ℝ) : ℂ) ^ 2 = (((m + 2 : ℕ) : ℝ) : ℂ) := by
            exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ))
          rw [hweight] at hw
          have hn' := normalize_forced_weak_mode hs hk (by simpa only [hs2, Complex.ofReal_natCast] using hw)
          rw [ht2] at hn'
          change localConformalDiskHalfTrace hR F hFs hL u kZ -
            (((sobWeight kZ / |(kZ : ℝ)| : ℝ) : ℂ)) * b kZ =
              diskMassForcingCoeff (localConformalMassForcing hR F hFs hL hK q) kZ
          rw [localConformalDiskHalfTrace_apply]
          change (Real.sqrt (sobWeight kZ) : ℂ) * boundaryFourier (localConformalDiskH1Trace hR F hFs hL u) kZ - _ = _
          rw [hweight, boundaryFourier_apply, habs]
          exact (by simpa only [kZ, localConformalDiskH1Trace, ContinuousLinearMap.comp_apply,
            Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast,
            diskMassForcingCoeff, diskMassForcingScale, mul_assoc] using hn')
  | negSucc m =>
      let kZ : ℤ := -((m + 1 : ℕ) : ℤ)
      have hi : Int.negSucc m = kZ := by dsimp [kZ]; omega
      obtain ⟨f, _, hp⟩ := exists_localConformal_physical_test hR F hFs hb hL hhol hinj hC
        e he hsource hes (contDiff_diskAntiholomorphicMode (m + 1))
      have hp' : localConformalH1Pullback hR F hFs hL (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) =
          diskAntiholomorphicH1Test (m + 1) := hp
      have hw := hu (smoothTraceH1 (F '' ball (0 : ℂ) 1) f)
      have htr : localConformalDiskHalfTrace hR F hFs hL (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) =
          ((Real.sqrt (sobWeight kZ) : ℂ) * (Real.sqrt (2 * π) : ℂ)) • stdBasisZ kZ := by
        change diskHalfTrace (localConformalH1Pullback hR F hFs hL _) = _
        rw [hp']; exact diskHalfTrace_antiholomorphicTest (m + 1)
      rw [← localConformalH1Pullback_gradient_inner hR F hFs hb hL hhol hinj hC _ u,
        localConformal_mass_pairing hR F hFs hb hL hhol hinj hC hK _ q,
        hp', disk_gradient_form_antiholomorphicTest, h1Value_diskAntiholomorphicH1Test,
        inner_diskAntiholomorphicArea_eq_integral, htr] at hw
      simp only [inner_smul_left, stdBasisZ_apply, lp.inner_single_left,
        RCLike.inner_apply', map_mul, Complex.conj_ofReal, map_one, one_mul] at hw
      have habs : |(kZ : ℝ)| = ((m + 1 : ℕ) : ℝ) := by
        dsimp [kZ]; push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]
      have hweight : sobWeight kZ = ((m + 2 : ℕ) : ℝ) := by
        simp only [sobWeight, habs]; push_cast; ring
      have hk : (((m + 1 : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
      have ht2 : (Real.sqrt ((m + 2 : ℕ) : ℝ) : ℂ) ^ 2 = (((m + 2 : ℕ) : ℝ) : ℂ) := by
        exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ))
      rw [hweight] at hw
      have hn' := normalize_forced_weak_mode hs hk (by simpa only [hs2, Complex.ofReal_natCast] using hw)
      rw [ht2] at hn'
      rw [hi, localConformalDiskHalfTrace_apply]
      change (Real.sqrt (sobWeight kZ) : ℂ) * boundaryFourier (localConformalDiskH1Trace hR F hFs hL u) kZ - _ = _
      rw [hweight, boundaryFourier_apply, habs, ← hi]
      exact (by simpa only [kZ, ← hi, localConformalDiskH1Trace, ContinuousLinearMap.comp_apply,
        Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast,
        diskMassForcingCoeff, diskMassForcingScale, mul_assoc] using hn')

include hb hhol hinj hC e he hsource hes in
theorem isCompactOperator_localConformal_normalizedNeumannRegular_sub_one
    {E₀ E : ℝ} (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1ComplementForm (F '' ball (0 : ℂ) 1) E₀ E)) :
    IsCompactOperator
      (normalizedNeumannRegular (localConformalDiskHalfTrace hR F hFs hL) E₀ E -
        (1 : L2Z →L[ℂ] L2Z)) := by
  obtain ⟨K, _, hK⟩ := exists_localConformalMassDensity_bound hR F hFs
  let Q := localConformalDiskHalfTrace hR F hFs hL
  let T := normalizedNeumannRegular Q E₀ E
  let MI : L2Z →L[ℂ] NeumannH1 (F '' ball (0 : ℂ) 1) :=
    (((E : ℂ) • h1RegularResolvent (F '' ball (0 : ℂ) 1) E₀ E) -
      ((E₀ + 1 : ℝ) : ℂ) • (h1ResonantSpace (F '' ball (0 : ℂ) 1) E₀).starProjection).comp
        (ContinuousLinearMap.adjoint Q)
  let M : L2Z →L[ℂ] L2Z := (localConformalMassFourierH1 hR F hFs hL hK).comp MI
  have hfac : T - 1 = (sobolevSmoothing 1 (by norm_num)).comp (normalizedInverseAbsOperator + M) +
      zeroModeProjection.comp (T - 1) := by
    apply ContinuousLinearMap.ext; intro b; apply lp.ext; funext n
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      sobolevSmoothing, diagOp_apply, Real.rpow_neg_one, Complex.ofReal_inv,
      normalizedInverseAbsOperator_apply, zeroModeProjection_apply,
      lp.coeFn_sub, lp.coeFn_add, Pi.sub_apply, Pi.add_apply, M, localConformalMassFourierH1_apply]
    by_cases hn : n = 0
    · subst n; simp [normalizedInverseAbsSymbol, diskMassForcingCoeff]
    · rw [if_neg hn, zero_mul, add_zero]
      refine forced_remainder_mode n hn ?_
      have hforced : IsNormalizedNeumannForcedSolution Q b
          (h1RegularResolvent (F '' ball (0 : ℂ) 1) E₀ E (ContinuousLinearMap.adjoint Q b)) (MI b) := fun v => by
        have h := h1RegularResolvent_adjoint_weak_pairing Q hE₀ hunit b v
        simp only [MI, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply, map_sub, map_smul, inner_sub_right, inner_smul_right]
        linear_combination h
      simpa only [T, normalizedNeumannRegular, ContinuousLinearMap.comp_apply,
        normalizedInverseAbsSymbol, if_neg hn] using
        localConformal_forced_principal_mode_ne_zero hR F hFs hb hL hhol hinj hC hK
          e he hsource hes b _ (MI b) hforced n hn
  rw [hfac]
  exact ((isCompactOperator_sobolevSmoothing (by norm_num : (0 : ℝ) < 1)).comp_clm
    (normalizedInverseAbsOperator + M)).add (isCompactOperator_zeroModeProjection.comp_clm (T - 1))

end RegularPrincipal

end PolyaNeumann
end
