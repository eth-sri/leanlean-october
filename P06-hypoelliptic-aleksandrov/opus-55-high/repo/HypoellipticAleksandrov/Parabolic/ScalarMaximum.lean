module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Linarith

/-!
# Scalar backward parabolic maximum principle

This file proves the scalar, plus-sign maximum principle on an arbitrary open
bounded velocity domain.  The initial face is handled by compact cylinders
whose lower time is strictly later than the original initial time, followed by
closed-cylinder continuity.  In particular, neither the PDE nor `C^{1,2}`
regularity is queried at the initial face.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Set Matrix
open scoped MatrixOrder Topology

variable {n : ℕ} {A H : PDE.Mat n} {α r₁ : ℝ} {Ω : Set (PDE.Vec n)} {w : TimeVelocity n → ℝ} {u : TimeVelocity n → ℝ} {D : Set (TimeVelocity n)} {z : TimeVelocity n}

def insetCylinder  (α r₁ : ℝ) (Ω : Set (PDE.Vec n)) :
    Set (TimeVelocity n) :=
  Set.Icc α r₁ ×ˢ closure Ω

def insetActive  (α r₁ : ℝ) (Ω : Set (PDE.Vec n)) :
    Set (TimeVelocity n) :=
  Set.Ico α r₁ ×ˢ Ω

def terminalTilt  (u : TimeVelocity n → ℝ) (ε r₁ : ℝ) :
    TimeVelocity n → ℝ :=
  fun z => u z - ε * (r₁ - z.1)

theorem isCompact_insetCylinder  (hΩbounded : Bornology.IsBounded Ω) :
    IsCompact (insetCylinder α r₁ Ω) :=
  isCompact_Icc.prod hΩbounded.isCompact_closure

theorem insetActive_subset_original_open  {r₀ α r₁ : ℝ}
    {Ω : Set (PDE.Vec n)} (hr₀α : r₀ < α) :
    insetActive α r₁ Ω ⊆ scalarParabolicOpenCylinder r₀ r₁ Ω := by
  rintro z ⟨⟨hzα, hzr₁⟩, hzΩ⟩
  exact ⟨⟨lt_of_lt_of_le hr₀α hzα, hzr₁⟩, hzΩ⟩

theorem insetCylinder_diff_insetActive_eq  (hΩopen : IsOpen Ω) (hαr₁ : α < r₁) :
    insetCylinder α r₁ Ω \ insetActive α r₁ Ω =
      scalarParabolicTerminalFace r₁ Ω ∪
        (Set.Icc α r₁ ×ˢ frontier Ω) := by
  ext z
  rcases z with ⟨r, y⟩
  rw [hΩopen.frontier_eq]
  constructor
  · rintro ⟨⟨⟨hrα, hr₁⟩, hycl⟩, hnot⟩
    by_cases hr : r = r₁
    · simp_all
    · right
      refine ⟨⟨hrα, hr₁⟩, ?_⟩
      exact ⟨hycl, fun hy => hnot ⟨⟨hrα, lt_of_le_of_ne hr₁ hr⟩, hy⟩⟩
  · rintro (hterminal | hlateral)
    · rcases hterminal with ⟨hr, hycl⟩
      simp only [mem_singleton_iff] at hr
      subst r
      refine ⟨⟨⟨le_of_lt hαr₁, le_rfl⟩, hycl⟩, ?_⟩
      simp [insetActive]
    · rcases hlateral with ⟨⟨hrα, hr₁⟩, hycl, hynot⟩
      refine ⟨⟨⟨hrα, hr₁⟩, hycl⟩, ?_⟩
      intro hactive
      exact hynot hactive.2

theorem hasDerivAt_affine_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x q : E) (s : ℝ) :
    HasDerivAt (fun r : ℝ => x + r • q) q s := by
  simpa using
    ((hasDerivAt_id' (𝕜 := ℝ) s).smul_const q).const_add x

theorem deriv_deriv_nonpos_of_isLocalMax
    {f : ℝ → ℝ} {a c : ℝ}
    (hmax : IsLocalMax f a)
    (hsecond : HasDerivAt (deriv f) c a)
    (hcont : ContinuousAt f a) :
    c ≤ 0 := by
  by_contra hc
  have hcpos : 0 < c := lt_of_not_ge hc
  have hmin  :=
    isLocalMin_of_deriv_deriv_pos
      (by simpa only [hsecond.deriv] using hcpos)
      hmax.deriv_eq_zero hcont
  have heq : f =ᶠ[𝓝 a] fun _ => f a := by
    filter_upwards [hmax, hmin] with y hymax hymin
    linarith
  have hderivEq : deriv f =ᶠ[𝓝 a] fun _ => 0 := by
    filter_upwards [heq.deriv] with y hy
    simp_all
  have  := by
    calc
      c = deriv _ a := hsecond.deriv.symm
      _ = deriv _ a := hderivEq.deriv_eq
      _ = 0 := deriv_const _ _
  simp_all

theorem hasDerivAt_fderiv_restrict_affine_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hsecond : HasFDerivAt (fderiv ℝ g) H x) :
    HasDerivAt
      (fun r : ℝ => fderiv ℝ g (x + r • q) q)
      (H q q) 0 := by
  have hline  :=
    hasDerivAt_affine_line x q 0
  have hsecond' : HasFDerivAt (fderiv ℝ g) H (x + (0 : ℝ) • q) := by
    simp_all
  have hgrad : HasDerivAt (fun r : ℝ => fderiv ℝ g _) (H q) 0 :=
    hsecond'.comp_hasDerivAt 0 hline
  simpa using
    hgrad.clm_apply (hasDerivAt_const (x := 0) (c := q))

theorem hasDerivAt_deriv_restrict_affine_line_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    (hg : ContDiffAt ℝ 2 g x) :
    HasDerivAt (deriv (fun r : ℝ => g (x + r • q)))
      (fderiv ℝ (fderiv ℝ g) x q q) 0 := by
  have hgGradDiffAt : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hEvalLine : HasDerivAt
      (fun r : ℝ => fderiv ℝ g _ q)
      (fderiv ℝ (fderiv ℝ g) x q q) 0 :=
    hasDerivAt_fderiv_restrict_affine_line hgGradDiffAt.hasFDerivAt
  have hgEventually  :=
    hg.eventually (by norm_num)
  have hgEventuallyAtLineZero :
      ∀ᶠ y in 𝓝 (x + (0 : ℝ) • q), ContDiffAt ℝ 2 g y := by
    simp_all
  apply hEvalLine.congr_of_eventuallyEq
  filter_upwards [
    (hasDerivAt_affine_line x q 0).continuousAt hgEventuallyAtLineZero] with r hr
  change ContDiffAt ℝ 2 g (x + r • q) at hr
  exact (hr.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
    r (hasDerivAt_affine_line x q r) |>.deriv

theorem fderiv_fderiv_apply_nonpos_of_isLocalMax_affineLine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    (hg : ContDiffAt ℝ 2 g x)
    (hmax : IsLocalMax (fun r : ℝ => g (x + r • q)) 0) :
    fderiv ℝ (fderiv ℝ g) x q q ≤ 0 := by
  have hlineCont : ContinuousAt (fun r : ℝ => x + r • q) 0 :=
    (hasDerivAt_affine_line x q 0).continuousAt
  have hgAtLineZero : ContinuousAt g (x + (0 : ℝ) • q) := by
    simpa using hg.continuousAt
  have hcompCont  :=
    hgAtLineZero.comp' (f := fun r : ℝ => x + r • q) hlineCont
  exact deriv_deriv_nonpos_of_isLocalMax hmax
    (hasDerivAt_deriv_restrict_affine_line_of_contDiffAt hg) hcompCont

theorem scalarSpatialHessian_apply_eq_sndFDeriv 
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2)
    (i j : Fin n) :
    scalarSpatialHessian u z i j =
      fderiv ℝ (fderiv ℝ (fun y : PDE.Vec n => u (z.1, y))) z.2
        (PDE.basisVec i) (PDE.basisVec j) := by
  let g  := fun y => u (z.1, y)
  have hsecond : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) z.2) z.2 :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hdiff : ∀ j : Fin n,
      DifferentiableAt ℝ (fun y : PDE.Vec n => fderiv ℝ g y (PDE.basisVec j)) z.2 := by
    fun_prop
  change (fderiv ℝ (fun y : PDE.Vec n => fun j =>
      fderiv ℝ g y _) z.2 _) j = _
  rw [fderiv_pi hdiff]
  have hj := (hsecond.clm_apply (hasFDerivAt_const (PDE.basisVec j) z.2)).fderiv
  aesop

theorem scalarSpatialHessian_quadratic_eq 
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2)
    (q : PDE.Vec n) :
    dotProduct q ((scalarSpatialHessian u z).mulVec q) =
      fderiv ℝ (fderiv ℝ (fun y : PDE.Vec n => u (z.1, y))) z.2 q q := by
  let g  := fun y => u (z.1, y)
  let H := fderiv ℝ (fderiv ℝ g) z.2
  change (∑ i : Fin n, q i * ∑ j : Fin n,
      scalarSpatialHessian u z i j * q j) = H q q
  simp_rw [scalarSpatialHessian_apply_eq_sndFDeriv hu]
  calc
    (∑ i : Fin n, q i * ∑ j : Fin n,
        H _ _ * q j) =
        ∑ i : Fin n, q i * H _
          (∑ j : Fin n, q j • PDE.basisVec j) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i : Fin n, q i * H _ q := by
      rw [PDE.sum_smul_basisVec]
    _ = H (∑ i : Fin n, q i • PDE.basisVec i) q := by
      simp
    _ = H q q := by rw [PDE.sum_smul_basisVec]

theorem scalarSpatialHessian_isSymm_of_contDiffAt 
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2) :
    (scalarSpatialHessian u z).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  rw [scalarSpatialHessian_apply_eq_sndFDeriv hu,
    scalarSpatialHessian_apply_eq_sndFDeriv hu]
  exact
    (hu.isSymmSndFDerivAt (by norm_num)).eq _ _

theorem neg_scalarSpatialHessian_posSemidef_of_spatial_localMax
    
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2)
    (hmax : IsLocalMax (fun y : PDE.Vec n => u (z.1, y)) z.2) :
    (-scalarSpatialHessian u z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    exact congrArg Neg.neg ((scalarSpatialHessian_isSymm_of_contDiffAt hu).apply i j)
  · intro q
    rw [neg_mulVec, dotProduct_neg]
    have hlineMax : IsLocalMax
        (fun r : ℝ => u (z.1, z.2 + r • q)) 0 := by
      have hmaxAtLineZero : IsLocalMax (fun y : PDE.Vec n => u (z.1, y))
          (z.2 + (0 : ℝ) • q) := by
        simp_all
      simpa only [Function.comp_def, id_eq] using hmaxAtLineZero.comp_continuous
        (g := fun r : ℝ => z.2 + r • q)
        (hasDerivAt_affine_line z.2 q 0).continuousAt
    change -dotProduct q
      ((scalarSpatialHessian u z).mulVec q) ≥ 0
    rw [scalarSpatialHessian_quadratic_eq hu q]
    exact neg_nonneg.mpr
      (fderiv_fderiv_apply_nonpos_of_isLocalMax_affineLine hu hlineMax)

theorem scalarSpatialGradient_eq_zero_of_spatial_localMax
    
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2)
    (hmax : IsLocalMax (fun y : PDE.Vec n => u (z.1, y)) z.2) :
    scalarSpatialGradient u z = 0 := by
  ext i
  change fderiv ℝ _ z.2 _ = 0
  have hzero := hmax.hasFDerivAt_eq_zero
    ((hu.differentiableAt (by norm_num)).hasFDerivAt)
  simp_all

theorem trace_mul_nonneg_of_posSemidef 
    (hA : A.PosSemidef) (hH : H.PosSemidef) :
    0 ≤ (A * H).trace := by
  classical
  let S  := CFC.sqrt H
  have hS : S.PosSemidef := CFC.sqrt_nonneg H |>.posSemidef
  have hconj : (S * A * Sᴴ).PosSemidef := hA.mul_mul_conjTranspose_same S
  calc
    0 ≤ (S * A * Sᴴ).trace := hconj.trace_nonneg
    _ = (S * A * S).trace := by rw [hS.isHermitian.eq]
    _ = (A * S * S).trace := (Matrix.trace_mul_cycle A S S).symm
    _ = (A * (S * S)).trace := by grind
    _ = (A * H).trace := by rw [show S * S = H by
      exact CFC.sqrt_mul_sqrt_self H hH.nonneg]

theorem matrixContraction_nonpos_of_psd_neg 
    (hA : A.PosSemidef) (hH : (-H).PosSemidef) (hHsymm : H.IsSymm) :
    matrixContraction A H ≤ 0 := by
  have htrace  := trace_mul_nonneg_of_posSemidef hA hH
  rw [matrixContraction_eq_trace_mul_of_isSymm A H hHsymm]
  simp_all

theorem terminalTilt_spatialGradient_eq  (u : TimeVelocity n → ℝ)
    (ε r₁ : ℝ) (z : TimeVelocity n) :
    scalarSpatialGradient (terminalTilt u ε r₁) z = scalarSpatialGradient u z := by
  ext i
  simp [terminalTilt, scalarSpatialGradient,
    fderiv_sub_const]

theorem terminalTilt_spatialHessian_eq  (u : TimeVelocity n → ℝ)
    (ε r₁ : ℝ) (z : TimeVelocity n) :
    scalarSpatialHessian (terminalTilt u ε r₁) z = scalarSpatialHessian u z := by
  have hgradient :
      (fun y : PDE.Vec n =>
        PDE.classicalGradient (fun w : PDE.Vec n => u (z.1, w) - ε * (r₁ - z.1)) y) =
        fun y => PDE.classicalGradient (fun w : PDE.Vec n => u (z.1, w)) y := by
    funext y
    ext i
    exact congrArg (fun L : PDE.Vec n →L[ℝ] ℝ => L _)
      (fderiv_sub_const (𝕜 := ℝ) (f := fun w : PDE.Vec n => u _)
        (x := y) _)
  change (fun i j => fderiv ℝ
      (fun y : PDE.Vec n => PDE.classicalGradient
        (fun w : PDE.Vec n => u _ - ε * (r₁ - z.1)) y)
      z.2 _ j) = _
  aesop

theorem terminalTilt_timeDerivative_eq  (hu : IsScalarC12On u D)
    (hz : z ∈ D) (ε r₁ : ℝ) :
    scalarTimeDerivative (terminalTilt u ε r₁) z = scalarTimeDerivative u z + ε := by
  have hderiv : HasDerivAt (fun r : ℝ => terminalTilt u ε r₁ (r, z.2))
      (scalarTimeDerivative u z + ε) z.1 := by
    convert (hu.timeSlice_hasDerivAt hz).sub
      ((hasDerivAt_const (x := z.1) (c := ε)).mul
        ((hasDerivAt_const (x := z.1) (c := r₁)).sub (hasDerivAt_id z.1))) using 1
    all_goals simp only [Pi.sub_def, Pi.mul_def, id_eq,
      terminalTilt] <;> ring
  exact hderiv.deriv

theorem terminalTilt_continuousOn 
    {K : Set (TimeVelocity n)} (hu : ContinuousOn u K) (ε r₁ : ℝ) :
    ContinuousOn (terminalTilt u ε r₁) K := by
  apply hu.sub
  fun_prop

theorem spatial_localMax_of_inset_localMax  (hΩopen : IsOpen Ω) {w : TimeVelocity n → ℝ}
    {z : TimeVelocity n} (hz : z ∈ insetActive α r₁ Ω)
    (hmax : IsLocalMaxOn w (insetCylinder α r₁ Ω) z) :
    IsLocalMax (fun y : PDE.Vec n => w (z.1, y)) z.2 := by
  have hslice  := by
    simpa using hmax.comp_continuousOn
      (s := Ω)
      (by intro y hy; exact ⟨⟨hz.1.1, le_of_lt hz.1.2⟩, subset_closure hy⟩)
      (continuous_const.prodMk continuous_id).continuousOn hz.2
  exact hslice.isLocalMax (hΩopen.mem_nhds hz.2)

theorem terminalTilt_spatialContDiffAt  (hu : IsScalarC12On u D)
    (hz : z ∈ D) (ε r₁ : ℝ) :
    ContDiffAt ℝ 2 (fun y : PDE.Vec n => terminalTilt u ε r₁ (z.1, y)) z.2 := by
  simpa [terminalTilt] using (hu.spatialSlice_contDiffAt hz).sub contDiffAt_const

theorem timeDerivative_terminalTilt_nonpos_of_inset_localMax
     (hz : z ∈ insetActive α r₁ Ω)
    (hmax : IsLocalMaxOn w (insetCylinder α r₁ Ω) z)
    (hderiv : HasDerivAt (fun r : ℝ => w (r, z.2)) (scalarTimeDerivative w z) z.1) :
    scalarTimeDerivative w z ≤ 0 := by
  have htime  := by
    simpa using hmax.comp_continuousOn
      (s := Set.Icc α r₁)
      (by intro r hr; exact ⟨hr, subset_closure hz.2⟩)
      (continuous_id.prodMk continuous_const).continuousOn ⟨hz.1.1, le_of_lt hz.1.2⟩
  have hdirection : r₁ - z.1 ∈ posTangentConeAt (Set.Icc α r₁) z.1 := by
    apply sub_mem_posTangentConeAt_of_segment_subset
    intro s hs
    exact ⟨le_trans hz.1.1 (segment_subset_Icc (𝕜 := ℝ) (le_of_lt hz.1.2) hs).1,
      (segment_subset_Icc (𝕜 := ℝ) (le_of_lt hz.1.2) hs).2⟩
  have hnonpos := htime.hasFDerivWithinAt_nonpos hderiv.hasFDerivAt.hasFDerivWithinAt
    hdirection
  have hpos : 0 < r₁ - z.1 := sub_pos.mpr hz.1.2
  have hproduct  := by
    simpa [smul_eq_mul] using hnonpos
  exact nonpos_of_mul_nonpos_right hproduct hpos

theorem scalarOperator_nonpos_at_inset_tilt_max
     {r₀ α r₁ : ℝ} {Ω : Set (PDE.Vec n)} (hΩopen : IsOpen Ω)
    (hr₀α : r₀ < α) (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n) (u : TimeVelocity n → ℝ)
    (huC12 : IsScalarC12On u (scalarParabolicOpenCylinder r₀ r₁ Ω))
    (haPsd : ∀ r y, (a r y).PosSemidef) {ε : ℝ} {z : TimeVelocity n}
    (hz : z ∈ insetActive α r₁ Ω)
    (hmax : IsLocalMaxOn (terminalTilt u ε r₁) (insetCylinder α r₁ Ω) z) :
    scalarParabolicOperator a b u z + ε ≤ 0 := by
  have hzopen  :=
    insetActive_subset_original_open hr₀α hz
  have hspatialMax  :=
    spatial_localMax_of_inset_localMax hΩopen hz hmax
  have htiltDiff  :=
    terminalTilt_spatialContDiffAt huC12 hzopen ε r₁
  have hgradientTilt  :=
    scalarSpatialGradient_eq_zero_of_spatial_localMax htiltDiff hspatialMax
  have hgradient : scalarSpatialGradient u z = 0 := by
    rw [← terminalTilt_spatialGradient_eq]
    exact hgradientTilt
  have hhessianTilt  :=
    neg_scalarSpatialHessian_posSemidef_of_spatial_localMax htiltDiff hspatialMax
  have hhessian : (-scalarSpatialHessian u z).PosSemidef := by
    rw [← terminalTilt_spatialHessian_eq]
    exact hhessianTilt
  have hsymmetric  :=
    scalarSpatialHessian_isSymm_of_contDiffAt (huC12.spatialSlice_contDiffAt hzopen)
  have hcontraction  :=
    matrixContraction_nonpos_of_psd_neg (haPsd z.1 z.2) hhessian hsymmetric
  have htimeTilt  := by
    have hderivTilt : HasDerivAt (fun r : ℝ => terminalTilt u ε r₁ (r, z.2))
        (scalarTimeDerivative (terminalTilt u ε r₁) z) z.1 := by
      rw [terminalTilt_timeDerivative_eq huC12 hzopen]
      convert (huC12.timeSlice_hasDerivAt hzopen).sub
        ((hasDerivAt_const (x := z.1) (c := ε)).mul
          ((hasDerivAt_const (x := z.1) (c := r₁)).sub (hasDerivAt_id z.1))) using 1
      all_goals simp only [Pi.sub_def, Pi.mul_def, id_eq,
      terminalTilt] <;> ring
    exact timeDerivative_terminalTilt_nonpos_of_inset_localMax hz hmax
      hderivTilt
  rw [terminalTilt_timeDerivative_eq huC12 hzopen] at htimeTilt
  rw [scalarParabolicOperator_apply, hgradient]
  simp only [PDE.vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  linarith

private theorem le_on_insetCylinder_of_terminal_lateral_le
     {r₀ α r₁ : ℝ}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hr₀α : r₀ < α) (hαr₁ : α < r₁) (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n)
    (haPsd : ∀ r y, (a r y).PosSemidef) (u : TimeVelocity n → ℝ)
    (hu : ContinuousOn u (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (huC12 : IsScalarC12On u (scalarParabolicOpenCylinder r₀ r₁ Ω))
    (hsub : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      0 ≤ scalarParabolicOperator a b u z)
    {M ε : ℝ} (hε : 0 < ε)
    (hterminal : ∀ z ∈ scalarParabolicTerminalFace r₁ Ω, u z ≤ M)
    (hlateral : ∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, u z ≤ M) :
    ∀ z ∈ insetCylinder α r₁ Ω, terminalTilt u ε r₁ z ≤ M := by
  intro z hz
  by_cases hKempty : (insetCylinder α r₁ Ω).Nonempty
  · obtain ⟨zmax, hzmax, hmax⟩ :=
      (isCompact_insetCylinder hΩbounded).exists_isMaxOn hKempty
        (terminalTilt_continuousOn (hu.mono (by
          rintro q ⟨⟨hqα, hqr₁⟩, hqΩ⟩
          exact ⟨⟨le_trans (le_of_lt hr₀α) hqα, hqr₁⟩, hqΩ⟩)) ε r₁)
    have hmaxle : terminalTilt u ε r₁ z ≤ terminalTilt u ε r₁ zmax := hmax hz
    by_cases hzactive : zmax ∈ insetActive α r₁ Ω
    · have hnonpos := scalarOperator_nonpos_at_inset_tilt_max hΩopen hr₀α a b u
        huC12 haPsd hzactive hmax.localize
      have hsubmax := hsub zmax
        (insetActive_subset_original_open hr₀α hzactive)
      linarith
    · have hboundary : terminalTilt u ε r₁ zmax ≤ M := by
        have hzmaxBoundary : zmax ∈ insetCylinder α r₁ Ω \ insetActive α r₁ Ω :=
          ⟨hzmax, hzactive⟩
        rw [insetCylinder_diff_insetActive_eq hΩopen hαr₁] at hzmaxBoundary
        rcases hzmaxBoundary with hterminalFace | hlateralFace
        · calc
            terminalTilt u ε r₁ zmax ≤ u zmax := by
              dsimp [terminalTilt]
              aesop
            _ ≤ M := hterminal zmax hterminalFace
        · calc
            terminalTilt u ε r₁ zmax ≤ u zmax := by
              dsimp [terminalTilt]
              simp_all
            _ ≤ M := hlateral zmax (by
              exact ⟨⟨le_trans (le_of_lt hr₀α) hlateralFace.1.1,
                hlateralFace.1.2⟩, hlateralFace.2⟩)
      linarith
  · exact (hKempty ⟨z, hz⟩).elim

/-
The remaining comparison assembly is deliberately kept below the pointwise
calculus lemmas so the initial-face continuity argument never enters the
active-set branch.
-/

private theorem le_at_strictly_later_time
     {r₀ r r₁ : ℝ}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hr₀r : r₀ < r) (hrr₁ : r < r₁) (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n)
    (haPsd : ∀ r y, (a r y).PosSemidef) (u : TimeVelocity n → ℝ)
    (hu : ContinuousOn u (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (huC12 : IsScalarC12On u (scalarParabolicOpenCylinder r₀ r₁ Ω))
    (hsub : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      0 ≤ scalarParabolicOperator a b u z)
    {M : ℝ} (hterminal : ∀ z ∈ scalarParabolicTerminalFace r₁ Ω, u z ≤ M)
    (hlateral : ∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, u z ≤ M)
    {y : PDE.Vec n} (hyclosure : y ∈ closure Ω) :
    u (r, y) ≤ M := by
  by_contra hnot
  have hexcess : 0 < u _ - M := sub_pos.mpr (lt_of_not_ge hnot)
  let α  := (r₀ + r) / 2
  have hα0 : r₀ < α := by grind
  have hα1 : α < r₁ := by grind
  have hzinset : (r, y) ∈ insetCylinder α r₁ Ω :=
    ⟨⟨le_of_lt (by grind), le_of_lt hrr₁⟩, hyclosure⟩
  let ε  := (u (r, y) - M) / (2 * (r₁ - r))
  have hε : 0 < ε := div_pos hexcess (by positivity)
  have htilt := le_on_insetCylinder_of_terminal_lateral_le hΩopen hΩbounded hα0 hα1 a b
    haPsd u hu huC12 hsub hε hterminal hlateral (z := (r, y)) hzinset
  dsimp [terminalTilt] at htilt
  have hhalf : (u (r, y) - M) / (2 * (r₁ - r)) * (r₁ - r) =
      (u (r, y) - M) / 2 := by
    grind
  linarith

/--
If the scalar plus-sign parabolic operator is nonnegative on the open cylinder,
then terminal and lateral constant upper bounds control the whole closed cylinder.
The proof uses strictly inset cylinders before passing to the initial face by
continuity, so no derivative or PDE assertion is used at the initial time.
-/
theorem scalar_le_on_closedCylinder_of_terminal_lateral_le
     {r₀ r₁ : ℝ}
    (hΩopen : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (hr : r₀ < r₁)
    (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n)
    (haContinuous : IsContinuousCoefficient a)
    (hbContinuous : Continuous (fun z : TimeVelocity n => b z.1 z.2))
    (haPsd : ∀ r y, (a r y).PosSemidef)
    (u : TimeVelocity n → ℝ)
    (hu : ContinuousOn u (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (huC12 : IsScalarC12On u (scalarParabolicOpenCylinder r₀ r₁ Ω))
    (hsub : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      0 ≤ scalarParabolicOperator a b u z)
    {M : ℝ}
    (hterminal : ∀ z ∈ scalarParabolicTerminalFace r₁ Ω, u z ≤ M)
    (hlateral : ∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, u z ≤ M) :
    ∀ z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω, u z ≤ M := by
  intro z hz
  rcases z with ⟨r, y⟩
  rcases hz with ⟨⟨hr₀, hr₁⟩, hyclosure⟩
  by_cases hyr₀ : r = r₀
  · subst r
    by_cases hyΩ : y ∈ Ω
    · let t : ℕ → ℝ := fun k => r₀ + (r₁ - r₀) * (1 / ((k : ℝ) + 1))
      have ht : Tendsto t atTop (𝓝 r₀) := by
        dsimp [t]
        simpa using tendsto_const_nhds.add
          (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      have hcurve : Tendsto (fun k : ℕ => (t k, y)) atTop (𝓝 (r₀, y)) := by
        rw [nhds_prod_eq]
        exact ht.prodMk (tendsto_const_nhds (x := y))
      have hcurveWithin : Tendsto (fun k : ℕ => (t k, y)) atTop
          (𝓝[(scalarParabolicClosedCylinder r₀ r₁ Ω)] (r₀, y)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hcurve, ?_⟩
        filter_upwards with k
        have hk : 0 < (k : ℝ) + 1 := by positivity
        have hsmall : 1 / ((k : ℝ) + 1) ≤ 1 := (div_le_one₀ hk).mpr (by linarith)
        have hprod : (r₁ - r₀) * (1 / (k + 1)) ≤ r₁ - r₀ :=
          by simp_all
        exact ⟨⟨by nlinarith [one_div_pos.mpr hk],
          by linarith⟩, subset_closure hyΩ⟩
      apply le_of_tendsto ((hu (r₀, y) ⟨⟨le_rfl, le_of_lt hr⟩,
        subset_closure hyΩ⟩).tendsto.comp hcurveWithin)
      filter_upwards [eventually_ge_atTop 1] with k hkNat
      have hk : 0 < (k : ℝ) + 1 := by positivity
      have hkone : 1 < (k : ℝ) + 1 := by
        aesop
      have hsmall : 1 / ((k : ℝ) + 1) < 1 := (div_lt_one₀ hk).mpr hkone
      have hprod : (r₁ - r₀) * (1 / (k + 1)) < r₁ - r₀ :=
        by simp_all
      exact le_at_strictly_later_time hΩopen hΩbounded
        (by aesop)
        (by linarith) a b haPsd u hu huC12 hsub hterminal hlateral
        (subset_closure hyΩ)
    · have hyfrontier : y ∈ frontier Ω := by
        rw [hΩopen.frontier_eq]
        simp_all
      simp_all
  · by_cases hrterminal : r = r₁
    · simp_all
    · exact le_at_strictly_later_time hΩopen hΩbounded
        (lt_of_le_of_ne hr₀ (Ne.symm hyr₀)) (lt_of_le_of_ne hr₁ hrterminal)
        a b haPsd u hu huC12 hsub hterminal hlateral hyclosure

end HypoellipticAleksandrov.Parabolic
