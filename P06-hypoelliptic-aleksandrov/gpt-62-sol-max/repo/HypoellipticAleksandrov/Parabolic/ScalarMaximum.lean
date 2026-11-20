module

public import HypoellipticAleksandrov.Parabolic.ScalarCalculus
public import HypoellipticAleksandrov.Parabolic.MinimumPrinciple
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

section
variable {n : ℕ}

section
variable (α r₁ : ℝ) (Ω : Set (PDE.Vec n))
include α r₁ Ω

private def insetCylinder :
    Set (TimeVelocity n) :=
  Set.Icc α r₁ ×ˢ closure Ω

private def insetActive :
    Set (TimeVelocity n) :=
  Set.Ico α r₁ ×ˢ Ω

end

private def terminalTilt (u : TimeVelocity n → ℝ) (ε r₁ : ℝ) :
    TimeVelocity n → ℝ :=
  fun z => u z - ε * (r₁ - z.1)

private theorem isCompact_insetCylinder {α r₁ : ℝ}
    {Ω : Set (PDE.Vec n)} (hΩbounded : Bornology.IsBounded Ω) :
    IsCompact (insetCylinder α r₁ Ω) :=
  isCompact_Icc.prod hΩbounded.isCompact_closure

private theorem insetActive_subset_original_open {r₀ α r₁ : ℝ}
    {Ω : Set (PDE.Vec n)} (hr₀α : r₀ < α) :
    insetActive α r₁ Ω ⊆ scalarParabolicOpenCylinder r₀ r₁ Ω := by
  rintro z ⟨⟨hzα, hzr₁⟩, hzΩ⟩
  exact ⟨⟨lt_of_lt_of_le hr₀α hzα, hzr₁⟩, hzΩ⟩

end

section
variable {n : ℕ} {u : TimeVelocity n → ℝ} {z : TimeVelocity n}
  (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2)
  (hmax : IsLocalMax (fun y : PDE.Vec n => u (z.1, y)) z.2)
include hu hmax

theorem neg_scalarSpatialHessian_posSemidef_of_spatial_localMax :
    (-scalarSpatialHessian u z).PosSemidef := neg_classicalGradient_fderiv_posSemidef hu hmax

private theorem scalarSpatialGradient_eq_zero_of_spatial_localMax :
    scalarSpatialGradient u z = 0 := by
  ext i
  change fderiv ℝ (fun y : PDE.Vec n => u (z.1, y)) z.2 (PDE.basisVec i) = 0
  have hzero := hmax.hasFDerivAt_eq_zero
    ((hu.differentiableAt (by norm_num)).hasFDerivAt)
  simpa using congrArg (fun L : PDE.Vec n →L[ℝ] ℝ => L (PDE.basisVec i)) hzero

end

section
variable {n : ℕ}

theorem matrixContraction_nonpos_of_psd_neg {A H : PDE.Mat n}
    (hA : A.PosSemidef) (hH : (-H).PosSemidef) :
    matrixContraction A H ≤ 0 := by
  rw [← neg_nonneg, ← matrixContraction_neg_right,
    matrixContraction_eq_trace_mul_of_isSymm _ _ hH.isHermitian.isSymm]
  exact trace_mul_nonneg_of_posSemidef hA hH

section
variable (u : TimeVelocity n → ℝ) (ε r₁ : ℝ) (z : TimeVelocity n)

private theorem terminalTilt_spatialGradient_eq :
    scalarSpatialGradient (terminalTilt u ε r₁) z = scalarSpatialGradient u z := by
  ext i
  simp [terminalTilt, scalarSpatialGradient, PDE.classicalGradient,
    fderiv_sub_const]

private theorem terminalTilt_spatialHessian_eq :
    scalarSpatialHessian (terminalTilt u ε r₁) z = scalarSpatialHessian u z := by
  have hgradient :
      (fun y : PDE.Vec n =>
        PDE.classicalGradient (fun w : PDE.Vec n => u (z.1, w) - ε * (r₁ - z.1)) y) =
        fun y => PDE.classicalGradient (fun w : PDE.Vec n => u (z.1, w)) y := by
    funext y
    ext i
    exact congrArg (fun L : PDE.Vec n →L[ℝ] ℝ => L (PDE.basisVec i))
      (fderiv_sub_const (𝕜 := ℝ) (f := fun w : PDE.Vec n => u (z.1, w))
        (x := y) (ε * (r₁ - z.1)))
  change (fun i j => fderiv ℝ
      (fun y : PDE.Vec n => PDE.classicalGradient
        (fun w : PDE.Vec n => u (z.1, w) - ε * (r₁ - z.1)) y)
      z.2 (PDE.basisVec i) j) = _
  simp only [hgradient]
  rfl

end

private theorem terminalTilt_hasDerivAt {u : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} {z : TimeVelocity n} (hu : IsScalarC12On u D)
    (hz : z ∈ D) (ε r₁ : ℝ) :
    HasDerivAt (fun r : ℝ => terminalTilt u ε r₁ (r, z.2))
      (scalarTimeDerivative u z + ε) z.1 := by
  convert (hu.timeSlice_hasDerivAt hz).sub
    ((hasDerivAt_const (x := z.1) (c := ε)).mul
      ((hasDerivAt_const (x := z.1) (c := r₁)).sub (hasDerivAt_id z.1))) using 1
  all_goals simp only [Pi.sub_def, Pi.mul_def, id_eq, terminalTilt] <;> ring

private theorem terminalTilt_continuousOn {u : TimeVelocity n → ℝ}
    {K : Set (TimeVelocity n)} (hu : ContinuousOn u K) (ε r₁ : ℝ) :
    ContinuousOn (terminalTilt u ε r₁) K := by
  apply hu.sub
  fun_prop

private theorem spatial_localMax_of_inset_localMax {α r₁ : ℝ}
    {Ω : Set (PDE.Vec n)} (hΩopen : IsOpen Ω) {w : TimeVelocity n → ℝ}
    {z : TimeVelocity n} (hz : z ∈ insetActive α r₁ Ω)
    (hmax : IsLocalMaxOn w (insetCylinder α r₁ Ω) z) :
    IsLocalMax (fun y : PDE.Vec n => w (z.1, y)) z.2 := by
  have hslice : IsLocalMaxOn (fun y : PDE.Vec n => w (z.1, y)) Ω z.2 := by
    simpa only [Function.comp_def, id_eq] using hmax.comp_continuousOn
      (s := Ω)
      (by intro y hy; exact ⟨⟨hz.1.1, le_of_lt hz.1.2⟩, subset_closure hy⟩)
      (continuous_const.prodMk continuous_id).continuousOn hz.2
  exact hslice.isLocalMax (hΩopen.mem_nhds hz.2)

private theorem terminalTilt_spatialContDiffAt {u : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} {z : TimeVelocity n} (hu : IsScalarC12On u D)
    (hz : z ∈ D) (ε r₁ : ℝ) :
    ContDiffAt ℝ 2 (fun y : PDE.Vec n => terminalTilt u ε r₁ (z.1, y)) z.2 := by
  simpa [terminalTilt] using (hu.spatialSlice_contDiffAt hz).sub contDiffAt_const

private theorem timeDerivative_terminalTilt_nonpos_of_inset_localMax {α r₁ : ℝ} {Ω : Set (PDE.Vec n)} {w : TimeVelocity n → ℝ}
    {z : TimeVelocity n} (hz : z ∈ insetActive α r₁ Ω)
    (hmax : IsLocalMaxOn w (insetCylinder α r₁ Ω) z) {a : ℝ}
    (hderiv : HasDerivAt (fun r : ℝ => w (r, z.2)) a z.1) : a ≤ 0 := by
  have htime : IsLocalMaxOn (fun r : ℝ => w (r, z.2)) (Set.Icc α r₁) z.1 := by
    simpa only [Function.comp_def, id_eq] using hmax.comp_continuousOn
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
  have hpos := sub_pos.mpr hz.1.2
  have hproduct : (r₁ - z.1) * a ≤ 0 := by
    simpa [smul_eq_mul] using hnonpos
  exact nonpos_of_mul_nonpos_right hproduct hpos

end

private theorem scalarOperator_nonpos_at_inset_tilt_max
    {n : ℕ} {r₀ α r₁ : ℝ} {Ω : Set (PDE.Vec n)} (hΩopen : IsOpen Ω)
    (hr₀α : r₀ < α) (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n) (u : TimeVelocity n → ℝ)
    (huC12 : IsScalarC12On u (scalarParabolicOpenCylinder r₀ r₁ Ω))
    (haPsd : ∀ r y, (a r y).PosSemidef) {ε : ℝ} {z : TimeVelocity n}
    (hz : z ∈ insetActive α r₁ Ω)
    (hmax : IsLocalMaxOn (terminalTilt u ε r₁) (insetCylinder α r₁ Ω) z) :
    scalarParabolicOperator a b u z + ε ≤ 0 := by
  have hzopen : z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω :=
    insetActive_subset_original_open hr₀α hz
  have hspatialMax : IsLocalMax (fun y : PDE.Vec n => terminalTilt u ε r₁ (z.1, y)) z.2 :=
    spatial_localMax_of_inset_localMax hΩopen hz hmax
  have htiltDiff : ContDiffAt ℝ 2
      (fun y : PDE.Vec n => terminalTilt u ε r₁ (z.1, y)) z.2 :=
    terminalTilt_spatialContDiffAt huC12 hzopen ε r₁
  have hgradientTilt : scalarSpatialGradient (terminalTilt u ε r₁) z = 0 :=
    scalarSpatialGradient_eq_zero_of_spatial_localMax htiltDiff hspatialMax
  have hgradient : scalarSpatialGradient u z = 0 := by
    rw [← terminalTilt_spatialGradient_eq]
    exact hgradientTilt
  have hhessianTilt : (-scalarSpatialHessian (terminalTilt u ε r₁) z).PosSemidef :=
    neg_scalarSpatialHessian_posSemidef_of_spatial_localMax htiltDiff hspatialMax
  have hhessian : (-scalarSpatialHessian u z).PosSemidef := by
    rw [← terminalTilt_spatialHessian_eq]
    exact hhessianTilt
  have hcontraction := matrixContraction_nonpos_of_psd_neg (haPsd z.1 z.2) hhessian
  have htime := timeDerivative_terminalTilt_nonpos_of_inset_localMax hz hmax
    (terminalTilt_hasDerivAt huC12 hzopen ε r₁)
  rw [scalarParabolicOperator_apply, hgradient]
  simp only [PDE.vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  linarith

private theorem le_on_insetCylinder_of_terminal_lateral_le
    {n : ℕ} {Ω : Set (PDE.Vec n)} {r₀ α r₁ : ℝ}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hr₀α : r₀ < α) (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n)
    (haPsd : ∀ r y, (a r y).PosSemidef) (u : TimeVelocity n → ℝ)
    (hu : ContinuousOn u (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (huC12 : IsScalarC12On u (scalarParabolicOpenCylinder r₀ r₁ Ω))
    {M ε : ℝ} (hε : 0 < ε)
    (hsub : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      M < u z → 0 ≤ scalarParabolicOperator a b u z)
    (hterminal : ∀ z ∈ scalarParabolicTerminalFace r₁ Ω, u z ≤ M)
    (hlateral : ∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, u z ≤ M) :
    ∀ z ∈ insetCylinder α r₁ Ω, terminalTilt u ε r₁ z ≤ M := by
  intro z hz
  have hsubset : insetCylinder α r₁ Ω ⊆ scalarParabolicClosedCylinder r₀ r₁ Ω :=
    fun _ hq => ⟨⟨hr₀α.le.trans hq.1.1, hq.1.2⟩, hq.2⟩
  obtain ⟨w, hw, hmax⟩ := (isCompact_insetCylinder hΩbounded).exists_isMaxOn
    ⟨z, hz⟩ (terminalTilt_continuousOn (hu.mono hsubset) ε r₁)
  have htilt : terminalTilt u ε r₁ w ≤ u w :=
    sub_le_self _ (mul_nonneg hε.le (sub_nonneg.mpr hw.1.2))
  refine (hmax hz).trans ?_
  by_cases ht : w.1 = r₁
  · exact htilt.trans (hterminal w ⟨ht, hw.2⟩)
  by_cases hy : w.2 ∈ Ω
  · by_contra! hlt
    have hactive : w ∈ insetActive α r₁ Ω := ⟨⟨hw.1.1, lt_of_le_of_ne hw.1.2 ht⟩, hy⟩
    have hge := hsub w (insetActive_subset_original_open hr₀α hactive) (hlt.trans_le htilt)
    linarith [scalarOperator_nonpos_at_inset_tilt_max hΩopen hr₀α a b u
      huC12 haPsd hactive hmax.localize]
  · exact htilt.trans (hlateral w ⟨(hsubset hw).1, hΩopen.frontier_eq.symm ▸ ⟨hw.2, hy⟩⟩)

section
variable {n : ℕ} {Ω : Set (PDE.Vec n)} {r₀ r₁ : ℝ} (hΩopen : IsOpen Ω)
  (hΩbounded : Bornology.IsBounded Ω) (hr : r₀ < r₁) (a : CoefficientField n)
  (b : ℝ → PDE.Vec n → PDE.Vec n)
include hΩopen hΩbounded hr

/-- The maximum principle only requires the differential inequality where the
function exceeds the boundary bound. -/
theorem scalar_le_on_closedCylinder_of_operator_nonneg_above
    (haPsd : ∀ r y, (a r y).PosSemidef) (u : TimeVelocity n → ℝ)
    (hu : ContinuousOn u (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (huC12 : IsScalarC12On u (scalarParabolicOpenCylinder r₀ r₁ Ω)) {M : ℝ}
    (hsub : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      M < u z → 0 ≤ scalarParabolicOperator a b u z)
    (hterminal : ∀ z ∈ scalarParabolicTerminalFace r₁ Ω, u z ≤ M)
    (hlateral : ∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, u z ≤ M) :
    ∀ z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω, u z ≤ M := by
  let D := Ioc r₀ r₁ ×ˢ closure Ω
  have hD : closure D = scalarParabolicClosedCylinder r₀ r₁ Ω := by
    simp [D, closure_prod_eq, closure_Ioc hr.ne, scalarParabolicClosedCylinder]
  rw [← hD] at hu ⊢
  refine le_on_closure (g := fun _ => M) ?_ hu continuousOn_const
  intro z hz
  by_cases ht : z.1 = r₁
  · exact hterminal z ⟨ht, hz.2⟩
  have hgap := sub_pos.mpr (lt_of_le_of_ne hz.1.2 ht)
  let α := (r₀ + z.1) / 2
  have hα : r₀ < α := by dsimp [α]; linarith [hz.1.1]
  have hzα : z ∈ insetCylinder α r₁ Ω :=
    ⟨⟨by dsimp [α]; linarith [hz.1.1], hz.1.2⟩, hz.2⟩
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have htilt := le_on_insetCylinder_of_terminal_lateral_le hΩopen hΩbounded hα a b haPsd u
    (by rwa [hD] at hu) huC12 (div_pos hδ hgap) hsub hterminal hlateral z hzα
  simpa only [terminalTilt, div_mul_cancel₀ _ hgap.ne', sub_le_iff_le_add] using htilt

/--
If the scalar plus-sign parabolic operator is nonnegative on the open cylinder,
then terminal and lateral constant upper bounds control the whole closed cylinder.
The proof uses strictly inset cylinders before passing to the initial face by
continuity, so no derivative or PDE assertion is used at the initial time.
-/
theorem scalar_le_on_closedCylinder_of_terminal_lateral_le
    (_haContinuous : IsContinuousCoefficient a)
    (_hbContinuous : Continuous (fun z : TimeVelocity n => b z.1 z.2))
    (haPsd : ∀ r y, (a r y).PosSemidef)
    (u : TimeVelocity n → ℝ)
    (hu : ContinuousOn u (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (huC12 : IsScalarC12On u (scalarParabolicOpenCylinder r₀ r₁ Ω))
    (hsub : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      0 ≤ scalarParabolicOperator a b u z)
    {M : ℝ}
    (hterminal : ∀ z ∈ scalarParabolicTerminalFace r₁ Ω, u z ≤ M)
    (hlateral : ∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, u z ≤ M) :
    ∀ z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω, u z ≤ M :=
  scalar_le_on_closedCylinder_of_operator_nonneg_above hΩopen hΩbounded hr a b haPsd u hu huC12
    (fun z hz _ => hsub z hz) hterminal hlateral

end

end HypoellipticAleksandrov.Parabolic
