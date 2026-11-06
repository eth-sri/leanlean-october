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
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Parabolic.MinimumPrinciple
import HypoellipticAleksandrov.Parabolic.ScalarClassical
import Mathlib.Tactic.Linarith
import all HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
import all HypoellipticAleksandrov.KineticAleksandrov.Lieberman.TerminalLift
import all HypoellipticAleksandrov.Parabolic.Derivatives

open private HypoellipticAleksandrov.KineticAleksandrov.Lieberman.scalarSpatialHessian_apply_eq_sndFDeriv from HypoellipticAleksandrov.KineticAleksandrov.Lieberman.TerminalLift
open private HypoellipticAleksandrov.KineticAleksandrov.hasDerivAt_deriv_restrict_affine_line_of_contDiffAt from HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
open private HypoellipticAleksandrov.Parabolic.hasDerivAt_fderiv_restrict_affine_line from HypoellipticAleksandrov.Parabolic.Derivatives
open private HypoellipticAleksandrov.Parabolic.deriv_deriv_nonpos_of_isLocalMax from HypoellipticAleksandrov.Parabolic.Derivatives
open private HypoellipticAleksandrov.KineticAleksandrov.fderiv_fderiv_apply_nonpos_of_isLocalMax_affineLine from HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
open private HypoellipticAleksandrov.Parabolic.hasDerivAt_affine_line from HypoellipticAleksandrov.Parabolic.Derivatives


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

variable {n : ℕ}

variable (α r₁ : ℝ) (Ω : PDE.VelocityRegion n)



private def insetActive   :
    HypoellipticAleksandrov.Parabolic.Region n :=
  Set.Ico α r₁ ×ˢ Ω

private def terminalTilt  (u : TimeVelocity n → ℝ) (ε r₁ : ℝ) :
    TimeVelocity n → ℝ :=
  fun z => u z - ε * (r₁ - z.1)

private theorem isCompact_insetCylinder  {α r₁ : ℝ}
    {Ω : PDE.VelocityRegion n} (hΩbounded : Bornology.IsBounded Ω) :
    IsCompact (_root_.HypoellipticAleksandrov.Parabolic.scalarParabolicClosedCylinder α r₁ Ω) :=
  isCompact_Icc.prod hΩbounded.isCompact_closure

private theorem insetActive_subset_original_open  {r₀ α r₁ : ℝ}
    {Ω : PDE.VelocityRegion n} (hr₀α : r₀ < α) :
    insetActive α r₁ Ω ⊆ scalarParabolicOpenCylinder r₀ r₁ Ω := by
  rintro z ⟨⟨hzα, hzr₁⟩, hzΩ⟩
  exact ⟨⟨lt_of_lt_of_le hr₀α hzα, hzr₁⟩, hzΩ⟩

private theorem insetCylinder_diff_insetActive_eq  {α r₁ : ℝ}
    {Ω : PDE.VelocityRegion n} (hΩopen : IsOpen Ω) (hαr₁ : α < r₁) :
    _root_.HypoellipticAleksandrov.Parabolic.scalarParabolicClosedCylinder α r₁ Ω \ insetActive α r₁ Ω =
      scalarParabolicTerminalFace r₁ Ω ∪
        (Set.Icc α r₁ ×ˢ frontier Ω) := by
  ext z
  rcases z with ⟨r, y⟩
  rw [hΩopen.frontier_eq]
  constructor
  · rintro ⟨⟨⟨hrα, hr₁⟩, hycl⟩, hnot⟩
    by_cases hr : r = r₁
    · left
      exact ⟨hr, hycl⟩
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















variable {n : ℕ}

section
variable {u : TimeVelocity n → ℝ} {z : TimeVelocity n} (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2)




include hu in
private theorem scalarSpatialHessian_quadratic_eq

    (q : PDE.Vec n) :
    dotProduct q ((scalarSpatialHessian u z).mulVec q) =
      fderiv ℝ (fderiv ℝ (fun y  => u (z.1, y))) z.2 q q := by

  let H := fderiv ℝ (fderiv ℝ (fun y => u (z.1, y))) z.2
  change (∑ i : Fin n, q i * ∑ j : Fin n,
      scalarSpatialHessian u z i j * q j) = H q q
  simp_rw [_root_.HypoellipticAleksandrov.KineticAleksandrov.Lieberman.scalarSpatialHessian_apply_eq_sndFDeriv hu]
  change (∑ i : Fin n, q i * ∑ j : Fin n,
      H (PDE.basisVec i) (PDE.basisVec j) * q j) = H q q
  calc
    (∑ i : Fin n, q i * ∑ j : Fin n,
        H (PDE.basisVec i) (PDE.basisVec j) * q j) =
        ∑ i : Fin n, q i * H (PDE.basisVec i)
          (∑ j : Fin n, q j • PDE.basisVec j) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i : Fin n, q i * H (PDE.basisVec i) q := by
      rw [PDE.sum_smul_basisVec]
    _ = H (∑ i : Fin n, q i • PDE.basisVec i) q := by
      rw [map_sum, ContinuousLinearMap.sum_apply]
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    _ = H q q := by rw [PDE.sum_smul_basisVec]

include hu in
private theorem scalarSpatialHessian_isSymm_of_contDiffAt
     :
    (scalarSpatialHessian u z).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  rw [_root_.HypoellipticAleksandrov.KineticAleksandrov.Lieberman.scalarSpatialHessian_apply_eq_sndFDeriv hu,
    _root_.HypoellipticAleksandrov.KineticAleksandrov.Lieberman.scalarSpatialHessian_apply_eq_sndFDeriv hu]
  exact
    (hu.isSymmSndFDerivAt (by norm_num)).eq (PDE.basisVec j) (PDE.basisVec i)

variable (hmax : IsLocalMax (fun y : PDE.Vec n => u (z.1, y)) z.2)

include hu hmax
private theorem neg_scalarSpatialHessian_posSemidef_of_spatial_localMax

     :
    (-scalarSpatialHessian u z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · simp_all [scalarSpatialHessian, scalarSpatialHessian_isSymm_of_contDiffAt]
  · intro q
    rw [neg_mulVec, dotProduct_neg]

    change -dotProduct q
      ((scalarSpatialHessian u z).mulVec q) ≥ 0
    rw [scalarSpatialHessian_quadratic_eq hu q]
    exact neg_nonneg.mpr
      (_root_.HypoellipticAleksandrov.KineticAleksandrov.fderiv_fderiv_apply_nonpos_of_isLocalMax_affineLine hu (by
          have hmaxAtLineZero : IsLocalMax (fun y  => u (z.1, y))
              (z.2 + (0 : ℝ) • q) := by
            simpa only [zero_smul, add_zero] using hmax
          simpa only [Function.comp_def] using
            hmaxAtLineZero.comp_continuous (g := fun r : ℝ => z.2 + r • q)
              (_root_.HypoellipticAleksandrov.Parabolic.hasDerivAt_affine_line z.2 q 0).continuousAt))

private theorem scalarSpatialGradient_eq_zero_of_spatial_localMax

     :
    scalarSpatialGradient u z = 0 := by
  ext i
  change fderiv ℝ (fun y  => u (z.1, y)) z.2 (PDE.basisVec i) = 0
  have hzero := hmax.hasFDerivAt_eq_zero
    ((hu.differentiableAt (by norm_num)).hasFDerivAt)
  simpa using congrArg (fun L : PDE.Vec n →L[ℝ] ℝ => L (PDE.basisVec i)) hzero
end


section
variable {A H : PDE.Mat n} (hA : A.PosSemidef)



include hA in
private theorem matrixContraction_nonpos_of_psd_neg   (hH : (-H).PosSemidef) (hHsymm : H.IsSymm) :
    matrixContraction A H ≤ 0 := by

  rw [matrixContraction_eq_trace_mul_of_isSymm A H hHsymm]
  calc
    (A * H).trace = -((A * (-H)).trace) := by simp
    _ ≤ 0 := neg_nonpos.mpr (trace_mul_nonneg_of_posSemidef hA hH)
end


variable (u : TimeVelocity n → ℝ) (ε r₁ : ℝ) (z : TimeVelocity n)

private theorem terminalTilt_spatialGradient_eq   :
    scalarSpatialGradient (terminalTilt u ε r₁) z = scalarSpatialGradient u z := by
  ext i
  simp [terminalTilt, scalarSpatialGradient, PDE.classicalGradient,
    fderiv_sub_const]

private theorem terminalTilt_spatialHessian_eq   :
    scalarSpatialHessian (terminalTilt u ε r₁) z = scalarSpatialHessian u z := by
  let sharedTerm_55449623ec := ((fun y : PDE.Vec n => PDE.classicalGradient (fun w : PDE.Vec n => u (z.1, w) - ε * (r₁ - z.1)) y))
  have hgradient :
      (sharedTerm_55449623ec) =
        (PDE.classicalGradient (fun w : PDE.Vec n => u (z.1, w))) := by
    funext y
    ext i
    exact congrArg (fun L : PDE.Vec n →L[ℝ] ℝ => L (PDE.basisVec i))
      (fderiv_sub_const
         _)
  change (fun i j => fderiv ℝ
      sharedTerm_55449623ec
      z.2 (PDE.basisVec i) j) = _
  simp only [hgradient]
  rfl

variable {u : TimeVelocity n → ℝ}

private theorem terminalTilt_timeDerivative_eq
    {D : HypoellipticAleksandrov.Parabolic.Region n} {z : TimeVelocity n} (hu : IsScalarC12On u D)
    (hz : z ∈ D) (ε r₁ : ℝ) :
    scalarTimeDerivative (terminalTilt u ε r₁) z = scalarTimeDerivative u z + ε := by

  exact (show HasDerivAt (fun r  => terminalTilt u ε r₁ (r, z.2))
      (scalarTimeDerivative u z + ε) z.1 by
      change HasDerivAt (fun r  => u (r, z.2) - ε * (r₁ - r))
        (scalarTimeDerivative u z + ε) z.1
      convert (hu.timeSlice_hasDerivAt hz).sub
        ((hasDerivAt_const (x := z.1) (c := ε)).mul
          ((hasDerivAt_const (x := z.1) (c := r₁)).sub (hasDerivAt_id z.1))) using 1
      all_goals simp only [Pi.sub_def, Pi.mul_def, id_eq] <;> ring).deriv

private theorem terminalTilt_continuousOn
    {K : HypoellipticAleksandrov.Parabolic.Region n} (hu : ContinuousOn u K) (ε r₁ : ℝ) :
    ContinuousOn (terminalTilt u ε r₁) K := by
  apply hu.sub
  fun_prop

private theorem spatial_localMax_of_inset_localMax  {α r₁ : ℝ}
    {Ω : PDE.VelocityRegion n} (hΩopen : IsOpen Ω) {w : TimeVelocity n → ℝ}
    {z : TimeVelocity n} (hz : z ∈ insetActive α r₁ Ω)
    (hmax : IsLocalMaxOn w (_root_.HypoellipticAleksandrov.Parabolic.scalarParabolicClosedCylinder α r₁ Ω) z) :
    IsLocalMax (fun y  => w (z.1, y)) z.2 := (IsLocalMaxOn.isLocalMax
  (IsLocalMaxOn.comp_continuousOn hmax (fun ⦃y⦄ hy => ⟨⟨hz.left.left, le_of_lt hz.left.right⟩, subset_closure hy⟩)
    (Continuous.continuousOn (Continuous.prodMk continuous_const continuous_id)) hz.right)
  (IsOpen.mem_nhds hΩopen hz.right))

private theorem terminalTilt_spatialContDiffAt  {u : TimeVelocity n → ℝ}
    {D : HypoellipticAleksandrov.Parabolic.Region n} {z : TimeVelocity n} (hu : IsScalarC12On u D)
    (hz : z ∈ D) (ε r₁ : ℝ) :
    ContDiffAt ℝ 2 (fun y  => terminalTilt u ε r₁ (z.1, y)) z.2 := by
  simpa [terminalTilt] using (hu.spatialSlice_contDiffAt hz).sub contDiffAt_const

private theorem timeDerivative_terminalTilt_nonpos_of_inset_localMax
     {α r₁ : ℝ} {Ω : PDE.VelocityRegion n} {w : TimeVelocity n → ℝ}
    {z : TimeVelocity n} (hz : z ∈ insetActive α r₁ Ω)
    (hmax : IsLocalMaxOn w (_root_.HypoellipticAleksandrov.Parabolic.scalarParabolicClosedCylinder α r₁ Ω) z)
    (hderiv : HasDerivAt (fun r  => w (r, z.2)) (scalarTimeDerivative w z) z.1) :
    scalarTimeDerivative w z ≤ 0 := by


  have hnonpos := (show IsLocalMaxOn (fun r  => w (r, z.2)) (Set.Icc α r₁) z.1 by
      simpa only [Function.comp_def, id_eq] using hmax.comp_continuousOn
        (s := Set.Icc α r₁)
        (by intro r hr; exact ⟨hr, subset_closure hz.2⟩)
        (continuous_id.prodMk continuous_const).continuousOn ⟨hz.1.1, le_of_lt hz.1.2⟩).hasFDerivWithinAt_nonpos hderiv.hasFDerivAt.hasFDerivWithinAt
    (by
        apply sub_mem_posTangentConeAt_of_segment_subset
        intro s hs
        exact ⟨le_trans hz.1.1 (segment_subset_Icc  (le_of_lt hz.1.2) hs).1,
          (segment_subset_Icc  (le_of_lt hz.1.2) hs).2⟩)


  exact nonpos_of_mul_nonpos_right (hnonpos) (sub_pos.mpr hz.1.2)

private theorem scalarOperator_nonpos_at_inset_tilt_max
     {r₀ α r₁ : ℝ} {Ω : PDE.VelocityRegion n} (hΩopen : IsOpen Ω)
    (hr₀α : r₀ < α) (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n) (u : TimeVelocity n → ℝ)
    (huC12 : IsScalarC12On u (scalarParabolicOpenCylinder r₀ r₁ Ω))
    (haPsd : ∀ r y, (a r y).PosSemidef) {ε : ℝ} {z : TimeVelocity n}
    (hz : z ∈ insetActive α r₁ Ω)
    (hmax : IsLocalMaxOn (terminalTilt u ε r₁) (_root_.HypoellipticAleksandrov.Parabolic.scalarParabolicClosedCylinder α r₁ Ω) z) :
    scalarParabolicOperator a b u z + ε ≤ 0 := by
  have hzopen  :=
    insetActive_subset_original_open hr₀α hz
  have hspatialMax  :=
    spatial_localMax_of_inset_localMax hΩopen hz hmax
  have htiltDiff  :=
    terminalTilt_spatialContDiffAt huC12 hzopen ε r₁

  have hgradient : scalarSpatialGradient u z = 0 := by
    rw [← terminalTilt_spatialGradient_eq]
    exact (scalarSpatialGradient_eq_zero_of_spatial_localMax htiltDiff hspatialMax)



  have hcontraction  :=
    matrixContraction_nonpos_of_psd_neg (haPsd z.1 z.2) (by
        rw [← terminalTilt_spatialHessian_eq]
        exact (neg_scalarSpatialHessian_posSemidef_of_spatial_localMax htiltDiff hspatialMax)) (scalarSpatialHessian_isSymm_of_contDiffAt (huC12.spatialSlice_contDiffAt hzopen))
  have htimeTilt : scalarTimeDerivative (terminalTilt u ε r₁) z ≤ 0 := by

    exact timeDerivative_terminalTilt_nonpos_of_inset_localMax hz hmax
      (by
          rw [terminalTilt_timeDerivative_eq huC12 hzopen ε r₁]
          convert (huC12.timeSlice_hasDerivAt hzopen).sub
            ((hasDerivAt_const (x := z.1) (c := ε)).mul
              ((hasDerivAt_const (x := z.1) (c := r₁)).sub (hasDerivAt_id z.1))) using 1
          all_goals simp only [Pi.sub_def, Pi.mul_def, id_eq, terminalTilt] <;> ring)
  rw [terminalTilt_timeDerivative_eq huC12 hzopen ε r₁] at htimeTilt
  rw [scalarParabolicOperator_apply, hgradient]
  simp only [PDE.vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  linarith

variable {Ω : PDE.VelocityRegion n}

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
    ∀ z ∈ _root_.HypoellipticAleksandrov.Parabolic.scalarParabolicClosedCylinder α r₁ Ω, terminalTilt u ε r₁ z ≤ M := by
  intro z hz
  by_cases hKempty : (_root_.HypoellipticAleksandrov.Parabolic.scalarParabolicClosedCylinder α r₁ Ω).Nonempty
  · obtain ⟨zmax, hzmax, hmax⟩ :=
      (isCompact_insetCylinder hΩbounded).exists_isMaxOn hKempty
        (terminalTilt_continuousOn (hu.mono (by
          rintro q ⟨⟨hqα, hqr₁⟩, hqΩ⟩
          exact ⟨⟨le_trans (le_of_lt hr₀α) hqα, hqr₁⟩, hqΩ⟩)) ε r₁)

    by_cases hzactive : zmax ∈ insetActive α r₁ Ω
    · have hnonpos := scalarOperator_nonpos_at_inset_tilt_max hΩopen hr₀α a b u
        huC12 haPsd hzactive hmax.localize
      have hsubmax := hsub zmax
        (insetActive_subset_original_open hr₀α hzactive)
      linarith
    ·
      exact (hmax hz).trans (by
          have hzmaxBoundary : zmax ∈ _root_.HypoellipticAleksandrov.Parabolic.scalarParabolicClosedCylinder α r₁ Ω \ insetActive α r₁ Ω :=
            ⟨hzmax, hzactive⟩
          rw [insetCylinder_diff_insetActive_eq hΩopen hαr₁] at hzmaxBoundary
          rcases hzmaxBoundary with hterminalFace | hlateralFace
          · calc
              terminalTilt u ε r₁ zmax ≤ u zmax := by
                dsimp [terminalTilt]
                exact sub_le_self _ (mul_nonneg (le_of_lt hε)
                  (sub_nonneg.mpr hterminalFace.1.le))
              _ ≤ M := hterminal zmax hterminalFace
          · calc
              terminalTilt u ε r₁ zmax ≤ u zmax := by
                dsimp [terminalTilt]
                exact sub_le_self _ (mul_nonneg (le_of_lt hε)
                  (sub_nonneg.mpr hlateralFace.1.2))
              _ ≤ M := hlateral zmax (⟨⟨le_trans (le_of_lt hr₀α) hlateralFace.1.1,
                  hlateralFace.1.2⟩, hlateralFace.2⟩))
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
  let sharedTerm_c0632c40d3 := (u (r, y) - M)
  by_contra hnot

  let α : ℝ := (r₀ + r) / 2


  have hzinset : (r, y) ∈ _root_.HypoellipticAleksandrov.Parabolic.scalarParabolicClosedCylinder α r₁ Ω :=
    ⟨⟨le_of_lt (by dsimp [α]; linarith), le_of_lt hrr₁⟩, hyclosure⟩
  let ε : ℝ := (sharedTerm_c0632c40d3) / (2 * (r₁ - r))
  have hgap  := sub_pos.mpr hrr₁

  have htilt := le_on_insetCylinder_of_terminal_lateral_le hΩopen hΩbounded (show r₀ < α by dsimp [α]; linarith) (show α < r₁ by dsimp [α]; linarith) a b
    haPsd u hu huC12 hsub (show 0 < ε from div_pos (sub_pos.mpr (lt_of_not_ge hnot)) (by positivity)) hterminal hlateral (z := (r, y)) hzinset
  dsimp [terminalTilt, ε] at htilt
  have hdenom : 2 * (r₁ - r) ≠ 0 := by positivity
  have hhalf : (sharedTerm_c0632c40d3) / (2 * (r₁ - r)) * (r₁ - r) =
      (sharedTerm_c0632c40d3) / 2 := by
    field_simp [hdenom]
  rw [hhalf] at htilt
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



      apply le_of_tendsto ((hu (r₀, y) ⟨⟨le_rfl, le_of_lt hr⟩,
        subset_closure hyΩ⟩).tendsto.comp (by
            rw [tendsto_nhdsWithin_iff]
            refine ⟨(by
                rw [nhds_prod_eq]
                exact (show Tendsto t atTop (𝓝 r₀) by
                    dsimp [t]
                    simpa using tendsto_const_nhds.add
                      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))).prodMk (tendsto_const_nhds )), ?_⟩
            filter_upwards with k
            have hk : 0 < (k : ℝ) + 1 := by positivity

            have hprod : (r₁ - r₀) * (1 / ((k : ℝ) + 1)) ≤ r₁ - r₀ :=
              by simpa using mul_le_mul_of_nonneg_left (show 1 / ((k : ℝ) + 1) ≤ 1 from (div_le_one₀ hk).mpr (by linarith)) (le_of_lt (sub_pos.mpr hr))
            exact ⟨⟨by dsimp [t]; nlinarith [one_div_pos.mpr hk],
              by dsimp [t]; nlinarith⟩, subset_closure hyΩ⟩))
      filter_upwards [eventually_ge_atTop 1] with k hkNat
      have hk : 0 < (k : ℝ) + 1 := by positivity


      have hprod : (r₁ - r₀) * (1 / ((k : ℝ) + 1)) < r₁ - r₀ :=
        by simpa using mul_lt_mul_of_pos_left ((div_lt_one₀ hk).mpr (show 1 < (k : ℝ) + 1 by
            exact_mod_cast Nat.lt_succ_of_le hkNat)) (sub_pos.mpr hr)
      exact le_at_strictly_later_time hΩopen hΩbounded
        (by dsimp [t]; nlinarith [one_div_pos.mpr hk])
        (by dsimp [t]; nlinarith) a b haPsd u hu huC12 hsub hterminal hlateral
        (subset_closure hyΩ)
    ·
      exact hlateral (r₀, y) ⟨⟨le_rfl, le_of_lt hr⟩, (by
          rw [hΩopen.frontier_eq]
          exact ⟨hyclosure, hyΩ⟩)⟩
  · by_cases hrterminal : r = r₁
    · exact hterminal (r, y) ⟨hrterminal, hyclosure⟩
    · exact le_at_strictly_later_time hΩopen hΩbounded
        (lt_of_le_of_ne hr₀ (Ne.symm hyr₀)) (lt_of_le_of_ne hr₁ hrterminal)
        a b haPsd u hu huC12 hsub hterminal hlateral hyclosure

end HypoellipticAleksandrov.Parabolic
