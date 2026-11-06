module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
public import HypoellipticAleksandrov.Parabolic.ScalarMaximum
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Parabolic.MinimumPrinciple
import all HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
import all HypoellipticAleksandrov.KineticAleksandrov.Lieberman.TerminalLift
import all HypoellipticAleksandrov.Parabolic.Derivatives
import all HypoellipticAleksandrov.Parabolic.ScalarMaximum

open private HypoellipticAleksandrov.Parabolic.scalarSpatialHessian_quadratic_eq from HypoellipticAleksandrov.Parabolic.ScalarMaximum
open private HypoellipticAleksandrov.KineticAleksandrov.Lieberman.scalarSpatialHessian_apply_eq_sndFDeriv from HypoellipticAleksandrov.KineticAleksandrov.Lieberman.TerminalLift
open private HypoellipticAleksandrov.KineticAleksandrov.hasDerivAt_deriv_restrict_affine_line_of_contDiffAt from HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
open private HypoellipticAleksandrov.Parabolic.neg_scalarSpatialHessian_posSemidef_of_spatial_localMax from HypoellipticAleksandrov.Parabolic.ScalarMaximum
open private HypoellipticAleksandrov.Parabolic.hasDerivAt_fderiv_restrict_affine_line from HypoellipticAleksandrov.Parabolic.Derivatives
open private HypoellipticAleksandrov.Parabolic.deriv_deriv_nonpos_of_isLocalMax from HypoellipticAleksandrov.Parabolic.Derivatives
open private HypoellipticAleksandrov.KineticAleksandrov.fderiv_fderiv_apply_nonpos_of_isLocalMax_affineLine from HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
open private HypoellipticAleksandrov.Parabolic.scalarSpatialGradient_eq_zero_of_spatial_localMax from HypoellipticAleksandrov.Parabolic.ScalarMaximum
open private HypoellipticAleksandrov.Parabolic.matrixContraction_nonpos_of_psd_neg from HypoellipticAleksandrov.Parabolic.ScalarMaximum
open private HypoellipticAleksandrov.Parabolic.scalarSpatialHessian_isSymm_of_contDiffAt from HypoellipticAleksandrov.Parabolic.ScalarMaximum
open private HypoellipticAleksandrov.Parabolic.hasDerivAt_affine_line from HypoellipticAleksandrov.Parabolic.Derivatives
section
open private HypoellipticAleksandrov.Parabolic.scalarOperator_nonpos_at_inset_tilt_max from HypoellipticAleksandrov.Parabolic.ScalarMaximum
private alias _sharedProof_254_0 := HypoellipticAleksandrov.Parabolic.scalarOperator_nonpos_at_inset_tilt_max
end
section
open private HypoellipticAleksandrov.Parabolic.terminalTilt_spatialHessian_eq from HypoellipticAleksandrov.Parabolic.ScalarMaximum
private alias _sharedProof_97_0 := HypoellipticAleksandrov.Parabolic.terminalTilt_spatialHessian_eq
end
section
open private HypoellipticAleksandrov.Parabolic.timeDerivative_terminalTilt_nonpos_of_inset_localMax from HypoellipticAleksandrov.Parabolic.ScalarMaximum
private alias _sharedProof_31_0 := HypoellipticAleksandrov.Parabolic.timeDerivative_terminalTilt_nonpos_of_inset_localMax
end
section
open private HypoellipticAleksandrov.Parabolic.insetCylinder_diff_insetActive_eq from HypoellipticAleksandrov.Parabolic.ScalarMaximum
private alias _sharedProof_6_0 := HypoellipticAleksandrov.Parabolic.insetCylinder_diff_insetActive_eq
end
section
open private HypoellipticAleksandrov.Parabolic.terminalTilt_timeDerivative_eq from HypoellipticAleksandrov.Parabolic.ScalarMaximum
private alias _sharedProof_267_0 := HypoellipticAleksandrov.Parabolic.terminalTilt_timeDerivative_eq
end
section
open private HypoellipticAleksandrov.Parabolic.spatial_localMax_of_inset_localMax from HypoellipticAleksandrov.Parabolic.ScalarMaximum
private alias _sharedProof_17_0 := HypoellipticAleksandrov.Parabolic.spatial_localMax_of_inset_localMax
end


/-!
# Scalar zero-order backward parabolic maximum principle

This file proves the scalar backward maximum principle with a nonpositive
zero-order coefficient on an arbitrary open bounded velocity domain.  The
initial face is handled by compact cylinders whose lower time is strictly later
than the original initial time, followed by closed-cylinder continuity.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Set Matrix
open scoped MatrixOrder Topology

variable {n : ℕ}

variable (α r₁ : ℝ) (Ω : PDE.VelocityRegion n)

private def insetCylinder   :
    HypoellipticAleksandrov.Parabolic.Region n :=
  Set.Icc α r₁ ×ˢ closure Ω

private def insetActive   :
    HypoellipticAleksandrov.Parabolic.Region n :=
  Set.Ico α r₁ ×ˢ Ω

private def terminalTilt  (u : TimeVelocity n → ℝ) (ε r₁ : ℝ) :
    TimeVelocity n → ℝ :=
  fun z => u z - ε * (r₁ - z.1)

private theorem isCompact_insetCylinder  {α r₁ : ℝ}
    {Ω : PDE.VelocityRegion n} (hΩbounded : Bornology.IsBounded Ω) :
    IsCompact (insetCylinder α r₁ Ω) :=
  isCompact_Icc.prod hΩbounded.isCompact_closure

private theorem insetActive_subset_original_open  {r₀ α r₁ : ℝ}
    {Ω : PDE.VelocityRegion n} (hr₀α : r₀ < α) :
    insetActive α r₁ Ω ⊆ scalarParabolicOpenCylinder r₀ r₁ Ω := by
  rintro z ⟨⟨hzα, hzr₁⟩, hzΩ⟩
  exact ⟨⟨lt_of_lt_of_le hr₀α hzα, hzr₁⟩, hzΩ⟩

private theorem insetCylinder_diff_insetActive_eq  {α r₁ : ℝ}
    {Ω : PDE.VelocityRegion n} (hΩopen : IsOpen Ω) (hαr₁ : α < r₁) :
    insetCylinder α r₁ Ω \ insetActive α r₁ Ω =
      scalarParabolicTerminalFace r₁ Ω ∪
        (Set.Icc α r₁ ×ˢ frontier Ω) := (_sharedProof_6_0 hΩopen hαr₁)
















variable {n : ℕ}





















variable (u : TimeVelocity n → ℝ) (ε r₁ : ℝ) (z : TimeVelocity n)

private theorem terminalTilt_spatialGradient_eq   :
    scalarSpatialGradient (terminalTilt u ε r₁) z = scalarSpatialGradient u z := by
  ext i
  simp [terminalTilt, scalarSpatialGradient, PDE.classicalGradient,
    fderiv_sub_const]

private theorem terminalTilt_spatialHessian_eq   :
    scalarSpatialHessian (terminalTilt u ε r₁) z = scalarSpatialHessian u z := (_sharedProof_97_0 u ε r₁ z)


variable {u : TimeVelocity n → ℝ}

private theorem terminalTilt_timeDerivative_eq
    {D : HypoellipticAleksandrov.Parabolic.Region n} {z : TimeVelocity n} (hu : IsScalarC12On u D)
    (hz : z ∈ D) (ε r₁ : ℝ) :
    scalarTimeDerivative (terminalTilt u ε r₁) z = scalarTimeDerivative u z + ε := (_sharedProof_267_0 hu hz ε r₁)


private theorem terminalTilt_continuousOn
    {K : HypoellipticAleksandrov.Parabolic.Region n} (hu : ContinuousOn u K) (ε r₁ : ℝ) :
    ContinuousOn (terminalTilt u ε r₁) K := by
  apply hu.sub
  fun_prop









private theorem scalarOperator_nonpos_at_inset_tilt_max
     {r₀ α r₁ : ℝ} {Ω : PDE.VelocityRegion n} (hΩopen : IsOpen Ω)
    (hr₀α : r₀ < α) (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n) (u : TimeVelocity n → ℝ)
    (huC12 : IsScalarC12On u (scalarParabolicOpenCylinder r₀ r₁ Ω))
    (haPsd : ∀ r y, (a r y).PosSemidef) {ε : ℝ} {z : TimeVelocity n}
    (hz : z ∈ insetActive α r₁ Ω)
    (hmax : IsLocalMaxOn (terminalTilt u ε r₁) (insetCylinder α r₁ Ω) z) :
    scalarParabolicOperator a b u z + ε ≤ 0 := (_sharedProof_254_0 hΩopen hr₀α a b u huC12 haPsd hz hmax)


variable {Ω : PDE.VelocityRegion n}

private theorem le_on_insetCylinder_of_zeroOrder_terminal_lateral_le
      {r₀ α r₁ : ℝ}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hr₀α : r₀ < α) (hαr₁ : α < r₁) (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n) (c : ℝ → PDE.Vec n → ℝ)
    (haPsd : ∀ r y, (a r y).PosSemidef)
    (hc : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω, c z.1 z.2 ≤ 0)
    (w : TimeVelocity n → ℝ)
    (hw : ContinuousOn w (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hwC12 : IsScalarC12On w (scalarParabolicOpenCylinder r₀ r₁ Ω))
    (hPDE : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      0 ≤ scalarParabolicZeroOrderOperator a b c w z)
    {ε : ℝ} (hε : 0 < ε)
    (hterminal : ∀ z ∈ scalarParabolicTerminalFace r₁ Ω, w z ≤ 0)
    (hlateral : ∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, w z ≤ 0) :
    ∀ z ∈ insetCylinder α r₁ Ω, terminalTilt w ε r₁ z ≤ 0 := by
  intro z hz
  by_cases hKempty : (insetCylinder α r₁ Ω).Nonempty
  · obtain ⟨zmax, hzmax, hmax⟩ :=
      (isCompact_insetCylinder hΩbounded).exists_isMaxOn hKempty
        (terminalTilt_continuousOn (hw.mono (by
          rintro q ⟨⟨hqα, hqr₁⟩, hqΩ⟩
          exact ⟨⟨le_trans (le_of_lt hr₀α) hqα, hqr₁⟩, hqΩ⟩)) ε r₁)
    refine (hmax hz).trans ?_
    by_cases hzactive : zmax ∈ insetActive α r₁ Ω
    · by_contra hnot

      have hzopen  :=
        insetActive_subset_original_open hr₀α hzactive
      have hprincipal := scalarOperator_nonpos_at_inset_tilt_max hΩopen hr₀α a b w
        hwC12 haPsd hzactive hmax.localize
      have hcAt  := hc zmax hzopen
      have hctilt  :=
        mul_nonpos_of_nonpos_of_nonneg hcAt (lt_of_not_ge hnot).le


      have hcorrection  :=
        mul_nonneg (neg_nonneg.mpr hcAt) (mul_nonneg hε.le (sub_nonneg.mpr hzactive.1.2.le))
      have hzeroTiltEq :
          scalarParabolicZeroOrderOperator a b c (terminalTilt w ε r₁) zmax =
            scalarParabolicZeroOrderOperator a b c w zmax + ε -
              c zmax.1 zmax.2 * (ε * (r₁ - zmax.1)) := by
        simp only [scalarParabolicZeroOrderOperator_apply,
          terminalTilt_timeDerivative_eq hwC12 hzopen ε r₁,
          terminalTilt_spatialHessian_eq, terminalTilt_spatialGradient_eq]
        dsimp [terminalTilt]
        ring

      exact (not_lt_of_ge (show scalarParabolicZeroOrderOperator a b c (terminalTilt w ε r₁) zmax ≤ 0 by
          rw [scalarParabolicZeroOrderOperator_apply,
            terminalTilt_timeDerivative_eq hwC12 hzopen ε r₁,
            terminalTilt_spatialHessian_eq, terminalTilt_spatialGradient_eq]
          rw [scalarParabolicOperator_apply] at hprincipal
          linarith)) (show 0 < scalarParabolicZeroOrderOperator a b c (terminalTilt w ε r₁) zmax by
          rw [hzeroTiltEq]
          linarith [hPDE zmax hzopen])
    · have hzmaxBoundary : zmax ∈ insetCylinder α r₁ Ω \ insetActive α r₁ Ω :=
        ⟨hzmax, hzactive⟩
      rw [insetCylinder_diff_insetActive_eq hΩopen hαr₁] at hzmaxBoundary
      rcases hzmaxBoundary with hterminalFace | hlateralFace
      · calc
          terminalTilt w ε r₁ zmax ≤ w zmax := by
            dsimp [terminalTilt]
            exact sub_le_self _ (mul_nonneg hε.le
              (sub_nonneg.mpr hterminalFace.1.le))
          _ ≤ 0 := hterminal zmax hterminalFace
      · calc
          terminalTilt w ε r₁ zmax ≤ w zmax := by
            dsimp [terminalTilt]
            exact sub_le_self _ (mul_nonneg hε.le
              (sub_nonneg.mpr hlateralFace.1.2))
          _ ≤ 0 := hlateral zmax
            ⟨⟨le_trans (le_of_lt hr₀α) hlateralFace.1.1, hlateralFace.1.2⟩,
              hlateralFace.2⟩
  · exact (hKempty ⟨z, hz⟩).elim

/-
The remaining comparison assembly is deliberately kept below the pointwise
calculus lemmas so the initial-face continuity argument never enters the
active-set branch.
-/

private theorem le_zero_at_strictly_later_time
      {r₀ r r₁ : ℝ}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hr₀r : r₀ < r) (hrr₁ : r < r₁) (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n) (c : ℝ → PDE.Vec n → ℝ)
    (haPsd : ∀ r y, (a r y).PosSemidef)
    (hc : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω, c z.1 z.2 ≤ 0)
    (w : TimeVelocity n → ℝ)
    (hw : ContinuousOn w (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hwC12 : IsScalarC12On w (scalarParabolicOpenCylinder r₀ r₁ Ω))
    (hPDE : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      0 ≤ scalarParabolicZeroOrderOperator a b c w z)
    (hterminal : ∀ z ∈ scalarParabolicTerminalFace r₁ Ω, w z ≤ 0)
    (hlateral : ∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, w z ≤ 0)
    {y : PDE.Vec n} (hyclosure : y ∈ closure Ω) :
    w (r, y) ≤ 0 := by
  by_contra hnot

  let α : ℝ := (r₀ + r) / 2


  have hzinset : (r, y) ∈ insetCylinder α r₁ Ω :=
    ⟨⟨le_of_lt (by dsimp [α]; linarith), le_of_lt hrr₁⟩, hyclosure⟩
  let ε : ℝ := w (r, y) / (2 * (r₁ - r))
  have hgap  := sub_pos.mpr hrr₁

  have htilt := le_on_insetCylinder_of_zeroOrder_terminal_lateral_le
    hΩopen hΩbounded (show r₀ < α by dsimp [α]; linarith) (show α < r₁ by dsimp [α]; linarith) a b c haPsd hc w hw hwC12 hPDE (show 0 < ε from div_pos (lt_of_not_ge hnot) (by positivity)) hterminal hlateral
    (z := (r, y)) hzinset
  dsimp [terminalTilt, ε] at htilt
  have hdenom : 2 * (r₁ - r) ≠ 0 := by positivity
  have hhalf : w (r, y) / (2 * (r₁ - r)) * (r₁ - r) = w (r, y) / 2 := by
    field_simp [hdenom]
  rw [hhalf] at htilt
  linarith

/--
If the backward scalar operator with a nonpositive zero-order coefficient is
nonnegative on the open cylinder, then nonpositive terminal and lateral data
control the whole closed cylinder.  The proof uses strictly inset cylinders
before passing to the initial face by continuity.
-/
theorem scalar_le_zero_on_closedCylinder_of_zeroOrderOperator_nonneg
      {r₀ r₁ : ℝ}
    (hΩOpen : IsOpen Ω)
    (hΩBounded : Bornology.IsBounded Ω)
    (hr : r₀ < r₁)
    (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c : ℝ → PDE.Vec n → ℝ)
    (haContinuous : IsContinuousCoefficient a)
    (hbContinuous : Continuous (fun z : TimeVelocity n => b z.1 z.2))
    (haPsd : ∀ r y, (a r y).PosSemidef)
    (hc : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      c z.1 z.2 ≤ 0)
    (w : TimeVelocity n → ℝ)
    (hw : ContinuousOn w (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hwC12 : IsScalarC12On w (scalarParabolicOpenCylinder r₀ r₁ Ω))
    (hPDE : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      0 ≤ scalarParabolicZeroOrderOperator a b c w z)
    (hTerminal : ∀ z ∈ scalarParabolicTerminalFace r₁ Ω, w z ≤ 0)
    (hLateral : ∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, w z ≤ 0) :
    ∀ z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω, w z ≤ 0 := by


  intro z hz
  rcases z with ⟨r, y⟩
  rcases hz with ⟨⟨hr₀, hr₁⟩, hyclosure⟩
  by_cases hyr₀ : r = r₀
  · subst r
    by_cases hyΩ : y ∈ Ω
    · let t : ℕ → ℝ := fun k => r₀ + (r₁ - r₀) * (1 / ((k : ℝ) + 1))



      apply le_of_tendsto ((hw (r₀, y) ⟨⟨le_rfl, le_of_lt hr⟩,
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
      exact le_zero_at_strictly_later_time hΩOpen hΩBounded
        (by dsimp [t]; nlinarith [one_div_pos.mpr hk])
        (by dsimp [t]; nlinarith) a b c haPsd hc w hw hwC12 hPDE hTerminal hLateral
        (subset_closure hyΩ)
    ·
      exact hLateral (r₀, y) ⟨⟨le_rfl, le_of_lt hr⟩, (by
          rw [hΩOpen.frontier_eq]
          exact ⟨hyclosure, hyΩ⟩)⟩
  · by_cases hrterminal : r = r₁
    · exact hTerminal (r, y) ⟨hrterminal, hyclosure⟩
    · exact le_zero_at_strictly_later_time hΩOpen hΩBounded
        (lt_of_le_of_ne hr₀ (Ne.symm hyr₀)) (lt_of_le_of_ne hr₁ hrterminal)
        a b c haPsd hc w hw hwC12 hPDE hTerminal hLateral hyclosure

end HypoellipticAleksandrov.Parabolic
