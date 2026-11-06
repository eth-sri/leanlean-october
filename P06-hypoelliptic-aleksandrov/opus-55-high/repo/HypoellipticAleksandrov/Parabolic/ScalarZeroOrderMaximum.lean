module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
public import HypoellipticAleksandrov.Parabolic.ScalarMaximum

/-!
# Scalar zero-order backward parabolic maximum principle

This file proves the scalar backward maximum principle with a nonpositive
zero-order coefficient on an arbitrary open bounded velocity domain.  The
initial face is handled by compact cylinders whose lower time is strictly later
than the original initial time, followed by closed-cylinder continuity.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open Filter Set Matrix
open scoped MatrixOrder Topology

variable {n : ℕ} {A H : PDE.Mat n} {α r₁ : ℝ} {Ω : Set (PDE.Vec n)} {w : TimeVelocity n → ℝ} {u : TimeVelocity n → ℝ} {D : Set (TimeVelocity n)} {z : TimeVelocity n}



























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
      have htiltPos : 0 < terminalTilt w ε r₁ zmax := lt_of_not_ge hnot
      have hzopen : zmax ∈ scalarParabolicOpenCylinder r₀ r₁ Ω :=
        insetActive_subset_original_open hr₀α hzactive
      have hprincipal := scalarOperator_nonpos_at_inset_tilt_max hΩopen hr₀α a b w
        hwC12 haPsd hzactive hmax.localize
      have hcAt : c zmax.1 zmax.2 ≤ 0 := hc zmax hzopen
      have hctilt : c zmax.1 zmax.2 * terminalTilt w ε r₁ zmax ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hcAt htiltPos.le
      have hzeroTiltNonpos :
          scalarParabolicZeroOrderOperator a b c (terminalTilt w ε r₁) zmax ≤ 0 := by
        rw [scalarParabolicZeroOrderOperator_apply,
          terminalTilt_timeDerivative_eq hwC12 hzopen,
          terminalTilt_spatialHessian_eq, terminalTilt_spatialGradient_eq]
        rw [scalarParabolicOperator_apply] at hprincipal
        linarith
      have hfactor : 0 ≤ ε * (r₁ - zmax.1) :=
        mul_nonneg hε.le (sub_nonneg.mpr hzactive.1.2.le)
      have hcorrection : 0 ≤ -c zmax.1 zmax.2 * (ε * (r₁ - zmax.1)) :=
        mul_nonneg (neg_nonneg.mpr hcAt) hfactor
      have hzeroTiltEq :
          scalarParabolicZeroOrderOperator a b c (terminalTilt w ε r₁) zmax =
            scalarParabolicZeroOrderOperator a b c w zmax + ε -
              c zmax.1 zmax.2 * (ε * (r₁ - zmax.1)) := by
        simp only [scalarParabolicZeroOrderOperator_apply,
          terminalTilt_timeDerivative_eq hwC12 hzopen,
          terminalTilt_spatialHessian_eq, terminalTilt_spatialGradient_eq]
        dsimp [terminalTilt]
        ring
      grind
    · have hzmaxBoundary : zmax ∈ insetCylinder α r₁ Ω \ insetActive α r₁ Ω :=
        ⟨hzmax, hzactive⟩
      rw [insetCylinder_diff_insetActive_eq hΩopen hαr₁] at hzmaxBoundary
      rcases hzmaxBoundary with hterminalFace | hlateralFace
      · calc
          terminalTilt w ε r₁ zmax ≤ w zmax := by
            dsimp [terminalTilt]
            aesop
          _ ≤ 0 := hterminal zmax hterminalFace
      · calc
          terminalTilt w ε r₁ zmax ≤ w zmax := by
            dsimp [terminalTilt]
            simp_all
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
  have hpositive : 0 < w _ := lt_of_not_ge hnot
  let α  := (r₀ + r) / 2
  have hα0 : r₀ < α := by grind
  have hα1 : α < r₁ := by grind
  have hzinset : (r, y) ∈ insetCylinder α r₁ Ω :=
    ⟨⟨le_of_lt (by grind), le_of_lt hrr₁⟩, hyclosure⟩
  let ε  := w (r, y) / (2 * (r₁ - r))
  have hε : 0 < ε := div_pos hpositive (by positivity)
  have htilt := le_on_insetCylinder_of_zeroOrder_terminal_lateral_le
    hΩopen hΩbounded hα0 hα1 a b c haPsd hc w hw hwC12 hPDE hε hterminal hlateral
    (z := (r, y)) hzinset
  dsimp [terminalTilt] at htilt
  have hhalf : w (r, y) / (2 * (r₁ - r)) * (r₁ - r) = w (r, y) / 2 := by
    grind
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
      apply le_of_tendsto ((hw (r₀, y) ⟨⟨le_rfl, le_of_lt hr⟩,
        subset_closure hyΩ⟩).tendsto.comp hcurveWithin)
      filter_upwards [eventually_ge_atTop 1] with k hkNat
      have hk : 0 < (k : ℝ) + 1 := by positivity
      have hkone : 1 < (k : ℝ) + 1 := by
        aesop
      have hsmall : 1 / ((k : ℝ) + 1) < 1 := (div_lt_one₀ hk).mpr hkone
      have hprod : (r₁ - r₀) * (1 / (k + 1)) < r₁ - r₀ :=
        by simp_all
      exact le_zero_at_strictly_later_time hΩOpen hΩBounded
        (by aesop)
        (by linarith) a b c haPsd hc w hw hwC12 hPDE hTerminal hLateral
        (subset_closure hyΩ)
    · have hyfrontier : y ∈ frontier Ω := by
        rw [hΩOpen.frontier_eq]
        simp_all
      simp_all
  · by_cases hrterminal : r = r₁
    · simp_all
    · exact le_zero_at_strictly_later_time hΩOpen hΩBounded
        (lt_of_le_of_ne hr₀ (Ne.symm hyr₀)) (lt_of_le_of_ne hr₁ hrterminal)
        a b c haPsd hc w hw hwC12 hPDE hTerminal hLateral hyclosure

end HypoellipticAleksandrov.Parabolic
