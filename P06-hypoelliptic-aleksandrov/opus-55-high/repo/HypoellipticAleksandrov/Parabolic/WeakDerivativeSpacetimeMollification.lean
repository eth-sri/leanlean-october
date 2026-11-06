module

public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifier
public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Weak derivatives and spacetime mollification

This file supplies the translated-test infrastructure for commuting ambient
raw weak derivatives with the fixed spacetime mollifier.
-/

@[expose] public section


open Function MeasureTheory Set
open scoped Convolution Pointwise Topology

namespace HypoellipticAleksandrov.Parabolic.SpacetimeMollifier

variable {d : ℕ} {ε : ℝ}

private theorem translatedKernel_contDiff
     (z : TimeVelocity d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y : TimeVelocity d => spacetimeMollifier ε (z - y)) := (spacetimeMollifier_contDiff ε).comp (contDiff_const.sub contDiff_id)

private theorem translatedKernel_hasCompactSupport
     (hε : 0 < ε) (z : TimeVelocity d) :
    HasCompactSupport
      (fun y : TimeVelocity d => spacetimeMollifier ε (z - y)) := by
  let C  :=
    (fun x : TimeVelocity d => z - x) '' tsupport (spacetimeMollifier (d := d) ε)
  have hC : IsCompact C :=
    (spacetimeMollifier_hasCompactSupport hε).isCompact.image
      (continuous_const.sub continuous_id)
  apply HasCompactSupport.of_support_subset_isCompact hC
  intro y hy
  have hzy : z - y ∈ tsupport _ :=
    subset_tsupport _ hy
  grind

private theorem fderiv_translatedKernel_apply
     (z y q : TimeVelocity d) :
    fderiv ℝ (fun w : TimeVelocity d => spacetimeMollifier ε (z - w)) y q =
      -(fderiv ℝ (spacetimeMollifier (d := d) ε) (z - y) q) := by
  have hk : DifferentiableAt ℝ (spacetimeMollifier (d := d) ε) _ :=
    (spacetimeMollifier_contDiff ε).differentiable (by simp) (z - y)
  have ha : HasFDerivAt (fun w : TimeVelocity d => z - w)
      (-(ContinuousLinearMap.id ℝ (TimeVelocity d))) y := by
    fun_prop
  change fderiv ℝ (spacetimeMollifier ε ∘ fun w : TimeVelocity d => z - w) y q = _
  rw [fderiv_comp y hk ha.differentiableAt, ha.fderiv]
  simp

private theorem fderiv_spacetimeMollification_apply
     (hε : 0 < ε)
    (u du : TimeVelocity d → ℝ)
    (huLoc : LocallyIntegrable u
      (volume : Measure (TimeVelocity d)))
    (hduLoc : LocallyIntegrable du
      (volume : Measure (TimeVelocity d)))
    (q : TimeVelocity d)
    (hu : ∀ φ : TimeVelocity d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Set.univ →
      (∫ y in Set.univ, u y * fderiv ℝ φ y q
        ∂(volume : Measure (TimeVelocity d))) =
        -∫ y in Set.univ, du y * φ y
          ∂(volume : Measure (TimeVelocity d)))
    (z : TimeVelocity d) :
    fderiv ℝ (spacetimeMollification ε u) z q =
      spacetimeMollification ε du z := by
  let ρ : TimeVelocity d → ℝ := spacetimeMollifier ε
  let φ  := fun y => ρ (z - y)
  have hφSmooth : ContDiff ℝ _ φ := translatedKernel_contDiff z
  have hφCompact : HasCompactSupport φ := translatedKernel_hasCompactSupport hε z
  have hweak := hu φ hφSmooth hφCompact (Set.subset_univ _)
  have hweak' :
      -(∫ y : TimeVelocity d, fderiv ℝ ρ (z - y) q * u y
        ∂volume) =
        -(∫ y : TimeVelocity d, ρ (z - y) * du y
          ∂volume) := by
    calc
      -(∫ y, fderiv ℝ ρ _ q * u y ∂volume) =
          ∫ y, u y * fderiv ℝ φ y q ∂volume := by
        rw [← integral_neg]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          dsimp [φ]
          rw [fderiv_translatedKernel_apply]
          ring
      _ = -(∫ y, du y * φ y ∂volume) := by
        simp_all
      _ = -(∫ y, ρ _ * du y ∂volume) := by
        grind
  have hintegrals  := neg_injective hweak'
  have hduConvExists : MeasureTheory.ConvolutionExistsAt
      ρ du z (ContinuousLinearMap.lsmul ℝ ℝ)
      volume :=
    (spacetimeMollifier_hasCompactSupport hε).convolutionExists_left
      _
      (spacetimeMollifier_contDiff ε).continuous hduLoc z
  have hduIntegrable : Integrable
      (fun y : TimeVelocity d => ρ (z - y) * du y)
      volume := by
    simpa only [Function.comp_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      (MeasureTheory.convolutionExistsAt_iff_integrable_swap.mp hduConvExists)
  have hderiv := (spacetimeMollifier_hasCompactSupport hε).hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) ((spacetimeMollifier_contDiff ε).of_le (by simp))
      huLoc z
  have hdρCompact : HasCompactSupport (fderiv ℝ ρ) :=
    (spacetimeMollifier_hasCompactSupport hε).fderiv ℝ
  have hdρContinuous : Continuous (fderiv ℝ ρ) :=
    (spacetimeMollifier_contDiff ε).continuous_fderiv (by simp)
  have hconvExists : MeasureTheory.ConvolutionExistsAt
      (fderiv ℝ ρ) u z
      (ContinuousLinearMap.precompL _ (ContinuousLinearMap.lsmul ℝ ℝ))
      volume :=
    hdρCompact.convolutionExists_left _ hdρContinuous huLoc z
  have hderivIntegrable : Integrable
      (fun y : TimeVelocity d =>
        ((ContinuousLinearMap.precompL (TimeVelocity d)
          (ContinuousLinearMap.lsmul ℝ ℝ))
            (fderiv ℝ (spacetimeMollifier ε) (z - y))) (u y))
      volume := by
    apply MeasureTheory.convolutionExistsAt_iff_integrable_swap.mp
    omega
  unfold spacetimeMollification
  rw [hderiv.fderiv, MeasureTheory.convolution_eq_swap]
  calc
    (∫ y : TimeVelocity d,
        ((ContinuousLinearMap.precompL _
          _)
            _) _
        ∂volume) q =
        ∫ y : TimeVelocity d,
          (((ContinuousLinearMap.precompL _
            (ContinuousLinearMap.lsmul ℝ ℝ))
              _) _) q
          ∂volume := ((ContinuousLinearMap.apply ℝ ℝ q).integral_comp_comm hderivIntegrable).symm
    _ = ∫ y, fderiv ℝ ρ _ q * u y
          ∂volume := by
      aesop
    _ = ∫ y, ρ _ * du y
        ∂volume := hintegrals
    _ = (spacetimeMollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        volume] du) z := by
      by_cases hI : Integrable
          (fun y : TimeVelocity d => ρ (z - y) * du y)
          (volume : Measure (TimeVelocity d))
      · rw [MeasureTheory.convolution_lsmul_swap]
        aesop
      simp_all

private theorem spacetimeMollification_congr_on_of_eqOn_thickening_aux
     (hε : 0 < ε)
    {K : Set (TimeVelocity d)}
    {f g : TimeVelocity d → ℝ}
    (hfg : Set.EqOn f g (Metric.thickening ε K)) :
    Set.EqOn (spacetimeMollification ε f)
      (spacetimeMollification ε g) K := by
  intro z hz
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hρ : spacetimeMollifier (d := d) ε x = 0
    · grind
    · have hxball : x ∈ Metric.ball (0 : TimeVelocity d) ε := by
        rw [← spacetimeMollifier_support hε]
        exact hρ
      have hread : z - x ∈ Metric.thickening ε K := by
        apply Metric.mem_thickening_iff.mpr
        refine ⟨z, hz, ?_⟩
        simp_all
      grind

/-- Ambient raw weak time differentiation commutes with the fixed positive-
radius spacetime mollifier. -/
theorem timeDerivative_spacetimeMollification
     (hε : 0 < ε)
    (u du : TimeVelocity d → ℝ)
    (huLoc : LocallyIntegrable u
      (volume : Measure (TimeVelocity d)))
    (hduLoc : LocallyIntegrable du
      (volume : Measure (TimeVelocity d)))
    (hu : HasWeakTimeDerivOn Set.univ u du) :
    timeDerivative (spacetimeMollification ε u) =
      spacetimeMollification ε du := by
  funext z
  exact fderiv_spacetimeMollification_apply hε u du huLoc hduLoc _ hu z

/-- Ambient raw weak differentiation in one velocity coordinate commutes with
the fixed positive-radius spacetime mollifier. -/
theorem velocityGradient_spacetimeMollification
     (hε : 0 < ε)
    (i : Fin d) (u dui : TimeVelocity d → ℝ)
    (huLoc : LocallyIntegrable u
      (volume : Measure (TimeVelocity d)))
    (hduiLoc : LocallyIntegrable dui
      (volume : Measure (TimeVelocity d)))
    (hu : HasWeakVelocityPartialDerivOn Set.univ i u dui) :
    (fun z => velocityGradient (spacetimeMollification ε u) z i) =
      spacetimeMollification ε dui := by
  funext z
  exact fderiv_spacetimeMollification_apply hε u dui huLoc hduiLoc
    _ hu z

/-- Convolution by the fixed positive-radius kernel only reads a function on
the open radius thickening of the evaluation carrier. -/
theorem spacetimeMollification_congr_on_of_eqOn_thickening
     (hε : 0 < ε)
    {K : Set (TimeVelocity d)}
    {f g : TimeVelocity d → ℝ}
    (hfg : Set.EqOn f g (Metric.thickening ε K)) :
    Set.EqOn (spacetimeMollification ε f)
      (spacetimeMollification ε g) K :=
  spacetimeMollification_congr_on_of_eqOn_thickening_aux hε hfg

end HypoellipticAleksandrov.Parabolic.SpacetimeMollifier
