module

public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifier
public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.Analysis.Calculus.FDeriv.Comp
import Batteries.Tactic.Alias
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder





/-!
# Weak derivatives and spacetime mollification

This file supplies the translated-test infrastructure for commuting ambient
raw weak derivatives with the fixed spacetime mollifier.
-/

 public section



open MeasureTheory Set
open scoped Convolution Pointwise

namespace HypoellipticAleksandrov.Parabolic.SpacetimeMollifier

variable {d : ℕ} {ε : ℝ}

private theorem translatedKernel_contDiff
     (z : TimeVelocity d) :
    ContDiff ℝ PDE.smoothOrder
      (fun y  => spacetimeMollifier ε (z - y)) := (spacetimeMollifier_contDiff ε).comp (contDiff_const.sub contDiff_id)

private theorem translatedKernel_hasCompactSupport
     (hε : 0 < ε) (z : TimeVelocity d) :
    HasCompactSupport
      (fun y  => spacetimeMollifier ε (z - y)) := (HasCompactSupport.of_support_subset_isCompact
  (IsCompact.image (HasCompactSupport.isCompact (spacetimeMollifier_hasCompactSupport hε))
    (Continuous.sub continuous_const continuous_id))
  fun ⦃y⦄ hy => Exists.intro (z - y) ⟨subset_tsupport (spacetimeMollifier ε) hy, sub_sub_cancel z y⟩)

private theorem fderiv_translatedKernel_apply
     (z y q : TimeVelocity d) :
    fderiv ℝ (fun w  => spacetimeMollifier ε (z - w)) y q =
      -(fderiv ℝ (spacetimeMollifier (d := d) ε) (z - y) q) := by

  have ha : HasFDerivAt (fun w  => z - w)
      (-(ContinuousLinearMap.id ℝ (TimeVelocity d))) y := by
    simpa only [Pi.sub_def, id_eq, zero_sub] using
      (hasFDerivAt_const (𝕜 := ℝ) (x := y) (c := z)).sub
        (hasFDerivAt_id  y)
  change fderiv ℝ (spacetimeMollifier ε ∘ fun w  => z - w) y q = _
  rw [fderiv_comp y ((spacetimeMollifier_contDiff ε).differentiable (by simp) (z - y)) ha.differentiableAt]
  rw [ha.fderiv]
  simp

variable (hε : 0 < ε)

include hε
private theorem fderiv_spacetimeMollification_apply

    (u du : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (huLoc : LocallyIntegrable u
      )
    (hduLoc : LocallyIntegrable du
      )
    (q : TimeVelocity d)
    (hu : ∀ φ : HypoellipticAleksandrov.Parabolic.ScalarField d,
      ContDiff ℝ PDE.smoothOrder φ → HasCompactSupport φ → tsupport φ ⊆ Set.univ →
      (∫ y in Set.univ, u y * fderiv ℝ φ y q
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
        -∫ y in Set.univ, du y * φ y
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
    (z : TimeVelocity d) :
    fderiv ℝ (spacetimeMollification ε u) z q =
      spacetimeMollification ε du z := by
  let sharedTerm_b64a3dedfe := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
  let ρ : HypoellipticAleksandrov.Parabolic.ScalarField d := spacetimeMollifier ε
  let φ  := fun y => ρ (z - y)




  have hintegrals :
      (∫ y : TimeVelocity d, fderiv ℝ ρ (z - y) q * u y
        ∂sharedTerm_b64a3dedfe) =
        ∫ y : TimeVelocity d, ρ (z - y) * du y
          ∂sharedTerm_b64a3dedfe := neg_injective (by
              calc
                -(∫ y, fderiv ℝ ρ (z - y) q * u y ∂sharedTerm_b64a3dedfe) =
                    ∫ y, u y * fderiv ℝ φ y q ∂sharedTerm_b64a3dedfe := by
                  rw [← integral_neg]
                  apply integral_congr_ae
                  exact Filter.Eventually.of_forall fun y => by
                    dsimp [φ, ρ]
                    rw [fderiv_translatedKernel_apply z y q]
                    ring
                _ = -(∫ y, du y * φ y ∂sharedTerm_b64a3dedfe) := by
                  simpa only [setIntegral_univ] using (hu φ (translatedKernel_contDiff z) (translatedKernel_hasCompactSupport hε z) (Set.subset_univ _))
                _ = -(∫ y, ρ (z - y) * du y ∂sharedTerm_b64a3dedfe) := by
                  congr 1
                  apply integral_congr_ae
                  exact Filter.Eventually.of_forall fun y => by
                    simp only [φ]
                    ring)
  have hduConvExists : MeasureTheory.ConvolutionExistsAt
      ρ du z (ContinuousLinearMap.lsmul ℝ ℝ)
      sharedTerm_b64a3dedfe :=
    (spacetimeMollifier_hasCompactSupport hε).convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (spacetimeMollifier_contDiff ε).continuous hduLoc z

  have hderiv := (spacetimeMollifier_hasCompactSupport hε).hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) ((spacetimeMollifier_contDiff ε).of_le (by simp))
      huLoc z




  unfold spacetimeMollification
  rw [hderiv.fderiv]
  rw [MeasureTheory.convolution_eq_swap]
  calc
    (∫ y : TimeVelocity d,
        ((ContinuousLinearMap.precompL (TimeVelocity d)
          (ContinuousLinearMap.lsmul ℝ ℝ))
            (fderiv ℝ (spacetimeMollifier ε) (z - y))) (u y)
        ∂sharedTerm_b64a3dedfe) q =
        ∫ y : TimeVelocity d,
          (((ContinuousLinearMap.precompL (TimeVelocity d)
            (ContinuousLinearMap.lsmul ℝ ℝ))
              (fderiv ℝ (spacetimeMollifier ε) (z - y))) (u y)) q
          ∂sharedTerm_b64a3dedfe := ((ContinuousLinearMap.apply ℝ ℝ q).integral_comp_comm (by
              apply MeasureTheory.convolutionExistsAt_iff_integrable_swap.mp
              exact (((spacetimeMollifier_hasCompactSupport hε).fderiv ℝ).convolutionExists_left _ ((spacetimeMollifier_contDiff ε).continuous_fderiv (by simp)) huLoc z))).symm
    _ = ∫ y, fderiv ℝ ρ (z - y) q * u y
          ∂sharedTerm_b64a3dedfe := rfl
    _ = ∫ y, ρ (z - y) * du y
        ∂sharedTerm_b64a3dedfe := hintegrals
    _ = (spacetimeMollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        sharedTerm_b64a3dedfe] du) z := by
      by_cases hI : Integrable
          (fun y  => ρ (z - y) * du y)
          sharedTerm_b64a3dedfe
      · rw [MeasureTheory.convolution_lsmul_swap]
        rfl
      · exact (hI (by
          simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
            (MeasureTheory.convolutionExistsAt_iff_integrable_swap.mp hduConvExists))).elim

private theorem spacetimeMollification_congr_on_of_eqOn_thickening_aux

    {K : HypoellipticAleksandrov.Parabolic.Region d}
    {f g : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hfg : Set.EqOn f g (Metric.thickening ε K)) :
    Set.EqOn (spacetimeMollification ε f)
      (spacetimeMollification ε g) K := by
  intro z hz
  unfold spacetimeMollification MeasureTheory.convolution
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hρ : spacetimeMollifier  ε x = 0
    · simp [hρ]
    · have hxball : x ∈ Metric.ball (0 : TimeVelocity d) ε := by
        rw [← spacetimeMollifier_support hε]
        exact hρ

      change spacetimeMollifier ε x * f (z - x) =
        spacetimeMollifier ε x * g (z - x)
      rw [hfg (by
          apply Metric.mem_thickening_iff.mpr
          refine ⟨z, hz, ?_⟩
          simpa [dist_eq_norm] using hxball)]

/-- Ambient raw weak time differentiation commutes with the fixed positive-
radius spacetime mollifier. -/
theorem timeDerivative_spacetimeMollification

    (u du : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (huLoc : LocallyIntegrable u
      )
    (hduLoc : LocallyIntegrable du
      )
    (hu : HasWeakTimeDerivOn Set.univ u du) :
    timeDerivative (spacetimeMollification ε u) =
      spacetimeMollification ε du := by
  funext z
  exact fderiv_spacetimeMollification_apply hε u du huLoc hduLoc (1, 0) hu z

/-- Ambient raw weak differentiation in one velocity coordinate commutes with
the fixed positive-radius spacetime mollifier. -/
theorem velocityGradient_spacetimeMollification

    (i : Fin d) (u dui : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (huLoc : LocallyIntegrable u
      )
    (hduiLoc : LocallyIntegrable dui
      )
    (hu : HasWeakVelocityPartialDerivOn Set.univ i u dui) :
    (fun z => velocityGradient (spacetimeMollification ε u) z i) =
      spacetimeMollification ε dui := by
  funext z
  exact fderiv_spacetimeMollification_apply hε u dui huLoc hduiLoc
    _ hu z

/-- Convolution by the fixed positive-radius kernel only reads a function on
the open radius thickening of the evaluation carrier. -/
alias spacetimeMollification_congr_on_of_eqOn_thickening := _root_.HypoellipticAleksandrov.Parabolic.SpacetimeMollifier.spacetimeMollification_congr_on_of_eqOn_thickening_aux


end HypoellipticAleksandrov.Parabolic.SpacetimeMollifier
