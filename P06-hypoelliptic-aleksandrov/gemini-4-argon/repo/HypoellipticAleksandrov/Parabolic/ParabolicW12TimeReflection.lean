module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTime
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesLocal
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Reflection of parabolic weak jets in time

This file transports the representative-level parabolic `W^{1,2,p}` data
through an affine reflection of the time coordinate.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

/- Applying the affine time reflection twice returns the original point. -/
theorem reverseTimeMap_involutive_private
    {d : ℕ} (r₁ : ℝ) (z : TimeVelocity d) :
    reverseTimeMap r₁ (reverseTimeMap r₁ z) = z := by
  rcases z with ⟨r, y⟩
  ext <;> simp [reverseTimeMap]

/- The affine time reflection `(r, y) ↦ (r₁ - r, y)` as a homeomorphism. -/
def reverseTimeHomeomorph {d : ℕ} (r₁ : ℝ) :
    TimeVelocity d ≃ₜ TimeVelocity d where
  toFun := reverseTimeMap r₁
  invFun := reverseTimeMap r₁
  left_inv := reverseTimeMap_involutive_private r₁
  right_inv := reverseTimeMap_involutive_private r₁
  continuous_toFun := (continuous_const.sub continuous_fst).prodMk continuous_snd
  continuous_invFun := (continuous_const.sub continuous_fst).prodMk continuous_snd

/- Evaluation of the affine reverse-time homeomorphism. -/
@[simp] theorem reverseTimeMap_involutive
    {d : ℕ} (r₁ : ℝ) (z : TimeVelocity d) :
    reverseTimeMap r₁ (reverseTimeMap r₁ z) = z :=
  reverseTimeMap_involutive_private r₁ z

/- Affine reverse time preserves time--velocity Lebesgue measure. -/
theorem reverseTimeMap_measurePreserving {d : ℕ} (r₁ : ℝ) :
    MeasurePreserving (reverseTimeMap r₁)
      (volume : Measure (TimeVelocity d)) volume := by
  let htime : MeasurePreserving (fun r : ℝ => r₁ - r)
      (volume : Measure ℝ) volume := by
    have hneg : MeasurePreserving (fun r : ℝ => -r)
        (volume : Measure ℝ) volume := by
      refine ⟨measurable_neg, ?_⟩
      rw [show (fun r : ℝ => -r) = fun r : ℝ => (-1 : ℝ) • r by
        funext r
        simp, Measure.map_addHaar_smul (volume : Measure ℝ) (by norm_num)]
      norm_num
    simpa only [sub_eq_add_neg, Function.comp_def] using
      (measurePreserving_add_left (volume : Measure ℝ) r₁).comp
        hneg
  have hprod := htime.prod (MeasurePreserving.id (volume : Measure (PDE.Vec d)))
  rw [volume_timeVelocity_eq_prod d]
  simpa only [reverseTimeMap, Function.uncurry_def, Function.comp_def, Prod.map_def, id_eq]
    using! hprod

/- Affine reverse time preserves the corresponding restricted measures. -/
theorem reverseTimeMap_measurePreserving_restrict
    {d : ℕ} (r₁ : ℝ) {U : Set (TimeVelocity d)}
    (hU : MeasurableSet U) :
    MeasurePreserving (reverseTimeMap r₁)
      (timeVelocityVolumeOn (reverseTimeMap r₁ ⁻¹' U))
      (timeVelocityVolumeOn U) :=
  (reverseTimeMap_measurePreserving r₁).restrict_preimage hU

private def reverseTimeLinear (d : ℕ) :
    TimeVelocity d →L[ℝ] TimeVelocity d :=
  (-ContinuousLinearMap.fst ℝ ℝ (PDE.Vec d)).prod
    (ContinuousLinearMap.snd ℝ ℝ (PDE.Vec d))

private theorem fderiv_comp_reverseTimeMap
    {d : ℕ} {r₁ : ℝ} {φ : TimeVelocity d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (z : TimeVelocity d) :
    fderiv ℝ (φ ∘ reverseTimeMap r₁) z =
      (fderiv ℝ φ (reverseTimeMap r₁ z)).comp (reverseTimeLinear d) := by
  have hφAt : HasFDerivAt φ (fderiv ℝ φ (reverseTimeMap r₁ z))
      (reverseTimeMap r₁ z) :=
    (hφ.differentiable (by simp) _).hasFDerivAt
  have _h_inl_15 : HasFDerivAt (reverseTimeMap r₁) (reverseTimeLinear d) z := by
    change HasFDerivAt (fun w : TimeVelocity d => (r₁ - w.1, w.2))
      (reverseTimeLinear d) z
    simpa only [reverseTimeLinear] using
      ((hasFDerivAt_fst (𝕜 := ℝ) (p := z)).const_sub r₁).prodMk
        (hasFDerivAt_snd (𝕜 := ℝ) (p := z))
  simpa only [Function.comp_def] using
    (hφAt.comp z _h_inl_15
).fderiv

private theorem timeDerivative_comp_reverseTimeMap
    {d : ℕ} {r₁ : ℝ} {φ : TimeVelocity d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (z : TimeVelocity d) :
    timeDerivative (φ ∘ reverseTimeMap r₁) z =
      -timeDerivative φ (reverseTimeMap r₁ z) := by
  unfold timeDerivative
  rw [fderiv_comp_reverseTimeMap hφ, ContinuousLinearMap.comp_apply]
  have hr : reverseTimeLinear d ((1, 0) : TimeVelocity d) = (-1, 0) := by
    simp [reverseTimeLinear]
  rw [hr]
  have hvec : ((-1, 0) : TimeVelocity d) = -((1, 0) : TimeVelocity d) := by
    ext <;> simp
  rw [hvec, map_neg]

private theorem velocityGradient_comp_reverseTimeMap
    {d : ℕ} {r₁ : ℝ} {φ : TimeVelocity d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (z : TimeVelocity d) :
    velocityGradient (φ ∘ reverseTimeMap r₁) z =
      velocityGradient φ (reverseTimeMap r₁ z) := by
  funext i
  unfold velocityGradient
  rw [fderiv_comp_reverseTimeMap hφ, ContinuousLinearMap.comp_apply]
  have hr : reverseTimeLinear d ((0, Pi.single i 1) : TimeVelocity d) =
      (0, Pi.single i 1) := by
    simp [reverseTimeLinear]
  rw [hr]

private theorem tsupport_comp_reverseTimeMap
    {d } (r₁ : ℝ) (φ : TimeVelocity d → ℝ) :
    tsupport (φ ∘ reverseTimeMap r₁) =
      reverseTimeMap r₁ ⁻¹' tsupport φ := by
  change closure (Function.support (φ ∘ ⇑(reverseTimeHomeomorph r₁))) =
    ⇑(reverseTimeHomeomorph r₁) ⁻¹' closure (Function.support φ)
  rw [Function.support_comp_eq_preimage]
  exact ((reverseTimeHomeomorph r₁).preimage_closure _).symm

/- Time reflection transports a weak time derivative with reversed sign. -/
theorem hasWeakTimeDerivOn_timeReflect
    {d U} {u du : TimeVelocity d → ℝ}
    (hU : MeasurableSet U) (h : HasWeakTimeDerivOn U u du) (r₁ : ℝ) :
    HasWeakTimeDerivOn (reverseTimeMap r₁ ⁻¹' U)
      (u ∘ reverseTimeMap r₁) ((fun x => -x) ∘ du ∘ reverseTimeMap r₁) := by
  intro φ hφ hφcompact hφsupport
  let e := reverseTimeHomeomorph (d := d) r₁
  let ψ := φ ∘ reverseTimeMap r₁
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    hφ.comp ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd)
  have hψcompact : HasCompactSupport ψ := hφcompact.comp_homeomorph e
  have hψsupport : tsupport ψ ⊆ U := by
    rw [tsupport_comp_reverseTimeMap]
    intro z hz
    simpa only [Set.mem_preimage, reverseTimeMap_apply, sub_sub_cancel] using! (hφsupport hz)
  have hw := h ψ hψ hψcompact hψsupport
  change (∫ z, (u ∘ reverseTimeMap r₁) z * timeDerivative φ z
      ∂timeVelocityVolumeOn (reverseTimeMap r₁ ⁻¹' U)) =
    -∫ z, ((fun x => -x) ∘ du ∘ reverseTimeMap r₁) z * φ z
      ∂timeVelocityVolumeOn (reverseTimeMap r₁ ⁻¹' U)
  change (∫ z, u z * timeDerivative ψ z ∂timeVelocityVolumeOn U) =
    -∫ z, du z * ψ z ∂timeVelocityVolumeOn U at hw
  have hmp := reverseTimeMap_measurePreserving_restrict r₁ hU
  have hleft :
      (∫ z, (u ∘ reverseTimeMap r₁) z * timeDerivative φ z
        ∂timeVelocityVolumeOn (reverseTimeMap r₁ ⁻¹' U)) =
      -(∫ z, u z * timeDerivative ψ z ∂timeVelocityVolumeOn U) := by
    rw [← hmp.integral_comp e.measurableEmbedding, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [ψ]
    rw [timeDerivative_comp_reverseTimeMap hφ]
    simp only [reverseTimeMap_apply]
    ring_nf
  have hright :
      (∫ z, ((fun x => -x) ∘ du ∘ reverseTimeMap r₁) z * φ z
        ∂timeVelocityVolumeOn (reverseTimeMap r₁ ⁻¹' U)) =
      -(∫ z, du z * ψ z ∂timeVelocityVolumeOn U) := by
    rw [← hmp.integral_comp e.measurableEmbedding, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [ψ]
    rw [sub_sub_cancel]
    ring
  rw [hleft, hright, hw]

/- Time reflection transports weak velocity partial derivatives. -/
theorem hasWeakVelocityPartialDerivOn_timeReflect
    {d U u dui} {i : Fin d}
    (hU : MeasurableSet U) (h : HasWeakVelocityPartialDerivOn U i u dui)
    (r₁ : ℝ) :
    HasWeakVelocityPartialDerivOn (reverseTimeMap r₁ ⁻¹' U) i
      (u ∘ reverseTimeMap r₁) (dui ∘ reverseTimeMap r₁) := by
  intro φ hφ hφcompact hφsupport
  let e := reverseTimeHomeomorph (d := d) r₁
  let ψ := φ ∘ reverseTimeMap r₁
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    hφ.comp ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd)
  have hψcompact : HasCompactSupport ψ := hφcompact.comp_homeomorph e
  have hψsupport : tsupport ψ ⊆ U := by
    rw [tsupport_comp_reverseTimeMap]
    intro z hz
    simpa only [Set.mem_preimage, reverseTimeMap_apply, sub_sub_cancel] using! (hφsupport hz)
  have hw := h ψ hψ hψcompact hψsupport
  change (∫ z, (u ∘ reverseTimeMap r₁) z * velocityGradient φ z i
      ∂timeVelocityVolumeOn (reverseTimeMap r₁ ⁻¹' U)) =
    -∫ z, (dui ∘ reverseTimeMap r₁) z * φ z
      ∂timeVelocityVolumeOn (reverseTimeMap r₁ ⁻¹' U)
  change (∫ z, u z * velocityGradient ψ z i ∂timeVelocityVolumeOn U) =
    -∫ z, dui z * ψ z ∂timeVelocityVolumeOn U at hw
  have hmp := reverseTimeMap_measurePreserving_restrict r₁ hU
  rw [← hmp.integral_comp e.measurableEmbedding,
    ← hmp.integral_comp e.measurableEmbedding] at hw
  have hgrad (z : TimeVelocity d) :
      velocityGradient ψ (reverseTimeMap r₁ z) i = velocityGradient φ z i := by
    simpa only [ψ, Function.comp_def, reverseTimeMap_involutive] using! (congrFun (velocityGradient_comp_reverseTimeMap (r₁ := r₁) hφ (reverseTimeMap r₁ z)) i)
  simp only [hgrad] at hw
  simp only [ψ, reverseTimeMap_involutive, Function.comp_def] at hw
  simpa only [Function.comp_def] using! hw

/- Pull a selected parabolic weak jet back by affine time reflection. -/
def ParabolicW12Function.timeReflect
    {d U p}
    (w : ParabolicW12Function d U p)
    (r₁ : ℝ) (hU : MeasurableSet U) :
    ParabolicW12Function d (reverseTimeMap r₁ ⁻¹' U) p where
  toFun z := w.toFun (reverseTimeMap r₁ z)
  timeDeriv z := -w.timeDeriv (reverseTimeMap r₁ z)
  velocityGrad z := w.velocityGrad (reverseTimeMap r₁ z)
  velocityHessian z := w.velocityHessian (reverseTimeMap r₁ z)
  memLp := w.memLp.comp_measurePreserving
    (reverseTimeMap_measurePreserving_restrict r₁ hU)
  timeDeriv_memLp := (w.timeDeriv_memLp.comp_measurePreserving
    (reverseTimeMap_measurePreserving_restrict r₁ hU)).neg
  velocityGrad_memLp := fun i => (w.velocityGrad_memLp i).comp_measurePreserving
    (reverseTimeMap_measurePreserving_restrict r₁ hU)
  velocityHessian_memLp := fun i j =>
    (w.velocityHessian_memLp i j).comp_measurePreserving
      (reverseTimeMap_measurePreserving_restrict r₁ hU)
  hasWeakTimeDeriv := hasWeakTimeDerivOn_timeReflect hU w.hasWeakTimeDeriv r₁
  hasWeakVelocityPartialDeriv := fun i =>
    hasWeakVelocityPartialDerivOn_timeReflect hU
      (w.hasWeakVelocityPartialDeriv i) r₁
  hasWeakVelocitySecondPartialDeriv := fun i j =>
    hasWeakVelocityPartialDerivOn_timeReflect hU
      (w.hasWeakVelocitySecondPartialDeriv i j) r₁

/- Evaluation of the reflected weak-jet value. -/
end HypoellipticAleksandrov.Parabolic
