module

public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Raw algebra for parabolic weak derivatives

This module records coefficient-free algebraic closure properties of the raw
time and velocity weak-derivative predicates.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory
open scoped ENNReal Topology

private theorem integrable_restrict_mul_of_locallyIntegrableOn
    {d : ℕ} {U : Set (TimeVelocity d)} {f g : TimeVelocity d → ℝ}
    (hf : LocallyIntegrableOn f U volume) (hg : Continuous g)
    (hgCompact : HasCompactSupport g) (hgSub : tsupport g ⊆ U) :
    Integrable (fun z => f z * g z) (timeVelocityVolumeOn U) := by
  have hfgK : IntegrableOn (fun z => f z * g z) (tsupport g) volume := by
    simpa using
      (hf.integrableOn_compact_subset hgSub hgCompact.isCompact).smul_continuousOn hg.continuousOn hgCompact.isCompact
  have hsupport : Function.support (fun z => f z * g z) ⊆ tsupport g := by
    intro z hz
    exact tsupport_mul_subset_right (subset_closure hz)
  exact (integrableOn_iff_integrable_of_support_subset hsupport).mp hfgK |>.restrict

private theorem timeDerivative_continuous {d : ℕ} {f : TimeVelocity d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (timeDerivative f) := by
  unfold timeDerivative
  simpa using (hf.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem timeDerivative_compact {d : ℕ} {f : TimeVelocity d → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (timeDerivative f) := by
  unfold timeDerivative
  simpa using hf.fderiv_apply (𝕜 := ℝ) ((1, 0) : TimeVelocity d)

private theorem timeDerivative_tsupport {d : ℕ} (f : TimeVelocity d → ℝ) :
    tsupport (timeDerivative f) ⊆ tsupport f := by
  unfold timeDerivative
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]



private theorem velocityGradient_tsupport {d : ℕ} {i : Fin d} (f : TimeVelocity d → ℝ) :
    tsupport (fun z => velocityGradient f z i) ⊆ tsupport f := by
  unfold velocityGradient
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

namespace HasWeakTimeDerivOn



/-- Raw weak time derivatives are additive when all representatives are
locally integrable. -/
theorem add {d : ℕ} {U : Set (TimeVelocity d)}
    {u du v dv : TimeVelocity d → ℝ}
    (hu : HasWeakTimeDerivOn U u du)
    (hv : HasWeakTimeDerivOn U v dv)
    (huLoc : LocallyIntegrableOn u U volume)
    (hduLoc : LocallyIntegrableOn du U volume)
    (hvLoc : LocallyIntegrableOn v U volume)
    (hdvLoc : LocallyIntegrableOn dv U volume) :
    HasWeakTimeDerivOn U (fun z => u z + v z) (fun z => du z + dv z) := by
  intro φ hφ hφCompact hφSub
  let μU : Measure (TimeVelocity d) := timeVelocityVolumeOn U
  let dφ : TimeVelocity d → ℝ := timeDerivative φ
  have hφCont : Continuous φ := hφ.continuous
  have hdφCont : Continuous dφ := timeDerivative_continuous hφ
  have hdφCompact : HasCompactSupport dφ := timeDerivative_compact hφCompact
  have hdφSub : tsupport dφ ⊆ U := timeDerivative_tsupport φ |>.trans hφSub
  have huPair : Integrable (fun z => u z * dφ z) μU := by
    simpa using
      integrable_restrict_mul_of_locallyIntegrableOn huLoc hdφCont hdφCompact hdφSub
  have hvPair : Integrable (fun z => v z * dφ z) μU := by
    simpa using
      integrable_restrict_mul_of_locallyIntegrableOn hvLoc hdφCont hdφCompact hdφSub
  have hduPair : Integrable (fun z => du z * φ z) μU := by
    simpa using
      integrable_restrict_mul_of_locallyIntegrableOn hduLoc hφCont hφCompact hφSub
  have hdvPair : Integrable (fun z => dv z * φ z) μU := by
    simpa using
      integrable_restrict_mul_of_locallyIntegrableOn hdvLoc hφCont hφCompact hφSub
  calc
    (∫ z, (u z + v z) * dφ z ∂μU) =
        (∫ z, u z * dφ z ∂μU) + ∫ z, v z * dφ z ∂μU := by
      rw [← integral_add huPair hvPair]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
    _ = -∫ z, du z * φ z ∂μU + -∫ z, dv z * φ z ∂μU := by
      rw [show (∫ z, u z * dφ z ∂μU) = -∫ z, du z * φ z ∂μU by
        simpa using hu φ hφ hφCompact hφSub,
        show (∫ z, v z * dφ z ∂μU) = -∫ z, dv z * φ z ∂μU by
        simpa using hv φ hφ hφCompact hφSub]
    _ = -(∫ z, du z * φ z ∂μU + ∫ z, dv z * φ z ∂μU) := by ring
    _ = -∫ z, (du z + dv z) * φ z ∂μU := by
      rw [← integral_add hduPair hdvPair]
      apply congrArg Neg.neg
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring


end HasWeakTimeDerivOn

namespace HasWeakVelocityPartialDerivOn



/-- Raw weak velocity derivatives are additive when all representatives are
locally integrable. -/
theorem add {d : ℕ} {U : Set (TimeVelocity d)} {i : Fin d}
    {u du v dv : TimeVelocity d → ℝ}
    (hu : HasWeakVelocityPartialDerivOn U i u du)
    (hv : HasWeakVelocityPartialDerivOn U i v dv)
    (huLoc : LocallyIntegrableOn u U volume)
    (hduLoc : LocallyIntegrableOn du U volume)
    (hvLoc : LocallyIntegrableOn v U volume)
    (hdvLoc : LocallyIntegrableOn dv U volume) :
    HasWeakVelocityPartialDerivOn U i (fun z => u z + v z) (fun z => du z + dv z)   := by
  have velocityGradient_compact {f : TimeVelocity d → ℝ} (hf : HasCompactSupport f) :
      HasCompactSupport (fun z => velocityGradient f z i) := by
    unfold velocityGradient
    simpa using hf.fderiv_apply (𝕜 := ℝ) ((0, Pi.single i 1) : TimeVelocity d)
  have velocityGradient_continuous {f : TimeVelocity d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
      Continuous (fun z => velocityGradient f z i) := by
    unfold velocityGradient
    simpa using (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  intro φ hφ hφCompact hφSub
  let μU : Measure (TimeVelocity d) := timeVelocityVolumeOn U
  let dφ : TimeVelocity d → ℝ := fun z => velocityGradient φ z i
  have hφCont : Continuous φ := hφ.continuous
  have hdφCont : Continuous dφ := velocityGradient_continuous hφ
  have hdφCompact : HasCompactSupport dφ := velocityGradient_compact hφCompact
  have hdφSub : tsupport dφ ⊆ U := velocityGradient_tsupport φ |>.trans hφSub
  have huPair : Integrable (fun z => u z * dφ z) μU := by
    simpa using
      integrable_restrict_mul_of_locallyIntegrableOn huLoc hdφCont hdφCompact hdφSub
  have hvPair : Integrable (fun z => v z * dφ z) μU := by
    simpa using
      integrable_restrict_mul_of_locallyIntegrableOn hvLoc hdφCont hdφCompact hdφSub
  have hduPair : Integrable (fun z => du z * φ z) μU := by
    simpa using
      integrable_restrict_mul_of_locallyIntegrableOn hduLoc hφCont hφCompact hφSub
  have hdvPair : Integrable (fun z => dv z * φ z) μU := by
    simpa using
      integrable_restrict_mul_of_locallyIntegrableOn hdvLoc hφCont hφCompact hφSub
  calc
    (∫ z, (u z + v z) * dφ z ∂μU) =
        (∫ z, u z * dφ z ∂μU) + ∫ z, v z * dφ z ∂μU := by
      rw [← integral_add huPair hvPair]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
    _ = -∫ z, du z * φ z ∂μU + -∫ z, dv z * φ z ∂μU := by
      rw [show (∫ z, u z * dφ z ∂μU) = -∫ z, du z * φ z ∂μU by
        simpa using hu φ hφ hφCompact hφSub,
        show (∫ z, v z * dφ z ∂μU) = -∫ z, dv z * φ z ∂μU by
        simpa using hv φ hφ hφCompact hφSub]
    _ = -(∫ z, du z * φ z ∂μU + ∫ z, dv z * φ z ∂μU) := by ring
    _ = -∫ z, (du z + dv z) * φ z ∂μU := by
      rw [← integral_add hduPair hdvPair]
      apply congrArg Neg.neg
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring



end HasWeakVelocityPartialDerivOn

end HypoellipticAleksandrov.Parabolic
