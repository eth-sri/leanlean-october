module

public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory
open scoped ENNReal Topology

theorem integrable_restrict_mul_of_locallyIntegrableOn
    {d : ℕ} {U : Set (TimeVelocity d)} {f g : TimeVelocity d → ℝ}
    (hf : LocallyIntegrableOn f U volume) (hg : Continuous g)
    (hgCompact : HasCompactSupport g) (hgSub : tsupport g ⊆ U) :
    Integrable (fun z => f z * g z) (timeVelocityVolumeOn U) := by
  have hfK : IntegrableOn f (tsupport g) volume :=
    hf.integrableOn_compact_subset hgSub hgCompact.isCompact
  have hfgK : IntegrableOn (fun z => f z * g z) (tsupport g) volume := by
    simpa only [smul_eq_mul] using
      hfK.smul_continuousOn hg.continuousOn hgCompact.isCompact
  have hsupport : Function.support (fun z => f z * g z) ⊆ tsupport g := by
    intro z hz
    exact tsupport_mul_subset_right (subset_closure hz)
  exact (integrableOn_iff_integrable_of_support_subset hsupport).mp hfgK |>.restrict

theorem contDiff_timeDerivative {d : ℕ} {f : TimeVelocity d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (timeDerivative f) := by
  unfold timeDerivative
  exact (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

theorem timeDerivative_continuous {d : ℕ} {f : TimeVelocity d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (timeDerivative f) :=
  (contDiff_timeDerivative hf).continuous

theorem timeDerivative_compact {d : ℕ} {f : TimeVelocity d → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (timeDerivative f) := by
  unfold timeDerivative
  simpa using hf.fderiv_apply (𝕜 := ℝ) ((1, 0) : TimeVelocity d)

theorem timeDerivative_tsupport {d : ℕ} (f : TimeVelocity d → ℝ) :
    tsupport (timeDerivative f) ⊆ tsupport f := by
  unfold timeDerivative
  change closure (Function.support (fun z => fderiv ℝ f z (1, 0))) ⊆ tsupport f
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

theorem contDiff_velocityGradient_infty {d : ℕ} {f : TimeVelocity d → ℝ} {i : Fin d}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (fun z => velocityGradient f z i) := by
  unfold velocityGradient
  exact (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

theorem velocityGradient_continuous {d : ℕ} {f : TimeVelocity d → ℝ} {i : Fin d}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (fun z => velocityGradient f z i) :=
  (contDiff_velocityGradient_infty hf).continuous

theorem velocityGradient_compact {d : ℕ} {f : TimeVelocity d → ℝ} {i : Fin d}
    (hf : HasCompactSupport f) : HasCompactSupport (fun z => velocityGradient f z i) := by
  unfold velocityGradient
  simpa using hf.fderiv_apply (𝕜 := ℝ) ((0, Pi.single i 1) : TimeVelocity d)

theorem velocityGradient_tsupport {d : ℕ} {i : Fin d} (f : TimeVelocity d → ℝ) :
    tsupport (fun z => velocityGradient f z i) ⊆ tsupport f := by
  unfold velocityGradient
  change closure (Function.support (fun z => fderiv ℝ f z (0, Pi.single i 1))) ⊆ tsupport f
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

theorem continuous_velocityHessian_infty {d : ℕ} {f : TimeVelocity d → ℝ} {i j : Fin d}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (fun z => velocityHessian f z i j) := by
  unfold velocityHessian
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
  simpa using (hgrad.continuous_fderiv (by simp)).clm_apply continuous_const |>.clm_apply
    continuous_const

theorem velocityHessian_compact_support {d : ℕ} {f : TimeVelocity d → ℝ} {i j : Fin d}
    (hf : HasCompactSupport f) : HasCompactSupport (fun z => velocityHessian f z i j) := by
  unfold velocityHessian
  have hsecond : HasCompactSupport (fderiv ℝ (fderiv ℝ f)) := (hf.fderiv ℝ).fderiv ℝ
  simpa only [Function.comp_def] using hsecond.comp_left
    (g := fun H : TimeVelocity d →L[ℝ] TimeVelocity d →L[ℝ] ℝ =>
      H ((0, Pi.single i 1) : TimeVelocity d) ((0, Pi.single j 1) : TimeVelocity d)) rfl

private theorem fderiv_continuous {d : ℕ} {f : TimeVelocity d → ℝ} {w : TimeVelocity d}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (fun z => fderiv ℝ f z w) := by
  exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem fderiv_compact {d : ℕ} {f : TimeVelocity d → ℝ} {w : TimeVelocity d}
    (hf : HasCompactSupport f) : HasCompactSupport (fun z => fderiv ℝ f z w) := by
  exact hf.fderiv_apply (𝕜 := ℝ) w

private theorem fderiv_tsupport {d : ℕ} (f : TimeVelocity d → ℝ) {w : TimeVelocity d} :
    tsupport (fun z => fderiv ℝ f z w) ⊆ tsupport f := by
  change closure (Function.support (fun z => fderiv ℝ f z w)) ⊆ tsupport f
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

namespace HasWeakDirectionalDerivOn

theorem smul {d : ℕ} {U : Set (TimeVelocity d)}
    {u du : TimeVelocity d → ℝ}
    (w : TimeVelocity d) (hu : HasWeakDirectionalDerivOn U w u du) (c : ℝ) :
    HasWeakDirectionalDerivOn U w (c • u) (c • du) := by
  intro φ hφ hφCompact hφSub
  calc
    (∫ z in U, (c • u) z * fderiv ℝ φ z w ∂volume) =
        c * ∫ z in U, u z * fderiv ℝ φ z w ∂volume := by
      rw [show (fun z => (c • u) z * fderiv ℝ φ z w) =
          fun z => c * (u z * fderiv ℝ φ z w) by
        funext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring,
        integral_const_mul]
    _ = c * (-(∫ z in U, du z * φ z ∂volume)) := by
      rw [hu φ hφ hφCompact hφSub]
    _ = -∫ z in U, (c • du) z * φ z ∂volume := by
      rw [show (fun z => (c • du) z * φ z) = fun z => c * (du z * φ z) by
        funext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring,
        integral_const_mul]
      ring

theorem add {d : ℕ} {U : Set (TimeVelocity d)}
    {u du v dv : TimeVelocity d → ℝ}
    (w : TimeVelocity d) (hu : HasWeakDirectionalDerivOn U w u du)
    (hv : HasWeakDirectionalDerivOn U w v dv)
    (huLoc : LocallyIntegrableOn u U volume)
    (hduLoc : LocallyIntegrableOn du U volume)
    (hvLoc : LocallyIntegrableOn v U volume)
    (hdvLoc : LocallyIntegrableOn dv U volume) :
    HasWeakDirectionalDerivOn U w (fun z => u z + v z) (fun z => du z + dv z) := by
  intro φ hφ hφCompact hφSub
  let μU : Measure (TimeVelocity d) := timeVelocityVolumeOn U
  let dφ : TimeVelocity d → ℝ := fun z => fderiv ℝ φ z w
  have hφCont : Continuous φ := hφ.continuous
  have hdφCont : Continuous dφ := fderiv_continuous hφ
  have hdφCompact : HasCompactSupport dφ := fderiv_compact hφCompact
  have hdφSub : tsupport dφ ⊆ U := fderiv_tsupport φ |>.trans hφSub
  have huPair : Integrable (fun z => u z * dφ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn huLoc hdφCont hdφCompact hdφSub
  have hvPair : Integrable (fun z => v z * dφ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn hvLoc hdφCont hdφCompact hdφSub
  have hduPair : Integrable (fun z => du z * φ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn hduLoc hφCont hφCompact hφSub
  have hdvPair : Integrable (fun z => dv z * φ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn hdvLoc hφCont hφCompact hφSub
  change (∫ z, (u z + v z) * dφ z ∂μU) =
    -∫ z, (du z + dv z) * φ z ∂μU
  calc
    (∫ z, (u z + v z) * dφ z ∂μU) =
        (∫ z, u z * dφ z ∂μU) + ∫ z, v z * dφ z ∂μU := by
      rw [← integral_add huPair hvPair]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
    _ = -∫ z, du z * φ z ∂μU + -∫ z, dv z * φ z ∂μU := by
      rw [show (∫ z, u z * dφ z ∂μU) = -∫ z, du z * φ z ∂μU by
        simpa only [μU, dφ] using hu φ hφ hφCompact hφSub,
        show (∫ z, v z * dφ z ∂μU) = -∫ z, dv z * φ z ∂μU by
        simpa only [μU, dφ] using hv φ hφ hφCompact hφSub]
    _ = -(∫ z, du z * φ z ∂μU + ∫ z, dv z * φ z ∂μU) := by ring
    _ = -∫ z, (du z + dv z) * φ z ∂μU := by
      rw [← integral_add hduPair hdvPair]
      apply congrArg Neg.neg
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring

theorem zero {d : ℕ} {U : Set (TimeVelocity d)} (w : TimeVelocity d) :
    HasWeakDirectionalDerivOn U w (0 : TimeVelocity d → ℝ) 0 := by
  intro φ hφ hφCompact hφSub
  simp only [Pi.zero_apply, zero_mul, integral_zero, neg_zero]

theorem sub {d : ℕ} {U : Set (TimeVelocity d)}
    {u du v dv : TimeVelocity d → ℝ}
    (w : TimeVelocity d) (hu : HasWeakDirectionalDerivOn U w u du)
    (hv : HasWeakDirectionalDerivOn U w v dv)
    (huLoc : LocallyIntegrableOn u U volume)
    (hduLoc : LocallyIntegrableOn du U volume)
    (hvLoc : LocallyIntegrableOn v U volume)
    (hdvLoc : LocallyIntegrableOn dv U volume) :
    HasWeakDirectionalDerivOn U w (fun z => u z - v z) (fun z => du z - dv z) := by
  have h := add w hu (smul w hv (-1)) huLoc hduLoc
    (by simpa only [neg_one_smul] using hvLoc.neg)
    (by simpa only [neg_one_smul] using hdvLoc.neg)
  simpa only [sub_eq_add_neg, Pi.neg_apply, neg_one_smul] using h

theorem fin_sum {d n : ℕ} {U : Set (TimeVelocity d)}
    {u du : Fin n → TimeVelocity d → ℝ}
    (w : TimeVelocity d) (hu : ∀ j, HasWeakDirectionalDerivOn U w (u j) (du j))
    (huLoc : ∀ j, LocallyIntegrableOn (u j) U volume)
    (hduLoc : ∀ j, LocallyIntegrableOn (du j) U volume) :
    HasWeakDirectionalDerivOn U w
      (fun z => ∑ j, u j z) (fun z => ∑ j, du j z) := by
  classical
  have huSumLoc : ∀ s : Finset (Fin n),
      LocallyIntegrableOn (fun z => ∑ j ∈ s, u j z) U volume := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using
        (locallyIntegrableOn_zero (X := TimeVelocity d) (s := U)
          (μ := volume) (ε'' := ℝ))
    | @insert j s hj ih =>
        simpa [Finset.sum_insert hj, Pi.add_def] using (huLoc j).add ih
  have hduSumLoc : ∀ s : Finset (Fin n),
      LocallyIntegrableOn (fun z => ∑ j ∈ s, du j z) U volume := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using
        (locallyIntegrableOn_zero (X := TimeVelocity d) (s := U)
          (μ := volume) (ε'' := ℝ))
    | @insert j s hj ih =>
        simpa [Finset.sum_insert hj, Pi.add_def] using (hduLoc j).add ih
  have hweak : ∀ s : Finset (Fin n),
      HasWeakDirectionalDerivOn U w
        (fun z => ∑ j ∈ s, u j z) (fun z => ∑ j ∈ s, du j z) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [HasWeakDirectionalDerivOn]
    | @insert j s hj ih =>
        have hadd := add w (hu j) ih (huLoc j) (hduLoc j) (huSumLoc s) (hduSumLoc s)
        simpa [Finset.sum_insert hj] using hadd
  simpa using hweak Finset.univ

end HasWeakDirectionalDerivOn

namespace HasWeakTimeDerivOn

/-- Zero has zero weak time derivative. -/
theorem zero {d : ℕ} {U : Set (TimeVelocity d)} :
    HasWeakTimeDerivOn U (0 : TimeVelocity d → ℝ) 0 := by
  intro φ hφ hφCompact hφSub
  simp only [Pi.zero_apply, zero_mul, integral_zero, neg_zero]

/-- Weak time differentiation commutes with constant scalar multiplication. -/
theorem smul {d : ℕ} {U : Set (TimeVelocity d)}
    {u du : TimeVelocity d → ℝ}
    (hu : HasWeakTimeDerivOn U u du) (c : ℝ) :
    HasWeakTimeDerivOn U (c • u) (c • du) := by
  simpa only [HasWeakDirectionalDerivOn, HasWeakTimeDerivOn, timeDerivative] using
    HasWeakDirectionalDerivOn.smul (1, 0) hu c

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
  simpa only [HasWeakDirectionalDerivOn, HasWeakTimeDerivOn, timeDerivative] using
    HasWeakDirectionalDerivOn.add (1, 0) hu hv huLoc hduLoc hvLoc hdvLoc

/-- Weak time differentiation commutes with finite sums when every value and
derivative representative is locally integrable. -/
theorem fin_sum
    {d n : ℕ} {U : Set (TimeVelocity d)}
    {u du : Fin n → TimeVelocity d → ℝ}
    (hu : ∀ j, HasWeakTimeDerivOn U (u j) (du j))
    (huLoc : ∀ j, LocallyIntegrableOn (u j) U volume)
    (hduLoc : ∀ j, LocallyIntegrableOn (du j) U volume) :
    HasWeakTimeDerivOn U
      (fun z => ∑ j, u j z) (fun z => ∑ j, du j z) := by
  simpa only [HasWeakDirectionalDerivOn, HasWeakTimeDerivOn, timeDerivative] using
    HasWeakDirectionalDerivOn.fin_sum (1, 0) hu huLoc hduLoc

end HasWeakTimeDerivOn

namespace HasWeakVelocityPartialDerivOn

/-- Zero has zero weak velocity derivative. -/
theorem zero {d : ℕ} {U : Set (TimeVelocity d)} {i : Fin d} :
    HasWeakVelocityPartialDerivOn U i (0 : TimeVelocity d → ℝ) 0 := by
  intro φ hφ hφCompact hφSub
  simp only [Pi.zero_apply, zero_mul, integral_zero, neg_zero]

/-- Weak velocity differentiation commutes with constant scalar multiplication. -/
theorem smul {d : ℕ} {U : Set (TimeVelocity d)} {i : Fin d}
    {u dui : TimeVelocity d → ℝ}
    (hu : HasWeakVelocityPartialDerivOn U i u dui) (c : ℝ) :
    HasWeakVelocityPartialDerivOn U i (c • u) (c • dui) := by
  simpa only [HasWeakDirectionalDerivOn, HasWeakVelocityPartialDerivOn, velocityGradient] using
    HasWeakDirectionalDerivOn.smul (0, Pi.single i 1) hu c

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
    HasWeakVelocityPartialDerivOn U i (fun z => u z + v z) (fun z => du z + dv z) := by
  simpa only [HasWeakDirectionalDerivOn, HasWeakVelocityPartialDerivOn, velocityGradient] using
    HasWeakDirectionalDerivOn.add (0, Pi.single i 1) hu hv huLoc hduLoc hvLoc hdvLoc

/-- Raw weak velocity derivatives commute with subtraction when all
representatives are locally integrable. -/
theorem sub {d : ℕ} {U : Set (TimeVelocity d)} {i : Fin d}
    {u du v dv : TimeVelocity d → ℝ}
    (hu : HasWeakVelocityPartialDerivOn U i u du)
    (hv : HasWeakVelocityPartialDerivOn U i v dv)
    (huLoc : LocallyIntegrableOn u U volume)
    (hduLoc : LocallyIntegrableOn du U volume)
    (hvLoc : LocallyIntegrableOn v U volume)
    (hdvLoc : LocallyIntegrableOn dv U volume) :
    HasWeakVelocityPartialDerivOn U i
      (fun z => u z - v z) (fun z => du z - dv z) := by
  simpa only [HasWeakDirectionalDerivOn, HasWeakVelocityPartialDerivOn, velocityGradient] using
    HasWeakDirectionalDerivOn.sub (0, Pi.single i 1) hu hv huLoc hduLoc hvLoc hdvLoc

/-- Weak velocity differentiation commutes with finite sums when every value
and derivative representative is locally integrable. -/
theorem fin_sum
    {d n : ℕ} {U : Set (TimeVelocity d)} {i : Fin d}
    {u du : Fin n → TimeVelocity d → ℝ}
    (hu : ∀ j, HasWeakVelocityPartialDerivOn U i (u j) (du j))
    (huLoc : ∀ j, LocallyIntegrableOn (u j) U volume)
    (hduLoc : ∀ j, LocallyIntegrableOn (du j) U volume) :
    HasWeakVelocityPartialDerivOn U i
      (fun z => ∑ j, u j z) (fun z => ∑ j, du j z) := by
  simpa only [HasWeakDirectionalDerivOn, HasWeakVelocityPartialDerivOn, velocityGradient] using
    HasWeakDirectionalDerivOn.fin_sum (0, Pi.single i 1) hu huLoc hduLoc

end HasWeakVelocityPartialDerivOn

end HypoellipticAleksandrov.Parabolic
