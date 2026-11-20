module

public import HypoellipticAleksandrov.Parabolic.Derivatives
public import HypoellipticAleksandrov.Measure.TimeVelocity

/-!
# Weak derivatives on time--velocity space

This module defines the representative-level anisotropic weak-derivative data
used for the time--velocity parabolic regularity surface.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal Topology

section
variable {d : Nat} (U : Set (TimeVelocity d))
include U

/-- Product Lebesgue volume restricted to a time--velocity set. -/
noncomputable abbrev timeVelocityVolumeOn :
    Measure (TimeVelocity d) :=
  (volume : Measure (TimeVelocity d)).restrict U

/-- Restricted-product-volume `L^p` membership on time--velocity space. -/
abbrev ParabolicMemLpOn (p : ℝ≥0∞)
    (f : TimeVelocity d → ℝ) : Prop :=
  MeasureTheory.MemLp f p (timeVelocityVolumeOn U)

end

/-- Distributional differentiation along a fixed vector in time--velocity space. -/
abbrev HasWeakFDerivApplyOn {d : ℕ} (U : Set (TimeVelocity d)) (e : TimeVelocity d)
    (u du : TimeVelocity d → ℝ) : Prop :=
  ∀ φ : TimeVelocity d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∫ z in U, u z * fderiv ℝ φ z e ∂volume) = -∫ z in U, du z * φ z ∂volume

section
variable {d : Nat} (U : Set (TimeVelocity d))
include U

/-- The distributional time derivative relation on a raw time--velocity set. -/
def HasWeakTimeDerivOn
    (u du : TimeVelocity d → ℝ) : Prop :=
  ∀ φ : TimeVelocity d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    (∫ z in U, u z * timeDerivative φ z ∂(volume : Measure (TimeVelocity d))) =
      -∫ z in U, du z * φ z ∂(volume : Measure (TimeVelocity d))

/-- The distributional derivative relation in one velocity coordinate on a raw
time--velocity set. -/
def HasWeakVelocityPartialDerivOn
    (i : Fin d) (u dui : TimeVelocity d → ℝ) : Prop :=
  ∀ φ : TimeVelocity d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    (∫ z in U, u z * velocityGradient φ z i
      ∂(volume : Measure (TimeVelocity d))) =
      -∫ z in U, dui z * φ z ∂(volume : Measure (TimeVelocity d))

end

/-- A representative-level anisotropic weak `W^{1,2,p}` jet on a raw
time--velocity set. -/
structure ParabolicW12Function (d : Nat) (U : Set (TimeVelocity d)) (p : ℝ≥0∞) where
  toFun : TimeVelocity d → ℝ
  timeDeriv : TimeVelocity d → ℝ
  velocityGrad : TimeVelocity d → PDE.Vec d
  velocityHessian : TimeVelocity d → PDE.Mat d
  memLp : ParabolicMemLpOn U p toFun
  timeDeriv_memLp : ParabolicMemLpOn U p timeDeriv
  velocityGrad_memLp : ∀ i : Fin d,
    ParabolicMemLpOn U p (fun z => velocityGrad z i)
  velocityHessian_memLp : ∀ i j : Fin d,
    ParabolicMemLpOn U p (fun z => velocityHessian z i j)
  hasWeakTimeDeriv : HasWeakTimeDerivOn U toFun timeDeriv
  hasWeakVelocityPartialDeriv : ∀ i : Fin d,
    HasWeakVelocityPartialDerivOn U i toFun (fun z => velocityGrad z i)
  hasWeakVelocitySecondPartialDeriv : ∀ i j : Fin d,
    HasWeakVelocityPartialDerivOn U j (fun z => velocityGrad z i)
      (fun z => velocityHessian z i j)

theorem setIntegral_mul_eq_of_tsupport_subset
    {d : ℕ} {V U : Set (TimeVelocity d)} (hU : MeasurableSet U)
    (hVU : V ⊆ U) (f g : TimeVelocity d → ℝ) (hgV : tsupport g ⊆ V) :
    (∫ z in U, f z * g z ∂(volume : Measure (TimeVelocity d))) =
      ∫ z in V, f z * g z ∂(volume : Measure (TimeVelocity d)) := by
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero hU hVU
  intro z hz
  have hgz : g z = 0 := by
    by_contra hn
    exact hz.2 (hgV (subset_closure hn))
  simp [hgz]

theorem continuousOn_bounded_mul_memLp
    {d : ℕ} {V : Set (TimeVelocity d)} (hV : IsOpen V)
    (q f : TimeVelocity d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hq : ContinuousOn q V) (hqBound : ∀ z ∈ V, |q z| ≤ C)
    (hf : ParabolicMemLpOn V 2 f) :
    ParabolicMemLpOn V 2 (fun z ↦ q z * f z) := by
  apply MemLp.of_le_mul (c := C) hf
    ((hq.aestronglyMeasurable hV.measurableSet).mul hf.aestronglyMeasurable)
  exact ae_restrict_of_forall_mem hV.measurableSet fun z hz => by
    rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hqBound z hz) (norm_nonneg _)

end HypoellipticAleksandrov.Parabolic
