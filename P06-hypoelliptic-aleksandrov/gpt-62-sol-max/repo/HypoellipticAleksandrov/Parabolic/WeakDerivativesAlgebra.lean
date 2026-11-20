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

theorem integrable_restrict_mul_of_locallyIntegrableOn
    {d : ℕ} {U : Set (TimeVelocity d)} {f g : TimeVelocity d → ℝ}
    (hf : LocallyIntegrableOn f U volume) (hg : Continuous g)
    (hgCompact : HasCompactSupport g) (hgSub : tsupport g ⊆ U) :
    Integrable (fun z => f z * g z) (timeVelocityVolumeOn U) := by
  have hfK :=
    hf.integrableOn_compact_subset hgSub hgCompact.isCompact
  have hfgK : IntegrableOn (fun z => f z * g z) (tsupport g) volume := by
    simpa only [smul_eq_mul] using
      hfK.smul_continuousOn hg.continuousOn hgCompact.isCompact
  have hsupport : Function.support (fun z => f z * g z) ⊆ tsupport g := by
    intro z hz
    exact tsupport_mul_subset_right (subset_closure hz)
  exact (integrableOn_iff_integrable_of_support_subset hsupport).mp hfgK |>.restrict

namespace HasWeakFDerivApplyOn

variable {d : ℕ} {U : Set (TimeVelocity d)} {e : TimeVelocity d}

/-- The zero function has zero weak derivative in every direction. -/
theorem zero : HasWeakFDerivApplyOn U e 0 0 := by
  intro φ hφ hc hs
  simp

/-- Weak differentiation is compatible with constant scaling. -/
theorem smul {u du : TimeVelocity d → ℝ} (hu : HasWeakFDerivApplyOn U e u du) (c : ℝ) :
    HasWeakFDerivApplyOn U e (c • u) (c • du) := by
  intro φ hφ hc hs
  simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul, mul_neg] using
    congrArg (c * ·) (hu φ hφ hc hs)

private theorem integrable_pairing_deriv {u φ : TimeVelocity d → ℝ}
    (hu : LocallyIntegrableOn u U volume) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    Integrable (fun z => u z * fderiv ℝ φ z e) (timeVelocityVolumeOn U) :=
  integrable_restrict_mul_of_locallyIntegrableOn hu
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ e) ((tsupport_fderiv_apply_subset ℝ e).trans hs)

section
variable {u du v dv : TimeVelocity d → ℝ} (hu : HasWeakFDerivApplyOn U e u du)
  (hv : HasWeakFDerivApplyOn U e v dv) (huLoc : LocallyIntegrableOn u U volume)
  (hduLoc : LocallyIntegrableOn du U volume) (hvLoc : LocallyIntegrableOn v U volume)
  (hdvLoc : LocallyIntegrableOn dv U volume)
include hu hv huLoc hduLoc hvLoc hdvLoc

/-- Addition for locally integrable distributional derivatives. -/
theorem add :
    HasWeakFDerivApplyOn U e (u + v) (du + dv) := by
  intro φ hφ hc hs
  simp only [Pi.add_apply, add_mul]
  rw [integral_add (integrable_pairing_deriv huLoc hφ hc hs) (integrable_pairing_deriv hvLoc hφ hc hs),
    integral_add (integrable_restrict_mul_of_locallyIntegrableOn hduLoc hφ.continuous hc hs)
      (integrable_restrict_mul_of_locallyIntegrableOn hdvLoc hφ.continuous hc hs),
    hu φ hφ hc hs, hv φ hφ hc hs, neg_add]

/-- Subtraction for locally integrable distributional derivatives. -/
theorem sub :
    HasWeakFDerivApplyOn U e (u - v) (du - dv) := by
  intro φ hφ hc hs
  simp only [Pi.sub_apply, sub_mul]
  rw [integral_sub (integrable_pairing_deriv huLoc hφ hc hs) (integrable_pairing_deriv hvLoc hφ hc hs),
    integral_sub (integrable_restrict_mul_of_locallyIntegrableOn hduLoc hφ.continuous hc hs)
      (integrable_restrict_mul_of_locallyIntegrableOn hdvLoc hφ.continuous hc hs),
    hu φ hφ hc hs, hv φ hφ hc hs, neg_sub]
  ring

end

/-- Weak differentiation commutes with a finite sum of locally integrable representatives. -/
theorem fintype_sum {ι : Type*} [Fintype ι] {u du : ι → TimeVelocity d → ℝ}
    (hu : ∀ j, HasWeakFDerivApplyOn U e (u j) (du j))
    (huLoc : ∀ j, LocallyIntegrableOn (u j) U volume)
    (hduLoc : ∀ j, LocallyIntegrableOn (du j) U volume) :
    HasWeakFDerivApplyOn U e (fun z => ∑ j, u j z) (fun z => ∑ j, du j z) := by
  intro φ hφ hc hs
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun j _ => integrable_pairing_deriv (huLoc j) hφ hc hs),
    integral_finsetSum _ (fun j _ => integrable_restrict_mul_of_locallyIntegrableOn (hduLoc j) hφ.continuous hc hs),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => hu j φ hφ hc hs

end HasWeakFDerivApplyOn

namespace HasWeakTimeDerivOn

section
variable {d : ℕ} {U : Set (TimeVelocity d)}

/-- Zero has zero weak time derivative. -/
theorem zero :
    HasWeakTimeDerivOn U (0 : TimeVelocity d → ℝ) 0 := HasWeakFDerivApplyOn.zero (e := (1, 0))

/-- Weak time differentiation commutes with constant scalar multiplication. -/
theorem smul
    {u du : TimeVelocity d → ℝ}
    (hu : HasWeakTimeDerivOn U u du) (c : ℝ) :
    HasWeakTimeDerivOn U (c • u) (c • du) := HasWeakFDerivApplyOn.smul (e := (1, 0)) hu c

/-- Raw weak time derivatives are additive when all representatives are
locally integrable. -/
theorem add
    {u du v dv : TimeVelocity d → ℝ}
    (hu : HasWeakTimeDerivOn U u du)
    (hv : HasWeakTimeDerivOn U v dv)
    (huLoc : LocallyIntegrableOn u U volume)
    (hduLoc : LocallyIntegrableOn du U volume)
    (hvLoc : LocallyIntegrableOn v U volume)
    (hdvLoc : LocallyIntegrableOn dv U volume) :
    HasWeakTimeDerivOn U (fun z => u z + v z) (fun z => du z + dv z) := HasWeakFDerivApplyOn.add (e := (1, 0)) hu hv huLoc hduLoc hvLoc hdvLoc

end

end HasWeakTimeDerivOn

namespace HasWeakVelocityPartialDerivOn

section
variable {d : ℕ} {U : Set (TimeVelocity d)} {i : Fin d}

/-- Zero has zero weak velocity derivative. -/
theorem zero :
    HasWeakVelocityPartialDerivOn U i (0 : TimeVelocity d → ℝ) 0 := HasWeakFDerivApplyOn.zero (e := (0, Pi.single i 1))

/-- Weak velocity differentiation commutes with constant scalar multiplication. -/
theorem smul
    {u dui : TimeVelocity d → ℝ}
    (hu : HasWeakVelocityPartialDerivOn U i u dui) (c : ℝ) :
    HasWeakVelocityPartialDerivOn U i (c • u) (c • dui) := HasWeakFDerivApplyOn.smul (e := (0, Pi.single i 1)) hu c

end

section
variable {d : ℕ} {U : Set (TimeVelocity d)} {i : Fin d} {u du v dv : TimeVelocity d → ℝ}
  (hu : HasWeakVelocityPartialDerivOn U i u du) (hv : HasWeakVelocityPartialDerivOn U i v dv)
  (huLoc : LocallyIntegrableOn u U volume) (hduLoc : LocallyIntegrableOn du U volume)
  (hvLoc : LocallyIntegrableOn v U volume) (hdvLoc : LocallyIntegrableOn dv U volume)
include hu hv huLoc hduLoc hvLoc hdvLoc

/-- Raw weak velocity derivatives are additive when all representatives are
locally integrable. -/
theorem add :
    HasWeakVelocityPartialDerivOn U i (fun z => u z + v z) (fun z => du z + dv z) := HasWeakFDerivApplyOn.add (e := (0, Pi.single i 1)) hu hv huLoc hduLoc hvLoc hdvLoc

/-- Raw weak velocity derivatives commute with subtraction when all
representatives are locally integrable. -/
theorem sub :
    HasWeakVelocityPartialDerivOn U i
      (fun z => u z - v z) (fun z => du z - dv z) := HasWeakFDerivApplyOn.sub (e := (0, Pi.single i 1)) hu hv huLoc hduLoc hvLoc hdvLoc

end

end HasWeakVelocityPartialDerivOn

end HypoellipticAleksandrov.Parabolic
