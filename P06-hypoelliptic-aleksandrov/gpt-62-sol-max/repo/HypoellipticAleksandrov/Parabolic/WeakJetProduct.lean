module

public import HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Smooth compact multipliers for parabolic weak jets

This file records raw distributional product rules on time--velocity space and
uses them to multiply a selected `ParabolicW12Function` jet by a smooth,
compactly supported scalar.  The stored velocity Hessian remains ordered: its
`(i,j)` entry differentiates the selected `i`-gradient in direction `j`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory
open scoped ENNReal Topology

/-- The smooth multiplier rule in a fixed direction. -/
theorem HasWeakFDerivApplyOn.mul_contDiff
    {d : ℕ} {U : Set (TimeVelocity d)} {u du b : TimeVelocity d → ℝ} {e : TimeVelocity d}
    (hu : HasWeakFDerivApplyOn U e u du) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (huLoc : LocallyIntegrableOn u U volume) (hduLoc : LocallyIntegrableOn du U volume) :
    HasWeakFDerivApplyOn U e (b * u) (fun z => b z * du z + u z * fderiv ℝ b z e) := by
  intro φ hφ hc hs
  let D (f : TimeVelocity d → ℝ) := fun z => fderiv ℝ f z e
  have hD {f} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (D f) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsD := (tsupport_fderiv_apply_subset ℝ (f := φ) e).trans hs
  have hI₁ := integrable_restrict_mul_of_locallyIntegrableOn huLoc
    (hb.continuous.mul (hD hφ)) ((hc.fderiv_apply ℝ e).mul_left (f := b))
    (tsupport_mul_subset_right.trans hsD)
  have hI₂ := integrable_restrict_mul_of_locallyIntegrableOn huLoc
    (hφ.continuous.mul (hD hb)) (hc.mul_right (f' := D b)) (tsupport_mul_subset_left.trans hs)
  have hI₃ := integrable_restrict_mul_of_locallyIntegrableOn hduLoc
    (hb.continuous.mul hφ.continuous) (hc.mul_left (f := b)) (tsupport_mul_subset_right.trans hs)
  have h := hu (b * φ) (hb.mul hφ) hc.mul_left (tsupport_mul_subset_right.trans hs)
  have hp (z : TimeVelocity d) : D (b * φ) z = b z * D φ z + φ z * D b z := by
    dsimp [D]
    rw [fderiv_mul (hb.differentiable (by simp) z) (hφ.differentiable (by simp) z)]
    rfl
  change (∫ z in U, u z * D (b * φ) z) = -∫ z in U, du z * (b z * φ z) at h
  simp only [Pi.mul_apply, timeVelocityVolumeOn] at hI₁ hI₂ hI₃
  simp_rw [hp, mul_add] at h
  rw [integral_add hI₁ hI₂] at h
  change (∫ z in U, (b z * u z) * D φ z) =
    -∫ z in U, (b z * du z + u z * D b z) * φ z
  simp_rw [add_mul]
  rw [integral_add (by simpa only [mul_assoc, mul_left_comm] using hI₃)
    (by simpa only [mul_assoc, mul_comm (D b _)] using hI₂)]
  simpa only [mul_assoc, mul_left_comm, mul_comm (D b _), neg_add, ← sub_eq_add_neg] using
    (eq_sub_of_add_eq h)

namespace HasWeakTimeDerivOn

/-- Smooth scalar multiplication obeys the raw weak time-derivative product rule. -/
theorem mul_contDiff {d : ℕ} {U : Set (TimeVelocity d)} {u du b : TimeVelocity d → ℝ}
    (hu : HasWeakTimeDerivOn U u du) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (huLoc : LocallyIntegrableOn u U volume)
    (hduLoc : LocallyIntegrableOn du U volume) :
    HasWeakTimeDerivOn U (fun z => b z * u z)
      (fun z => b z * du z + u z * timeDerivative b z) :=
  HasWeakFDerivApplyOn.mul_contDiff (e := (1, 0)) hu hb huLoc hduLoc

end HasWeakTimeDerivOn

namespace HasWeakVelocityPartialDerivOn

/-- Smooth scalar multiplication obeys the raw weak velocity product rule. -/
theorem mul_contDiff {d : ℕ} {U : Set (TimeVelocity d)} {i : Fin d}
    {u dui b : TimeVelocity d → ℝ}
    (hu : HasWeakVelocityPartialDerivOn U i u dui) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (huLoc : LocallyIntegrableOn u U volume)
    (hduiLoc : LocallyIntegrableOn dui U volume) :
    HasWeakVelocityPartialDerivOn U i (fun z => b z * u z)
      (fun z => b z * dui z + u z * velocityGradient b z i) :=
  HasWeakFDerivApplyOn.mul_contDiff (e := (0, Pi.single i 1)) hu hb huLoc hduiLoc

end HasWeakVelocityPartialDerivOn

section
variable {d : ℕ} (b q : TimeVelocity d → ℝ)
include b q

/-- The scalar localized by multiplication with the cutoff. -/
def localizedScalar :
    TimeVelocity d → ℝ := fun z => b z * q z

/-- The gradient coordinate of the localized scalar. -/
def localizedGradient
    (QG : TimeVelocity d → PDE.Vec d) (j : Fin d) : TimeVelocity d → ℝ :=
  fun z => b z * QG z j + q z * velocityGradient b z j

/-- The ordered Hessian coordinate of the localized scalar. -/
def localizedHessian
    (QG : TimeVelocity d → PDE.Vec d) (QH : TimeVelocity d → PDE.Mat d)
    (j i : Fin d) : TimeVelocity d → ℝ := fun z =>
  b z * QH z j i + velocityGradient b z i * QG z j +
    velocityGradient b z j * QG z i + q z * velocityHessian b z j i

end

/-- The time derivative of the localized scalar. -/
def localizedTimeDeriv {d : ℕ} (b q QW : TimeVelocity d → ℝ) : TimeVelocity d → ℝ :=
  fun z => b z * QW z + q z * timeDerivative b z

/-- A continuous compactly supported multiplier preserves restricted `Lᵖ`. -/
theorem ParabolicMemLpOn.mul_continuous_compact {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞}
    {f b : TimeVelocity d → ℝ} (hf : ParabolicMemLpOn U p f) (hb : Continuous b)
    (hc : HasCompactSupport b) : ParabolicMemLpOn U p (fun z => b z * f z) := by
  have hB : ParabolicMemLpOn U ∞ b := (hb.memLp_of_hasCompactSupport hc).restrict U
  simpa only [mul_comm] using hf.mul' hB

variable {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞} {b q QW : TimeVelocity d → ℝ}
  {QG : TimeVelocity d → PDE.Vec d} {QH : TimeVelocity d → PDE.Mat d}

lemma localizedTimeDeriv_memLp (hq : ParabolicMemLpOn U p q) (hW : ParabolicMemLpOn U p QW)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : HasCompactSupport b) :
    ParabolicMemLpOn U p (localizedTimeDeriv b q QW) := by
  refine (hW.mul_continuous_compact hb.continuous hc).add ?_
  simpa only [mul_comm] using hq.mul_continuous_compact (timeDerivative_continuous hb) (timeDerivative_compact hc)

lemma localizedGradient_memLp {j : Fin d} (hq : ParabolicMemLpOn U p q)
    (hG : ParabolicMemLpOn U p (fun z => QG z j))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : HasCompactSupport b) :
    ParabolicMemLpOn U p (localizedGradient b q QG j) := by
  refine (hG.mul_continuous_compact hb.continuous hc).add ?_
  simpa only [mul_comm] using hq.mul_continuous_compact (velocityGradient_continuous (i := j) hb)
    (velocityGradient_compact (i := j) hc)

/-- Ordered second weak differentiation of a smooth compact multiplier, with its `Lᵖ` bound.
Only the specified second derivative of the original jet is needed. -/
theorem localizedHessian_memLp_hasWeakDeriv {j i : Fin d} (hp : 1 ≤ p)
    (hq : ParabolicMemLpOn U p q)
    (hGj : ParabolicMemLpOn U p (fun z => QG z j))
    (hGi : ParabolicMemLpOn U p (fun z => QG z i))
    (hH : ParabolicMemLpOn U p (fun z => QH z j i))
    (hqG : HasWeakVelocityPartialDerivOn U i q (fun z => QG z i))
    (hGH : HasWeakVelocityPartialDerivOn U i (fun z => QG z j) (fun z => QH z j i))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : HasCompactSupport b) :
    ParabolicMemLpOn U p (localizedHessian b q QG QH j i) ∧
      HasWeakVelocityPartialDerivOn U i (localizedGradient b q QG j) (localizedHessian b q QG QH j i) := by
  have bc (k : Fin d) := velocityGradient_continuous (i := k) hb
  have bs (k : Fin d) := velocityGradient_compact (i := k) hc
  have hA := hH.mul_continuous_compact hb.continuous hc
  have hB := hGj.mul_continuous_compact (bc i) (bs i)
  have hC := hGi.mul_continuous_compact (bc j) (bs j)
  have hD : ParabolicMemLpOn U p (fun z => q z * velocityHessian b z j i) := by
    simpa only [mul_comm] using hq.mul_continuous_compact
      (velocityHessian_continuous (i := j) (j := i) hb) (velocityHessian_compact (i := j) (j := i) hc)
  refine ⟨((hA.add hB).add hC).add hD, ?_⟩
  have h₁ := hGH.mul_contDiff hb (hGj.locallyIntegrableOn hp) (hH.locallyIntegrableOn hp)
  have h₂ := hqG.mul_contDiff (velocityGradient_contDiff (i := j) hb)
    (hq.locallyIntegrableOn hp) (hGi.locallyIntegrableOn hp)
  have h := h₁.add h₂
    ((hGj.mul_continuous_compact hb.continuous hc).locallyIntegrableOn hp)
    (by
      convert (hA.locallyIntegrableOn hp).add (hB.locallyIntegrableOn hp) using 1
      funext z
      simp only [Pi.add_apply, mul_comm (QG z j) (velocityGradient b z i)])
    ((hq.mul_continuous_compact (bc j) (bs j)).locallyIntegrableOn hp)
    (by
      convert (hC.locallyIntegrableOn hp).add (hD.locallyIntegrableOn hp) using 1
      funext z
      simp only [Pi.add_apply, velocityGradient_velocityGradient hb])
  convert h using 1 <;> funext z
  · unfold localizedGradient
    ring
  · simp only [localizedHessian, velocityGradient_velocityGradient hb]
    ring

namespace ParabolicW12Function

/-- Multiply a raw parabolic weak jet by a globally smooth compactly supported scalar. -/
noncomputable def mulContDiffHasCompactSupport {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞}
    (w : ParabolicW12Function d U p) (hp : 1 ≤ p) {b : TimeVelocity d → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbCompact : HasCompactSupport b) :
    ParabolicW12Function d U p := by
  have h₂ (j i : Fin d) := localizedHessian_memLp_hasWeakDeriv hp w.memLp (w.velocityGrad_memLp j)
    (w.velocityGrad_memLp i) (w.velocityHessian_memLp j i) (w.hasWeakVelocityPartialDeriv i)
    (w.hasWeakVelocitySecondPartialDeriv j i) hb hbCompact
  have hhess (j i : Fin d) : localizedHessian b w.toFun w.velocityGrad w.velocityHessian j i =
      fun z => b z * w.velocityHessian z j i + velocityGradient b z i * w.velocityGrad z j +
        w.velocityGrad z i * velocityGradient b z j + w.toFun z * Parabolic.velocityHessian b z j i := by
    funext z
    dsimp only [localizedHessian]
    rw [mul_comm (velocityGradient b z j) (w.velocityGrad z i)]
  exact {
    toFun := fun z => b z * w.toFun z
    timeDeriv := fun z => b z * w.timeDeriv z + w.toFun z * timeDerivative b z
    velocityGrad := fun z i => b z * w.velocityGrad z i + w.toFun z * velocityGradient b z i
    velocityHessian := fun z i j =>
      b z * w.velocityHessian z i j + velocityGradient b z j * w.velocityGrad z i +
        w.velocityGrad z j * velocityGradient b z i + w.toFun z *
          HypoellipticAleksandrov.Parabolic.velocityHessian b z i j
    memLp := w.memLp.mul_continuous_compact hb.continuous hbCompact
    timeDeriv_memLp := localizedTimeDeriv_memLp w.memLp w.timeDeriv_memLp hb hbCompact
    velocityGrad_memLp := fun i => localizedGradient_memLp w.memLp (w.velocityGrad_memLp i) hb hbCompact
    velocityHessian_memLp := fun j i => by
      simpa only [hhess] using (h₂ j i).1
    hasWeakTimeDeriv := w.hasWeakTimeDeriv.mul_contDiff hb
      (w.memLp.locallyIntegrableOn hp) (w.timeDeriv_memLp.locallyIntegrableOn hp)
    hasWeakVelocityPartialDeriv := fun i => (w.hasWeakVelocityPartialDeriv i).mul_contDiff hb
      (w.memLp.locallyIntegrableOn hp) ((w.velocityGrad_memLp i).locallyIntegrableOn hp)
    hasWeakVelocitySecondPartialDeriv := fun j i => by
      rw [← hhess]
      exact (h₂ j i).2 }

section
variable {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞} (w : ParabolicW12Function d U p) (hp : 1 ≤ p)
  {b : TimeVelocity d → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbCompact : HasCompactSupport b)

@[simp] theorem mulContDiffHasCompactSupport_toFun :
    (w.mulContDiffHasCompactSupport hp hb hbCompact).toFun = fun z => b z * w.toFun z := rfl

@[simp] theorem mulContDiffHasCompactSupport_timeDeriv :
    (w.mulContDiffHasCompactSupport hp hb hbCompact).timeDeriv =
      fun z => b z * w.timeDeriv z + w.toFun z * timeDerivative b z := rfl

@[simp] theorem mulContDiffHasCompactSupport_velocityGrad :
    (w.mulContDiffHasCompactSupport hp hb hbCompact).velocityGrad =
      fun z i => b z * w.velocityGrad z i + w.toFun z * velocityGradient b z i := rfl

@[simp] theorem mulContDiffHasCompactSupport_velocityHessian :
    (w.mulContDiffHasCompactSupport hp hb hbCompact).velocityHessian =
      fun z i j => b z * w.velocityHessian z i j + velocityGradient b z j * w.velocityGrad z i +
        w.velocityGrad z j * velocityGradient b z i + w.toFun z *
          HypoellipticAleksandrov.Parabolic.velocityHessian b z i j := rfl

end

end ParabolicW12Function

end HypoellipticAleksandrov.Parabolic
