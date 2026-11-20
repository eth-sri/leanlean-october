module

public import HypoellipticAleksandrov.Parabolic.WeakDerivatives

/-!
# Elementary locality for weak time--velocity derivatives

This module transports the raw weak-derivative predicates across restricted
domains and restricted-volume almost-everywhere representative changes.  It
also packages the corresponding local representative predicate.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace ParabolicMemLpOn

/-- Restricted `L^p` membership is monotone under domain restriction. -/
theorem mono {d : ℕ} {U V : Set (TimeVelocity d)} {p : ℝ≥0∞}
    {f : TimeVelocity d → ℝ} (hf : ParabolicMemLpOn U p f) (hVU : V ⊆ U) :
    ParabolicMemLpOn V p f :=
  hf.mono_measure (Measure.restrict_mono_set volume hVU)

end ParabolicMemLpOn

namespace HasWeakFDerivApplyOn

variable {d : ℕ} {U V : Set (TimeVelocity d)} {e : TimeVelocity d}

/-- Changing representatives almost everywhere preserves the weak derivative. -/
theorem congr_ae {u v du dv : TimeVelocity d → ℝ}
    (hu : HasWeakFDerivApplyOn U e u du) (huv : u =ᵐ[timeVelocityVolumeOn U] v)
    (hd : du =ᵐ[timeVelocityVolumeOn U] dv) : HasWeakFDerivApplyOn U e v dv := by
  intro φ hφ hc hs
  rw [← integral_congr_ae (huv.mono fun z hz => congrArg (· * fderiv ℝ φ z e) hz),
    ← integral_congr_ae (hd.mono fun z hz => congrArg (· * φ z) hz)]
  exact hu φ hφ hc hs

/-- Restriction to any smaller carrier preserves the weak derivative. -/
theorem restrict {u du : TimeVelocity d → ℝ}
    (hu : HasWeakFDerivApplyOn U e u du) (hVU : V ⊆ U) : HasWeakFDerivApplyOn V e u du := by
  intro φ hφ hc hs
  have hI {f g : TimeVelocity d → ℝ} (h : tsupport g ⊆ V) :
      (∫ z in V, f z * g z ∂volume) = ∫ z in U, f z * g z ∂volume := by
    have hzero {S : Set (TimeVelocity d)} (hS : tsupport g ⊆ S) :
        ∀ z ∉ S, f z * g z = 0 := fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport (fun hzg => hz (hS hzg)), mul_zero]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (hzero h)).trans
      (setIntegral_eq_integral_of_forall_compl_eq_zero (hzero (h.trans hVU))).symm
  rw [hI ((tsupport_fderiv_apply_subset ℝ e).trans hs), hI hs]
  exact hu φ hφ hc (hs.trans hVU)

end HasWeakFDerivApplyOn

namespace HasWeakTimeDerivOn

section
variable {d : ℕ} {U : Set (TimeVelocity d)}

/-- Change only the value representative in a weak time-derivative identity. -/
theorem congr_value_ae
    {u v du : TimeVelocity d → ℝ}
    (hu : HasWeakTimeDerivOn U u du)
    (huv : u =ᵐ[timeVelocityVolumeOn U] v) :
    HasWeakTimeDerivOn U v du := HasWeakFDerivApplyOn.congr_ae (e := (1, 0)) hu huv Filter.EventuallyEq.rfl

/-- Change both representatives in a weak time-derivative identity. -/
theorem congr_ae
    {u v du dv : TimeVelocity d → ℝ}
    (hu : HasWeakTimeDerivOn U u du)
    (huv : u =ᵐ[timeVelocityVolumeOn U] v)
    (hdudv : du =ᵐ[timeVelocityVolumeOn U] dv) :
    HasWeakTimeDerivOn U v dv := HasWeakFDerivApplyOn.congr_ae (e := (1, 0)) hu huv hdudv

end

/-- Restrict a raw weak time-derivative identity to any smaller set. -/
theorem restrict {d : ℕ} {U V : Set (TimeVelocity d)}
    {u du : TimeVelocity d → ℝ} (hu : HasWeakTimeDerivOn U u du)
    (hVU : V ⊆ U) : HasWeakTimeDerivOn V u du := HasWeakFDerivApplyOn.restrict (e := (1, 0)) hu hVU

end HasWeakTimeDerivOn

namespace HasWeakVelocityPartialDerivOn

section
variable {d : ℕ} {U : Set (TimeVelocity d)} {i : Fin d}

/-- Change only the value representative in a weak velocity-derivative identity. -/
theorem congr_value_ae
    {u v dui : TimeVelocity d → ℝ}
    (hu : HasWeakVelocityPartialDerivOn U i u dui)
    (huv : u =ᵐ[timeVelocityVolumeOn U] v) :
    HasWeakVelocityPartialDerivOn U i v dui := HasWeakFDerivApplyOn.congr_ae (e := (0, Pi.single i 1)) hu huv Filter.EventuallyEq.rfl

/-- Change both representatives in a weak velocity-derivative identity. -/
theorem congr_ae
    {u v dui dvi : TimeVelocity d → ℝ}
    (hu : HasWeakVelocityPartialDerivOn U i u dui)
    (huv : u =ᵐ[timeVelocityVolumeOn U] v)
    (hduidvi : dui =ᵐ[timeVelocityVolumeOn U] dvi) :
    HasWeakVelocityPartialDerivOn U i v dvi := HasWeakFDerivApplyOn.congr_ae (e := (0, Pi.single i 1)) hu huv hduidvi

end

/-- Restrict a raw weak velocity-derivative identity to any smaller set. -/
theorem restrict {d : ℕ} {U V : Set (TimeVelocity d)} {i : Fin d}
    {u dui : TimeVelocity d → ℝ} (hu : HasWeakVelocityPartialDerivOn U i u dui)
    (hVU : V ⊆ U) : HasWeakVelocityPartialDerivOn V i u dui := HasWeakFDerivApplyOn.restrict (e := (0, Pi.single i 1)) hu hVU

end HasWeakVelocityPartialDerivOn

namespace ParabolicW12Function

/-- Keep the selected jet representatives while restricting their domain. -/
def restrict {d : ℕ} {U V : Set (TimeVelocity d)} {p : ℝ≥0∞}
    (w : ParabolicW12Function d U p) (hVU : V ⊆ U) :
    ParabolicW12Function d V p where
  toFun := w.toFun
  timeDeriv := w.timeDeriv
  velocityGrad := w.velocityGrad
  velocityHessian := w.velocityHessian
  memLp := w.memLp.mono hVU
  timeDeriv_memLp := w.timeDeriv_memLp.mono hVU
  velocityGrad_memLp := fun i => (w.velocityGrad_memLp i).mono hVU
  velocityHessian_memLp := fun i j => (w.velocityHessian_memLp i j).mono hVU
  hasWeakTimeDeriv := w.hasWeakTimeDeriv.restrict hVU
  hasWeakVelocityPartialDeriv := fun i =>
    (w.hasWeakVelocityPartialDeriv i).restrict hVU
  hasWeakVelocitySecondPartialDeriv := fun i j =>
    (w.hasWeakVelocitySecondPartialDeriv i j).restrict hVU

end ParabolicW12Function

/-- Local anisotropic weak `W^{1,2,p}` membership, formulated through
compactly-contained open representative witnesses. -/
def ParabolicW12Loc {d : ℕ} (U : Set (TimeVelocity d)) (p : ℝ≥0∞)
    (u : TimeVelocity d → ℝ) : Prop :=
  ∀ V : Set (TimeVelocity d), IsOpen V → IsCompact (closure V) → closure V ⊆ U →
    ∃ w : ParabolicW12Function d V p, w.toFun =ᵐ[timeVelocityVolumeOn V] u

namespace ParabolicW12Function

end ParabolicW12Function

namespace ParabolicW12Loc

/-- Extract the compactly-contained jet witness in the local predicate. -/
theorem exists_parabolicW12Function {d : ℕ} {U V : Set (TimeVelocity d)}
    {p : ℝ≥0∞} {u : TimeVelocity d → ℝ}
    (hu : ParabolicW12Loc U p u) (hVOpen : IsOpen V)
    (hVCompact : IsCompact (closure V)) (hVU : closure V ⊆ U) :
    ∃ w : ParabolicW12Function d V p, w.toFun =ᵐ[timeVelocityVolumeOn V] u :=
  hu V hVOpen hVCompact hVU

end ParabolicW12Loc

end HypoellipticAleksandrov.Parabolic
