module

public import HypoellipticAleksandrov.Parabolic.WeakDerivativesLocal
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Distributional uniqueness for weak time--velocity derivatives

This module proves uniqueness of locally integrable weak derivative
representatives on open time--velocity domains, and the resulting coherence
of the selected representatives in a parabolic weak jet.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

section
variable {d : ℕ} {U : Set (TimeVelocity d)}

theorem ae_eq_of_pairing_eq
    (hU : IsOpen U) {du dv : TimeVelocity d → ℝ}
    (hdu : LocallyIntegrableOn du U volume)
    (hdv : LocallyIntegrableOn dv U volume)
    (hpair : ∀ φ : TimeVelocity d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z in U, du z * φ z ∂volume) = ∫ z in U, dv z * φ z ∂volume) :
    du =ᵐ[timeVelocityVolumeOn U] dv := by
  have hdiff := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hdu.sub hdv) (f := fun z => du z - dv z) ?_
  · rw [Filter.EventuallyEq, ae_restrict_iff' hU.measurableSet]
    filter_upwards [hdiff] with z hz hzU
    exact sub_eq_zero.mp (hz hzU)
  intro φ hφ hc hs
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) (by
    intro z hz
    simp [image_eq_zero_of_notMem_tsupport (fun h => hz (hs h))])]
  simp only [smul_eq_mul, mul_sub, mul_comm (φ _) (du _), mul_comm (φ _) (dv _)]
  rw [integral_sub (integrable_restrict_mul_of_locallyIntegrableOn hdu hφ.continuous hc hs)
    (integrable_restrict_mul_of_locallyIntegrableOn hdv hφ.continuous hc hs),
    hpair φ hφ hc hs, sub_self]

/-- Locally integrable weak-derivative representatives agree almost everywhere. -/
theorem HasWeakFDerivApplyOn.ae_eq {e : TimeVelocity d}
    (hU : IsOpen U) {u du dv : TimeVelocity d → ℝ}
    (hdu : LocallyIntegrableOn du U volume) (hdv : LocallyIntegrableOn dv U volume)
    (hu : HasWeakFDerivApplyOn U e u du) (hv : HasWeakFDerivApplyOn U e u dv) :
    du =ᵐ[timeVelocityVolumeOn U] dv := by
  apply ae_eq_of_pairing_eq hU hdu hdv
  intro φ hφ hc hs
  exact neg_injective ((hu φ hφ hc hs).symm.trans (hv φ hφ hc hs))

end

namespace HasWeakTimeDerivOn

/-- Locally integrable weak time-derivative representatives agree almost
everywhere on an open domain. -/
theorem ae_eq {d : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    {u du dv : TimeVelocity d → ℝ}
    (hdu : LocallyIntegrableOn du U volume)
    (hdv : LocallyIntegrableOn dv U volume)
    (hu : HasWeakTimeDerivOn U u du)
    (hv : HasWeakTimeDerivOn U u dv) :
    du =ᵐ[timeVelocityVolumeOn U] dv := HasWeakFDerivApplyOn.ae_eq (e := (1, 0)) hU hdu hdv hu hv

end HasWeakTimeDerivOn

namespace HasWeakVelocityPartialDerivOn

/-- Locally integrable weak velocity-partial representatives agree almost
everywhere on an open domain. -/
theorem ae_eq {d : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    {i : Fin d} {u dui dvi : TimeVelocity d → ℝ}
    (hdui : LocallyIntegrableOn dui U volume)
    (hdvi : LocallyIntegrableOn dvi U volume)
    (hu : HasWeakVelocityPartialDerivOn U i u dui)
    (hv : HasWeakVelocityPartialDerivOn U i u dvi) :
    dui =ᵐ[timeVelocityVolumeOn U] dvi := HasWeakFDerivApplyOn.ae_eq (e := (0, Pi.single i 1)) hU hdui hdvi hu hv

end HasWeakVelocityPartialDerivOn

namespace ParabolicMemLpOn

/-- Restricted `L^p` membership with exponent at least one is locally
integrable on the underlying raw set. -/
theorem locallyIntegrableOn {d : ℕ} {U : Set (TimeVelocity d)}
    {p : ℝ≥0∞} {f : TimeVelocity d → ℝ}
    (hf : ParabolicMemLpOn U p f) (hp : 1 ≤ p) :
    LocallyIntegrableOn f U volume := by
  letI : IsLocallyFiniteMeasure (timeVelocityVolumeOn U) :=
    Measure.isLocallyFiniteMeasure_of_le Measure.restrict_le_self
  exact locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable hp)

end ParabolicMemLpOn

namespace HasWeakTimeDerivOn

/-- Weak time-derivative representatives in restricted `L^p`, with `p ≥ 1`,
agree almost everywhere on an open domain. -/
theorem ae_eq_of_memLp {d : ℕ} {U : Set (TimeVelocity d)}
    {p : ℝ≥0∞} (hU : IsOpen U) (hp : 1 ≤ p)
    {u du dv : TimeVelocity d → ℝ}
    (hdu : ParabolicMemLpOn U p du)
    (hdv : ParabolicMemLpOn U p dv)
    (hu : HasWeakTimeDerivOn U u du)
    (hv : HasWeakTimeDerivOn U u dv) :
    du =ᵐ[timeVelocityVolumeOn U] dv :=
  ae_eq hU (hdu.locallyIntegrableOn hp) (hdv.locallyIntegrableOn hp) hu hv

end HasWeakTimeDerivOn

namespace HasWeakVelocityPartialDerivOn

/-- Weak velocity-partial representatives in restricted `L^p`, with `p ≥ 1`,
agree almost everywhere on an open domain. -/
theorem ae_eq_of_memLp {d : ℕ} {U : Set (TimeVelocity d)}
    {p : ℝ≥0∞} (hU : IsOpen U) (hp : 1 ≤ p)
    {i : Fin d} {u dui dvi : TimeVelocity d → ℝ}
    (hdui : ParabolicMemLpOn U p dui)
    (hdvi : ParabolicMemLpOn U p dvi)
    (hu : HasWeakVelocityPartialDerivOn U i u dui)
    (hv : HasWeakVelocityPartialDerivOn U i u dvi) :
    dui =ᵐ[timeVelocityVolumeOn U] dvi :=
  ae_eq hU (hdui.locallyIntegrableOn hp) (hdvi.locallyIntegrableOn hp) hu hv

end HasWeakVelocityPartialDerivOn

/-- The ordered velocity Hessian differentiates the selected gradient component. -/
theorem velocityGradient_velocityGradient {d : ℕ} {b : TimeVelocity d → ℝ}
    {i j : Fin d} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (z : TimeVelocity d) :
    velocityGradient (fun y => velocityGradient b y i) z j =
      HypoellipticAleksandrov.Parabolic.velocityHessian b z i j := by
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ b) :=
    (contDiff_infty_iff_fderiv.mp hb).2
  have hgradDiff : DifferentiableAt ℝ (fderiv ℝ b) z :=
    hgrad.contDiffAt.differentiableAt (by simp)
  have hraw : velocityGradient (fun y => velocityGradient b y i) z j =
      HypoellipticAleksandrov.Parabolic.velocityHessian b z j i := by
    unfold velocityGradient HypoellipticAleksandrov.Parabolic.velocityHessian
    rw [fderiv_clm_apply hgradDiff (differentiableAt_const _)]
    have hconst : fderiv ℝ (fun _ : TimeVelocity d =>
        ((0, Pi.single i 1) : TimeVelocity d)) z = 0 :=
      (hasFDerivAt_const ((0, Pi.single i 1) : TimeVelocity d) z).fderiv
    rw [hconst]
    simp
  have hsymm := velocityHessian_isSymm
    (hb.of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)) z
  exact hraw.trans (hsymm.apply i j)

namespace ParabolicW12Function

section
variable {d : ℕ}

/-- A.e.-equal values of two weak jets force a.e. equality of their selected
time, velocity-gradient, and ordered velocity-Hessian representatives. -/
theorem ae_eq_jet_of_value_ae {U : Set (TimeVelocity d)}
    {p : ℝ≥0∞} (hU : IsOpen U) (hp : 1 ≤ p)
    (w w' : ParabolicW12Function d U p)
    (hvalue : w.toFun =ᵐ[timeVelocityVolumeOn U] w'.toFun) :
    w.timeDeriv =ᵐ[timeVelocityVolumeOn U] w'.timeDeriv ∧
      (∀ i : Fin d,
        (fun z => w.velocityGrad z i) =ᵐ[timeVelocityVolumeOn U]
          (fun z => w'.velocityGrad z i)) ∧
      (∀ i j : Fin d,
        (fun z => w.velocityHessian z i j) =ᵐ[timeVelocityVolumeOn U]
          (fun z => w'.velocityHessian z i j)) := by
  have htime :=
    HasWeakTimeDerivOn.ae_eq_of_memLp hU hp
      w.timeDeriv_memLp w'.timeDeriv_memLp w.hasWeakTimeDeriv
      (w'.hasWeakTimeDeriv.congr_value_ae hvalue.symm)
  have hgrad : ∀ i : Fin d,
      (fun z => w.velocityGrad z i) =ᵐ[timeVelocityVolumeOn U]
        (fun z => w'.velocityGrad z i) := by
    intro i
    exact HasWeakVelocityPartialDerivOn.ae_eq_of_memLp hU hp
      (w.velocityGrad_memLp i) (w'.velocityGrad_memLp i)
      (w.hasWeakVelocityPartialDeriv i)
      ((w'.hasWeakVelocityPartialDeriv i).congr_value_ae hvalue.symm)
  refine ⟨htime, hgrad, ?_⟩
  intro i j
  exact HasWeakVelocityPartialDerivOn.ae_eq_of_memLp hU hp
    (w.velocityHessian_memLp i j) (w'.velocityHessian_memLp i j)
    (w.hasWeakVelocitySecondPartialDeriv i j)
    ((w'.hasWeakVelocitySecondPartialDeriv i j).congr_value_ae (hgrad i).symm)

theorem velocityGradient_contDiff_infty
    {f : TimeVelocity d → ℝ} {i : Fin d}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => velocityGradient f z i) := velocityGradient_contDiff hf

theorem velocityGradient_velocityGradient_commute
    {f : TimeVelocity d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i j : Fin d) (z : TimeVelocity d) :
    velocityGradient (fun y => velocityGradient f y i) z j =
      velocityGradient (fun y => velocityGradient f y j) z i := by
  rw [velocityGradient_velocityGradient hf, velocityGradient_velocityGradient hf]
  exact (velocityHessian_isSymm (hf.of_le (by exact WithTop.coe_le_coe.mpr le_top)) z).apply j i

/-- Ordered weak velocity-Hessian representatives commute almost everywhere
on an open domain. -/
theorem velocityHessian_ae_eq_swap {U : Set (TimeVelocity d)}
    (hU : IsOpen U)
    (w : ParabolicW12Function d U 2)
    (i j : Fin d) :
    (fun z => w.velocityHessian z i j)
      =ᵐ[timeVelocityVolumeOn U]
        fun z => w.velocityHessian z j i := by
  apply ae_eq_of_pairing_eq hU
    ((w.velocityHessian_memLp i j).locallyIntegrableOn (by norm_num))
    ((w.velocityHessian_memLp j i).locallyIntegrableOn (by norm_num))
  intro φ hφSmooth hφCompact hφSub
  have htestSmooth (k : Fin d) :
      ContDiff ℝ (⊤ : ℕ∞) (fun z => velocityGradient φ z k) :=
    velocityGradient_contDiff_infty hφSmooth
  have htestCompact (k : Fin d) :
      HasCompactSupport (fun z => velocityGradient φ z k) :=
    _root_.HypoellipticAleksandrov.Parabolic.velocityGradient_compact hφCompact
  have htestSub (k : Fin d) :
      tsupport (fun z => velocityGradient φ z k) ⊆ U :=
    (velocityGradient_tsupport _).trans hφSub
  have hijSecond := w.hasWeakVelocitySecondPartialDeriv i j
    φ hφSmooth hφCompact hφSub
  have hiFirst := w.hasWeakVelocityPartialDeriv i
    (fun z => velocityGradient φ z j) (htestSmooth j)
    (htestCompact j) (htestSub j)
  have hjiSecond := w.hasWeakVelocitySecondPartialDeriv j i
    φ hφSmooth hφCompact hφSub
  have hjFirst := w.hasWeakVelocityPartialDeriv j
    (fun z => velocityGradient φ z i) (htestSmooth i)
    (htestCompact i) (htestSub i)
  calc
    (∫ z in U, w.velocityHessian z i j * φ z ∂volume) =
        ∫ z in U, w.toFun z *
          velocityGradient (fun y => velocityGradient φ y j) z i ∂volume := by
      linarith only [hijSecond, hiFirst]
    _ = ∫ z in U, w.toFun z *
          velocityGradient (fun y => velocityGradient φ y i) z j ∂volume := by
      apply setIntegral_congr_fun hU.measurableSet
      intro z hz
      simp only
      rw [velocityGradient_velocityGradient_commute hφSmooth]
    _ = ∫ z in U, w.velocityHessian z j i * φ z ∂volume := by
      linarith only [hjiSecond, hjFirst]

end

end ParabolicW12Function

end HypoellipticAleksandrov.Parabolic
