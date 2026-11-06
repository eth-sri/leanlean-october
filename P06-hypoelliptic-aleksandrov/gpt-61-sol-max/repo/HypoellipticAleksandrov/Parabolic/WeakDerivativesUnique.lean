module

public import HypoellipticAleksandrov.Parabolic.WeakDerivativesLocal
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Distributional uniqueness for weak time--velocity derivatives

This module proves uniqueness of locally integrable weak derivative
representatives on open time--velocity domains, and the resulting coherence
of the selected representatives in a parabolic weak jet.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal

private theorem ae_eq_of_pairing_eq {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d}
    (hU : IsOpen U) {du dv : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hdu : LocallyIntegrableOn du U )
    (hdv : LocallyIntegrableOn dv U )
    (hpair : ∀ φ : HypoellipticAleksandrov.Parabolic.ScalarField d, ContDiff ℝ PDE.smoothOrder φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z in U, du z * φ z) = ∫ z in U, dv z * φ z) :
    du =ᵐ[timeVelocityVolumeOn U] dv := by

  rw [Filter.EventuallyEq, ae_restrict_iff' hU.measurableSet]
  filter_upwards [(by
      refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (f := fun z => du z - dv z) (hdu.sub hdv) ?_
      intro φ hφSmooth hφCompact hφSub
      have hφCont  := hφSmooth.continuous


      have hduφK : IntegrableOn (fun z => du z * φ z) (tsupport φ)  := by
        simpa [smul_eq_mul] using
          (hdu.integrableOn_compact_subset hφSub hφCompact.isCompact).smul_continuousOn hφCont.continuousOn hφCompact.isCompact
      have hdvφK : IntegrableOn (fun z => dv z * φ z) (tsupport φ)  := by
        simpa [smul_eq_mul] using
          (hdv.integrableOn_compact_subset hφSub hφCompact.isCompact).smul_continuousOn hφCont.continuousOn hφCompact.isCompact






      calc
        ∫ z, φ z • (du z - dv z) =
            ∫ z, φ z * (du z - dv z) := rfl
        _ = ∫ z in U, φ z * (du z - dv z) := by
              rw [setIntegral_eq_integral_of_forall_compl_eq_zero (by
                  intro z hz

                  simp [image_eq_zero_of_notMem_tsupport (fun hz' => hz (hφSub hz'))])]
        _ = 0 := (by
            calc
              ∫ z in U, φ z * (du z - dv z) =
                  ∫ z in U, (du z * φ z - dv z * φ z) := by
                    apply setIntegral_congr_fun hU.measurableSet
                    intro z hz
                    ring
              _ = (∫ z in U, du z * φ z) - ∫ z in U, dv z * φ z := by
                    rw [integral_sub (by
                        simpa [IntegrableOn, timeVelocityVolumeOn] using
                          hduφK.of_forall_diff_eq_zero hU.measurableSet (by
                              intro z hz
                              simp [image_eq_zero_of_notMem_tsupport hz.2])) (by
                        simpa [IntegrableOn, timeVelocityVolumeOn] using
                          hdvφK.of_forall_diff_eq_zero hU.measurableSet (by
                              intro z hz
                              simp [image_eq_zero_of_notMem_tsupport hz.2]))]
              _ = 0 := by rw [hpair φ hφSmooth hφCompact hφSub, sub_self]))] with z hz hzU
  exact sub_eq_zero.mp (hz hzU)

namespace HasWeakTimeDerivOn

/-- Locally integrable weak time-derivative representatives agree almost
everywhere on an open domain. -/
theorem ae_eq {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} (hU : IsOpen U)
    {u du dv : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hdu : LocallyIntegrableOn du U )
    (hdv : LocallyIntegrableOn dv U )
    (hu : HasWeakTimeDerivOn U u du)
    (hv : HasWeakTimeDerivOn U u dv) :
    du =ᵐ[timeVelocityVolumeOn U] dv := by
  apply ae_eq_of_pairing_eq hU hdu hdv
  intro φ hφSmooth hφCompact hφSub
  apply neg_injective
  rw [← hu φ hφSmooth hφCompact hφSub, ← hv φ hφSmooth hφCompact hφSub]

end HasWeakTimeDerivOn

namespace HasWeakVelocityPartialDerivOn

/-- Locally integrable weak velocity-partial representatives agree almost
everywhere on an open domain. -/
theorem ae_eq {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} (hU : IsOpen U)
    {i : Fin d} {u dui dvi : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hdui : LocallyIntegrableOn dui U )
    (hdvi : LocallyIntegrableOn dvi U )
    (hu : HasWeakVelocityPartialDerivOn U i u dui)
    (hv : HasWeakVelocityPartialDerivOn U i u dvi) :
    dui =ᵐ[timeVelocityVolumeOn U] dvi := by
  apply ae_eq_of_pairing_eq hU hdui hdvi
  intro φ hφSmooth hφCompact hφSub
  apply neg_injective
  rw [← hu φ hφSmooth hφCompact hφSub, ← hv φ hφSmooth hφCompact hφSub]

end HasWeakVelocityPartialDerivOn

namespace ParabolicMemLpOn

/-- Restricted `L^p` membership with exponent at least one is locally
integrable on the underlying raw set. -/
theorem locallyIntegrableOn {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d}
    {p : ℝ≥0∞} {f : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hf : ParabolicMemLpOn U p f) (hp : 1 ≤ p) :
    LocallyIntegrableOn f U  := (locallyIntegrableOn_of_locallyIntegrable_restrict (MemLp.locallyIntegrable hf hp))

end ParabolicMemLpOn

namespace HasWeakTimeDerivOn

/-- Weak time-derivative representatives in restricted `L^p`, with `p ≥ 1`,
agree almost everywhere on an open domain. -/
theorem ae_eq_of_memLp {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d}
    {p : ℝ≥0∞} (hU : IsOpen U) (hp : 1 ≤ p)
    {u du dv : HypoellipticAleksandrov.Parabolic.ScalarField d}
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
theorem ae_eq_of_memLp {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d}
    {p : ℝ≥0∞} (hU : IsOpen U) (hp : 1 ≤ p)
    {i : Fin d} {u dui dvi : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hdui : ParabolicMemLpOn U p dui)
    (hdvi : ParabolicMemLpOn U p dvi)
    (hu : HasWeakVelocityPartialDerivOn U i u dui)
    (hv : HasWeakVelocityPartialDerivOn U i u dvi) :
    dui =ᵐ[timeVelocityVolumeOn U] dvi :=
  ae_eq hU (hdui.locallyIntegrableOn hp) (hdvi.locallyIntegrableOn hp) hu hv

end HasWeakVelocityPartialDerivOn

namespace ParabolicW12Function

/-- A.e.-equal values of two weak jets force a.e. equality of their selected
time, velocity-gradient, and ordered velocity-Hessian representatives. -/
theorem ae_eq_jet_of_value_ae {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d}
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
  have htime  :=
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

variable {d : ℕ}

variable {f : HypoellipticAleksandrov.Parabolic.ScalarField d}

variable {i : Fin d}

private theorem velocityGradient_contDiff_infty

    (hf : ContDiff ℝ PDE.smoothOrder f) :
    ContDiff ℝ PDE.smoothOrder (fun z => velocityGradient f z i) := by
  unfold velocityGradient
  exact (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

private theorem velocityGradient_hasCompactSupport

    (hf : HasCompactSupport f) :
    HasCompactSupport (fun z => velocityGradient f z i) := (id (HasCompactSupport.fderiv_apply ℝ hf (0, Pi.single i 1)))

private theorem velocityGradient_tsupport_subset
      :
    tsupport (fun z => velocityGradient f z i) ⊆ tsupport f := by
  unfold velocityGradient
  change closure (Function.support
    (fun z => fderiv ℝ f z (0, Pi.single i 1))) ⊆ tsupport f
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

private theorem velocityGradient_velocityGradient_commute
     (hf : ContDiff ℝ PDE.smoothOrder f)
    (i j : Fin d) (z : TimeVelocity d) :
    velocityGradient (fun y => velocityGradient f y i) z j =
      velocityGradient (fun y => velocityGradient f y j) z i := by



  have hgradDiff : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((contDiff_infty_iff_fderiv.mp hf).2).contDiffAt.differentiableAt (by simp)
  have hleft : velocityGradient (fun y => velocityGradient f y i) z j =
      HypoellipticAleksandrov.Parabolic.velocityHessian f z j i := by
    unfold velocityGradient HypoellipticAleksandrov.Parabolic.velocityHessian
    rw [fderiv_clm_apply hgradDiff (differentiableAt_const _)]

    rw [((hasFDerivAt_const ((((0, Pi.single i 1) : TimeVelocity d))) z).fderiv)]
    simp
  have hright : velocityGradient (fun y => velocityGradient f y j) z i =
      HypoellipticAleksandrov.Parabolic.velocityHessian f z i j := by
    unfold velocityGradient HypoellipticAleksandrov.Parabolic.velocityHessian
    rw [fderiv_clm_apply hgradDiff (differentiableAt_const _)]

    rw [((hasFDerivAt_const ((((0, Pi.single j 1) : TimeVelocity d))) z).fderiv)]
    simp
  rw [hleft, hright]
  exact (HypoellipticAleksandrov.Parabolic.velocityHessian_isSymm
      (hf.of_le (by
        simp_all)) z).apply i j

/-- Ordered weak velocity-Hessian representatives commute almost everywhere
on an open domain. -/
theorem velocityHessian_ae_eq_swap
     {U : HypoellipticAleksandrov.Parabolic.Region d}
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
      ContDiff ℝ PDE.smoothOrder (fun z => velocityGradient φ z k) :=
    velocityGradient_contDiff_infty hφSmooth
  have htestCompact (k : Fin d) :
      HasCompactSupport (fun z => velocityGradient φ z k) :=
    velocityGradient_hasCompactSupport hφCompact
  have htestSub (k : Fin d) :
      tsupport (fun z => velocityGradient φ z k) ⊆ U :=
    velocityGradient_tsupport_subset.trans hφSub
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
    (∫ z in U, w.velocityHessian z i j * φ z) =
        ∫ z in U, w.toFun z *
          velocityGradient (fun y => velocityGradient φ y j) z i := by
      linarith only [hijSecond, hiFirst]
    _ = ∫ z in U, w.toFun z *
          velocityGradient (fun y => velocityGradient φ y i) z j := by
      apply setIntegral_congr_fun hU.measurableSet
      intro z hz
      simp only
      rw [velocityGradient_velocityGradient_commute hφSmooth]
    _ = ∫ z in U, w.velocityHessian z j i * φ z := by
      linarith only [hjiSecond, hjFirst]

end ParabolicW12Function

end HypoellipticAleksandrov.Parabolic
