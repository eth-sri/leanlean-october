module

public import HypoellipticAleksandrov.Parabolic.WeakJetExtension
public import Mathlib.Analysis.Convolution
import Mathlib.Tactic.FunProp
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder





/-!
# Convolution of selected parabolic weak jets

This module smooths a global selected weak jet by right convolution against one
smooth compactly supported scalar kernel.  It records only the selected time,
velocity-gradient, and ordered velocity-Hessian commutations.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped Convolution ENNReal Topology

variable {d : Nat}

/-- Right convolution on time--velocity space against its literal product volume. -/
def parabolicConvolution
    (f rho : TimeVelocity d -> Real) : TimeVelocity d -> Real :=
  f ⋆[ContinuousLinearMap.mul Real Real, (volume )] rho

variable {rho : TimeVelocity d -> Real}

private theorem contDiff_translatedKernel
    (hrho : ContDiff Real PDE.smoothOrder rho) (z : TimeVelocity d) :
    ContDiff Real PDE.smoothOrder (fun y => rho (z - y)) := by
  fun_prop

private theorem hasCompactSupport_translatedKernel
    (hrho : HasCompactSupport rho) (z : TimeVelocity d) :
    HasCompactSupport (fun y => rho (z - y)) := (HasCompactSupport.comp_homeomorph hrho (Homeomorph.subLeft z))

private theorem fderiv_translatedKernel_apply
    (hrho : ContDiff Real PDE.smoothOrder rho) (z y q : TimeVelocity d) :
    fderiv Real (fun x => rho (z - x)) y q = -fderiv Real rho (z - y) q := by


  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    neg_apply, ContinuousLinearMap.id_apply, map_neg] using
    congrArg (fun L : TimeVelocity d →L[Real] Real => L q) ((hrho.differentiable (by simp) (z - y)).hasFDerivAt.comp y (show HasFDerivAt (fun x  => z - x)
      (-ContinuousLinearMap.id Real (TimeVelocity d)) y by
        simpa only [sub_eq_add_neg, Pi.neg_apply, id_eq] using ((hasFDerivAt_id y).neg.const_add z))).fderiv

private theorem fderiv_parabolicConvolution_eq
    {u du rho : TimeVelocity d -> Real}
    {D : (TimeVelocity d -> Real) -> TimeVelocity d -> Real} (q : TimeVelocity d)
    (hweak : forall phi : TimeVelocity d -> Real,
      ContDiff Real PDE.smoothOrder phi ->
      HasCompactSupport phi ->
      (∫ y, u y * D phi y) = -∫ y, du y * phi y)
    (hD : forall (z y : TimeVelocity d),
      D (fun x => rho (z - x)) y = -fderiv Real rho (z - y) q)
    (huLoc : LocallyIntegrable u )
    (hduLoc : LocallyIntegrable du )
    (hrho : ContDiff Real PDE.smoothOrder rho)
    (hrhoCompact : HasCompactSupport rho) (z : TimeVelocity d) :
    fderiv Real (parabolicConvolution u rho) z q = parabolicConvolution du rho z := by
  let sharedTerm_8e572b75f1 := (∫ y, u y * fderiv Real rho (z - y) q)
  let sharedTerm_92c8e36684 := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))

  let phi  := fun y => rho (z - y)



  have hleft : (∫ y, u y * D phi y) =
      -(sharedTerm_8e572b75f1) := by
    calc
      (∫ y, u y * D phi y) =
          ∫ y, -(u y * fderiv Real rho (z - y) q) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [hD z y]
        ring
      _ = -(sharedTerm_8e572b75f1) := by
        rw [integral_neg]

  have hconv := hrhoCompact.hasFDerivAt_convolution_right
    (ContinuousLinearMap.mul Real Real) huLoc (hrho.of_le (by simp)) z
  calc
    fderiv Real (parabolicConvolution u rho) z q =
        ((u ⋆[ContinuousLinearMap.precompR (TimeVelocity d)
          (ContinuousLinearMap.mul Real Real),
          sharedTerm_92c8e36684] fderiv Real rho) z) q := (id (congrArg (fun L => L q) (HasFDerivAt.fderiv hconv)))
    _ = (u ⋆[ContinuousLinearMap.mul Real Real, sharedTerm_92c8e36684]
        fun a => fderiv Real rho a q) z := convolution_precompR_apply (ContinuousLinearMap.mul Real Real) huLoc
        (hrhoCompact.fderiv Real) (hrho.continuous_fderiv (by simp)) z q
    _ = sharedTerm_8e572b75f1 := convolution_def (ContinuousLinearMap.mul Real Real)
    _ = -(-(sharedTerm_8e572b75f1)) := by ring
    _ = -(∫ y, u y * D phi y) := by rw [hleft]
    _ = ∫ y, du y * phi y := by simp only [(hweak phi (contDiff_translatedKernel hrho z) (hasCompactSupport_translatedKernel hrhoCompact z)), neg_neg]
    _ = parabolicConvolution du rho z := (by
        calc
          (∫ y, du y * phi y) = ∫ y, du y * rho (z - y) := rfl
          _ = parabolicConvolution du rho z := rfl)

/-- Convolution by a smooth compactly supported kernel is globally smooth. -/
theorem contDiff_parabolicConvolution
     {f rho : TimeVelocity d -> Real}
    (hf : LocallyIntegrable f )
    (hrho : ContDiff Real PDE.smoothOrder rho)
    (hrhoCompact : HasCompactSupport rho) :
    ContDiff Real PDE.smoothOrder (parabolicConvolution f rho) := (id (HasCompactSupport.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hrhoCompact hf hrho))

/-- Right convolution commutes with the selected global weak time derivative. -/
theorem timeDerivative_parabolicConvolution
     {u du rho : TimeVelocity d -> Real}
    (hu : HasWeakTimeDerivOn Set.univ u du)
    (huLoc : LocallyIntegrable u )
    (hduLoc : LocallyIntegrable du )
    (hrho : ContDiff Real PDE.smoothOrder rho)
    (hrhoCompact : HasCompactSupport rho) :
    timeDerivative (parabolicConvolution u rho) = parabolicConvolution du rho := by
  funext z
  unfold timeDerivative
  apply fderiv_parabolicConvolution_eq (u := u) (du := du) (rho := rho) (1, 0)
    (D := timeDerivative) ?_ ?_ huLoc hduLoc hrho hrhoCompact z
  · intro phi hphi hphiCompact
    simpa only [Measure.restrict_univ] using hu phi hphi hphiCompact (Set.subset_univ _)
  · simp_all [timeDerivative, fderiv_translatedKernel_apply]

/-- Right convolution commutes with every selected global weak velocity derivative. -/
theorem velocityGradient_parabolicConvolution
     {u dui rho : TimeVelocity d -> Real} {i : Fin d}
    (hu : HasWeakVelocityPartialDerivOn Set.univ i u dui)
    (huLoc : LocallyIntegrable u )
    (hduiLoc : LocallyIntegrable dui )
    (hrho : ContDiff Real PDE.smoothOrder rho)
    (hrhoCompact : HasCompactSupport rho) :
    (fun z => velocityGradient (parabolicConvolution u rho) z i) =
      parabolicConvolution dui rho := by
  funext z
  unfold velocityGradient
  apply fderiv_parabolicConvolution_eq (u := u) (du := dui) (rho := rho)
    (0, Pi.single i 1) (D := fun f z => velocityGradient f z i) ?_ ?_ huLoc hduiLoc hrho
      hrhoCompact z
  · intro phi hphi hphiCompact
    simpa only [Measure.restrict_univ] using hu phi hphi hphiCompact (Set.subset_univ _)
  · simp_all [velocityGradient, fderiv_translatedKernel_apply]

variable {f : TimeVelocity d -> Real}

private theorem fderiv_velocityGradient_apply
    (hf : ContDiff Real 2 f) (z qi qj : TimeVelocity d) :
    fderiv Real (fun x => fderiv Real f x qi) z qj =
      fderiv Real (fderiv Real f) z qj qi := by

  rw [fderiv_clm_apply ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z) (differentiableAt_const (c := qi))]
  simp

private theorem velocityHessian_eq_fderiv_velocityGradient
     {i j : Fin d} (hf : ContDiff Real 2 f)
    (z : TimeVelocity d) :
    velocityHessian f z i j =
      fderiv Real (fun x => velocityGradient f x i) z (0, Pi.single j 1) := (Trans.trans
  (Trans.trans (Eq.symm (congrFun (congrFun (Matrix.IsSymm.eq (velocityHessian_isSymm hf z)) i) j))
    (Eq.symm (fderiv_velocityGradient_apply hf z (0, Pi.single i 1) (0, Pi.single j 1))))
  (Eq.refl ((fderiv ℝ (fun x => (fderiv ℝ f x) (0, Pi.single i 1)) z) (0, Pi.single j 1))))

/-- Right convolution commutes with the ordered selected global velocity Hessian. -/
theorem velocityHessian_parabolicConvolution
     {u dui duij rho : TimeVelocity d -> Real} {i j : Fin d}
    (hui : HasWeakVelocityPartialDerivOn Set.univ i u dui)
    (huij : HasWeakVelocityPartialDerivOn Set.univ j dui duij)
    (huLoc : LocallyIntegrable u )
    (hduiLoc : LocallyIntegrable dui )
    (hduijLoc : LocallyIntegrable duij )
    (hrho : ContDiff Real PDE.smoothOrder rho)
    (hrhoCompact : HasCompactSupport rho) :
    (fun z => velocityHessian (parabolicConvolution u rho) z i j) =
      parabolicConvolution duij rho := by


  funext z
  rw [velocityHessian_eq_fderiv_velocityGradient
    ((contDiff_parabolicConvolution huLoc hrho hrhoCompact).of_le
      (WithTop.coe_le_coe.mpr le_top))]
  rw [(velocityGradient_parabolicConvolution hui huLoc hduiLoc hrho hrhoCompact)]
  exact congrFun (velocityGradient_parabolicConvolution huij hduiLoc hduijLoc hrho hrhoCompact) z

namespace ParabolicW12Function

/-- The convolution of a global selected jet value is smooth. -/
theorem contDiff_convolution {d : Nat} {p : ENNReal}
    (w : ParabolicW12Function d Set.univ p) (hp : 1 <= p)
    (rho : TimeVelocity d -> Real) (hrho : ContDiff Real PDE.smoothOrder rho)
    (hrhoCompact : HasCompactSupport rho) :
    ContDiff Real PDE.smoothOrder (parabolicConvolution w.toFun rho) := (contDiff_parabolicConvolution (locallyIntegrableOn_univ.mp (ParabolicMemLpOn.locallyIntegrableOn w.memLp hp)) hrho
  hrhoCompact)

variable {d : Nat} {p : ENNReal} (w : ParabolicW12Function d Set.univ p) (hp : 1 <= p) (rho : TimeVelocity d -> Real) (hrho : ContDiff Real PDE.smoothOrder rho) (hrhoCompact : HasCompactSupport rho)

include hp hrho hrhoCompact
/-- The convolution of a global selected jet commutes with its time representative. -/
theorem timeDerivative_convolution  :
    timeDerivative (parabolicConvolution w.toFun rho) = parabolicConvolution w.timeDeriv rho := by
  apply timeDerivative_parabolicConvolution w.hasWeakTimeDeriv ?_ ?_ hrho hrhoCompact
  · exact locallyIntegrableOn_univ.mp (w.memLp.locallyIntegrableOn hp)
  · exact locallyIntegrableOn_univ.mp (w.timeDeriv_memLp.locallyIntegrableOn hp)

/-- The convolution of a global selected jet commutes with each velocity gradient. -/
theorem velocityGradient_convolution  (i : Fin d) :
    (fun z => velocityGradient (parabolicConvolution w.toFun rho) z i) =
      parabolicConvolution (fun y => w.velocityGrad y i) rho := by
  apply velocityGradient_parabolicConvolution (w.hasWeakVelocityPartialDeriv i) ?_ ?_
    hrho hrhoCompact
  · exact locallyIntegrableOn_univ.mp (w.memLp.locallyIntegrableOn hp)
  · exact locallyIntegrableOn_univ.mp ((w.velocityGrad_memLp i).locallyIntegrableOn hp)

/-- The convolution of a global selected jet commutes with its ordered velocity Hessian. -/
theorem velocityHessian_convolution  (i j : Fin d) :
    (fun z => HypoellipticAleksandrov.Parabolic.velocityHessian
        (parabolicConvolution w.toFun rho) z i j) =
      parabolicConvolution (fun y => w.velocityHessian y i j) rho := by
  apply velocityHessian_parabolicConvolution
    (w.hasWeakVelocityPartialDeriv i) (w.hasWeakVelocitySecondPartialDeriv i j) ?_ ?_ ?_
    hrho hrhoCompact
  · exact locallyIntegrableOn_univ.mp (w.memLp.locallyIntegrableOn hp)
  · exact locallyIntegrableOn_univ.mp ((w.velocityGrad_memLp i).locallyIntegrableOn hp)
  · exact locallyIntegrableOn_univ.mp ((w.velocityHessian_memLp i j).locallyIntegrableOn hp)

end ParabolicW12Function

end HypoellipticAleksandrov.Parabolic
