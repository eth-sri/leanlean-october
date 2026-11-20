module

public import HypoellipticAleksandrov.Parabolic.WeakJetExtension
public import Mathlib.Analysis.Convolution

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

section
variable {d : Nat} {rho : TimeVelocity d -> Real} (hrho : ContDiff Real (⊤ : ℕ∞) rho)

/-- Right convolution on time--velocity space against its literal product volume. -/
noncomputable def parabolicConvolution
    (f rho : TimeVelocity d -> Real) : TimeVelocity d -> Real :=
  f ⋆[ContinuousLinearMap.mul Real Real, (volume : Measure (TimeVelocity d))] rho

include hrho in
private theorem contDiff_translatedKernel (z : TimeVelocity d) :
    ContDiff Real (⊤ : ℕ∞) (fun y => rho (z - y)) := by
  fun_prop

private theorem hasCompactSupport_translatedKernel
    (hrho : HasCompactSupport rho) (z : TimeVelocity d) :
    HasCompactSupport (fun y => rho (z - y)) := by
  exact hrho.comp_homeomorph (Homeomorph.subLeft z)

include hrho in
private theorem fderiv_translatedKernel_apply (z y q : TimeVelocity d) :
    fderiv Real (fun x => rho (z - x)) y q = -fderiv Real rho (z - y) q := by
  have hmap : HasFDerivAt (fun x : TimeVelocity d => z - x)
      (-ContinuousLinearMap.id Real (TimeVelocity d)) y := by
    exact ((hasFDerivAt_id y).neg.const_add z)
  have hcomp := (hrho.differentiable (by simp) (z - y)).hasFDerivAt.comp y hmap
  simpa [Function.comp_def] using
    congrArg (fun L : TimeVelocity d →L[Real] Real => L q) hcomp.fderiv

end

section
variable {d : Nat} {u du rho : TimeVelocity d -> Real} {f : TimeVelocity d -> Real}
    {D : (TimeVelocity d -> Real) -> TimeVelocity d -> Real}
    (hu : HasWeakTimeDerivOn Set.univ u du) {i j : Fin d} (q : TimeVelocity d)
    (hf : ContDiff Real 2 f)
    (hweak : forall phi : TimeVelocity d -> Real,
      ContDiff Real (⊤ : ℕ∞) phi ->
      HasCompactSupport phi ->
      (∫ y, u y * D phi y) = -∫ y, du y * phi y)
    (hD : forall (z y : TimeVelocity d),
      D (fun x => rho (z - x)) y = -fderiv Real rho (z - y) q)
    (huLoc : LocallyIntegrable u (volume : Measure (TimeVelocity d)))
    (hduLoc : LocallyIntegrable du (volume : Measure (TimeVelocity d)))
    (hrho : ContDiff Real (⊤ : ℕ∞) rho) (hrhoCompact : HasCompactSupport rho) (z : TimeVelocity d)

include hweak hD huLoc hduLoc hrho hrhoCompact in
private theorem fderiv_parabolicConvolution_eq :
    fderiv Real (parabolicConvolution u rho) z q = parabolicConvolution du rho z := by
  let _ := hduLoc
  let phi := fun y => rho (z - y)
  have hraw := hweak phi (contDiff_translatedKernel hrho z) (hasCompactSupport_translatedKernel hrhoCompact z)
  have hleft : (∫ y, u y * D phi y) =
      -(∫ y, u y * fderiv Real rho (z - y) q) := by
    calc
      (∫ y, u y * D phi y) =
          ∫ y, -(u y * fderiv Real rho (z - y) q) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [hD z y]
        ring
      _ = -(∫ y, u y * fderiv Real rho (z - y) q) := by
        rw [integral_neg]
  have hright : (∫ y, du y * phi y) = parabolicConvolution du rho z := by
    rfl
  have hconv := hrhoCompact.hasFDerivAt_convolution_right
    (ContinuousLinearMap.mul Real Real) huLoc (hrho.of_le (by simp)) z
  calc
    fderiv Real (parabolicConvolution u rho) z q =
        ((u ⋆[ContinuousLinearMap.precompR (TimeVelocity d)
          (ContinuousLinearMap.mul Real Real),
          volume] fderiv Real rho) z) q := by
      exact congrArg (fun L : TimeVelocity d →L[Real] Real => L q) hconv.fderiv
    _ = (u ⋆[ContinuousLinearMap.mul Real Real, volume]
        fun a => fderiv Real rho a q) z := convolution_precompR_apply (ContinuousLinearMap.mul Real Real) huLoc
        (hrhoCompact.fderiv Real) (hrho.continuous_fderiv (by simp)) z q
    _ = ∫ y, u y * fderiv Real rho (z - y) q := by
      apply convolution_def
    _ = -(-(∫ y, u y * fderiv Real rho (z - y) q)) := by ring
    _ = -(∫ y, u y * D phi y) := by rw [hleft]
    _ = ∫ y, du y * phi y := by simp [hraw]
    _ = parabolicConvolution du rho z := hright

/-- Convolution by a smooth compactly supported kernel is globally smooth. -/
theorem contDiff_parabolicConvolution {f rho : TimeVelocity d -> Real}
    (hf : LocallyIntegrable f (volume : Measure (TimeVelocity d)))
    (hrho : ContDiff Real (⊤ : ℕ∞) rho)
    (hrhoCompact : HasCompactSupport rho) :
    ContDiff Real (⊤ : ℕ∞) (parabolicConvolution f rho) := by
  simpa only [parabolicConvolution] using
    hrhoCompact.contDiff_convolution_right (ContinuousLinearMap.mul Real Real) hf hrho

include hu huLoc hduLoc hrho hrhoCompact in
/-- Right convolution commutes with the selected global weak time derivative. -/
theorem timeDerivative_parabolicConvolution :
    timeDerivative (parabolicConvolution u rho) = parabolicConvolution du rho := by
  funext z
  unfold timeDerivative
  apply fderiv_parabolicConvolution_eq (u := u) (du := du) (rho := rho) (1, 0)
    (D := timeDerivative) ?_ ?_ huLoc hduLoc hrho hrhoCompact z
  · intro phi hphi hphiCompact
    simpa only [Measure.restrict_univ] using hu phi hphi hphiCompact (Set.subset_univ _)
  · intro x y
    simpa only [timeDerivative] using fderiv_translatedKernel_apply hrho x y (1, 0)

/-- Right convolution commutes with every selected global weak velocity derivative. -/
theorem velocityGradient_parabolicConvolution {u dui rho : TimeVelocity d -> Real} {i : Fin d}
    (hu : HasWeakVelocityPartialDerivOn Set.univ i u dui)
    (huLoc : LocallyIntegrable u (volume : Measure (TimeVelocity d)))
    (hduiLoc : LocallyIntegrable dui (volume : Measure (TimeVelocity d)))
    (hrho : ContDiff Real (⊤ : ℕ∞) rho)
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
  · intro x y
    simpa only [velocityGradient] using
      fderiv_translatedKernel_apply hrho x y (0, Pi.single i 1)

include hf in
private theorem fderiv_velocityGradient_apply (z qi qj : TimeVelocity d) :
    fderiv Real (fun x => fderiv Real f x qi) z qj =
      fderiv Real (fderiv Real f) z qj qi := by
  have hderiv : DifferentiableAt Real (fderiv Real f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z
  rw [fderiv_clm_apply hderiv (differentiableAt_const (c := qi))]
  simp

include hf in
private theorem velocityHessian_eq_fderiv_velocityGradient :
    velocityHessian f z i j =
      fderiv Real (fun x => velocityGradient f x i) z (0, Pi.single j 1) := by
  let qi : TimeVelocity d := (0, Pi.single i 1)
  let qj : TimeVelocity d := (0, Pi.single j 1)
  calc
    velocityHessian f z i j = velocityHessian f z j i := by
      exact (congrFun (congrFun (velocityHessian_isSymm hf z).eq i) j).symm
    _ = fderiv Real (fun x => fderiv Real f x qi) z qj := by
      exact (fderiv_velocityGradient_apply hf z qi qj).symm
    _ = fderiv Real (fun x => velocityGradient f x i) z (0, Pi.single j 1) := by
      rfl

/-- Right convolution commutes with the ordered selected global velocity Hessian. -/
theorem velocityHessian_parabolicConvolution {u dui duij rho : TimeVelocity d -> Real} {i j : Fin d}
    (hui : HasWeakVelocityPartialDerivOn Set.univ i u dui)
    (huij : HasWeakVelocityPartialDerivOn Set.univ j dui duij)
    (huLoc : LocallyIntegrable u (volume : Measure (TimeVelocity d)))
    (hduiLoc : LocallyIntegrable dui (volume : Measure (TimeVelocity d)))
    (hduijLoc : LocallyIntegrable duij (volume : Measure (TimeVelocity d)))
    (hrho : ContDiff Real (⊤ : ℕ∞) rho)
    (hrhoCompact : HasCompactSupport rho) :
    (fun z => velocityHessian (parabolicConvolution u rho) z i j) =
      parabolicConvolution duij rho := by
  have hfirst := velocityGradient_parabolicConvolution hui huLoc hduiLoc hrho hrhoCompact
  have hsecond := velocityGradient_parabolicConvolution huij hduiLoc hduijLoc hrho hrhoCompact
  funext z
  rw [velocityHessian_eq_fderiv_velocityGradient
    ((contDiff_parabolicConvolution huLoc hrho hrhoCompact).of_le
      (WithTop.coe_le_coe.mpr le_top))]
  rw [hfirst]
  exact congrFun hsecond z

end

namespace ParabolicW12Function

variable {d : Nat} {p : ENNReal} (w : ParabolicW12Function d Set.univ p) (hp : 1 <= p)
    (rho : TimeVelocity d -> Real) (hrho : ContDiff Real (⊤ : ℕ∞) rho)
    (hrhoCompact : HasCompactSupport rho)
include hp hrho hrhoCompact

/-- The convolution of a global selected jet value is smooth. -/
theorem contDiff_convolution :
    ContDiff Real (⊤ : ℕ∞) (parabolicConvolution w.toFun rho) := by
  apply contDiff_parabolicConvolution (rho := rho) ?_ hrho hrhoCompact
  exact locallyIntegrableOn_univ.mp (w.memLp.locallyIntegrableOn hp)

/-- The convolution of a global selected jet commutes with its time representative. -/
theorem timeDerivative_convolution :
    timeDerivative (parabolicConvolution w.toFun rho) = parabolicConvolution w.timeDeriv rho := by
  apply timeDerivative_parabolicConvolution w.hasWeakTimeDeriv ?_ ?_ hrho hrhoCompact
  · exact locallyIntegrableOn_univ.mp (w.memLp.locallyIntegrableOn hp)
  · exact locallyIntegrableOn_univ.mp (w.timeDeriv_memLp.locallyIntegrableOn hp)

/-- The convolution of a global selected jet commutes with each velocity gradient. -/
theorem velocityGradient_convolution (i : Fin d) :
    (fun z => velocityGradient (parabolicConvolution w.toFun rho) z i) =
      parabolicConvolution (fun y => w.velocityGrad y i) rho := by
  apply velocityGradient_parabolicConvolution (w.hasWeakVelocityPartialDeriv i) ?_ ?_
    hrho hrhoCompact
  · exact locallyIntegrableOn_univ.mp (w.memLp.locallyIntegrableOn hp)
  · exact locallyIntegrableOn_univ.mp ((w.velocityGrad_memLp i).locallyIntegrableOn hp)

/-- The convolution of a global selected jet commutes with its ordered velocity Hessian. -/
theorem velocityHessian_convolution (i j : Fin d) :
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
