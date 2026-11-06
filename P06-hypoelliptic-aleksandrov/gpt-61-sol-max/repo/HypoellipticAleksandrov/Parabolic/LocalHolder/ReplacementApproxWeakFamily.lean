module

public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.MixedTimeVelocityWeakDerivativeCommutation
public import PDEFoundation.Calculus.RegularityOrder


open private HypoellipticAleksandrov.Parabolic.timeDerivative_contDiff_infty from HypoellipticAleksandrov.Parabolic.MixedTimeVelocityWeakDerivativeCommutation


/-! # Closure of finite weak derivative families under integral testing

All successor identities pass along the same sequence. The limiting representatives
remain coherent through the prescribed parabolic weight.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped Topology ENNReal

variable {d : ℕ} {φ : HypoellipticAleksandrov.Parabolic.ScalarField d} (hφ : ContDiff ℝ PDE.smoothOrder φ)




include hφ in
private theorem test_velocity_smooth  (i : Fin d) :
    ContDiff ℝ PDE.smoothOrder (fun z => velocityGradient φ z i) := by
  unfold velocityGradient
  exact (contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const

/-- Limits of all compact test pairings retain every weak successor relation. -/
def weakDerivativeFamily_of_tendsto_integral_mul {d L : ℕ}
    (U : HypoellipticAleksandrov.Parabolic.Region d) (u : ℕ → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (D : ∀ n, ParabolicWeakDerivativeFamily d L U (u n))
    (v : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (g : ParabolicDerivativeIndex d L → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hg : ∀ β, ParabolicMemLpOn U 2 (g β))
    (hzero : g (ParabolicDerivativeIndex.zero d L) =ᵐ[timeVelocityVolumeOn U] v)
    (hlim : ∀ β (φ : HypoellipticAleksandrov.Parabolic.ScalarField d),
      ContDiff ℝ PDE.smoothOrder φ → HasCompactSupport φ → tsupport φ ⊆ U →
      Tendsto (fun n => ∫ z in U, (D n).representative β z * φ z) atTop
        (𝓝 (∫ z in U, g β z * φ z))) :
    ParabolicWeakDerivativeFamily d L U v where
  representative := g
  memLp := hg
  zero_ae := hzero
  hasWeakTimeSucc := by
    intro β h φ hφ hc hsub
    have hdc  :=
      hc.fderiv_apply (𝕜 := ℝ) (1, 0)
    have hds  :=
      (tsupport_fderiv_apply_subset ℝ (1, 0)).trans hsub
    have hleft := hlim β (timeDerivative φ) (_root_.HypoellipticAleksandrov.Parabolic.timeDerivative_contDiff_infty hφ) hdc hds
    have hright := (hlim (ParabolicDerivativeIndex.timeSucc β h) φ hφ hc hsub).neg
    have hright' : Tendsto
        (fun n => ∫ z in U, (D n).representative β z * timeDerivative φ z)
        atTop (𝓝 (-(∫ z in U, g (ParabolicDerivativeIndex.timeSucc β h) z * φ z))) := by
      apply hright.congr'
      exact Eventually.of_forall (fun n => ((D n).hasWeakTimeSucc β h φ hφ hc hsub).symm)
    exact tendsto_nhds_unique hleft hright'
  hasWeakVelocitySucc := by
    intro β i h φ hφ hc hsub
    have hdc  :=
      hc.fderiv_apply (𝕜 := ℝ) (0, PDE.basisVec i)
    have hds  :=
      (tsupport_fderiv_apply_subset ℝ (0, PDE.basisVec i)).trans hsub
    have hleft := hlim β (fun z => velocityGradient φ z i)
      (test_velocity_smooth hφ i) hdc hds
    have hright :=
      (hlim (ParabolicDerivativeIndex.velocitySucc β i h) φ hφ hc hsub).neg
    have hright' : Tendsto
        (fun n => ∫ z in U, (D n).representative β z * velocityGradient φ z i)
        atTop (𝓝 (-(∫ z in U, g (ParabolicDerivativeIndex.velocitySucc β i h) z * φ z))) := by
      apply hright.congr'
      exact Eventually.of_forall
        (fun n => ((D n).hasWeakVelocitySucc β i h φ hφ hc hsub).symm)
    exact tendsto_nhds_unique hleft hright'

end HypoellipticAleksandrov.Parabolic.LocalHolder
