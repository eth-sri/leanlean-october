module

public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Closure of finite weak derivative families under integral testing

All successor identities pass along the same sequence. The limiting representatives
remain coherent through the prescribed parabolic weight.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped Topology ENNReal

def weakDerivativeFamily_of_tendsto_integral_mul {d L }
    (U : Set (TimeVelocity d)) (u : ℕ → TimeVelocity d → ℝ)
    (D : ∀ n, ParabolicWeakDerivativeFamily d L U (u n))
    (v : TimeVelocity d → ℝ)
    (g : ParabolicDerivativeIndex d L → TimeVelocity d → ℝ)
    (hg : ∀ β, ParabolicMemLpOn U 2 (g β))
    (hzero : g (ParabolicDerivativeIndex.zero d L) =ᵐ[timeVelocityVolumeOn U] v)
    (hlim : ∀ β (φ : TimeVelocity d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      Tendsto (fun n => ∫ z in U, (D n).representative β z * φ z) atTop
        (𝓝 (∫ z in U, g β z * φ z))) :
    ParabolicWeakDerivativeFamily d L U v where
  representative := g
  memLp := hg
  zero_ae := hzero
  hasWeakTimeSucc := by
    intro β h φ hφ hc hsub
    have hdc :=
      hc.fderiv_apply (𝕜 := ℝ) (1, 0)
    have hds :=
      (tsupport_fderiv_apply_subset ℝ (1, 0)).trans hsub
    have _h_inl_9 : ContDiff ℝ (⊤ : ℕ∞) (timeDerivative φ) := by
      unfold timeDerivative
      exact (contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const
    have hleft := hlim β (timeDerivative φ) _h_inl_9 hdc hds
    have hright := (hlim (ParabolicDerivativeIndex.timeSucc β h) φ hφ hc hsub).neg
    have hright' : Tendsto
        (fun n => ∫ z in U, (D n).representative β z * timeDerivative φ z)
        atTop (𝓝 (-(∫ z in U, g (ParabolicDerivativeIndex.timeSucc β h) z * φ z))) := by
      apply hright.congr'
      exact Eventually.of_forall (fun n => ((D n).hasWeakTimeSucc β h φ hφ hc hsub).symm)
    exact tendsto_nhds_unique hleft hright'
  hasWeakVelocitySucc := by
    intro β i h φ hφ hc hsub
    have hdc :=
      hc.fderiv_apply (𝕜 := ℝ) (0, PDE.basisVec i)
    have hds :=
      (tsupport_fderiv_apply_subset ℝ (0, PDE.basisVec i)).trans hsub
    have _h_inl_10 : ContDiff ℝ (⊤ : ℕ∞) (fun z => velocityGradient φ z i) := by
      unfold velocityGradient
      exact (contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const
    have hleft := hlim β (fun z => velocityGradient φ z i)
      _h_inl_10 hdc hds
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
