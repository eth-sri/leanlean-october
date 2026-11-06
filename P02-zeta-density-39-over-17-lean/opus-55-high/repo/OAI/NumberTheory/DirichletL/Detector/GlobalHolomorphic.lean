module
public import OAI.NumberTheory.DirichletL.Detector.GlobalRegion
public import OAI.NumberTheory.DirichletL.Detector.EulerHolomorphic
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

section
variable (Q : ℝ) (hQ : 0<Q)
include Q hQ
lemma coordV_differentiable : Differentiable ℂ (coordV Q) := by
  unfold coordV
  pm_3596 hn Q hQ.ne'
  exact (differentiable_id.const_mul (-6)).const_cpow (Or.inl hn)

lemma coordW_differentiable (v : ℂ) : Differentiable ℂ (coordW Q v) := by
  unfold coordW
  pm_3596 hn Q hQ.ne'
  exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul v

lemma coordR_z_differentiable (A x : ℂ) :
    Differentiable ℂ (fun z=>coordR Q A x z) := by
  unfold coordR
  pm_3596 hn Q hQ.ne'
  exact (((differentiable_id.const_mul 6).const_sub (4-6*x)).const_cpow (Or.inl hn)).const_mul A

lemma coordK_w_differentiable (eta x : ℂ) :
    Differentiable ℂ (fun w=>coordK Q eta x w) := by
  unfold coordK
  pm_3596 hn Q hQ.ne'
  exact ((differentiable_id.const_sub (-x)).const_cpow (Or.inl hn)).const_mul (eta*(Q-1))

lemma unramifiedClosed_differentiableAt_w (A eta v x w z : ℂ)
    (_hR : 1-coordR Q A x z≠0) (_hV : 1-coordV Q z≠0) (_hD : 1-coordD Q eta v x≠0) :
    DifferentiableAt ℂ (fun t=>unramifiedClosed Q A eta v x t z) w := by
  have hw := coordW_differentiable Q hQ v
  have hk := coordK_w_differentiable Q hQ eta x
  have hp : DifferentiableAt ℂ (fun t=>
      markedFactor (coordR Q A x z) (coordV Q z) (Q:ℂ)⁻¹
        (coordK Q eta x t) (-coordD Q eta v x+coordW Q v t*coordR Q A x z) 1) w := by
    unfold markedFactor
    fun_prop (disch := assumption)
  pm_8101

lemma unramifiedClosed_differentiableAt_z (A eta v x w z : ℂ)
    (hR : 1-coordR Q A x z≠0) (hV : 1-coordV Q z≠0) (_hD : 1-coordD Q eta v x≠0) :
    DifferentiableAt ℂ (fun t=>unramifiedClosed Q A eta v x w t) z := by
  have hv := coordV_differentiable Q hQ
  have hr := coordR_z_differentiable Q hQ A x
  have hp : DifferentiableAt ℂ (fun t=>
      markedFactor (coordR Q A x t) (coordV Q t) (Q:ℂ)⁻¹
        (coordK Q eta x w) (-coordD Q eta v x+coordW Q v w*coordR Q A x t) 1) z := by
    unfold markedFactor
    fun_prop (disch := assumption)
  pm_8101
end

lemma open_region_denominators (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 7/8≤x.re) (hz : 4/25≤z.re) :
    1-coordR Q A x z≠0 ∧ 1-coordV Q z≠0 ∧ 1-coordD Q eta v x≠0 := by pm_3844

theorem unramifiedClosed_analytic_x (Q : ℝ) (A eta v w z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun x=>unramifiedClosed Q A eta v x w z) {x : ℂ|7/8<x.re} := by pm_3845 open_region_denominators

theorem unramifiedClosed_analytic_w (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 7/8≤x.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun w=>unramifiedClosed Q A eta v x w z) {w : ℂ|9/10<w.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  pm_635 open_region_denominators

theorem unramifiedClosed_analytic_z (Q : ℝ) (A eta v x w : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hx : 7/8≤x.re) :
    AnalyticOnNhd ℂ (fun z=>unramifiedClosed Q A eta v x w z) {z : ℂ|4/25<z.re} := by pm_3846 open_region_denominators

end SevenEighths.ProbeEuler
end

end OAI
