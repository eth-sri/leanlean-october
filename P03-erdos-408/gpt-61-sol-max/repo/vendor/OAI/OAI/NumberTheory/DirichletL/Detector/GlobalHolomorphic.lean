module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.GlobalRegion
public import OAI.NumberTheory.DirichletL.Detector.EulerHolomorphic

@[expose] public section

namespace OAI


namespace SevenEighths.ProbeEuler

section
variable (Q : ℝ) (hQ : 0<Q) (A eta v x w z : ℂ) (_hR : 1-coordR Q A x z≠0) (_hV : 1-coordV Q z≠0) (hR : 1-coordR Q A x z≠0) (hV : 1-coordV Q z≠0) (_hD : 1-coordD Q eta v x≠0)

include hQ in
lemma coordV_differentiable     : Differentiable ℂ (coordV Q) := by
  unfold coordV
  fun_prop (disch := aesop)

include hQ in
lemma coordW_differentiable       : Differentiable ℂ (coordW Q v) := by
  unfold coordW
  fun_prop (disch := aesop)

include hQ in
lemma coordR_z_differentiable       :
    Differentiable ℂ (coordR Q A x) := by
  unfold coordR
  fun_prop (disch := aesop)

include hQ in
lemma coordK_w_differentiable       :
    Differentiable ℂ (coordK Q eta x) := by
  unfold coordK
  fun_prop (disch := aesop)

include hQ _hR _hV _hD in
lemma unramifiedClosed_differentiableAt_w      
          :
    DifferentiableAt ℂ (fun t=>unramifiedClosed Q A eta v x t z) w := by
  have hw := coordW_differentiable Q hQ v
  have hk := coordK_w_differentiable Q hQ eta x
  have hp : DifferentiableAt ℂ (fun t=>
      markedFactor (coordR Q A x z) (coordV Q z) (Q:ℂ)⁻¹
        (coordK Q eta x t) (-coordD Q eta v x+coordW Q v t*coordR Q A x z) 1) w := by
    unfold markedFactor
    fun_prop (disch := assumption)
  unfold unramifiedClosed ProbeLocal.continuedCorrection
  dsimp only
  fun_prop (disch := assumption)

include hQ hR hV _hD in
lemma unramifiedClosed_differentiableAt_z      
          :
    DifferentiableAt ℂ (unramifiedClosed Q A eta v x w) z := by
  have hv := coordV_differentiable Q hQ
  have hr := coordR_z_differentiable Q hQ A x
  have hp : DifferentiableAt ℂ (fun t=>
      markedFactor (coordR Q A x t) (coordV Q t) (Q:ℂ)⁻¹
        (coordK Q eta x w) (-coordD Q eta v x+coordW Q v w*coordR Q A x t) 1) z := by
    unfold markedFactor
    fun_prop (disch := assumption)
  unfold unramifiedClosed ProbeLocal.continuedCorrection
  dsimp only
  fun_prop (disch := assumption)

end

section
variable (Q : ℝ) (A eta v x w z : ℂ) (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hx : 7/8≤x.re) (hz : 4/25≤z.re)

include hQ hA he hv hx hz in
lemma open_region_denominators    
           
        :
    1-coordR Q A x z≠0 ∧ 1-coordV Q z≠0 ∧ 1-coordD Q eta v x≠0 := by
  have hQ0 : 0<Q := by linarith
  
  have hR : ‖coordR Q A x z‖≤1/2 := by
    apply (coordR_norm_le Q hQ0 A x z hA).trans
    apply rpow_le_half Q _ hQ
    linarith
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    linarith
  have hD : ‖coordD Q eta v x‖≤1/2 := by
    apply (coordD_norm_le Q hQ0 eta v x he hv).trans
    apply rpow_le_half Q _ hQ
    linarith
  exact ⟨ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV,ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD⟩

include hQ hA he hv hz in
theorem unramifiedClosed_analytic_x    
              :
    AnalyticOnNhd ℂ (fun x=>unramifiedClosed Q A eta v x w z) {x : ℂ|7/8<x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := open_region_denominators Q A eta v x z hQ hA he hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

include hQ hA he hv hx hz in
theorem unramifiedClosed_analytic_w    
           
        :
    AnalyticOnNhd ℂ (fun w=>unramifiedClosed Q A eta v x w z) {w : ℂ|9/10<w.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hd := open_region_denominators Q A eta v x z hQ hA he hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

include hQ hA he hv hx in
theorem unramifiedClosed_analytic_z    
              :
    AnalyticOnNhd ℂ (unramifiedClosed Q A eta v x w) {z : ℂ|4/25<z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := open_region_denominators Q A eta v x z hQ hA he hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

end

end SevenEighths.ProbeEuler


end OAI
