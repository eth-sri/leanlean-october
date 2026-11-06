module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedError
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ProbeLocal

def unramifiedSelected (Q : ℝ) (A eta v x w z : ℂ) : ℂ :=
  compensatedReplacement (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta*(Q:ℂ)^x) ((Q:ℂ)^(-w))

lemma selected_phase_identities (Q : ℝ) (eta v x w : ℂ)
    (hQ : 0<Q) (heta : ‖eta‖=1) (hv : ‖v‖=1) :
    (star eta*(Q:ℂ)^x)*coordD Q eta v x=star v ∧
      star v*coordW Q v w=(Q:ℂ)^(-w) := by
  pm_3596 hQ0 Q hQ.ne'
  constructor
  · unfold coordD
    calc
      _=(star eta*eta)*((Q:ℂ)^x*(Q:ℂ)^(-x))*star v := by ring
      _=star v := by rw [PrincipalSlotEstimate.unit_phase_inverse eta heta,←Complex.cpow_add _ _ hQ0];simp
  · unfold coordW
    rw [←mul_assoc,PrincipalSlotEstimate.unit_phase_inverse v hv,one_mul]

section
variable (Q : ℝ) (A eta v x w z : ℂ) (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1) (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
include Q A eta v x w z hQ hA heta hv hx hw hz
lemma unramifiedSelected_error_bound :
    ‖unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v‖≤720 := by
  pm_3932
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ (by linarith)
  have hD : ‖coordD Q eta v x‖≤1/2 :=
    (coordD_norm_le Q hQ0 eta v x heta.le hv.le).trans (rpow_le_half Q _ hQ (by linarith))
  pm_5298 hv.le
  pm_3841
  have he := unramifiedMarked_selected_error Q A eta v x w z hQ hA heta.le hv.le hx hw hz
  pm_528 hi selected_phase_identities Q eta v x w hQ0 heta hv
  have hh := compensated_phase_error_bound (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta*(Q:ℂ)^x) ((Q:ℂ)^(-w)) (star v) 1
    (by norm_num) hV hW hD hq (by linarith) (by linarith)
    (by grind) (by grind) (by simp_all) hi.1 hi.2
  aesop

lemma unramifiedSelected_bound :
    ‖unramifiedSelected Q A eta v x w z‖≤961 := by
  have hd := unramifiedClosed_first_region_bound Q A eta v x w z (1/4) hQ hA heta.le hv.le
    (by norm_num) (by linarith) hz (by linarith) (by linarith)
  have hpow : Q^(-1-min (1/4:ℝ) (1/50))≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hH : ‖unramifiedClosed Q A eta v x w z‖≤241 := by
    have hh := norm_add_le (unramifiedClosed Q A eta v x w z-1) (1:ℂ)
    rw [sub_add_cancel,norm_one] at hh
    nlinarith
  have he := unramifiedSelected_error_bound Q A eta v x w z hQ hA heta hv hx hw hz
  have hh := norm_sub_le
    (unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v)
    (unramifiedClosed Q A eta v x w z*star v)
  rw [add_sub_cancel_right,norm_mul,norm_star,hv,mul_one] at hh
  linarith
end

section
variable (Q : ℝ) (v x w z : ℂ)
include Q v x w z
lemma unramifiedSelected_zero :
    unramifiedSelected Q 0 0 v x w z= -(Q:ℂ)^(-w)*(1-coordV Q z*coordW Q v w) := by
  simp only [unramifiedSelected,unramifiedMarked,coordR,coordD,coordK,zero_mul,
    neg_zero,add_zero,markedFactor,zero_sub,sub_zero,div_one,mul_zero,
    star_zero,compensatedReplacement]
  ring

lemma unramifiedSelected_zero_bound
    (hQ : 4≤Q) (hv : ‖v‖≤1) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖unramifiedSelected Q 0 0 v x w z‖≤2 := by
  pm_3932
  have hV : ‖coordV Q z‖≤1 := by
    rw [coordV_norm Q hQ0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
  pm_5298 hv
  pm_3841
  rw [unramifiedSelected_zero,norm_mul,norm_neg]
  have ht := norm_sub_le (1:ℂ) (coordV Q z*coordW Q v w)
  rw [norm_one,norm_mul] at ht
  have hp : ‖coordV Q z‖*‖coordW Q v w‖≤1 := by nlinarith [norm_nonneg (coordV Q z)]
  nlinarith [norm_nonneg (1-coordV Q z*coordW Q v w)]
end

end SevenEighths.ProbeEuler
end

end OAI
