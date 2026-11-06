module
public import OAI.NumberTheory.DirichletL.Detector.EulerRegion
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

section
variable (Q : ℝ) (hQ : 0 < Q)
include Q hQ
lemma coordR_differentiable (A z : ℂ) :
    Differentiable ℂ (fun x : ℂ => coordR Q A x z) := by
  unfold coordR
  pm_356 hn Q hQ.ne'
  exact (((differentiable_const (4:ℂ)).sub (differentiable_id.const_mul 6)).sub_const (6*z)).const_cpow
    (Or.inl hn) |>.const_mul A

lemma coordD_differentiable (eta v : ℂ) :
    Differentiable ℂ (fun x : ℂ => coordD Q eta v x) := by
  unfold coordD
  pm_356 hn Q hQ.ne'
  exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul (eta*star v)

lemma coordK_differentiable (eta w : ℂ) :
    Differentiable ℂ (fun x : ℂ => coordK Q eta x w) := by
  unfold coordK
  pm_356 hn Q hQ.ne'
  exact ((differentiable_id.neg.sub_const w).const_cpow (Or.inl hn)).const_mul (eta*(Q-1))

lemma unramifiedClosed_differentiableAt (A eta v x w z : ℂ)
    (hR : 1-coordR Q A x z ≠ 0) (_hV : 1-coordV Q z ≠ 0)
    (hD : 1-coordD Q eta v x ≠ 0) :
    DifferentiableAt ℂ (fun s : ℂ => unramifiedClosed Q A eta v s w z) x := by
  have hr := coordR_differentiable Q hQ A z
  have hd := coordD_differentiable Q hQ eta v
  have hk := coordK_differentiable Q hQ eta w
  have hp : DifferentiableAt ℂ (fun s : ℂ =>
      markedFactor (coordR Q A s z) (coordV Q z) (Q:ℂ)⁻¹
        (coordK Q eta s w) (-coordD Q eta v s + coordW Q v w*coordR Q A s z) 1) x := by
    unfold markedFactor
    fun_prop (disch := assumption)
  unfold unramifiedClosed ProbeLocal.continuedCorrection
  dsimp only
  fun_prop
end

end SevenEighths.ProbeEuler
end

end OAI
