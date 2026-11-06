module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.EulerRegion

@[expose] public section

namespace OAI


namespace SevenEighths.ProbeEuler

section
variable (Q : ℝ) (hQ : 0 < Q)
include Q hQ

lemma coordR_differentiable      A z  :
    Differentiable ℂ (fun x : ℂ => coordR Q A x z) := by
  unfold coordR
  fun_prop (disch := aesop)

lemma coordD_differentiable      eta v  :
    Differentiable ℂ (fun x : ℂ => coordD Q eta v x) := by
  unfold coordD
  fun_prop (disch := aesop)

lemma coordK_differentiable      eta w  :
    Differentiable ℂ (fun x : ℂ => coordK Q eta x w) := by
  unfold coordK
  fun_prop (disch := aesop)

lemma unramifiedClosed_differentiableAt      A eta v x w z 
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
  fun_prop (disch := assumption)

end

end SevenEighths.ProbeEuler


end OAI
