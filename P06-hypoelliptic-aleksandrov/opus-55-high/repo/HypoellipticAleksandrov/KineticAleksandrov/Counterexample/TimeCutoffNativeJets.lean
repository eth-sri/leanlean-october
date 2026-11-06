module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffClassical
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Native slice derivatives at a second regularity point -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter

variable {d : ℕ} (f : XV d → ℝ) (q : XV d)

/-- Position slice derivatives equal the product selectors at a differentiability point. -/
theorem dx_eq_classicalGradient_at 
    (hf : DifferentiableAt ℝ f q) :
    dx f q = PDE.classicalGradient (fun x => f (x, q.2)) q.1 := by
  unfold dx PDE.classicalGradient PDE.basisVec
  rw [fderiv_fun_comp q.1 hf
    (differentiableAt_id.prodMk (differentiableAt_const q.2))]
  have hinj := DifferentiableAt.fderiv_prodMk
    (differentiableAt_id (𝕜 := ℝ) (x := q.1)) (differentiableAt_const q.2)
  simp_all

/-- Velocity slice derivatives equal the product selectors at a differentiability point. -/
theorem dv_eq_classicalGradient_at 
    (hf : DifferentiableAt ℝ f q) :
    dv f q = PDE.classicalGradient (fun v => f (q.1, v)) q.2 := by
  unfold dv PDE.classicalGradient PDE.basisVec
  rw [fderiv_fun_comp q.2 hf
    ((differentiableAt_const q.1).prodMk differentiableAt_id)]
  have hinj := DifferentiableAt.fderiv_prodMk (differentiableAt_const q.1)
    (differentiableAt_id (𝕜 := ℝ) (x := q.2))
  simp_all

/-- Second velocity slice derivatives agree with product selectors at a C2 point. -/
theorem dvv_eq_sliceHessian_at 
    (hf : ContDiffAt ℝ 2 f q) :
    dvv f q = Parabolic.kineticVelocityHessian (fun P => f (P.position, P.velocity))
      ⟨0, q.1, q.2⟩ := by
  have hnear := hf.eventually (by norm_num)
  have hloc : (fun v => PDE.classicalGradient (fun w => f (q.1, w)) v) =ᶠ[nhds q.2]
      (fun v => dv f (q.1, v)) := by
    have hc : ContinuousAt (fun v : PDE.Vec d => (q.1, v)) q.2 :=
      continuousAt_const.prodMk continuousAt_id
    filter_upwards [hc.eventually hnear] with v hv
    exact (dv_eq_classicalGradient_at f _
      (hv.differentiableAt (by norm_num))).symm
  funext i k
  unfold Parabolic.kineticVelocityHessian
  rw [hloc.fderiv_eq]
  have hdv : DifferentiableAt ℝ (dv f) q := by
    have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    apply differentiableAt_pi.mpr
    intro j
    exact (hd.clm_apply (differentiableAt_const _))
  unfold dvv PDE.basisVec
  rw [fderiv_apply hdv, fderiv_fun_comp q.2 hdv
    ((differentiableAt_const q.1).prodMk differentiableAt_id)]
  have hinj := DifferentiableAt.fderiv_prodMk (differentiableAt_const q.1)
    (differentiableAt_id (𝕜 := ℝ) (x := q.2))
  simp_all

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
