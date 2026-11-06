module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffHessian
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierFinite
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Tactic
public import PDEFoundation.Calculus.RegularityOrder


/-! # Continuous raw-coordinate jets of the smooth unit cutoff -/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Holder



variable {d : ℕ}

/-- An affine slice Hessian is the restriction of the ambient second derivative. -/
theorem sliceHessian_comp_affine_embedding  {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {ι : PDE.Vec d → E} (hιc : ContDiff ℝ 2 ι)
    {J : PDE.Vec d →L[ℝ] E} (hι : ∀ x, HasFDerivAt ι J x)
    (x : PDE.Vec d) (i j : Fin d) :
    sliceHessian (fun w => f (ι w)) x i j =
      fderiv ℝ (fderiv ℝ f) (ι x) (J (PDE.basisVec i)) (J (PDE.basisVec j)) := by
  let sharedTerm_f054a79e8c := ((fun z => f (ι z)))
  let sharedTerm_f1604e330a := (fun w => fderiv ℝ f (ι w) (J (PDE.basisVec j)))
  have hg : ContDiffAt ℝ 2 sharedTerm_f054a79e8c x := (hf.comp hιc).contDiffAt
  rw [sliceHessian_apply_eq_sndFDeriv hg]
  have hd  := hf.differentiable (by norm_num)
  have hfd : ∀ w, fderiv ℝ sharedTerm_f054a79e8c w = (fderiv ℝ f (ι w)).comp J :=
    fun w => ((hd (ι w)).hasFDerivAt.comp w (hι w)).fderiv
  have hgd := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [← fderiv_clm_apply_const_eval hgd (PDE.basisVec j) (PDE.basisVec i)]
  have hfun : (fun w => fderiv ℝ sharedTerm_f054a79e8c w (PDE.basisVec j)) =
      sharedTerm_f1604e330a := by
    funext w
    rw [hfd w]
    rfl
  rw [hfun]
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) (ι x)
  have hh := (hdf.clm_apply (differentiableAt_const (J (PDE.basisVec j)))).hasFDerivAt
  have hc := hh.comp x (hι x)
  rw [show (sharedTerm_f1604e330a) =
    (fun z => fderiv ℝ f z (J (PDE.basisVec j))) ∘ ι from rfl, hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fderiv_clm_apply_const_eval hdf]

variable {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ} (hf : ContDiff ℝ PDE.smoothOrder f)

include hf
/-- Unit velocity-Hessian entries are the corresponding ambient coordinate derivatives. -/
theorem unitCutoffVelocitySlice_hessian
     (Q : KineticPoint d) (i j : Fin d) :
    sliceHessian (unitCutoffVelocitySlice f Q) Q.velocity i j =
      fderiv ℝ (fderiv ℝ f) (KineticPoint.equivProd d Q)
        (0, (0, PDE.basisVec i)) (0, (0, PDE.basisVec j)) := (sliceHessian_comp_affine_embedding
  (ContDiff.of_le hf
    (of_eq_true
      (Eq.trans WithTop.le_coe_top._simp_1
        (Eq.trans (congrArg Not (WithTop.ofNat_ne_top._simp_1 2)) not_false_eq_true))))
  (ContDiff.prodMk contDiff_const (ContDiff.prodMk contDiff_const contDiff_id))
  (fun w =>
    HasFDerivAt.prodMk (hasFDerivAt_const Q.time w)
      (HasFDerivAt.prodMk (hasFDerivAt_const Q.position w) (hasFDerivAt_id w)))
  Q.velocity i j)

/-- The unit velocity Hessian depends continuously on the physical point. -/
theorem continuous_unitCutoffVelocityHessian
     :
    Continuous (fun Q  =>
      sliceHessian (unitCutoffVelocitySlice f Q) Q.velocity) := by
  have hc : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (((hf.of_le (show (3 : WithTop ℕ∞) ≤ PDE.smoothOrder by simp)).fderiv_right
      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).continuous
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have h0 := (hc.comp (KineticPoint.homeomorphProd d).continuous).clm_apply
    (continuous_const (y := ((0, (0, PDE.basisVec i)) : ℝ × (PDE.Vec d × PDE.Vec d))))
  have h1 := h0.clm_apply (continuous_const
    (y := ((0, (0, PDE.basisVec j)) : ℝ × (PDE.Vec d × PDE.Vec d))))
  exact h1.congr (fun Q => (unitCutoffVelocitySlice_hessian hf Q i j).symm)

/-- The unit transport derivative depends continuously on the physical point. -/
theorem continuous_unitCutoffTransport
     :
    Continuous (fun Q  =>
      fderiv ℝ f (KineticPoint.equivProd d Q) (1, (Q.velocity, 0))) := by
  have h0 := ((hf.of_le (show (2 : WithTop ℕ∞) ≤ PDE.smoothOrder by simp)).fderiv_right
    (m := 1) (by norm_num)).continuous.comp (KineticPoint.homeomorphProd d).continuous
  exact h0.clm_apply
    (continuous_const.prodMk (continuous_velocity.prodMk continuous_const))

end HypoellipticAleksandrov.KineticAleksandrov.Holder
