module
public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.EllipsoidBarrier
public import HypoellipticAleksandrov.Parabolic.Transposition.ParabolicFields
public import HypoellipticAleksandrov.Parabolic.Transposition.BarrierSolve
import HypoellipticAleksandrov.Parabolic.ContDiffOnTwoToScalarC12
import Mathlib

/-! # Interior source correction between a terminal and a lateral barrier -/
@[expose] public noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Lieberman
open Parabolic Transposition Hypoellipticity Set
open scoped ContDiff MatrixOrder Matrix.Norms.Elementwise

theorem exists_signed_source_ellipsoidInterior_with_bounds {d : ℕ} (hd : 0 < d) {Q : PDE.Mat d}
    (hQ : Q.PosDef) (a T lam : ℝ) (hlam : 0 < lam) (A : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (hA : IsSmoothCoefficient A) (hlo : HasLowerEllipticity lam A)
    (hb : ContDiff ℝ ∞ (fun z : TimeVelocity d => b z.1 z.2)) (F : TimeVelocity d → ℝ)
    (hF : ContDiff ℝ ∞ F) (M : ℝ) (hM : 0 ≤ M)
    (hFM : ∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q), |F z| ≤ M) :
    ∃ (w : TimeVelocity d → ℝ) (q : PDE.Vec d → ℝ), Continuous q ∧
      (∀ y ∈ frontier (openEllipsoid Q), q y = 0) ∧
      IsScalarC12On w (scalarParabolicOpenCylinder a T (openEllipsoid Q)) ∧
      EqOn (scalarParabolicZeroOrderOperator A b (fun _ _ => 0) w) F (scalarParabolicOpenCylinder a T (openEllipsoid Q)) ∧
      ∀ z ∈ scalarParabolicOpenCylinder a T (openEllipsoid Q), |w z| ≤ min (M * (T - z.1)) (q z.2) := by
  let U : Domain d := ⟨scalarParabolicOpenCylinder a T (openEllipsoid Q), isOpen_Ioo.prod (isOpen_openEllipsoid Q)⟩
  have incl : (U : Set (TimeVelocity d)) ⊆ scalarParabolicClosedCylinder a T (openEllipsoid Q) := prod_mono Ioo_subset_Icc_self subset_closure
  change (U : Set (TimeVelocity d)) ⊆ Icc a T ×ˢ closure (openEllipsoid Q) at incl
  have hΩ := (openEllipsoid_geometry hQ).1
  obtain ⟨B,_,hbB⟩ := exists_closedCylinder_drift_bound hΩ a T b hb.continuous
  obtain ⟨q,hq,hpos,hzero,hL⟩ := exists_ellipsoid_drift_barrier hd hQ a T lam M B hlam hM A b (fun z _ => hlo z.1 z.2) hbB
  obtain ⟨X,hr,he⟩ := parabolic_fields (U := U) A b hA hb (fun z => posDef_of_loewner_lower hlam (hlo z.1 z.2))
  let f : Field d := ⟨fun z => M * (T-z.1), contDiff_const.mul (contDiff_const.sub contDiff_fst)⟩
  let g : Field d := ⟨fun z => q z.2,hq.comp contDiff_snd⟩
  have hf z (hz : z ∈ U) : 0 ≤ f.val z ∧ generator X f.val z ≤ -M := by
    refine ⟨mul_nonneg hM (sub_nonneg.mpr hz.1.2.le), ?_⟩
    rw [show generator X f.val z = _ from he (onDomain U f) hz]
    have ht := (((hasDerivAt_const z.1 T).sub (hasDerivAt_id z.1)).const_mul M).deriv
    change deriv (fun r => M * (T - r)) z.1 = M * (0 - 1) at ht
    have cg (x : PDE.Vec d) : PDE.classicalGradient (fun _ : PDE.Vec d => M*(T-z.1)) x = 0 := by ext i; simp
    simp [onDomain,f,scalarParabolicZeroOrderOperator_apply,scalarTimeDerivative, scalarSpatialGradient,scalarSpatialHessian,
      PDE.classicalGradient, matrixContraction, PDE.vecDot, ht,cg]
  have hg z (hz : z ∈ U) : 0 ≤ g.val z ∧ generator X g.val z ≤ -M :=
    ⟨hpos _ (subset_closure hz.2), (he (onDomain U g) hz).le.trans (hL z (incl hz))⟩
  obtain ⟨w,hw,bound⟩ := solve_with_barriers X hr ⟨F,hF⟩ f g.val g.prop.continuous
    (M := fun _ => M) (C := M*(T-a)) continuous_const (fun _ _ => hM) (fun z hz => hFM z (incl hz))
    (fun z hz => ⟨(hf z hz).1, mul_le_mul_of_nonneg_left (sub_le_sub_left hz.1.1.le T) hM,(hf z hz).2⟩)
    (fun z hz => (hg z hz).1) (fun ε hε => ⟨g,fun z hz => ⟨(hg z hz).1,(hg z hz).2,le_add_of_nonneg_right hε.le⟩⟩)
  exact ⟨w.val,q,hq.continuous,hzero,isScalarC12On_of_isOpen_contDiffOn_two U.isOpen ((smooth_local w).of_le (by simp)),
    (he w).symm.trans hw,bound⟩

end HypoellipticAleksandrov.KineticAleksandrov.Lieberman
