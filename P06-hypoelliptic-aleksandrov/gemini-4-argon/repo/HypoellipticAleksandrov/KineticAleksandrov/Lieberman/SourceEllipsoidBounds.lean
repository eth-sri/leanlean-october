module

public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.EllipsoidBarrier
public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.TerminalLift
public import HypoellipticAleksandrov.KineticAleksandrov.EllipsoidDirichlet
public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.SourceInteriorDrift
public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.SourceTimeDrift
public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.StationaryComparisonDrift
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBarrierPointwise
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletGeometry

/-! # Ellipsoid source bounds assembled from exact upstream theorem surfaces -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Lieberman
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.Parabolic.Dirichlet HypoellipticAleksandrov.Parabolic.LocalHolder
open Set MeasureTheory Filter
open scoped Matrix ENNReal Topology MatrixOrder Matrix.Norms.Elementwise BigOperators

/- Interior source bounds, conditional on the complete exact upstream declarations. -/
theorem exists_signed_source_ellipsoidInterior_with_bounds :
∀ {d : ℕ}, 0 < d → ∀ {Q : PDE.Mat d}, Q.PosDef →
  ∀ (a T lam Lam : ℝ), a < T → 0 < lam → lam ≤ Lam →
  ∀ (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d),
  (∀ t y, (A t y).IsSymm) → IsSmoothCoefficient A →
  HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
  ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2) →
  ∀ (F : TimeVelocity d → ℝ), ContDiff ℝ (⊤ : ℕ∞) F →
  ∀ (M : ℝ), 0 ≤ M →
  (∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q), |F z| ≤ M) →
  ∃ (w : TimeVelocity d → ℝ) (q : PDE.H10Function (openEllipsoid Q)),
    ContDiff ℝ (⊤ : ℕ∞) q.toH1Function.toFun ∧
    (∀ y ∈ frontier (openEllipsoid Q), q.toH1Function.toFun y = 0) ∧
    IsScalarC12On w (scalarParabolicOpenCylinder a T (openEllipsoid Q)) ∧
    (∀ z ∈ scalarParabolicOpenCylinder a T (openEllipsoid Q),
      scalarParabolicZeroOrderOperator A b (fun _ _ => 0) w z = F z) ∧
    (∀ z ∈ scalarParabolicOpenCylinder a T (openEllipsoid Q),
      |w z| ≤ M * (T - z.1)) ∧
    ∀ z ∈ scalarParabolicOpenCylinder a T (openEllipsoid Q),
      |w z| ≤ q.toH1Function.toFun z.2 := by
  have hOpen := (@isOpen_openEllipsoid)
  have hGeom := (@openEllipsoid_geometry)
  have hDrift := (@exists_closedCylinder_drift_bound)
  have hBarrier := (@exists_h10_ellipsoid_drift_barrier)
  have hInterior := (@exists_signed_source_classicalInterior_withDrift)
  have hTime := (@classical_abs_le_source_time_withDrift)
  have hCompare := (@variational_abs_le_stationary_withDrift)
  intro d hd Q hQ a T lam Lam haT hlam hLam A b hsym hA hlo hhi hb F hF M hM hFM
  have hΩ := hOpen Q
  have hΩb := (hGeom hQ).1
  obtain ⟨B, hB, hbB⟩ := hDrift hΩb a T b hb.continuous
  obtain ⟨q, hq, hqn, hqf, hqop⟩ :=
    hBarrier hd hQ a T lam M B hlam hM hB A b hsym
      (fun z _ => hlo z.1 z.2) hbB
  obtain ⟨u, g, hdu, hu, w, _, hs, hw, he⟩ :=
    hInterior hd hΩ hΩb a T haT lam Lam hlam hLam A b hb hA hlo hhi F hF
  have htime := hTime hΩ hΩb a T lam haT hlam A b hb hA hlo F hF
    M hM hFM u g hdu hu w hw.continuousOn hs
  let G : TimeVelocity d → ℝ := scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
    (fun p => q.toH1Function.toFun p.2)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := by
    have h := (contDiff_terminal_lift_source A b q.toH1Function.toFun hA hb hq).neg
    simpa only [neg_neg] using h
  have hcl : closure (scalarParabolicOpenCylinder a T (openEllipsoid Q)) =
      scalarParabolicClosedCylinder a T (openEllipsoid Q) := by
    unfold scalarParabolicOpenCylinder scalarParabolicClosedCylinder
    rw [closure_prod_eq, closure_Ioo haT.ne]
  have hGM : ∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q), G z ≤ -M := by
    intro z hz
    apply le_on_closure (s := scalarParabolicOpenCylinder a T (openEllipsoid Q))
      (fun p hp => hqop p ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2⟩)
      hG.continuous.continuousOn continuous_const.continuousOn
    rwa [hcl]
  have hGF : ∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q), G z ≤ -|F z| :=
    fun z hz => (hGM z hz).trans (neg_le_neg (hFM z hz))
  have henergy := hCompare hΩ hΩb a T haT lam hlam A b hb hA hlo F G hF hG q
    (hq.of_le (by simp)) (fun y hy => hqn y (subset_closure hy))
    (fun _ _ => rfl) hGF u g hdu hu
  refine ⟨w, q, hq, hqf, hw, ?_, htime, (classicalEnergyRepresentative_abs_le_continuous_barrier hΩ a T haT u g hdu q.toH1Function.toFun hq.continuous henergy w hw.continuousOn hs)⟩
  intro z hz
  simpa only [scalarParabolicZeroOrderOperator_apply, coefficientAt, zero_mul, add_zero]
    using he z hz

end HypoellipticAleksandrov.KineticAleksandrov.Lieberman
