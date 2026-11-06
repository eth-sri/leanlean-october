module

public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.SourceEllipsoidBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.SourceBoundaryExtension
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovRegularity
public import PDEFoundation.Calculus.RegularityOrder


/-! # Source correction on a closed ellipsoid cylinder using an earlier time collar -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Lieberman
open HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.Parabolic.Dirichlet HypoellipticAleksandrov.Parabolic.LocalHolder
open Set
open scoped Matrix ENNReal MatrixOrder Matrix.Norms.Elementwise

section
variable (hOpen : ∀ {d : ℕ} (Q : PDE.Mat d), IsOpen (openEllipsoid Q)) (hGeom : ∀ {d : ℕ} {Q : PDE.Mat d}, Q.PosDef → Bornology.IsBounded (openEllipsoid Q) ∧ closure (openEllipsoid Q) = {x | PDE.vecDot x (Q *ᵥ x) ≤ 1} ∧ frontier (openEllipsoid Q) = {x | PDE.vecDot x (Q *ᵥ x) = 1} ∧ HasUniformNondegenerateExteriorCone (openEllipsoid Q)) (hInterior : ∀ {d : ℕ}, 0 < d → ∀ {Q : PDE.Mat d}, Q.PosDef → ∀ (a T lam Lam : ℝ), a < T → 0 < lam → lam ≤ Lam → ∀ (A : CoefficientField d) (b : PDE.TimeVectorField d), (∀ t y, (A t y).IsSymm) → IsSmoothCoefficient A → HasLowerEllipticity lam A → HasUpperEllipticity Lam A → ContDiff ℝ PDE.smoothOrder (fun z : TimeVelocity d => b z.1 z.2) → ∀ (F : HypoellipticAleksandrov.Parabolic.ScalarField d), ContDiff ℝ PDE.smoothOrder F → ∀ (M : ℝ), 0 ≤ M → (∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q), |F z| ≤ M) → ∃ (w : HypoellipticAleksandrov.Parabolic.ScalarField d) (q : PDE.H10Function (openEllipsoid Q)), ContDiff ℝ PDE.smoothOrder q.toH1Function.toFun ∧ (∀ y ∈ frontier (openEllipsoid Q), q.toH1Function.toFun y = 0) ∧ IsScalarC12On w (scalarParabolicOpenCylinder a T (openEllipsoid Q)) ∧ (∀ z ∈ scalarParabolicOpenCylinder a T (openEllipsoid Q), scalarParabolicZeroOrderOperator A b (fun _ _ => 0) w z = F z) ∧ (∀ z ∈ scalarParabolicOpenCylinder a T (openEllipsoid Q), |w z| ≤ M * (T - z.1)) ∧ ∀ z ∈ scalarParabolicOpenCylinder a T (openEllipsoid Q), |w z| ≤ q.toH1Function.toFun z.2)

include hOpen hGeom hInterior
/-- Closed-cylinder correction from the complete interior and boundary theorem surfaces. -/
theorem exists_signed_source_ellipsoid_correction_of_upstream

    (hBoundary :
      ∀ {d : ℕ} {Ω : PDE.VelocityRegion d}, IsOpen Ω →
        ∀ (a₀ a T M : ℝ), a₀ < a → 0 ≤ M →
        ∀ (q : PDE.ScalarField d), Continuous q →
        (∀ y ∈ frontier Ω, q y = 0) →
        ∀ (w : HypoellipticAleksandrov.Parabolic.ScalarField d),
        ContinuousOn w (scalarParabolicOpenCylinder a₀ T Ω) →
        (∀ z ∈ scalarParabolicOpenCylinder a₀ T Ω, |w z| ≤ M * (T - z.1)) →
        (∀ z ∈ scalarParabolicOpenCylinder a₀ T Ω, |w z| ≤ q z.2) →
        ContinuousOn (sourceInteriorZeroExtension a₀ T Ω w)
          (scalarParabolicClosedCylinder a T Ω))
    : ∀ {d : ℕ}, 0 < d → ∀ {Q : PDE.Mat d}, Q.PosDef →
  ∀ (a T lam Lam : ℝ), a < T → 0 < lam → lam ≤ Lam →
  ∀ (A : CoefficientField d) (b : PDE.TimeVectorField d),
  (∀ t y, (A t y).IsSymm) → IsSmoothCoefficient A →
  HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
  ContDiff ℝ PDE.smoothOrder (fun z : TimeVelocity d => b z.1 z.2) →
  ∀ (F : HypoellipticAleksandrov.Parabolic.ScalarField d), ContDiff ℝ PDE.smoothOrder F →
  ∃ W : HypoellipticAleksandrov.Parabolic.ScalarField d,
    IsClassicalBackwardDirichletSolution a T (openEllipsoid Q) A b
      (fun _ _ => 0) (fun t y => F (t, y)) (fun _ => 0) (fun _ => 0) W := by
  intro d hd Q hQ a T lam Lam haT hlam hLam A b hsym hA hlo hhi hb F hF
  classical
  let Ω := openEllipsoid Q
  have hΩ  := hOpen Q

  have hleft  := sub_lt_self a zero_lt_one


  obtain ⟨C, hC⟩ := (isCompact_scalarParabolicClosedCylinder (a - 1) T ((hGeom hQ).1)).exists_bound_of_continuousOn hF.continuous.continuousOn
  let M := max C 0
  have hM : 0 ≤ M := le_max_right _ _

  obtain ⟨w, q, hq, hqf, hw, he, ht, hs⟩ := hInterior hd hQ
    (a - 1) T lam Lam (hleft.trans haT) hlam hLam A b hsym hA hlo hhi hb F hF M hM (by
        intro z hz
        rw [← Real.norm_eq_abs]
        exact (hC z hz).trans (le_max_left _ _))
  let U := scalarParabolicOpenCylinder (a - 1) T Ω
  let D := scalarParabolicOpenCylinder a T Ω
  let W := sourceInteriorZeroExtension (a - 1) T Ω w
  have hsub : D ⊆ U := prod_mono (Ioo_subset_Ioo hleft.le le_rfl) (Subset.refl _)
  have hWD : EqOn W w D := by
    intro z hz
    exact piecewise_eq_of_mem U w _ (hsub hz)
  have hwD : IsScalarC12On w D :=
    ⟨hw.continuousOn.mono hsub,
      fun z hz => hw.timeSlice_differentiableAt (hsub hz),
      fun z hz => hw.spatialSlice_contDiffAt (hsub hz),
      hw.continuousOn_scalarTimeDerivative.mono hsub,
      hw.continuousOn_scalarSpatialGradient.mono hsub,
      hw.continuousOn_scalarSpatialHessian.mono hsub⟩
  have hD : IsOpen D := isOpen_Ioo.prod hΩ
  have hWc := hBoundary hΩ (a - 1) a T M hleft hM
    q.toH1Function.toFun hq.continuous hqf w hw.continuousOn ht hs

  obtain ⟨hdt, hdg, hdd⟩ := Occupation.scalarJet_eqOn_of_eqOn_open hD hWD
  refine ⟨W, hWc, (Occupation.isScalarC12On_congr_open hD hwD hWD), ?_, ?_, ?_⟩
  · intro z hz
    simp only [scalarParabolicZeroOrderOperator_apply, zero_mul, add_zero,
      hdt hz, hdg hz, hdd hz] at ⊢
    simpa only [scalarParabolicZeroOrderOperator_apply, zero_mul, add_zero]
      using he z (hsub hz)
  · intro y _
    exact piecewise_eq_of_notMem U w _
      (fun h => (lt_irrefl T) h.1.2)
  · intro z hz

    exact piecewise_eq_of_notMem U w _ (fun h => (show z.2 ∉ Ω by
        have hf  := hz.2
        rw [hΩ.frontier_eq] at hf
        exact hf.2) h.2)

/-- The earlier time collar uses the domain-independent boundary squeeze. -/
theorem exists_signed_source_ellipsoid_correction_of_interior_geometry

    : ∀ {d : ℕ}, 0 < d → ∀ {Q : PDE.Mat d}, Q.PosDef →
  ∀ (a T lam Lam : ℝ), a < T → 0 < lam → lam ≤ Lam →
  ∀ (A : CoefficientField d) (b : PDE.TimeVectorField d),
  (∀ t y, (A t y).IsSymm) → IsSmoothCoefficient A →
  HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
  ContDiff ℝ PDE.smoothOrder (fun z : TimeVelocity d => b z.1 z.2) →
  ∀ (F : HypoellipticAleksandrov.Parabolic.ScalarField d), ContDiff ℝ PDE.smoothOrder F →
  ∃ W : HypoellipticAleksandrov.Parabolic.ScalarField d,
    IsClassicalBackwardDirichletSolution a T (openEllipsoid Q) A b
      (fun _ _ => 0) (fun t y => F (t, y)) (fun _ => 0) (fun _ => 0) W := exists_signed_source_ellipsoid_correction_of_upstream hOpen hGeom hInterior
    (@continuousOn_source_zeroExtension_closed_domain)
end


/-- Every smooth signed source has a continuous zero-boundary ellipsoid correction. -/
theorem exists_signed_source_ellipsoid_correction :
∀ {d : ℕ}, 0 < d → ∀ {Q : PDE.Mat d}, Q.PosDef →
  ∀ (a T lam Lam : ℝ), a < T → 0 < lam → lam ≤ Lam →
  ∀ (A : CoefficientField d) (b : PDE.TimeVectorField d),
  (∀ t y, (A t y).IsSymm) → IsSmoothCoefficient A →
  HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
  ContDiff ℝ PDE.smoothOrder (fun z : TimeVelocity d => b z.1 z.2) →
  ∀ (F : HypoellipticAleksandrov.Parabolic.ScalarField d), ContDiff ℝ PDE.smoothOrder F →
  ∃ W : HypoellipticAleksandrov.Parabolic.ScalarField d,
    IsClassicalBackwardDirichletSolution a T (openEllipsoid Q) A b
      (fun _ _ => 0) (fun t y => F (t, y)) (fun _ => 0) (fun _ => 0) W := exists_signed_source_ellipsoid_correction_of_interior_geometry
    (@isOpen_openEllipsoid) (@openEllipsoid_geometry)
    (@exists_signed_source_ellipsoidInterior_with_bounds)

end HypoellipticAleksandrov.KineticAleksandrov.Lieberman
