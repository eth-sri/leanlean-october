module

public import HypoellipticAleksandrov.Parabolic.ScalarClassicalRestriction

public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.SourceEllipsoidBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.SourceBoundaryExtension
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovRegularity

/-! # Source correction on a closed ellipsoid cylinder using an earlier time collar -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Lieberman
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.Parabolic.LocalHolder
open Set MeasureTheory Filter
open scoped Matrix ENNReal Topology MatrixOrder Matrix.Norms.Elementwise BigOperators

/-- Every smooth signed source has a continuous zero-boundary ellipsoid correction. -/
theorem exists_signed_source_ellipsoid_correction :
∀ {d : ℕ}, 0 < d → ∀ {Q : PDE.Mat d}, Q.PosDef →
  ∀ (a T lam Lam : ℝ), a < T → 0 < lam → lam ≤ Lam →
  ∀ (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d),
  (∀ t y, (A t y).IsSymm) → IsSmoothCoefficient A →
  HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
  ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2) →
  ∀ (F : TimeVelocity d → ℝ), ContDiff ℝ (⊤ : ℕ∞) F →
  ∃ W : TimeVelocity d → ℝ,
    IsClassicalBackwardDirichletSolution a T (openEllipsoid Q) A b
      (fun _ _ => 0) (fun t y => F (t, y)) (fun _ => 0) (fun _ => 0) W := by
  intro d hd Q hQ a T lam Lam haT hlam hLam A b hsym hA hlo hhi hb F hF
  classical
  let Ω := openEllipsoid Q
  have hΩ : IsOpen Ω := isOpen_openEllipsoid Q
  have hΩb : Bornology.IsBounded Ω := (openEllipsoid_geometry hQ).1
  have hleft : a - 1 < a := sub_lt_self a zero_lt_one
  have hK : IsCompact (scalarParabolicClosedCylinder (a-1) T Ω) := isCompact_Icc.prod hΩb.isCompact_closure
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuous.continuousOn
  let M := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hFM : ∀ z ∈ scalarParabolicClosedCylinder (a - 1) T Ω, |F z| ≤ M := by
    intro z hz
    rw [← Real.norm_eq_abs]
    exact (hC z hz).trans (le_max_left _ _)
  obtain ⟨w, q, hq, hqf, hw, he, bound⟩ := exists_signed_source_ellipsoidInterior_with_bounds hd hQ
    (a - 1) T lam hlam A b hA hlo hb F hF M hM hFM
  let U := scalarParabolicOpenCylinder (a - 1) T Ω
  let D := scalarParabolicOpenCylinder a T Ω
  let W := sourceInteriorZeroExtension (a - 1) T Ω w
  have hsub : D ⊆ U := prod_mono (Ioo_subset_Ioo hleft.le le_rfl) (Subset.refl _)
  have hWD : EqOn W w D := by
    intro z hz
    exact piecewise_eq_of_mem U w (fun _ => 0) (hsub hz)
  have hwD : IsScalarC12On w D := hw.mono hsub
  have hD : IsOpen D := isOpen_Ioo.prod hΩ
  have hWc := continuousOn_source_zeroExtension_closed_domain hΩ (a - 1) a T M hleft hM
    q hq hqf w hw.continuousOn (fun z hz => (le_min_iff.mp (bound z hz)).1) (fun z hz => (le_min_iff.mp (bound z hz)).2)
  have hWr := Occupation.isScalarC12On_congr_open hD hwD hWD
  obtain ⟨hdt, hdg, hdd⟩ := Occupation.scalarJet_eqOn_of_eqOn_open hD hWD
  refine ⟨W, hWc, hWr, ?_, ?_, ?_⟩
  · intro z hz
    simp only [scalarParabolicZeroOrderOperator_apply, zero_mul, add_zero,
      hdt hz, hdg hz, hdd hz] at ⊢
    simpa only [scalarParabolicZeroOrderOperator_apply, zero_mul, add_zero]
      using he (hsub hz)
  · intro y _
    exact piecewise_eq_of_notMem U w (fun _ => 0)
      (fun h => (lt_irrefl T) h.1.2)
  · intro z hz
    have hzo : z.2 ∉ Ω := by
      have hf : z.2 ∈ frontier Ω := hz.2
      rw [hΩ.frontier_eq] at hf
      exact hf.2
    exact piecewise_eq_of_notMem U w (fun _ => 0) (fun h => hzo h.2)

end HypoellipticAleksandrov.KineticAleksandrov.Lieberman
