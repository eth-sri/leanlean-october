module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementEnergyBall
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonTracesBall
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovRegularity
public import PDEFoundation.Calculus.RegularityOrder


/-! # Classical signed corrections continuous up to the ball boundary

A finite earlier time collar supplies continuity at the lower face. The two proved
envelopes supply zero terminal and lateral traces, without compact-source restrictions.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set Dirichlet KineticAleksandrov
open scoped ENNReal MatrixOrder Matrix.Norms.Elementwise

/-- Every smooth signed source has a continuous zero-boundary classical correction on a ball. -/
theorem exists_signed_source_ball_correction {d : ℕ} (hd : 0 < d)
    (v₀ : PDE.Vec d) (r : ℝ) (hr : 0 < r) (a T : ℝ) (haT : a < T)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (F : HypoellipticAleksandrov.Parabolic.ScalarField d) (hF : ContDiff ℝ PDE.smoothOrder F) :
    ∃ W : HypoellipticAleksandrov.Parabolic.ScalarField d,
      IsClassicalBackwardDirichletSolution a T (PDE.euclideanBall v₀ r) A
        (fun _ _ => 0) (fun _ _ => 0) (fun t y => F (t, y))
        (fun _ => 0) (fun _ => 0) W := by
  classical
  let Ω := PDE.euclideanBall v₀ r
  have hΩ  := PDE.isOpen_euclideanBall v₀ r

  have hleft : a - 1 < a := by linarith


  obtain ⟨C, hC⟩ := (isCompact_scalarParabolicClosedCylinder (a - 1) T (Occupation.isBounded_euclideanBall v₀ hr)).exists_bound_of_continuousOn hF.continuous.continuousOn
  let M := max C 0
  have hM : 0 ≤ M := le_max_right _ _

  obtain ⟨w, hw, he, ht, hs⟩ := exists_signed_source_ballInterior_with_bounds hd
    v₀ r hr (a - 1) T (hleft.trans haT) lam Lam hlam hLam A hA hlo hhi F hF M hM (by
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
  have hWc := continuousOn_source_zeroExtension_closed_ball (a - 1) a T hleft
    v₀ r lam M hM w hw.continuousOn ht hs

  obtain ⟨hdt, _, hdd⟩ := Occupation.scalarJet_eqOn_of_eqOn_open hD hWD
  refine ⟨W, hWc, (Occupation.isScalarC12On_congr_open hD hwD hWD), ?_, ?_, ?_⟩
  · intro z hz
    simp only [scalarParabolicZeroOrderOperator_apply, Pi.zero_apply, PDE.vecDot,
      zero_mul, Finset.sum_const_zero, add_zero, hdt hz, hdd hz]
    exact he z (hsub hz)
  · intro y _
    exact piecewise_eq_of_notMem U w _
      (fun h => (lt_irrefl T) h.1.2)
  · intro z hz

    exact piecewise_eq_of_notMem U w _ (fun h => (show z.2 ∉ Ω by
        have hf  := hz.2
        rw [hΩ.frontier_eq] at hf
        exact hf.2) h.2)

end HypoellipticAleksandrov.Parabolic.LocalHolder
