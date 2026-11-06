module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentationProduct
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentationCutoff
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
import HypoellipticAleksandrov.Parabolic.ScalarClassical

/-! # The cutoff transport speed in the actual free-transport frame -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Filter Parabolic
open scoped Topology

/- The multiplier on the literal time-position carrier. -/
def localPositionMultiplier {d : ℕ} (Z₀ : KineticPoint d) (χ : PDE.Vec d → ℝ)
    (z : TimeVelocity d) : ℝ := χ (z.2 - Z₀.position - (z.1 - Z₀.time) • Z₀.velocity)

/- The free-transport defect is the cutoff differential applied to relative velocity. -/
def localCutoffTransport {d : ℕ} (Z₀ : KineticPoint d) (χ : PDE.Vec d → ℝ)
    (P : KineticPoint d) : ℝ :=
  fderiv ℝ χ (relativePosition Z₀ P) (P.velocity - Z₀.velocity)

/- The time-position multiplier is globally smooth. -/
theorem continuous_localCutoffTransport {d : ℕ} (Z₀ : KineticPoint d)
    {χ : PDE.Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    Continuous (localCutoffTransport Z₀ χ) := by
  have hrel : Continuous (relativePosition Z₀) :=
    (continuous_position.sub continuous_const).sub
      ((continuous_time.sub continuous_const).smul continuous_const)
  exact ((hχ.continuous_fderiv (by simp)).comp hrel).clm_apply
    (continuous_velocity.sub continuous_const)

/- Outside the cutoff support there is no transport defect. -/
theorem localCutoffTransport_zero {d : ℕ} (Z₀ P : KineticPoint d)
    (χ : PDE.Vec d → ℝ) (hx : relativePosition Z₀ P ∉ tsupport χ) :
    localCutoffTransport Z₀ χ P = 0 := by
  rw [localCutoffTransport, fderiv_of_notMem_tsupport ℝ hx, zero_apply]

/- The two coordinate transport terms equal the differential on relative velocity. -/
theorem localCutoffSolution_operator {d : ℕ} (Z₀ : KineticPoint d)
    (A : FullKineticCoefficient d) {χ : PDE.Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {u D}
    (hu : IsKineticC112On u D) {P : KineticPoint d} (hP : P ∈ D) :
    forwardKineticOperator A (localCutoffSolution Z₀ χ u) P =
      localPositionCutoff Z₀ χ P * forwardKineticOperator A u P +
        localCutoffTransport Z₀ χ P * u P := by
  have h : forwardKineticOperator A (fun Q => (localPositionMultiplier Z₀ χ) (Q.time, Q.position) * u Q) P =
      (localPositionMultiplier Z₀ χ) (P.time, P.position) * forwardKineticOperator A u P +
        (scalarTimeDerivative (localPositionMultiplier Z₀ χ) (P.time, P.position) +
          PDE.vecDot P.velocity (scalarSpatialGradient (localPositionMultiplier Z₀ χ) (P.time, P.position))) * u P := by
    let η := (localPositionMultiplier Z₀ χ)
    have hη : ContDiff ℝ (⊤ : ℕ∞) (localPositionMultiplier Z₀ χ) := by
        exact (
      hχ.comp ((contDiff_snd.sub contDiff_const).sub
          ((contDiff_fst.sub contDiff_const).smul contDiff_const))
      )

    have hηt : DifferentiableAt ℝ (fun t => η (t, P.position)) P.time :=
      (hη.comp (contDiff_id.prodMk contDiff_const)).differentiable
        (by norm_num) |>.differentiableAt
    have hηx : DifferentiableAt ℝ (fun x => η (P.time, x)) P.position :=
      (hη.comp (contDiff_const.prodMk contDiff_id)).differentiable
        (by norm_num) |>.differentiableAt
    have hut := hu.timeSlice_differentiableAt hP
    have hux := (hu.positionSlice_contDiffAt hP).differentiableAt (by norm_num)
    have ht : kineticTimeDerivative (fun Q => η (Q.time, Q.position) * u Q) P =
        scalarTimeDerivative η (P.time, P.position) * u P +
          η (P.time, P.position) * kineticTimeDerivative u P := deriv_mul hηt hut
    have hx : kineticPositionGradient (fun Q => η (Q.time, Q.position) * u Q) P =
        η (P.time, P.position) • kineticPositionGradient u P +
          u P • scalarSpatialGradient η (P.time, P.position) := by
      ext i
      change fderiv ℝ ((fun x => η (P.time, x)) * fun x => u ⟨P.time, x, P.velocity⟩)
        P.position (PDE.basisVec i) = _
      rw [fderiv_mul hηx hux]
      simp only [add_apply, smul_apply,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, kineticPositionGradient,
        scalarSpatialGradient, PDE.classicalGradient_apply]
    have hv : kineticVelocityHessian (fun Q => η (Q.time, Q.position) * u Q) P =
        η (P.time, P.position) • kineticVelocityHessian u P := by
      simp only [kineticVelocityHessian_eq_sliceHessian]
      exact sliceHessian_const_mul _ (hu.velocitySlice_contDiffAt hP)
    rw [forwardKineticOperator_apply, ht, hx, hv, matrixContraction_smul_right,
      forwardKineticOperator_apply]
    simp only [PDE.vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib]
    have ha : (∑ i, P.velocity i *
        (η (P.time, P.position) * kineticPositionGradient u P i)) =
        η (P.time, P.position) * ∑ i, P.velocity i * kineticPositionGradient u P i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hb : (∑ i, P.velocity i *
        (u P * scalarSpatialGradient η (P.time, P.position) i)) =
        u P * ∑ i, P.velocity i * scalarSpatialGradient η (P.time, P.position) i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [ha, hb]
    ring
  have _h_inl_12 : scalarTimeDerivative (localPositionMultiplier Z₀ χ) (P.time, P.position) +
      PDE.vecDot P.velocity
        (scalarSpatialGradient (localPositionMultiplier Z₀ χ) (P.time, P.position)) =
      localCutoffTransport Z₀ χ P := by
      have hd := hχ.differentiable (by norm_num)
      have ht : HasDerivAt
          (fun t : ℝ => P.position - Z₀.position - (t - Z₀.time) • Z₀.velocity)
          (-Z₀.velocity) P.time := by
        convert (hasDerivAt_const P.time (P.position - Z₀.position)).sub
          (((hasDerivAt_id P.time).sub_const Z₀.time).smul_const Z₀.velocity) using 1
        · funext t
          rfl
        · simp only [zero_sub, one_smul]
      have htime := (hd (relativePosition Z₀ P)).hasFDerivAt.comp_hasDerivAt P.time ht
      have hspace := (hd (relativePosition Z₀ P)).hasFDerivAt.comp P.position
        (((hasFDerivAt_id P.position).sub_const Z₀.position).sub_const
          ((P.time - Z₀.time) • Z₀.velocity))
      have hte : scalarTimeDerivative (localPositionMultiplier Z₀ χ) (P.time, P.position) =
          fderiv ℝ χ (relativePosition Z₀ P) (-Z₀.velocity) := htime.deriv
      have hxe : scalarSpatialGradient (localPositionMultiplier Z₀ χ) (P.time, P.position) =
          PDE.classicalGradient χ (relativePosition Z₀ P) := by
        ext i
        change fderiv ℝ (fun x => χ (x - Z₀.position -
          (P.time - Z₀.time) • Z₀.velocity)) P.position (PDE.basisVec i) = _
        simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply, PDE.classicalGradient_apply] using
          congrArg (fun L : PDE.Vec d →L[ℝ] ℝ => L (PDE.basisVec i)) hspace.fderiv
      rw [hte, hxe, PDE.vecDot_comm]
      change fderiv ℝ χ (relativePosition Z₀ P) (-Z₀.velocity) +
        PDE.vecDot (fun i => fderiv ℝ χ (relativePosition Z₀ P) (PDE.basisVec i))
          P.velocity = _
      rw [← PDE.ContinuousLinearMap.apply_eq_vecDot_basisValues]
      simp only [localCutoffTransport, map_neg, map_sub]
      ring

    /- The exact local cutoff residual, at a point where the original solution is classical. -/
  rw [_h_inl_12] at h
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
