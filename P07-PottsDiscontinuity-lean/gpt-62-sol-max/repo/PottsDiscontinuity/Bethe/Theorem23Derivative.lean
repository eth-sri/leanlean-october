module

public import PottsDiscontinuity.Bethe.Theorem23Coordinates

/-! # The coordinate residual and its Frechet derivative -/

@[expose] public section

open scoped BigOperators

namespace PottsDiscontinuity.Bethe

/-- The residual in the first-half coordinates of the symmetric subspace. -/
noncomputable def discreteCoordinateResidual (Δ : ℝ) (N n : ℕ)
    (q : Fin (n / 2) → ℝ) : Fin (n / 2) → ℝ := fun i =>
  discreteBetheResidual Δ N n (discreteSymLift n q) (discreteHalfIndex n i)

/-- Joint analyticity depends only on the analyticity of the two-body phase. -/
theorem analyticAt_coordinateResidual_of_phase {θ : ℝ × ℝ × ℝ → ℝ} {t : ℝ}
    (hθ : ∀ a b, AnalyticAt ℝ θ (t, a, b)) (N n : ℕ) (q : Fin (n / 2) → ℝ) :
    AnalyticAt ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) => fun i =>
      z.2 i - (2 * Real.pi * discreteBetheIndex n (discreteHalfIndex n i) / N -
        (∑ j : Fin n, θ (z.1, discreteSymLift n z.2 (discreteHalfIndex n i), discreteSymLift n z.2 j)) / N)) (t, q) := by
  have hlift : AnalyticAt ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) => discreteSymLift n z.2) (t, q) :=
    ((discreteSymLift n).toContinuousLinearMap.analyticAt _).comp analyticAt_snd
  have hc := analyticAt_pi_iff.mp hlift
  apply AnalyticAt.pi
  intro i
  have hsum := Finset.analyticAt_fun_sum Finset.univ (fun (j : Fin n) _ =>
    AnalyticAt.comp (f := fun z : ℝ × (Fin (n / 2) → ℝ) =>
      (z.1, discreteSymLift n z.2 (discreteHalfIndex n i), discreteSymLift n z.2 j))
      (hθ _ _) (analyticAt_fst.prod ((hc (discreteHalfIndex n i)).prod (hc j))))
  exact ((analyticAt_pi_iff.mp analyticAt_snd) i).sub (analyticAt_const.sub hsum.div_const)

theorem analyticAt_discreteCoordinateResidual {Δ : ℝ} (hΔ : Δ < -1)
    (N n : ℕ) (q : Fin (n / 2) → ℝ) :
    AnalyticAt ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) =>
      discreteCoordinateResidual z.1 N n z.2) (Δ, q) := by
  unfold discreteCoordinateResidual discreteBetheResidual discreteBetheMap
  simpa only [discreteSymLift_half] using
    analyticAt_coordinateResidual_of_phase (analyticAt_theta hΔ) N n q

/-- Each column of the state Frechet derivative is the displayed source
Jacobian column, in the actual coordinates of the symmetric subspace. -/
theorem discreteCoordinateResidual_stateDerivative_column {Δ : ℝ} (hΔ : Δ < -1)
    (N n : ℕ) (q : Fin (n / 2) → ℝ) (i k : Fin (n / 2)) :
    (((fderiv ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) =>
      discreteCoordinateResidual z.1 N n z.2) (Δ, q)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Fin (n / 2) → ℝ))) (Pi.single k 1)) i =
      discreteBetheMatrixA Δ N n (discreteSymLift n q) i k := by
  let F := fun z : ℝ × (Fin (n / 2) → ℝ) => discreteCoordinateResidual z.1 N n z.2
  let e : Fin (n / 2) → ℝ := Pi.single k 1
  have hq : HasDerivAt (fun t : ℝ => q + t • e) e 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const e).const_add q
  have hpath := (hasDerivAt_const (0 : ℝ) Δ).prodMk hq
  have hF :=
    (analyticAt_discreteCoordinateResidual hΔ N n q).differentiableAt.hasFDerivAt
  have hF0 : HasFDerivAt F (fderiv ℝ F (Δ, q)) (Δ, q + (0 : ℝ) • e) := by
    simpa only [zero_smul, add_zero] using hF
  have hcomp := hF0.comp_hasDerivAt (0 : ℝ) hpath
  have hscalar := ((ContinuousLinearMap.proj i :
    (Fin (n / 2) → ℝ) →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) hcomp
  have heq : (fun t : ℝ => F (Δ, q + t • e) i) =
      (fun t => discreteBetheResidual Δ N n
        (discreteBetheAffinePath (discreteSymLift n q) (discreteSymBasis n k) t)
        (discreteHalfIndex n i)) := by
    funext t
    unfold F discreteCoordinateResidual
    congr 2
    simp only [map_add, map_smul, e, discreteSymLift_single]
    rfl
  change HasDerivAt (fun t => F (Δ, q + t • e) i)
    ((fderiv ℝ F (Δ, q)) (0, e) i) 0 at hscalar
  rw [heq] at hscalar
  exact hscalar.unique (hasDerivAt_discreteBetheResidual_basis hΔ (discreteSymLift n q) i k)

/-- Equality of the full state derivative and the source's matrix linear map. -/
theorem discreteCoordinateResidual_stateDerivative {Δ : ℝ} (hΔ : Δ < -1)
    (N n : ℕ) (q : Fin (n / 2) → ℝ) :
    (fderiv ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) =>
      discreteCoordinateResidual z.1 N n z.2) (Δ, q)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Fin (n / 2) → ℝ)) =
      (Matrix.toLin' (discreteBetheMatrixA Δ N n (discreteSymLift n q))).toContinuousLinearMap := by
  classical
  apply ContinuousLinearMap.coe_injective
  apply (Pi.basisFun ℝ (Fin (n / 2))).ext
  intro k
  funext i
  change _ = Matrix.toLin' (discreteBetheMatrixA Δ N n (discreteSymLift n q))
    (Pi.basisFun ℝ (Fin (n / 2)) k) i
  simpa only [ContinuousLinearMap.coe_coe, Pi.basisFun_apply, Matrix.toLin'_apply,
    Matrix.mulVec_single_one, Matrix.col_apply] using
    discreteCoordinateResidual_stateDerivative_column hΔ N n q i k

/-- Nonsingularity of the matrix supplies precisely the continuous linear
equivalence required by the analytic implicit function theorem. -/
theorem exists_discreteCoordinateResidual_stateEquiv {Δ : ℝ} (hΔ : Δ < -1)
    (N n : ℕ) (q : Fin (n / 2) → ℝ)
    (hdet : (discreteBetheMatrixA Δ N n (discreteSymLift n q)).det ≠ 0) :
    ∃ e : (Fin (n / 2) → ℝ) ≃L[ℝ] (Fin (n / 2) → ℝ),
      (fderiv ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) =>
        discreteCoordinateResidual z.1 N n z.2) (Δ, q)).comp
          (ContinuousLinearMap.inr ℝ ℝ (Fin (n / 2) → ℝ)) =
        (e : (Fin (n / 2) → ℝ) →L[ℝ] (Fin (n / 2) → ℝ)) := by
  classical
  let A := discreteBetheMatrixA Δ N n (discreteSymLift n q)
  let e := (Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin (n / 2))) A
    (isUnit_iff_ne_zero.mpr hdet)).toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  rw [discreteCoordinateResidual_stateDerivative hΔ]
  rfl

end PottsDiscontinuity.Bethe
