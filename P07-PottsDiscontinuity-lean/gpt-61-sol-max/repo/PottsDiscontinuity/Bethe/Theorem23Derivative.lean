module
public import Mathlib

public import PottsDiscontinuity.Bethe.Theorem23Coordinates

/-! # The coordinate residual and its Frechet derivative -/

@[expose] public section



namespace PottsDiscontinuity.Bethe

/-- The residual in the first-half coordinates of the symmetric subspace. -/
noncomputable def discreteCoordinateResidual (Δ : ℝ) (N n : ℕ)
    (q : Fin (n / 2) → ℝ) : Fin (n / 2) → ℝ := fun i =>
  discreteBetheResidual Δ N n (discreteSymLift n q) (discreteHalfIndex n i)

section

variable {Δ : ℝ} (hΔ : Δ < -1) (N n : ℕ) (q : Fin (n / 2) → ℝ)
include hΔ N q

theorem analyticAt_discreteCoordinateResidual  :
    AnalyticAt ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) =>
      discreteCoordinateResidual z.1 N n z.2) (Δ, q) := by
  have hlift : AnalyticAt ℝ (fun z  => discreteSymLift n z.2) (Δ, q) :=
    (discreteSymLift n).toContinuousLinearMap.analyticAt _ |>.comp analyticAt_snd
  have hcoord (j : Fin n)  :=
    (( ContinuousLinearMap.proj j ).analyticAt _).comp hlift
  apply AnalyticAt.pi
  intro i
  have hphase (j : Fin n)  :=
    AnalyticAt.comp
      (g := fun w  => theta w.1 w.2.1 w.2.2)
      (f := fun z : ℝ × (Fin (n / 2) → ℝ) =>
        (z.1, discreteSymLift n z.2 (discreteHalfIndex n i), discreteSymLift n z.2 j))
      (analyticAt_theta hΔ _ _) (analyticAt_fst.prod ((hcoord _).prod (hcoord j)))
  
  
  
  exact (hcoord _).sub (analyticAt_const.sub ((Finset.analyticAt_fun_sum Finset.univ  fun j _ => hphase j ).mul analyticAt_const))

/-- Each column of the state Frechet derivative is the displayed source
Jacobian column, in the actual coordinates of the symmetric subspace. -/
theorem discreteCoordinateResidual_stateDerivative_column  (i k : Fin (n / 2)) :
    (((fderiv ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) =>
      discreteCoordinateResidual z.1 N n z.2) (Δ, q)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Fin (n / 2) → ℝ))) (Pi.single k 1)) i =
      discreteBetheMatrixA Δ N n (discreteSymLift n q) i k := by
  let F := fun z : ℝ × (Fin (n / 2) → ℝ) => discreteCoordinateResidual z.1 N n z.2
  let e : Fin (n / 2) → ℝ := Pi.single k 1
  have hq : HasDerivAt (fun t : ℝ => q + t • e) e 0 := by
    change HasDerivAt ((fun _  => q) +  fun t : ℝ => t • e ) e 0
    convert (hasDerivAt_const  0  q).add
      ((hasDerivAt_id (0 : ℝ)).smul_const e) using 1
    all_goals simp_all
  have hpath := (hasDerivAt_const  0  Δ).prodMk hq
  
  have hF0 : HasFDerivAt F (fderiv ℝ F (Δ, q)) (Δ, q + (0 : ℝ) • e) := by
    simpa only [zero_smul, add_zero] using  (analyticAt_discreteCoordinateResidual hΔ N n q).differentiableAt.hasFDerivAt 
  
  have hscalar := ((ContinuousLinearMap.proj i ).hasFDerivAt).comp_hasDerivAt  0  (hF0.comp_hasDerivAt (0 : ℝ) hpath)
  
  change HasDerivAt (fun t => F (Δ, q + t • e) i)
    ((fderiv ℝ F (Δ, q)) (0, e) i) 0 at hscalar
  rw [(by
         
         unfold F discreteCoordinateResidual
         
         simp only [map_add, map_smul, e, discreteSymLift_single]
         rfl : (fun t  => F (Δ, q + t • e) i) =
       fun t => discreteBetheResidual Δ N n
        (discreteBetheAffinePath (discreteSymLift n q) (discreteSymBasis n k) t)
        (discreteHalfIndex n i))] at hscalar
  exact hscalar.unique (hasDerivAt_discreteBetheResidual_basis hΔ (discreteSymLift n q) i k)

/-- Equality of the full state derivative and the source's matrix linear map. -/
theorem discreteCoordinateResidual_stateDerivative  :
    (fderiv ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) =>
      discreteCoordinateResidual z.1 N n z.2) (Δ, q)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Fin (n / 2) → ℝ)) =
      (Matrix.toLin' (discreteBetheMatrixA Δ N n (discreteSymLift n q))).toContinuousLinearMap := by
  
  
  have hlin : ((fderiv ℝ (fun z  =>
                 discreteCoordinateResidual z.1 N n z.2) (Δ, q)).comp
                   (ContinuousLinearMap.inr ℝ ℝ (Fin (n / 2) → ℝ))).toLinearMap = Matrix.toLin' (discreteBetheMatrixA Δ N n (discreteSymLift n q)) := by
    apply (Pi.basisFun ℝ (Fin (n / 2))).ext
    intro k
    funext i
    simp only [Pi.basisFun_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one,
      Matrix.col_apply]
    convert discreteCoordinateResidual_stateDerivative_column hΔ N n q i k using 1
  ext q' i
  exact congrFun (LinearMap.congr_fun hlin q') i

/-- Nonsingularity of the matrix supplies precisely the continuous linear
equivalence required by the analytic implicit function theorem. -/
theorem exists_discreteCoordinateResidual_stateEquiv 
    (hdet : (discreteBetheMatrixA Δ N n (discreteSymLift n q)).det ≠ 0) :
    ∃ e : (Fin (n / 2) → ℝ) ≃L[ℝ]  Fin (n / 2) → ℝ ,
      (fderiv ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) =>
        discreteCoordinateResidual z.1 N n z.2) (Δ, q)).comp
          (ContinuousLinearMap.inr ℝ ℝ (Fin (n / 2) → ℝ)) =
        (e : (Fin (n / 2) → ℝ) →L[ℝ]  Fin (n / 2) → ℝ ) := by
  
  
  
  refine ⟨ (Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin (n / 2))) (discreteBetheMatrixA Δ N n (discreteSymLift n q))
             (isUnit_iff_ne_zero.mpr hdet)).toContinuousLinearEquiv , ?_⟩
  rw [discreteCoordinateResidual_stateDerivative hΔ]
  aesop

end

end PottsDiscontinuity.Bethe
