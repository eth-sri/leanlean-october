module
public import AlbertGeometry.AmbientLeviCivitaProduct

/-! Differentiate the Koszul pairing on the open locus of invertible metrics.
In the antisymmetrization the second derivatives of the metric cancel. -/
@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
attribute [local instance] taskAmbientDualNorm taskAmbientDualSpace taskAmbientBilinearNorm taskAmbientBilinearSpace taskAmbientTrilinearNorm taskAmbientTrilinearSpace taskAmbientEndNorm taskAmbientEndSpace taskAmbientVectorBilinearNorm taskAmbientVectorBilinearSpace taskAmbientInverseNorm taskAmbientInverseSpace
open Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]

theorem curvature_comm (P : BasedCubic E) {x : E} (hx : 0 < cubic P x) (hi : (metric P x).IsInvertible) (u v w : E) :
    ambientCurvature P x u v w = -(ambientConnection P x u (ambientConnection P x v w) -
      ambientConnection P x v (ambientConnection P x u w)) := by
  let C := ambientConnection P; let D := fderiv ℝ C x; let DD := fderiv ℝ (ambientMetricD1 P) x
  have dC : HasFDerivAt C D x := ((smooth_connection P hx hi).differentiableAt (by simp)).hasFDerivAt
  have dG := hasD_metric P hx
  have hd : ContDiffAt ℝ ⊤ (ambientMetricD1 P) x := (metric_smooth P hx).fderiv_right (by simp)
  have dJ : HasFDerivAt (ambientMetricD1 P) DD x := (hd.differentiableAt (by simp)).hasFDerivAt
  have dPair (a b c z : E) : metric P x (D a b c) z = 1/2 * DD a b c z - ambientMetricD1 P x a (C x b c) z := by
    have he : (fun y => metric P y (C y b c) z) =ᶠ[𝓝 x] fun y => (1/2 : ℝ) * ambientMetricD1 P y b c z := by
      filter_upwards [pos_near P hx,dG.continuousAt hi.eventually_nhds] with y h j using connection_pair P h j b c z
    have h₁ := evalD (dG.clm_apply (evalD (evalD dC b) c)) z
    have h₂ := (evalD (evalD (evalD dJ b) c) z).const_smul (1/2 : ℝ)
    have h := congrArg (fun L : E →L[ℝ] ℝ => L a) (h₁.unique (h₂.congr_of_eventuallyEq he))
    simp at h; linarith
  have nested (a b : E) : ambientCovariantDerivative P a (ambientCovariantDerivative P b (fun _ => w)) x =
      D a b w + C x a (C x b w) := by
    have h : ambientCovariantDerivative P b (fun _ => w) = fun y => C y b w := by funext y; simp [ambientCovariantDerivative,C]
    rw [h,ambientCovariantDerivative,(evalD (evalD dC b) w).fderiv]; rfl
  apply hi.injective; ext z
  simp only [ambientCurvature,nested,map_sub,map_add,map_neg,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.neg_apply, dPair]
  have sym : DD u v w z = DD v u w z := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L w z)
    (((metric_smooth P hx).isSymmSndFDerivAt le_top).eq u v)
  linarith [connection_pair P hx hi u (C x v w) z,connection_pair P hx hi v (C x u w) z]
end
end Glennie.SubmissionR04Intrinsic
