/-
Actual curvature is the commutator of the genuine
ambient covariant derivatives on constant affine fields (their bracket is zero).
The derivative-coefficient formula is proved with actual derivative certificates;
the negative multiplication commutator is then a theorem, never the definition.
Arbitrary positive based cubics, all ambient/radial slots, before Jordan.
This does not redefine or assume an ambient/level-chart curvature identification.
-/
module

public import AlbertGeometry.AmbientLeviCivitaProduct
@[expose] public section
namespace AlbertGeometry.AmbientCurvatureProduct
noncomputable section
open Glennie.SubmissionR04Intrinsic
open AlbertGeometry.Cubic
open AlbertGeometry.BasedNormDerivativeTransport
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso
open AlbertGeometry.BasedNormAdjointTransport
open AlbertGeometry.AmbientLeviCivitaProduct
open scoped AlbertGeometry.AmbientLeviCivitaProduct
open scoped ContDiff Topology
open Filter
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Literal second derivative of the actual varying ambient metric. -/
def ambientMetricD2 (P : BasedCubic E) (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (ambientMetricD1 P) x

theorem hasFDerivAt_actual_metricD1 (P : BasedCubic E) {x : E}
    (hx : 0 < cubic P x) :
    HasFDerivAt (ambientMetricD1 P) (ambientMetricD2 P x) x :=
  (((contDiffAt_actual_metric P hx).fderiv_right (m := ⊤) (by simp)).differentiableAt (by simp)).hasFDerivAt

/-- Fourth-derivative cancellation is an actual Schwarz theorem for g. -/
theorem ambientMetricD2_swap12 (P : BasedCubic E) {x : E}
    (hx : 0 < cubic P x) (u v w z : E) :
    ambientMetricD2 P x u v w z = ambientMetricD2 P x v u w z := by
  exact congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L w z)
    (((contDiffAt_actual_metric P hx).isSymmSndFDerivAt le_top).eq u v)

/-- The genuine derivative of the smooth actual connection coefficient. -/
def ambientGammaD1 (P : BasedCubic E) (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] E := fderiv ℝ (ambientConnection P) x

theorem hasFDerivAt_actual_ambientGamma (P : BasedCubic E) {x : E}
    (hx : 0 < cubic P x)
    (hp : ∀ u : E, u ≠ 0 → 0 < metric P x u u) :
    HasFDerivAt (ambientConnection P) (ambientGammaD1 P x) x :=
  ((contDiffAt_ambientGamma P hx hp).differentiableAt (by simp)).hasFDerivAt

theorem ambientCovariantDerivative_const (P : BasedCubic E) (u w : E) :
    ambientCovariantDerivative P u (fun _ : E => w) = fun x => ambientConnection P x u w := by
  funext x
  simp [ambientCovariantDerivative]

/-- The actual constant-field curvature has its actual D-Gamma expression,
by proved differentiability and uniqueness rather than total-fderiv fallback. -/
theorem ambientCurvature_apply (P : BasedCubic E) {x : E}
    (hx : 0 < cubic P x)
    (hp : ∀ u : E, u ≠ 0 → 0 < metric P x u u) (u v w : E) :
    ambientCurvature P x u v w =
      ambientGammaD1 P x u v w - ambientGammaD1 P x v u w +
        ambientConnection P x u (ambientConnection P x v w) -
          ambientConnection P x v (ambientConnection P x u w) := by
  have hΓ := hasFDerivAt_actual_ambientGamma P hx hp
  have hv := (hΓ.clm_apply_const v).clm_apply_const w
  have hu := (hΓ.clm_apply_const u).clm_apply_const w
  simp only [ambientCurvature, ambientCovariantDerivative_const]
  simp only [ambientCovariantDerivative,
    hv.fderiv, hu.fderiv, ContinuousLinearMap.flip_apply]
  abel

/-- The Hessian metric has Dg=2g(Gamma(.,.),.) at every positive metric point. -/
theorem ambientMetricD1_eq_two_Gamma (P : BasedCubic E) {x : E}
    (hx : 0 < cubic P x)
    (hp : ∀ u : E, u ≠ 0 → 0 < metric P x u u) (u v w : E) :
    ambientMetricD1 P x u v w =
      2 * metric P x (ambientConnection P x u v) w := by
  have h := ambientGamma_koszul P x (actual_metric_dual_isInvertible P x hp) u v w
  rw [ambientKoszulTensor_eq_half P hx] at h
  simp only [smul_apply, smul_eq_mul] at h
  linarith

/-- Differentiate actual Koszul pairing on a proved positive neighborhood.
All scalar/CLM derivatives have actual certificates. No inverse derivative
formula or prescribed fourth metric jet is assumed. -/
theorem ambientGammaD1_pairing (P : BasedCubic E) {x : E}
    (hx : 0 < cubic P x)
    (hp : ∀ u : E, u ≠ 0 → 0 < metric P x u u) (u v w z : E) :
    metric P x (ambientGammaD1 P x u v w) z =
      (1 / 2 : ℝ) * ambientMetricD2 P x u v w z -
        ambientMetricD1 P x u (ambientConnection P x v w) z := by
  have hG := hasFDerivAt_actual_metric P hx
  have hΓ := ((hasFDerivAt_actual_ambientGamma P hx hp).clm_apply_const v).clm_apply_const w
  have hpair := (hG.clm_apply hΓ).clm_apply_const z
  have hjet := (((hasFDerivAt_actual_metricD1 P hx).clm_apply_const v).clm_apply_const w).clm_apply_const z
  have hinv := (contDiffAt_actual_metric P hx).continuousAt.eventually
    (actual_metric_dual_isInvertible P x hp).eventually_nhds
  have hc : (fun y => metric P y (ambientConnection P y v w) z) =ᶠ[𝓝 x]
      (fun y => (1 / 2 : ℝ) * ambientMetricD1 P y v w z) := by
    filter_upwards [eventually_positive P hx, hinv] with y hy hi
    rw [ambientGamma_koszul P y hi, ambientKoszulTensor_eq_half P hy]
    rfl
  have hd := DFunLike.congr_fun
    (hpair.unique ((hjet.const_smul (1 / 2 : ℝ)).congr_of_eventuallyEq hc)) u
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    add_apply, smul_apply, smul_eq_mul] at hd
  linarith

/-- Actual Hessian curvature is the negative connection commutator at every
positive metric point. Symmetric fourth derivatives cancel, leaving the
inverse-raising terms with the manuscript's sign. -/
theorem ambientCurvature_eq_neg_Gamma_commutator (P : BasedCubic E) {x : E}
    (hx : 0 < cubic P x)
    (hp : ∀ u : E, u ≠ 0 → 0 < metric P x u u) (u v w : E) :
    ambientCurvature P x u v w =
      -(ambientConnection P x u (ambientConnection P x v w) -
        ambientConnection P x v (ambientConnection P x u w)) := by
  apply (actual_metric_dual_isInvertible P x hp).injective
  ext z
  simp only [ambientCurvature_apply P hx hp, map_sub, map_add, map_neg,
    sub_apply, add_apply, neg_apply, ambientGammaD1_pairing P hx hp,
    ambientMetricD2_swap12 P hx v u, ambientMetricD1_eq_two_Gamma P hx hp]
  ring

end
end AlbertGeometry.AmbientCurvatureProduct
