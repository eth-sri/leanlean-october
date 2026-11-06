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
open AlbertGeometry.Cubic
open AlbertGeometry.BasedNormAdjointTransport
open AlbertGeometry.AmbientLeviCivitaProduct
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

local instance dualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance dualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

/-- Literal second derivative of the actual varying ambient metric. -/
def ambientMetricD2 (P : SymmetricTrilinearForm E) (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (ambientMetricD1 P) x

theorem hasFDerivAt_actual_metricD1 (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    HasFDerivAt (ambientMetricD1 P) (ambientMetricD2 P x) x :=
  (((contDiffAt_actual_metric P hx).fderiv_right (m := ⊤) (by simp)).differentiableAt (by simp)).hasFDerivAt

/-- Fourth-derivative cancellation is an actual Schwarz theorem for g. -/
theorem ambientMetricD2_swap12 (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) (u v w z : E) :
    ambientMetricD2 P x u v w z = ambientMetricD2 P x v u w z :=
  congr($(((contDiffAt_actual_metric P hx).isSymmSndFDerivAt le_top).eq u v) w z)

/-- The genuine derivative of the smooth actual connection coefficient. -/
def ambientGammaD1 (P : SymmetricTrilinearForm E) (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] E := fderiv ℝ (ambientGamma P) x

theorem hasFDerivAt_actual_ambientGamma (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) :
    HasFDerivAt (ambientGamma P) (ambientGammaD1 P x) x :=
  ((contDiffAt_ambientGamma P hx hp).differentiableAt (by simp)).hasFDerivAt

/-- The actual connection on a field in a constant affine direction. Its
coefficient has the smooth torsion/metric/uniqueness laws in the imported leaf. -/
def ambientCovariantDerivative (P : SymmetricTrilinearForm E) (u : E)
    (Y : E → E) (x : E) : E := fderiv ℝ Y x u + ambientGamma P x u (Y x)

theorem ambientCovariantDerivative_const (P : SymmetricTrilinearForm E) (u w x : E) :
    ambientCovariantDerivative P u (fun _ => w) x = ambientGamma P x u w := by
  simp [ambientCovariantDerivative]

/-- Actual covariant-derivative commutator on constant affine fields. Those
direction fields commute, so their Lie-bracket term is zero. No product or
desired curvature expression occurs in this definition. -/
def ambientCurvature (P : SymmetricTrilinearForm E) (x u v w : E) : E :=
  ambientCovariantDerivative P u (ambientCovariantDerivative P v (fun _ => w)) x -
    ambientCovariantDerivative P v (ambientCovariantDerivative P u (fun _ => w)) x

/-- The actual constant-field curvature has its actual D-Gamma expression,
by proved differentiability and uniqueness rather than total-fderiv fallback. -/
theorem ambientCurvature_apply (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) (u v w : E) :
    ambientCurvature P x u v w =
      ambientGammaD1 P x u v w - ambientGammaD1 P x v u w +
        ambientGamma P x u (ambientGamma P x v w) -
          ambientGamma P x v (ambientGamma P x u w) := by
  have hΓ := hasFDerivAt_actual_ambientGamma P hx hp
  have hv := eval_const_hasFDerivAt (eval_const_hasFDerivAt hΓ v) w
  have hu := eval_const_hasFDerivAt (eval_const_hasFDerivAt hΓ u) w
  have f (a) : ambientCovariantDerivative P a (fun _ => w) = fun y => ambientGamma P y a w :=
    funext (ambientCovariantDerivative_const P a w)
  rw [ambientCurvature, f, f]
  simp [ambientCovariantDerivative, hv.fderiv, hu.fderiv, ContinuousLinearMap.flip_apply]
  abel

/-- The Hessian metric has Dg=2g(Gamma(.,.),.) at every positive metric point. -/
theorem ambientMetricD1_eq_two_Gamma (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) (u v w : E) :
    ambientMetricD1 P x u v w =
      2 * logHessianForm P x (ambientGamma P x u v) w := by
  have h := ambientGamma_koszul P x hp u v w
  rw [ambientKoszulTensor_eq_half P hx] at h
  simp [smul_eq_mul] at h
  linarith

/-- Differentiate actual Koszul pairing on a proved positive neighborhood.
All scalar/CLM derivatives have actual certificates. No inverse derivative
formula or prescribed fourth metric jet is assumed. -/
theorem ambientGammaD1_pairing (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) (u v w z : E) :
    logHessianForm P x (ambientGammaD1 P x u v w) z =
      (1 / 2 : ℝ) * ambientMetricD2 P x u v w z -
        ambientMetricD1 P x u (ambientGamma P x v w) z := by
  have hG := hasFDerivAt_actual_metric P hx
  have hΓ := eval_const_hasFDerivAt
    (eval_const_hasFDerivAt (hasFDerivAt_actual_ambientGamma P hx hp) v) w
  have hpair := eval_const_hasFDerivAt (hG.clm_apply hΓ) z
  have hjet := eval_const_hasFDerivAt (eval_const_hasFDerivAt
    (eval_const_hasFDerivAt (hasFDerivAt_actual_metricD1 P hx) v) w) z
  obtain ⟨U, hU, hxU, hgood⟩ :=
    exists_positive_definite_logHessian_neighborhood P x hx hp
  have hc : (fun y => logHessianForm P y (ambientGamma P y v w) z) =ᶠ[𝓝 x]
      (fun y => (1 / 2 : ℝ) * ambientMetricD1 P y v w z) :=
    Filter.eventually_of_mem (hU.mem_nhds hxU) (fun y hy => by
      linarith [ambientMetricD1_eq_two_Gamma P (hgood y hy).1 (hgood y hy).2.2 v w z])
  have hd := congrArg (fun L => L u)
    (hpair.unique ((hjet.const_smul (1 / 2 : ℝ)).congr_of_eventuallyEq hc))
  simp [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul] at hd
  linarith

/-- Actual Hessian curvature is the negative connection commutator at every
positive metric point. Symmetric fourth derivatives cancel, leaving the
inverse-raising terms with the manuscript's sign. -/
theorem ambientCurvature_eq_neg_Gamma_commutator (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) (u v w : E) :
    ambientCurvature P x u v w =
      -(ambientGamma P x u (ambientGamma P x v w) -
        ambientGamma P x v (ambientGamma P x u w)) := by
  apply injective_of_pos hp
  ext z
  rw [ambientCurvature_apply P hx hp]
  simp [map_sub, map_add]
  rw [ambientGammaD1_pairing P hx hp u v w z,
    ambientGammaD1_pairing P hx hp v u w z,
    ambientMetricD2_swap12 P hx u v w z,
    ambientMetricD1_eq_two_Gamma P hx hp u (ambientGamma P x v w) z,
    ambientMetricD1_eq_two_Gamma P hx hp v (ambientGamma P x u w) z]
  ring

/-- Original arbitrary-cubic full ambient tensor endpoint, before Jordan:
N(e)=1 and actual positivity alone give R_e=-[L_u,L_v], with all radial slots. -/
theorem ambientCurvature_at_one_eq_neg_product_commutator
    (P : SymmetricTrilinearForm E) (e : E) (he : diagonalCubic P.form e = 1)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u) (u v w : E) :
    ambientCurvature P e u v w =
      -(intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) u
          (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) v w) -
        intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) v
          (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) u w)) := by
  have h (a b) : ambientGamma P e a (ambientGamma P e b w) =
      intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) a
        (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) b w) := by
    rw [ambientGamma_at_one_eq_neg_product P e he hp b w, map_neg,
      ambientGamma_at_one_eq_neg_product P e he hp, neg_neg]
  rw [ambientCurvature_eq_neg_Gamma_commutator P (by rw [he]; norm_num) hp, h, h]

end
end AlbertGeometry.AmbientCurvatureProduct
