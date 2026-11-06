/-
Actual curvature is the commutator of the genuine
ambient covariant derivatives on constant affine fields (their bracket is zero).
The derivative-coefficient formula is proved with actual derivative certificates;
the negative multiplication commutator is then a theorem, never the definition.
Arbitrary positive based cubics, all ambient/radial slots, before Jordan.
This does not redefine or assume an ambient/level-chart curvature identification.
-/
module
public import AlbertGeometry.LinearSimp

public import AlbertGeometry.AmbientLeviCivitaProduct

@[expose] public section
namespace AlbertGeometry.AmbientCurvatureProduct
noncomputable section
open AlbertGeometry.Cubic
open AlbertGeometry.BasedNormDerivativeTransport
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso
open AlbertGeometry.BasedNormAdjointTransport
open AlbertGeometry.AmbientLeviCivitaProduct
open scoped ContDiff Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (P : SymmetricTrilinearForm E)
  [CompleteSpace E] [FiniteDimensional ℝ E]

-- Canonical local operator norms only; no native Albert/V instance is installed.
real_operator_norms dualNorm dualSpace E ℝ

real_operator_norms bilinearNorm bilinearSpace E (E →L[ℝ] ℝ)

real_operator_norms trilinearNorm trilinearSpace E (E →L[ℝ] E →L[ℝ] ℝ)

real_operator_norms endNorm endSpace E E

real_operator_norms vectorBilinearNorm vectorBilinearSpace E (E →L[ℝ] E)

/-- Literal second derivative of the actual varying ambient metric. -/
def ambientMetricD2  (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (ambientMetricD1 P) x

theorem hasFDerivAt_actual_metricD1  {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    HasFDerivAt (ambientMetricD1 P) (ambientMetricD2 P x) x := by
  have hD1 : ContDiffAt ℝ ⊤ (ambientMetricD1 P) x :=
    (contDiffAt_actual_metric P hx).fderiv_right (by simp)
  exact (hD1.differentiableAt (by simp)).hasFDerivAt

/-- Fourth-derivative cancellation is an actual Schwarz theorem for g. -/
theorem ambientMetricD2_swap12  {x : E}
    (hx : 0 < diagonalCubic P.form x) (u v w z : E) :
    ambientMetricD2 P x u v w z = ambientMetricD2 P x v u w z := by
  have h := (contDiffAt_actual_metric P hx).isSymmSndFDerivAt le_top
  have hs := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L w z) (h.eq u v)
  change fderiv ℝ (fderiv ℝ (logHessianForm P)) x u v w z =
    fderiv ℝ (fderiv ℝ (logHessianForm P)) x v u w z
  exact hs

/-- The genuine derivative of the smooth actual connection coefficient. -/
def ambientGammaD1  (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] E := fderiv ℝ (ambientGamma P) x

variable  {x : E}
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u)

include P x hx hp in
theorem hasFDerivAt_actual_ambientGamma  :
    HasFDerivAt (ambientGamma P) (ambientGammaD1 P x) x :=
  ((contDiffAt_ambientGamma P hx hp).differentiableAt (by simp)).hasFDerivAt

/-- The actual connection on a field in a constant affine direction. Its
coefficient has the smooth torsion/metric/uniqueness laws in the imported leaf. -/
def ambientCovariantDerivative  (u : E)
    (Y : E → E) (x : E) : E := fderiv ℝ Y x u + ambientGamma P x u (Y x)

theorem ambientCovariantDerivative_const  (u w x : E) :
    ambientCovariantDerivative P u (fun _ : E => w) x = ambientGamma P x u w := by
  simp only [ambientCovariantDerivative, fderiv_const_apply,
    ContinuousLinearMap.zero_apply, zero_add]

/-- Actual covariant-derivative commutator on constant affine fields. Those
direction fields commute, so their Lie-bracket term is zero. No product or
desired curvature expression occurs in this definition. -/
def ambientCurvature  (x u v w : E) : E :=
  ambientCovariantDerivative P u (ambientCovariantDerivative P v (fun _ : E => w)) x -
    ambientCovariantDerivative P v (ambientCovariantDerivative P u (fun _ : E => w)) x

include P x hx hp in
/-- The actual constant-field curvature has its actual D-Gamma expression,
by proved differentiability and uniqueness rather than total-fderiv fallback. -/
theorem ambientCurvature_apply  (u v w : E) :
    ambientCurvature P x u v w =
      ambientGammaD1 P x u v w - ambientGammaD1 P x v u w +
        ambientGamma P x u (ambientGamma P x v w) -
          ambientGamma P x v (ambientGamma P x u w) := by
  have hΓ := hasFDerivAt_actual_ambientGamma P hx hp
  have hv := eval_const_hasFDerivAt (eval_const_hasFDerivAt hΓ v) w
  have hu := eval_const_hasFDerivAt (eval_const_hasFDerivAt hΓ u) w
  have fv
                                      :=
    funext (fun y => ambientCovariantDerivative_const P v w y)
  have fu
                                      :=
    funext (fun y => ambientCovariantDerivative_const P u w y)
  rw [ambientCurvature, fv, fu]
  simp only [ambientCovariantDerivative, hv.fderiv, hu.fderiv,
    ContinuousLinearMap.flip_apply]
  simp only [sub_eq_add_neg, neg_add, add_assoc, add_left_comm, add_comm]

include P x hx hp in
/-- The Hessian metric has Dg=2g(Gamma(.,.),.) at every positive metric point. -/
theorem ambientMetricD1_eq_two_Gamma  (u v w : E) :
    ambientMetricD1 P x u v w =
      2 * logHessianForm P x (ambientGamma P x u v) w := by
  have h := ambientGamma_koszul P x (actual_metric_dual_isInvertible P x hp) u v w
  rw [ambientKoszulTensor_eq_half P hx] at h
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at h
  linarith

include P x hx hp in
/-- Differentiate actual Koszul pairing on a proved positive neighborhood.
All scalar/CLM derivatives have actual certificates. No inverse derivative
formula or prescribed fourth metric jet is assumed. -/
theorem ambientGammaD1_pairing  (u v w z : E) :
    logHessianForm P x (ambientGammaD1 P x u v w) z =
      (1 / 2 : ℝ) * ambientMetricD2 P x u v w z -
        ambientMetricD1 P x u (ambientGamma P x v w) z := by
  have hG := hasFDerivAt_actual_metric P hx
  have hΓ := eval_const_hasFDerivAt
    (eval_const_hasFDerivAt (hasFDerivAt_actual_ambientGamma P hx hp) v) w
  have hpair := eval_const_hasFDerivAt (hG.clm_apply hΓ) z
  have hjet := eval_const_hasFDerivAt (eval_const_hasFDerivAt
    (eval_const_hasFDerivAt (hasFDerivAt_actual_metricD1 P hx) v) w) z
  have hnear := (contDiffAt_actual_metric P hx).continuousAt.eventually
    (actual_metric_dual_isInvertible P x hp).eventually_nhds
  have hc := ((eventually_positive P hx).and hnear).mono (fun y hy => by
    change logHessianForm P y (ambientGamma P y v w) z =
      (1 / 2 : ℝ) * ambientMetricD1 P y v w z
    rw [ambientGamma_koszul P y hy.2, ambientKoszulTensor_eq_half P hy.1]
    rfl)
  have hd := congrArg (fun L : E →L[ℝ] ℝ => L u)
    (hpair.unique ((hjet.const_smul (1 / 2 : ℝ)).congr_of_eventuallyEq hc))
  simp only [clm_eval] at hd
  linarith

include P x hx hp in
/-- Actual Hessian curvature is the negative connection commutator at every
positive metric point. Symmetric fourth derivatives cancel, leaving the
inverse-raising terms with the manuscript's sign. -/
theorem ambientCurvature_eq_neg_Gamma_commutator  (u v w : E) :
    ambientCurvature P x u v w =
      -(ambientGamma P x u (ambientGamma P x v w) -
        ambientGamma P x v (ambientGamma P x u w)) := by
  apply actual_metric_dual_injective P x hp
  ext z
  rw [ambientCurvature_apply P hx hp]
  simp only [clm_eval, map_neg, ContinuousLinearMap.neg_apply]
  rw [ambientGammaD1_pairing P hx hp u v w z,
    ambientGammaD1_pairing P hx hp v u w z,
    ambientMetricD2_swap12 P hx u v w z,
    ambientMetricD1_eq_two_Gamma P hx hp u (ambientGamma P x v w) z,
    ambientMetricD1_eq_two_Gamma P hx hp v (ambientGamma P x u w) z]
  ring

/-- Original arbitrary-cubic full ambient tensor endpoint, before Jordan:
N(e)=1 and actual positivity alone give R_e=-[L_u,L_v], with all radial slots. -/
theorem ambientCurvature_at_one_eq_neg_product_commutator
     (e : E) (he : diagonalCubic P.form e = 1)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u) (u v w : E) :
    ambientCurvature P e u v w =
      -(intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) u
          (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) v w) -
        intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) v
          (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) u w)) := by
  have hx : 0 < diagonalCubic P.form e := by rw [he]; norm_num
  rw [ambientCurvature_eq_neg_Gamma_commutator P hx hp]
  have hleft : ambientGamma P e u (ambientGamma P e v w) =
      intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) u
        (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) v w) := by
    rw [ambientGamma_at_one_eq_neg_product P e he hp v w, map_neg,
      ambientGamma_at_one_eq_neg_product P e he hp, neg_neg]
  have hright : ambientGamma P e v (ambientGamma P e u w) =
      intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) v
        (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) u w) := by
    rw [ambientGamma_at_one_eq_neg_product P e he hp u w, map_neg,
      ambientGamma_at_one_eq_neg_product P e he hp, neg_neg]
  rw [hleft, hright]


end
end AlbertGeometry.AmbientCurvatureProduct
