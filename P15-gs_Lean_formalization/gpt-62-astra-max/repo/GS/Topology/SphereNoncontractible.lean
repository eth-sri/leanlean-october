module
public import GS.Topology.Jacobian
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.Topology.Homotopy.Contractible
@[expose] public section

/-! A nullhomotopy extends the identity on the unit sphere continuously across
the origin. Smooth its displacement relative to the fixed points and normalize.
The resulting map fixes the sphere, yet its Jacobian vanishes everywhere.
This contradicts the signed-volume identity. -/
noncomputable section
open Set Metric MeasureTheory ContinuousMap Filter
open scoped Topology RealInnerProductSpace
namespace GS.Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local notation "S" => sphere (0:E) 1

private lemma sphere_jacobian {g : E → E} (hg : ContDiff ℝ 1 g) (h : ∀ x, ‖g x‖ = 1) (x : E) :
    (fderiv ℝ g x).det = 0 := by
  by_contra hn
  obtain ⟨v,hv⟩ := (LinearMap.equivOfIsUnitDet (f := (fderiv ℝ g x).toLinearMap) (isUnit_iff_ne_zero.2 hn)).surjective (g x)
  simp only [LinearMap.equivOfIsUnitDet_apply,ContinuousLinearMap.coe_coe] at hv
  have d := (hg.differentiable one_ne_zero x).hasFDerivAt.norm_sq
  simp only [h,one_pow] at d
  have e := DFunLike.congr_fun (d.unique (hasFDerivAt_const _ _)) v
  simp [hv,real_inner_self_eq_norm_sq,h] at e

/-- A map which is the identity on the sphere must have a zero. -/
lemma sphere_zero {f : E → E} (hf : Continuous f) (fix : ∀ x, ‖x‖ = 1 → f x = x) (hn : ∀ x, f x ≠ 0) : False := by
  obtain ⟨p,hp,near,supp⟩ := (hf.sub continuous_id).exists_contDiff_approx 1 hf.norm (fun x => norm_pos_iff.mpr (hn x))
  let a x := x + p x
  have ne (x : E) : a x ≠ 0 := by
    have d := near x; change dist (p x) (f x - x) < ‖f x‖ at d
    rw [dist_eq_norm,show p x - (f x-x) = a x - f x by dsimp [a]; abel] at d
    intro e; simp [e] at d
  have ha : ContDiff ℝ 1 a := contDiff_id.add hp
  let g x := ‖a x‖⁻¹ • a x
  have hg : ContDiff ℝ 1 g := ((ha.norm ℝ ne).inv fun x => norm_ne_zero_iff.mpr (ne x)).smul ha
  have unit x : ‖g x‖ = 1 := by simp [g,norm_smul,norm_ne_zero_iff.mpr (ne x)]
  have fixed (x) (hx : ‖x‖ = 1) : g x = x := by
    have hp0 : p x = 0 := by by_contra he; exact supp he (by simp [fix _ hx])
    simp [g,a,hp0,hx]
  borelize E
  let μ : Measure E := .addHaar
  have vol := GS.Jacobian.signed_volume μ g hg fixed
  have hpos : 0 < μ.real (closedBall (0:E) 1) := ENNReal.toReal_pos (measure_closedBall_pos μ _ zero_lt_one).ne' measure_closedBall_lt_top.ne
  simp only [sphere_jacobian hg unit,integral_zero] at vol
  linarith
end GS.Topology
