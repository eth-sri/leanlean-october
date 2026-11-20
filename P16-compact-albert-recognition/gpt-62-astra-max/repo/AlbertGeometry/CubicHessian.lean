module
public import Glennie.ObservationData
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Actual derivatives of the given cubic. Currying once turns the first two
product rules into operator identities: DN = 3C(x,x,-), D²N = 6C(x,-,-). -/
@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
open Filter
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (P : BasedCubic E)

def tri : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)).toContinuousLinearEquiv.toContinuousLinearMap.comp P.form.curryRight.curryLeft
@[simp] theorem tri_apply (x y z : E) : tri P x y z = P.form ![x,y,z] := by simp [tri]

theorem cubic_diag (x : E) : cubic P x = tri P x x x := by
  rw [tri_apply]; apply congrArg P.form; funext i; fin_cases i <;> rfl

@[fun_prop] theorem contDiff_cubic (n : ℕ∞ω) : ContDiff ℝ n (cubic P) :=
  P.form.contDiff.comp (ContinuousLinearMap.pi (fun _ : Fin 3 => ContinuousLinearMap.id ℝ E)).contDiff

theorem hasD_cubic (x : E) : HasFDerivAt (cubic P) (traceAt P x) x :=
  ((contDiff_cubic P 1).differentiable (by simp) x).hasFDerivAt

theorem trace_eq (x : E) : traceAt P x = (3 : ℝ) • tri P x x := by
  have h := (((tri P).hasFDerivAt.clm_apply (hasFDerivAt_id x)).clm_apply (hasFDerivAt_id x)).fderiv
  simp only [id_eq] at h
  change fderiv ℝ (cubic P) x = _; rw [funext (cubic_diag P),h]; ext y
  simp [tri_apply,P.swap12 y x x,P.swap23 x y x]; ring

theorem hasD_trace (x : E) : HasFDerivAt (traceAt P) ((6:ℝ) • tri P x) x := by
  simp_rw [funext (trace_eq P)]
  apply (((tri P).hasFDerivAt.clm_apply (hasFDerivAt_id x)).const_smul (3:ℝ)).congr_fderiv
  ext u v; simp [P.swap12 u x v]; ring

theorem trace_unit (e : E) (he : cubic P e = 1) : traceAt P e e = 3 := by
  rw [trace_eq]; change 3 * tri P e e e = _; rw [← cubic_diag,he]; ring

theorem rawPair_apply (e x y : E) : rawPair P e x y = traceAt P e x * traceAt P e y - 6 * tri P e x y := by
  change _ - fderiv ℝ (traceAt P) e x y = _; rw [(hasD_trace P e).fderiv]; rfl

theorem pos_near {x : E} (h : 0 < cubic P x) : ∀ᶠ y in 𝓝 x, 0 < cubic P y :=
  (hasD_cubic P x).continuousAt.eventually_const_lt h

theorem hasD_invN {x : E} (h : 0 < cubic P x) : HasFDerivAt (fun y => (cubic P y)⁻¹)
    ((-(cubic P x ^ 2)⁻¹) • traceAt P x) x := (hasDerivAt_inv h.ne').comp_hasFDerivAt x (hasD_cubic P x)

theorem metric_formula {x : E} (h : 0 < cubic P x) (v w : E) : metric P x v w =
    -2 * tri P x v w * (cubic P x)⁻¹ + 1/3 * (traceAt P x v * traceAt P x w * (cubic P x)⁻¹ * (cubic P x)⁻¹) := by
  have eq : (fun y => fderiv ℝ (fun z => Real.log (cubic P z)) y) =ᶠ[𝓝 x] fun y => (cubic P y)⁻¹ • traceAt P y :=
    (pos_near P h).mono fun y hy => ((hasD_cubic P y).log hy.ne').fderiv
  have H := (((hasD_invN P h).smul (hasD_trace P x)).congr_of_eventuallyEq eq).fderiv
  simp [metric,H,inv_pow]; ring

theorem raw_metric {e : E} (he : cubic P e = 1) (u v : E) : rawPair P e u v = 3 * metric P e u v := by
  rw [rawPair_apply,metric_formula P (by simp [he] : 0 < cubic P e),he]; ring

theorem metric_smooth {x : E} (h : 0 < cubic P x) : ContDiffAt ℝ ⊤ (metric P) x := by
  have h1 : ContDiffAt ℝ ⊤ (fderiv ℝ (fun y => Real.log (cubic P y))) x := ((contDiff_cubic P ⊤).contDiffAt.log h.ne').fderiv_right (by simp)
  exact (h1.fderiv_right (by simp)).const_smul _

theorem hasD_metric {x : E} (h : 0 < cubic P x) : HasFDerivAt (metric P) (ambientMetricD1 P x) x :=
  ((metric_smooth P h).differentiableAt (by simp)).hasFDerivAt

theorem evalD {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {f : X → Y →L[ℝ] Z} {D : X →L[ℝ] Y →L[ℝ] Z} {x : X}
    (hf : HasFDerivAt f D x) (u : Y) : HasFDerivAt (fun y => f y u) (D.flip u) x := by
  simpa using hf.clm_apply (hasFDerivAt_const u x)

/-- Differentiate the pointwise rational formula on the nonvanishing neighborhood.
The symmetry in all three directions will also simplify the Koszul tensor. -/
theorem metric_jet {x : E} (hx : 0 < cubic P x) (u v w : E) : ambientMetricD1 P x u v w =
    -2 * tri P u v w * (cubic P x)⁻¹ + 2 * (cubic P x)⁻¹^2 *
      (traceAt P x u * tri P x v w + traceAt P x v * tri P x u w + traceAt P x w * tri P x u v) -
      2/3 * (cubic P x)⁻¹^3 * traceAt P x u * traceAt P x v * traceAt P x w := by
  have hd := evalD (evalD (hasD_metric P hx) v) w
  have ha := evalD (evalD ((tri P).hasFDerivAt (x := x)) v) w
  have ht := hasD_trace P x; have hr := hasD_invN P hx
  have rhs := ((ha.mul hr).const_smul (-2:ℝ)).add (((((evalD ht v).mul (evalD ht w)).mul hr).mul hr).const_smul (1/3:ℝ))
  have hc := congrArg (fun L : E →L[ℝ] ℝ => L u) (hd.unique (rhs.congr_of_eventuallyEq
    ((pos_near P hx).mono fun y hy => by simp only [Pi.add_apply,Pi.mul_apply,Pi.smul_apply,smul_eq_mul,metric_formula P hy]; ring)))
  simp at hc; rw [hc]; simp only [tri_apply, ← inv_pow]; ring
end
end Glennie.SubmissionR04Intrinsic
