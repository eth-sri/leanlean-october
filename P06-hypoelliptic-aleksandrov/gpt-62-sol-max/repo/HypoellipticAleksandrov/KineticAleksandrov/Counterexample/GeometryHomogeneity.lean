module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.NormNum

/-! # Differentiating kinetic homogeneity -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter

/-- The continuous linear map realizing kinetic dilation. -/
def dilationLinearMap (d : ℕ) (r : ℝ) : XV d →L[ℝ] XV d :=
  (r ^ 3 • ContinuousLinearMap.fst ℝ (PDE.Vec d) (PDE.Vec d)).prod
    (r • ContinuousLinearMap.snd ℝ (PDE.Vec d) (PDE.Vec d))

section
variable {d : ℕ} (r : ℝ) (q : XV d)

/-- The linear dilation agrees with the literal coordinate dilation. -/
theorem dilationLinearMap_apply :
    dilationLinearMap d r q = dilate r q := rfl

/-- Kinetic dilation has its constant linear differential. -/
theorem hasFDerivAt_dilate :
    HasFDerivAt (dilate r : XV d → XV d) (dilationLinearMap d r) q :=
  (dilationLinearMap d r).hasFDerivAt

end

/-- Differentiating a local homogeneity relation in a direction of dilation weight `k`. -/
private theorem homogeneous_direction {d : ℕ} {H : XV d → ℝ} {alpha r k : ℝ}
    {q w : XV d} (hr : 0 < r)
    (hhom : (fun z => H (dilate r z)) =ᶠ[nhds q] fun z => Real.rpow r alpha * H z)
    (hq : DifferentiableAt ℝ H q) (hrq : DifferentiableAt ℝ H (dilate r q))
    (hw : dilate r w = Real.rpow r k • w) :
    fderiv ℝ H (dilate r q) w = Real.rpow r (alpha - k) * fderiv ℝ H q w := by
  have h := congrArg (fun L : XV d →L[ℝ] ℝ => L w) hhom.fderiv_eq
  rw [fderiv_fun_comp q hrq (hasFDerivAt_dilate r q).differentiableAt,
    fderiv_const_mul hq, (hasFDerivAt_dilate r q).fderiv] at h
  simp only [ContinuousLinearMap.comp_apply, dilationLinearMap_apply, hw, map_smul,
    smul_apply, smul_eq_mul] at h
  simp only [Real.rpow_eq_pow] at h ⊢
  rw [Real.rpow_sub hr, div_mul_eq_mul_div, eq_div_iff (Real.rpow_pos_of_pos hr _).ne']
  simpa only [mul_comm] using h

section
variable {d : ℕ} {H : XV d → ℝ} {alpha r : ℝ} {q : XV d} (w : PDE.Vec d) (hr : 0 < r)
  (hhom : (fun z => H (dilate r z)) =ᶠ[nhds q] fun z => Real.rpow r alpha * H z)
  (hq : DifferentiableAt ℝ H q) (hrq : DifferentiableAt ℝ H (dilate r q))
include hr hhom hq hrq

/-- The exact position weight also follows from a local homogeneity identity. -/
theorem homogeneous_position_direction :
    fderiv ℝ H (dilate r q) (w, 0) = Real.rpow r (alpha - 3) * fderiv ℝ H q (w, 0) := by
  apply homogeneous_direction hr hhom hq hrq
  simp [dilate, Prod.smul_mk, Real.rpow_eq_pow, Real.rpow_ofNat]

/-- The exact velocity weight also follows from a local homogeneity identity. -/
theorem homogeneous_velocity_direction :
    fderiv ℝ H (dilate r q) (0, w) = Real.rpow r (alpha - 1) * fderiv ℝ H q (0, w) := by
  apply homogeneous_direction hr hhom hq hrq
  simp [dilate, Prod.smul_mk, Real.rpow_eq_pow]

end

section
variable {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ) (hr : 0 < r)
  (hhom : ∀ q, H (dilate r q) = Real.rpow r alpha * H q) (q : XV d) (hq : DifferentiableAt ℝ H q)
  (hrq : DifferentiableAt ℝ H (dilate r q)) (i : Fin d)
include hr hhom hq hrq

/-- A position derivative of a homogeneous profile has degree alpha minus three. -/
theorem homogeneous_dx_identity :
    dx H (dilate r q) i = Real.rpow r (alpha - 3) * dx H q i := homogeneous_position_direction (Pi.single i 1) hr (Eventually.of_forall hhom) hq hrq

/-- A velocity derivative of a homogeneous profile has degree alpha minus one. -/
theorem homogeneous_dv_identity :
    dv H (dilate r q) i = Real.rpow r (alpha - 1) * dv H q i := homogeneous_velocity_direction (Pi.single i 1) hr (Eventually.of_forall hhom) hq hrq

end

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
