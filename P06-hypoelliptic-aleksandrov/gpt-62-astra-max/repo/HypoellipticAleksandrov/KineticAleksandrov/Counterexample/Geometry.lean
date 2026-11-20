module

public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import PDEFoundation.Geometry.EuclideanBall.Topology
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Ring

/-!
# Literal stationary geometry for Appendix C

The gauge uses the Euclidean squared norms, independently of the native supremum norm.
The derivative selectors below are total Frechet derivatives on the native product.
Their identification with weak jets on axes is a separate analytic step.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- Native position--velocity coordinates. -/
abbrev XV (d : ℕ) := PDE.Vec d × PDE.Vec d

section
variable {d : ℕ} (A : XV d → PDE.Mat d) (r : ℝ) (H : XV d → ℝ) (q : XV d)

include q in
/-- The Euclidean kinetic gauge in Appendix C. -/
noncomputable def rho : ℝ :=
  Real.rpow (PDE.vecNormSq q.1 + (PDE.vecNormSq q.2) ^ 3) (1 / 6)

include r q in
/-- Kinetic dilation of position and velocity. -/
def dilate : XV d := (r ^ 3 • q.1, r • q.2)

include H q in
/-- Position derivative selectors on the native product. -/
noncomputable def dx : PDE.Vec d :=
  fun i => fderiv ℝ H q (Pi.single i 1, 0)

include H q in
/-- Velocity derivative selectors on the native product. -/
noncomputable def dv : PDE.Vec d :=
  fun i => fderiv ℝ H q (0, Pi.single i 1)

include H q in
/-- Velocity Hessian selectors, indexed as the derivative of component `k` along `i`. -/
noncomputable def dvv : PDE.Mat d :=
  fun i k => fderiv ℝ (fun z => dv H z k) q (0, Pi.single i 1)

include A H q in
/-- Stationary transport minus velocity diffusion. -/
noncomputable def statOp : ℝ :=
  PDE.vecDot q.2 (dx H q) - matrixContraction (A q) (dvv H q)

/-- The kinetic gauge is nonnegative. -/
theorem rho_nonneg : 0 ≤ rho q :=
  Real.rpow_nonneg
    (add_nonneg (PDE.vecNormSq_nonneg _) (pow_nonneg (PDE.vecNormSq_nonneg _) _)) _

end

/-- The kinetic gauge vanishes at the origin. -/
@[simp] theorem rho_zero (d : ℕ) : rho (0 : XV d) = 0 := by
  simp [rho, PDE.vecNormSq, PDE.vecDot]

section
variable {d : ℕ} (r : ℝ) (hr : 0 < r) (q : XV d)

/-- Unit dilation preserves both coordinates. -/
@[simp] theorem dilate_one : dilate 1 q = q := by
  simp [dilate]

/-- Every dilation preserves the origin. -/
@[simp] theorem dilate_zero : dilate r (0 : XV d) = 0 := by
  simp [dilate]

/-- Kinetic dilations compose multiplicatively. -/
theorem dilate_mul (r s : ℝ) (q : XV d) :
    dilate r (dilate s q) = dilate (r * s) q := by
  simp only [dilate, smul_smul, mul_pow]

/-- The sixth power inside the gauge has kinetic degree six. -/
theorem gauge_polynomial_dilate :
    PDE.vecNormSq (dilate r q).1 + (PDE.vecNormSq (dilate r q).2) ^ 3 =
      r ^ 6 * (PDE.vecNormSq q.1 + (PDE.vecNormSq q.2) ^ 3) := by
  simp only [dilate, PDE.vecNormSq_smul]
  ring

include hr in
/-- The gauge scales linearly under positive kinetic dilations. -/
theorem rho_dilate :
    rho (dilate r q) = r * rho q := by
  unfold rho
  simp only [Real.rpow_eq_pow]
  rw [gauge_polynomial_dilate]
  rw [Real.mul_rpow (pow_nonneg hr.le _) (z := (1 / 6))
    (show 0 ≤ PDE.vecNormSq q.1 + PDE.vecNormSq q.2 ^ 3 from
      add_nonneg (PDE.vecNormSq_nonneg _) (pow_nonneg (PDE.vecNormSq_nonneg _) _))]
  have hpower : (r ^ 6) ^ (1 / 6 : ℝ) = r := by
    rw [← Real.rpow_natCast_mul hr.le]
    norm_num
  rw [hpower]

end

/-- The gauge is continuous also at its unique singular point. -/
theorem continuous_rho (d : ℕ) : Continuous (rho (d := d)) := by
  exact (Real.continuous_rpow_const (by norm_num : 0 ≤ (1 / 6 : ℝ))).comp
    ((PDE.continuous_vecNormSq.comp continuous_fst).add
      ((PDE.continuous_vecNormSq.comp continuous_snd).pow 3))

/-- The gauge vanishes only at the origin. -/
theorem rho_eq_zero_iff {d : ℕ} (q : XV d) : rho q = 0 ↔ q = 0 := by
  have hx := PDE.vecNormSq_nonneg q.1
  have hv3 : 0 ≤ PDE.vecNormSq q.2 ^ 3 := pow_nonneg (PDE.vecNormSq_nonneg q.2) _
  rw [rho, Real.rpow_eq_pow, Real.rpow_eq_zero (add_nonneg hx hv3) (by norm_num)]
  constructor
  · intro h
    have hx0 := le_antisymm (by linarith only [h, hv3]) hx
    have hv0 : PDE.vecNormSq q.2 = 0 := by
      grind
    exact Prod.ext (PDE.vecNormSq_eq_zero hx0) (PDE.vecNormSq_eq_zero hv0)
  simp_all [PDE.vecNormSq, PDE.vecDot]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
