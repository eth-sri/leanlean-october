module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarPieces
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
import Mathlib.Tactic

/-!
# The reflected scalar profile

The definitions are literal Appendix C formulae. Reflection is proved on the native
carrier. No continuity, equation, or weak-derivative claim is hidden in a definition.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/- The scalar autonomous diffusivity, with value one on both axes. -/
def aLambda (Lam x v : ℝ) : ℝ := if x * v < 0 then Lam else 1

/- The common velocity-axis trace selected by the matching equation. -/
def scalarTrace (gamma : ScalarGamma) (Lam v : ℝ) : ℝ :=
  Real.rpow (9 * Lam) (-gamma.1) * Real.rpow |v| (3 * gamma.1)

/- The source ansatz on the positive position half-plane. -/
def scalarAnsatz (gamma : ScalarGamma) (Lam x v : ℝ) : ℝ :=
  Real.rpow x gamma.1 * F gamma Lam (-v / Real.rpow x (1 / 3))

/- The scalar source profile, reflected on the negative position half-plane. -/
def scalarProfile (gamma : ScalarGamma) (Lam : ℝ) (q : XV 1) : ℝ :=
  if 0 < q.1 0 then scalarAnsatz gamma Lam (q.1 0) (q.2 0)
  else if q.1 0 < 0 then scalarAnsatz gamma Lam (-q.1 0) (-q.2 0)
  else scalarTrace gamma Lam (q.2 0)

/- Simultaneous position and velocity reflection preserves the diffusivity. -/
theorem aLambda_reflect (Lam x v : ℝ) : aLambda Lam (-x) (-v) = aLambda Lam x v := by
  simp only [aLambda, neg_mul_neg]

/- The source's common trace is invariant under velocity reflection. -/
@[simp] theorem scalarTrace_neg (gamma : ScalarGamma) (Lam v : ℝ) :
    scalarTrace gamma Lam (-v) = scalarTrace gamma Lam v := by
  simp only [scalarTrace, abs_neg]

/- The source profile vanishes at the origin. -/
@[simp] theorem scalarProfile_zero (gamma : ScalarGamma) (Lam : ℝ) :
    scalarProfile gamma Lam 0 = 0 := by
  have he : (3 * gamma.1 : ℝ) ≠ 0 := (mul_pos (by norm_num) gamma.2.1).ne'
  simp [scalarProfile, scalarTrace, Real.zero_rpow he]

/- The axis trace scales with the source degree `alpha = 3 gamma`. -/
theorem scalarAnsatz_dilate (gamma : ScalarGamma) (Lam r x v : ℝ)
    (hr : 0 < r) (hx : 0 < x) :
    scalarAnsatz gamma Lam (r ^ 3 * x) (r * v) =
      Real.rpow r (3 * gamma.1) * scalarAnsatz gamma Lam x v := by
  have hc : (r ^ 3) ^ (1 / 3 : ℝ) = r := by
    rw [← Real.rpow_natCast r 3, ← Real.rpow_mul hr.le]
    norm_num
  have he : -(r * v) / (r * x ^ (1 / 3 : ℝ)) = -v / x ^ (1 / 3 : ℝ) := by
    field_simp
  unfold scalarAnsatz
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (pow_nonneg hr.le _) hx.le,
    Real.mul_rpow (pow_nonneg hr.le _) hx.le, hc, he,
    ← Real.rpow_natCast r 3, ← Real.rpow_mul hr.le]
  norm_num
  ring

/- The full native scalar profile has exactly the source kinetic homogeneity. -/
theorem scalarProfile_homogeneous (gamma : ScalarGamma) (Lam r : ℝ) (hr : 0 < r)
    (q : XV 1) : scalarProfile gamma Lam (dilate r q) =
      Real.rpow r (3 * gamma.1) * scalarProfile gamma Lam q := by
  have h3 := pow_pos hr 3
  simp only [scalarProfile, dilate, Pi.smul_apply, smul_eq_mul]
  rcases lt_trichotomy (q.1 0) 0 with hx | hx | hx
  · simp only [not_lt.mpr hx.le, hx, ↓reduceIte,
      mul_neg_of_pos_of_neg h3 hx, not_lt.mpr (mul_neg_of_pos_of_neg h3 hx).le]
    rw [show -(r ^ 3 * q.1 0) = r ^ 3 * (-q.1 0) by ring,
      show -(r * q.2 0) = r * (-q.2 0) by ring]
    exact scalarAnsatz_dilate gamma Lam r _ _ hr (neg_pos.mpr hx)
  · simp only [hx, mul_zero, lt_self_iff_false, ↓reduceIte]
    simp only [scalarTrace, Real.rpow_eq_pow]
    rw [abs_mul, abs_of_pos hr, Real.mul_rpow hr.le (abs_nonneg _)]
    ring
  · simp only [hx, ↓reduceIte, mul_pos h3 hx]
    exact scalarAnsatz_dilate gamma Lam r _ _ hr hx

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
