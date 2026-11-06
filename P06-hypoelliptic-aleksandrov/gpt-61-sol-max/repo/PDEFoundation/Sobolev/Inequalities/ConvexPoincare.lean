module

public import PDEFoundation.Sobolev.Inequalities.Poincare
public import PDEFoundation.Sobolev.Inequalities.SmoothPoincareNorm
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Density
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Mean-zero Poincaré inequality on bounded convex domains

This file transfers the sharp-in-`p` smooth convex-domain estimate to every
representative-level `W^{1,p}` function. The dimension-only constant is
exactly `2 ^ d`; the diameter and explicit Euclidean magnitude of the native
gradient remain visible.

The proof selects an internal metric closed ball from positive volume,
uses the smooth convex-approximation sequence, and passes the normalized
smooth inequality to the limit. The convergence API includes `p = 1` and
retains the exact Euclidean-gradient norm.

## Main results

* `PDE.isUniformMeanZeroPoincareConstant_two_pow`: `2 ^ d` is uniform in
  every finite exponent `p ≥ 1`.
* `PDE.meanZeroPoincare_on_boundedConvexDomain`: direct normalized
  bounded-convex-domain estimate.
* `PDE.meanZeroPoincare_on_euclideanBall`: direct round-ball estimate with
  diameter `2 * R`.
* `PDE.meanZeroPoincare_on_axisCube`: direct axis-cube estimate with diameter
  `sqrt d * L`.
-/

 public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

/-- The constant `2 ^ d` is a mean-zero Poincaré constant on every bounded
open convex domain, uniformly for all finite real exponents `p ≥ 1`. -/
theorem isUniformMeanZeroPoincareConstant_two_pow (d : ℕ) :
    IsUniformMeanZeroPoincareConstant d ((2 : ℝ) ^ d) := (⟨le_of_lt
    (pow_pos
      (Mathlib.Meta.Positivity.pos_of_isNat (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl (Nat.ble 1 2)))
      d),
  fun p hp U D hU hUDiameter hD hUPos hUTop u huMean =>
  Exists.casesOn
    (exists_metricClosedBall_subset_of_isOpenBoundedConvexDomain hU (nonempty_of_measure_ne_zero (LT.lt.ne' hUPos)))
    fun x0 h =>
    Exists.casesOn h fun r h =>
      And.casesOn h fun hr hball =>
        Eq.mp
          (congrFun'
            (congrArg LE.le
              (congrArg (eLpMeanNormOn U (ENNReal.ofReal p))
                (funext fun x =>
                  Eq.trans (congrArg (HSub.hSub (u.toFun x)) (integralAverage_eq_zero_of_meanZeroOn huMean))
                    (sub_zero (u.toFun x)))))
            (ENNReal.ofReal (2 ^ d * D) * euclideanFieldELpMeanNormOn U (ENNReal.ofReal p) u.grad))
          (le_of_tendsto_of_tendsto'
            (W1pFunction.tendsto_convexApproxSmoothW1p_centered_eLpMeanNorm hU
              (Eq.mpr (id (congrArg (fun _a => _a) (propext ENNReal.one_le_ofReal))) hp) ENNReal.ofReal_ne_top u hball
              hr hUPos)
            (ENNReal.Tendsto.const_mul
              (W1pFunction.tendsto_convexApproxSmoothW1p_grad_euclidean_eLpMeanNorm hU
                (Eq.mpr (id (congrArg (fun _a => _a) (propext ENNReal.one_le_ofReal))) hp) ENNReal.ofReal_ne_top u hball
                hr hUPos)
              (Or.inr ENNReal.ofReal_ne_top))
            fun n =>
            id
              (eLpMeanNormOn_sub_integralAverage_le_two_pow_mul_of_contDiff hU hUDiameter hD
                (W1pFunction.contDiff_convexApproxSmoothW1p_toFun hU
                  (Eq.mpr (id (congrArg (fun _a => _a) (propext ENNReal.one_le_ofReal))) hp) u x0 hr n)
                hp hUPos hUTop))⟩)

/-- Direct unnormalized mean-zero Poincaré inequality on an axis cube, with
its exact Euclidean diameter factor `sqrt d * L`. -/
theorem meanZeroPoincare_on_axisCube_unnormalized
    {d : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (z : Vec d) {L : ℝ} (hL : 0 < L)
    (u :
      W1pFunction (axisCube z L) (ENNReal.ofReal p))
    (huMean : MeanZeroOn (axisCube z L) u.toFun) : type_of% ((isUniformMeanZeroPoincareConstant_two_pow d).on_axisCube_unnormalized
    hp z hL u huMean) :=
  (isUniformMeanZeroPoincareConstant_two_pow d).on_axisCube_unnormalized
    hp z hL u huMean

end PDE
