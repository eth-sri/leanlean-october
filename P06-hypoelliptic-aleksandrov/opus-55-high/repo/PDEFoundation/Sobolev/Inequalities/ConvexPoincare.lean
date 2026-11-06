module

public import PDEFoundation.Sobolev.Inequalities.Poincare
public import PDEFoundation.Sobolev.Inequalities.SmoothPoincareNorm
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Density

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

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

/-- The constant `2 ^ d` is a mean-zero Poincaré constant on every bounded
open convex domain, uniformly for all finite real exponents `p ≥ 1`. -/
theorem isUniformMeanZeroPoincareConstant_two_pow (d : ℕ) :
    IsUniformMeanZeroPoincareConstant d ((2 : ℝ) ^ d) := by
  refine ⟨by positivity, ?_⟩
  intro p hp U D hU hUDiameter hD hUPos hUTop u huMean
  have hpENNReal : 1 ≤ ENNReal.ofReal p := by
    simp_all
  have hpTop : ENNReal.ofReal p ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have hUNonempty  :=
    nonempty_of_measure_ne_zero hUPos.ne'
  obtain ⟨x0, r, hr, hball⟩ :=
    exists_metricClosedBall_subset_of_isOpenBoundedConvexDomain
      hU hUNonempty
  let ψ  :=
    fun n =>
      W1pFunction.convexApproxSmoothW1p
        hU hpENNReal u x0 hr n
  have hBound :
      ∀ n,
        eLpMeanNormOn U (ENNReal.ofReal p)
            (fun x =>
              (ψ n).toFun x -
                integralAverage U (ψ n).toFun) ≤
          ENNReal.ofReal ((2) ^ d * D) *
            euclideanFieldELpMeanNormOn U
              (ENNReal.ofReal p) (ψ n).grad := by
    intro n
    have hSmooth :
        ContDiff ℝ (⊤ : ℕ∞) (ψ n).toFun := by
      simpa only [ψ] using
        W1pFunction.contDiff_convexApproxSmoothW1p_toFun
          hU hpENNReal u x0 hr n
    have hPoincare :=
      eLpMeanNormOn_sub_integralAverage_le_two_pow_mul_of_contDiff
        hU hUDiameter hD hSmooth hp hUPos hUTop
    aesop
  have hLeft :
      Tendsto
        (fun n =>
          eLpMeanNormOn U (ENNReal.ofReal p)
            (fun x =>
              (ψ n).toFun x -
                integralAverage U (ψ n).toFun))
        atTop
        (𝓝
          (eLpMeanNormOn U (ENNReal.ofReal p)
            (fun x =>
              u.toFun x -
                integralAverage U u.toFun))) := by
    simpa only [ψ] using
      W1pFunction.tendsto_convexApproxSmoothW1p_centered_eLpMeanNorm
        hU hpENNReal hpTop u hball hr hUPos
  have hGradient :
      Tendsto
        (fun n =>
          euclideanFieldELpMeanNormOn U
            (ENNReal.ofReal p) (ψ n).grad)
        atTop
        (𝓝
          (euclideanFieldELpMeanNormOn U
            (ENNReal.ofReal p) u.grad)) := by
    simpa only [ψ, euclideanFieldELpMeanNormOn] using
      W1pFunction.tendsto_convexApproxSmoothW1p_grad_euclidean_eLpMeanNorm
        hU hpENNReal hpTop u hball hr hUPos
  have hRight :
      Tendsto
        _
        atTop
        (𝓝
          (ENNReal.ofReal ((2) ^ d * D) *
            euclideanFieldELpMeanNormOn U
              _ u.grad)) :=
    ENNReal.Tendsto.const_mul hGradient
      (Or.inr ENNReal.ofReal_ne_top)
  have hCentered :
      eLpMeanNormOn U _
          _ ≤
        ENNReal.ofReal _ *
          euclideanFieldELpMeanNormOn U
            _ u.grad :=
    le_of_tendsto_of_tendsto'
      hLeft hRight hBound
  have hAverage  :=
    integralAverage_eq_zero_of_meanZeroOn huMean
  simp_all

/-- Direct unnormalized mean-zero Poincaré inequality on an axis cube, with
its exact Euclidean diameter factor `sqrt d * L`. -/
theorem meanZeroPoincare_on_axisCube_unnormalized
    {d : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (z : Vec d) {L : ℝ} (hL : 0 < L)
    (u :
      W1pFunction (axisCube z L) (ENNReal.ofReal p))
    (huMean : MeanZeroOn (axisCube z L) u.toFun) :
    eLpNormOn (axisCube z L)
        (ENNReal.ofReal p) u.toFun ≤
      ENNReal.ofReal
          ((2 : ℝ) ^ d *
            (Real.sqrt d * L)) *
        euclideanFieldELpNormOn (axisCube z L)
          (ENNReal.ofReal p) u.grad :=
  (isUniformMeanZeroPoincareConstant_two_pow d).on_axisCube_unnormalized
    hp z hL u huMean

end PDE
