module

public import HypoellipticAleksandrov.Parabolic.Operator
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Separation.Regular

/-!
# Compact cutoff gluing for local parabolic data

This module turns scalar and coefficient data given on an open neighbourhood
of a compact set into literal global data by multiplication with a smooth
cutoff. It also records the pointwise locality of the parabolic operator. No
ellipticity or parabolic estimate is asserted here.
-/

@[expose] public section

open Filter Function Set
open scoped ContDiff Manifold Topology

namespace HypoellipticAleksandrov.Parabolic

/-- A smooth cutoff which is identically one in a neighbourhood of the compact
set `K` and has topological support inside the open set `U`. -/
theorem exists_smooth_cutoff_tsupport_subset
    {d : ℕ} {K U : HypoellipticAleksandrov.Parabolic.Region d}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ b : HypoellipticAleksandrov.Parabolic.ScalarField d,
      ContDiff ℝ ∞ b ∧
      (∀ᶠ z in 𝓝ˢ K, b z = 1) ∧
      tsupport b ⊆ U := by
  obtain ⟨L, _hLcompact, hLclosed, hKinterior, hLU⟩ :=
    exists_compact_closed_between hK hU hKU
  obtain ⟨b, hbOne, hbZero, _hbRange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (I := 𝓘(ℝ, TimeVelocity d)) hK.isClosed
      (hKinterior)
  refine ⟨b, b.contMDiff.contDiff, hbOne, ?_⟩

  change closure (support (b : HypoellipticAleksandrov.Parabolic.ScalarField d)) ⊆ U
  exact (closure_minimal (by
      intro z hz
      by_contra hzL
      exact (mem_support.mp hz) (hbZero z hzL)) hLclosed).trans hLU

variable {d : ℕ}

variable {U : HypoellipticAleksandrov.Parabolic.Region d}

/-- Multiplication by a globally smooth cutoff whose topological support lies
inside `U` turns a `C²` function on the open set `U` into a literal globally
`C²` function. -/
theorem contDiff_cutoff_mul_of_tsupport_subset
      {b q : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hU : IsOpen U) (hb : ContDiff ℝ 2 b) (hbU : tsupport b ⊆ U)
    (hq : ContDiffOn ℝ 2 q U) :
    ContDiff ℝ 2 (fun z => b z * q z) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : z ∈ U
  · exact hb.contDiffAt.mul (hq.contDiffAt (hU.mem_nhds hz))
  · have hzSupport  := fun hzSupport => hz (hbU hzSupport)

    have hconst : ContDiffAt ℝ 2 (fun _ : TimeVelocity d => (0 : ℝ)) z :=
      contDiffAt_const
    apply hconst.congr_of_eventuallyEq
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hzSupport)] with y hy
    simp only [Pi.zero_apply] at hy
    simp only [hy, zero_mul]

/-- Multiplication by a globally smooth cutoff whose topological support lies
inside `U` turns a continuous scalar function on `U` into a literal globally
continuous scalar function. -/
theorem continuous_cutoff_mul_of_tsupport_subset
      {b F : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hU : IsOpen U) (hb : ContDiff ℝ 2 b) (hbU : tsupport b ⊆ U)
    (hF : ContinuousOn F U) :
    Continuous (fun z => b z * F z) := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  by_cases hz : z ∈ U
  · exact hb.continuous.continuousAt.mul (hF.continuousAt (hU.mem_nhds hz))
  · have hzSupport  := fun hzSupport => hz (hbU hzSupport)

    have hconst : ContinuousAt (fun _ : TimeVelocity d => (0 : ℝ)) z :=
      continuousAt_const
    apply hconst.congr_of_eventuallyEq
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hzSupport)] with y hy
    simp only [Pi.zero_apply] at hy
    simp only [hy, zero_mul]

variable (b : HypoellipticAleksandrov.Parabolic.ScalarField d) (B : CoefficientField d) (lam : ℝ)

/-- The literal curried coefficient field obtained by gluing `B` to the
constant field `lam I` with the cutoff `b`. -/
def cutoffExtendCoefficient
     :
    CoefficientField d :=
  fun t v => b (t, v) • B t v + (1 - b (t, v)) • (lam • (1 : PDE.Mat d))

/-- Evaluation of a cutoff-glued coefficient field. -/
@[simp] theorem coefficientAt_cutoffExtendCoefficient

    (z : TimeVelocity d) :
    coefficientAt (cutoffExtendCoefficient b B lam) z =
      b z • coefficientAt B z + (1 - b z) • (lam • (1 : PDE.Mat d)) :=
  rfl

/-- The cutoff-glued coefficient field is globally continuous when the
original coefficient is continuous only on the open set containing the
cutoff's topological support. -/
theorem continuous_coefficientAt_cutoffExtendCoefficient
     {U : HypoellipticAleksandrov.Parabolic.Region d} {b : HypoellipticAleksandrov.Parabolic.ScalarField d}
    {B : CoefficientField d} {lam : ℝ}
    (hU : IsOpen U) (hb : ContDiff ℝ 2 b) (hbU : tsupport b ⊆ U)
    (hB : ContinuousOn (coefficientAt B) U) :
    Continuous (coefficientAt (cutoffExtendCoefficient b B lam)) := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  by_cases hz : z ∈ U
  · have heq : coefficientAt (cutoffExtendCoefficient b B lam) =
        b • coefficientAt B + ((fun _ => 1) - b) • (fun _ => lam • (1 : PDE.Mat d)) := by
      funext y
      exact coefficientAt_cutoffExtendCoefficient b B lam y
    rw [heq]
    exact (hb.continuous.continuousAt.smul (hB.continuousAt (hU.mem_nhds hz))).add
        ((continuousAt_const.sub hb.continuous.continuousAt).smul continuousAt_const)
  · have hzSupport  := fun hzSupport => hz (hbU hzSupport)

    have hconst : ContinuousAt
        (fun _ : TimeVelocity d => lam • (1 : PDE.Mat d)) z :=
      continuousAt_const
    apply hconst.congr_of_eventuallyEq
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hzSupport)] with y hy
    simp_all

variable {K : HypoellipticAleksandrov.Parabolic.Region d}

/-- On the neighbourhood where the cutoff is one, the literal coefficient
extension agrees with the original curried coefficient field. -/
theorem coefficientAt_cutoffExtendCoefficient_eventuallyEq
      {b : HypoellipticAleksandrov.Parabolic.ScalarField d}
    {B : CoefficientField d} {lam : ℝ}
    (hbOne : ∀ᶠ z in 𝓝ˢ K, b z = 1) :
    coefficientAt (cutoffExtendCoefficient b B lam) =ᶠ[𝓝ˢ K] coefficientAt B := by
  filter_upwards [hbOne] with z hz
  simp [coefficientAt_cutoffExtendCoefficient, hz]

/-- On the neighbourhood where the cutoff is one, the literal scalar product
agrees with the original local function. -/
theorem cutoff_mul_eventuallyEq
      {b q : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hbOne : ∀ᶠ z in 𝓝ˢ K, b z = 1) :
    (fun z => b z * q z) =ᶠ[𝓝ˢ K] q := by
  filter_upwards [hbOne] with z hz
  simp [hz]

section
variable {q q' : HypoellipticAleksandrov.Parabolic.ScalarField d} {z : TimeVelocity d} (hqq' : q =ᶠ[𝓝 z] q')

include hqq'
/-- Eventual equality of scalar functions at a point gives equality of their
time derivatives there. No separate differentiability hypothesis is needed:
`fderiv` itself is local. -/
theorem timeDerivative_congr_of_eventuallyEq
      :
    timeDerivative q z = timeDerivative q' z := by
  unfold timeDerivative
  rw [hqq'.fderiv_eq]

/-- Eventual equality of scalar functions at a point gives equality of their
velocity Hessians there. No separate differentiability hypothesis is needed:
the iterated `fderiv` is local. -/
theorem velocityHessian_congr_of_eventuallyEq
      :
    velocityHessian q z = velocityHessian q' z := by
  ext i j
  unfold velocityHessian
  rw [hqq'.fderiv.fderiv_eq]
end


/-- Eventual equality of coefficient evaluations and scalar functions at a
point gives equality of their pointwise parabolic operators. -/
theorem parabolicOperator_congr_of_eventuallyEq_of_coefficientAt_eventuallyEq
     {B B' : CoefficientField d} {q q' : HypoellipticAleksandrov.Parabolic.ScalarField d}
    {z : TimeVelocity d} (hB : coefficientAt B =ᶠ[𝓝 z] coefficientAt B')
    (hqq' : q =ᶠ[𝓝 z] q') :
    parabolicOperator B q z = parabolicOperator B' q' z := by
  unfold parabolicOperator
  rw [timeDerivative_congr_of_eventuallyEq hqq', hB.self_of_nhds,
    velocityHessian_congr_of_eventuallyEq hqq']

end HypoellipticAleksandrov.Parabolic
