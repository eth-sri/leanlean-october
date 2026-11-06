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

/- A smooth cutoff which is identically one in a neighbourhood of the compact
set `K` and has topological support inside the open set `U`. -/
theorem exists_smooth_cutoff_tsupport_subset
    {d K U}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ b : TimeVelocity d → ℝ,
      ContDiff ℝ ∞ b ∧
      (∀ᶠ z in 𝓝ˢ K, b z = 1) ∧
      tsupport b ⊆ U := by
  obtain ⟨L, _hLcompact, hLclosed, hKinterior, hLU⟩ :=
    exists_compact_closed_between hK hU hKU
  obtain ⟨b, hbOne, hbZero, _hbRange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (I := 𝓘(ℝ, TimeVelocity d)) hK.isClosed
      (by simpa only [interior_interior] using hKinterior)
  refine ⟨b, b.contMDiff.contDiff, hbOne, ?_⟩
  have hsupport : support (b : TimeVelocity d → ℝ) ⊆ L := by
    intro z hz
    by_contra hzL
    exact (mem_support.mp hz) (hbZero z hzL)
  change closure (support (b : TimeVelocity d → ℝ)) ⊆ U
  exact (closure_minimal hsupport hLclosed).trans hLU

/- Multiplication by a globally smooth cutoff whose topological support lies
inside `U` turns a `C²` function on the open set `U` into a literal globally
`C²` function. -/
theorem contDiff_cutoff_mul_of_tsupport_subset
    {d U} {b q : TimeVelocity d → ℝ}
    (hU : IsOpen U) (hb : ContDiff ℝ 2 b) (hbU : tsupport b ⊆ U)
    (hq : ContDiffOn ℝ 2 q U) :
    ContDiff ℝ 2 (fun z => b z * q z) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : z ∈ U
  · exact hb.contDiffAt.mul (hq.contDiffAt (hU.mem_nhds hz))
  · have hzSupport : z ∉ tsupport b := fun hzSupport => hz (hbU hzSupport)
    have hzero : b =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hzSupport
    have hconst : ContDiffAt ℝ 2 (fun _ : TimeVelocity d => (0 : ℝ)) z :=
      contDiffAt_const
    apply hconst.congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [Pi.zero_apply] at hy
    simp only [hy, zero_mul]

/- Multiplication by a globally smooth cutoff whose topological support lies
inside `U` turns a continuous scalar function on `U` into a literal globally
continuous scalar function. -/
def cutoffExtendCoefficient {d }
    (b : TimeVelocity d → ℝ) (B : CoefficientField d) (lam : ℝ) :
    CoefficientField d :=
  fun t v => b (t, v) • B t v + (1 - b (t, v)) • (lam • (1 : PDE.Mat d))

/- Evaluation of a cutoff-glued coefficient field. -/
@[simp] theorem coefficientAt_cutoffExtendCoefficient
    {d } (b : TimeVelocity d → ℝ) (B : CoefficientField d) (lam : ℝ)
    (z : TimeVelocity d) :
    coefficientAt (cutoffExtendCoefficient b B lam) z =
      b z • coefficientAt B z + (1 - b z) • (lam • (1 : PDE.Mat d)) :=
  rfl

/- The cutoff-glued coefficient field is globally continuous when the
original coefficient is continuous only on the open set containing the
cutoff's topological support. -/
theorem cutoff_mul_eventuallyEq
    {d K} {b q : TimeVelocity d → ℝ}
    (hbOne : ∀ᶠ z in 𝓝ˢ K, b z = 1) :
    (fun z => b z * q z) =ᶠ[𝓝ˢ K] q := by
  filter_upwards [hbOne] with z hz
  simp [hz]

/- Eventual equality of scalar functions at a point gives equality of their
time derivatives there. No separate differentiability hypothesis is needed:
`fderiv` itself is local. -/
theorem parabolicOperator_congr_of_eventuallyEq_of_coefficientAt_eventuallyEq
    {d B B' q q'}
    {z : TimeVelocity d} (hB : coefficientAt B =ᶠ[𝓝 z] coefficientAt B')
    (hqq' : q =ᶠ[𝓝 z] q') :
    parabolicOperator B q z = parabolicOperator B' q' z := by
  unfold parabolicOperator
  have _h_inl_16 : timeDerivative q z = timeDerivative q' z := by
      unfold timeDerivative
      rw [hqq'.fderiv_eq]

    /- Eventual equality of scalar functions at a point gives equality of their
    velocity Hessians there. No separate differentiability hypothesis is needed:
    the iterated `fderiv` is local. -/
  have _h_inl_13 : velocityHessian q z = velocityHessian q' z := by
    ext i j
    unfold velocityHessian
    rw [hqq'.fderiv.fderiv_eq]
  rw [_h_inl_16, hB.self_of_nhds,
    _h_inl_13]

end HypoellipticAleksandrov.Parabolic
