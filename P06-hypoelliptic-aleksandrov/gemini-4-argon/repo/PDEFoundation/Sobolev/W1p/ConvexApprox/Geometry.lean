module

public import PDEFoundation.Geometry.ConvexSegment
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Convex-domain smoothing geometry

This file isolates the affine sampling map used by convex-domain smooth
approximation. Given an internal base
`Metric.closedBall x0 r ⊆ U`—a cube for the inherited supremum metric—the
map samples a function at

`(1 - ε) • x + ε • (x0 - r • z)`.

If `‖z‖ ≤ 1` and `0 ≤ ε ≤ 1`, the second endpoint lies in that base cube,
and convexity keeps the sample point in `U`.
-/

@[expose] public section

namespace PDE

/- A nonempty bounded open convex domain contains a positive-radius closed
ball for the inherited native-vector metric. Since that metric is the
finite-product supremum metric, this is an internal base cube, not a round
Euclidean ball. -/
theorem
    exists_metricClosedBall_subset_of_isOpenBoundedConvexDomain
    {d } {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hUNonempty : U.Nonempty) :
    ∃ x0 : Vec d, ∃ r : ℝ,
      0 < r ∧ Metric.closedBall x0 r ⊆ U := by
  rcases hUNonempty with ⟨x0, hx0⟩
  rcases Metric.isOpen_iff.1 hU.isOpen x0 hx0 with
    ⟨δ, hδ, hball⟩
  refine ⟨x0, δ / 2, by positivity, ?_⟩
  exact
    (Metric.closedBall_subset_ball
      (by linarith : δ / 2 < δ)).trans hball

/- The affine sample point used by the convex-domain smoothing operator. -/
def convexApproxSample {d }
    (x0 z : Vec d) (r ε : ℝ) (x : Vec d) : Vec d :=
  (1 - ε) • x + ε • (x0 - r • z)

theorem convexApproxSample_eq_segmentBlend {d }
    (x0 z : Vec d) (r ε : ℝ) (x : Vec d) :
    convexApproxSample x0 z r ε x =
      segmentBlend (x0 - r • z) ε x := by
  rw [convexApproxSample, segmentBlend_eq_smul_add]

theorem sub_smul_mem_closedBall {d }
    {x0 z : Vec d} {r } (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1) :
    x0 - r • z ∈ Metric.closedBall x0 r := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hsub : (x0 - r • z) - x0 = -(r • z) := by
    abel_nf
  rw [hsub, norm_neg, norm_smul]
  calc
    |r| * ‖z‖ ≤ |r| * 1 :=
      mul_le_mul_of_nonneg_left hz (abs_nonneg r)
    _ = r := by
      rw [abs_of_nonneg hr]
      ring

theorem sub_smul_mem_of_closedBall_subset {d U} {x0 z : Vec d} {r }
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1) :
    x0 - r • z ∈ U :=
  hball (sub_smul_mem_closedBall hr hz)

/- The base-ball sample point remains in the convex domain. -/
theorem convexApproxSample_mem_of_isOpenBoundedConvexDomain
    {d U}
    (hU : IsOpenBoundedConvexDomain U)
    {x x0 z : Vec d} {r ε } (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    convexApproxSample x0 z r ε x ∈ U := by
  have hy :=
    sub_smul_mem_of_closedBall_subset hball hr hz
  rw [convexApproxSample_eq_segmentBlend]
  exact
    segmentBlend_mem_of_isOpenBoundedConvexDomain
      hU hy hx hε0 hε1

/- The base-ball sampling map sends the whole convex domain to itself. -/
theorem convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
    {d U}
    (hU : IsOpenBoundedConvexDomain U)
    {x0 z : Vec d} {r ε }
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Set.MapsTo (convexApproxSample x0 z r ε) U U := by
  intro x hx
  exact
    convexApproxSample_mem_of_isOpenBoundedConvexDomain
      hU hx hball hr hz hε0 hε1

theorem norm_convexApproxSample_sub_le {d }
    (x0 z : Vec d) (r ε : ℝ) (x : Vec d)
    (hε0 : 0 ≤ ε) :
    ‖convexApproxSample x0 z r ε x - x‖ ≤
      ε * ‖(x0 - r • z) - x‖ := by
  have _h_inl_12 (x0 z : Vec d) (r ε : ℝ) (x : Vec d) : ‖convexApproxSample x0 z r ε x - x‖ = |ε| * ‖(x0 - r • z) - x‖ := by
    rw [convexApproxSample_eq_segmentBlend,
      norm_segmentBlend_sub_right]
  rw [_h_inl_12, abs_of_nonneg hε0]

private theorem IsBoundedDomain.norm_sub_le_two_mul_choose'
    {d U} (hU : IsBoundedDomain U)
    {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) :
    ‖x - y‖ ≤ 2 * Classical.choose hU := by
  have hRPos :=
    (Classical.choose_spec hU).1
  have hR :=
    (Classical.choose_spec hU).2
  have hxNorm : ‖x‖ ≤ Classical.choose hU := by
    refine (pi_norm_le_iff_of_nonneg hRPos.le).2 ?_
    intro i
    simpa only [Real.norm_eq_abs] using hR x hx i
  have hyNorm : ‖y‖ ≤ Classical.choose hU := by
    refine (pi_norm_le_iff_of_nonneg hRPos.le).2 ?_
    intro i
    simpa only [Real.norm_eq_abs] using hR y hy i
  calc
    ‖x - y‖ ≤ ‖x‖ + ‖y‖ :=
      norm_sub_le x y
    _ ≤ Classical.choose hU + Classical.choose hU :=
      add_le_add hxNorm hyNorm
    _ = 2 * Classical.choose hU := by
      ring

theorem
    norm_convexApproxSample_sub_le_two_mul_choose_of_isOpenBoundedConvexDomain
    {d U}
    (hU : IsOpenBoundedConvexDomain U)
    {x x0 z : Vec d} {r ε } (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1) (hε0 : 0 ≤ ε) :
    ‖convexApproxSample x0 z r ε x - x‖ ≤
      ε * (2 * Classical.choose hU.isBoundedDomain) := by
  have hU := hU.isBoundedDomain
  have hy :=
    sub_smul_mem_of_closedBall_subset hball hr hz
  calc
    ‖convexApproxSample x0 z r ε x - x‖ ≤
        ε * ‖(x0 - r • z) - x‖ :=
      norm_convexApproxSample_sub_le x0 z r ε x hε0
    _ ≤ ε * (2 * Classical.choose hU) :=
      mul_le_mul_of_nonneg_left
        (hU.norm_sub_le_two_mul_choose' hy hx) hε0

end PDE
