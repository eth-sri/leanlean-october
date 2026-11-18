module

public import PDEFoundation.Geometry.ConvexDomain
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import PDEFoundation.Measure.AffineVolume
public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public noncomputable section

namespace PDE

/-- The point on the segment from `y` to `x` with parameter `t`. -/
noncomputable def segmentBlend {d : ℕ} (x : Vec d) (t : ℝ) (y : Vec d) : Vec d :=
  AffineMap.lineMap y x t

@[simp]
theorem segmentBlend_eq_lineMap {d : ℕ} (x y : Vec d) (t : ℝ) :
    segmentBlend x t y = AffineMap.lineMap y x t :=
  rfl





/-- The segment parametrization as an affine combination of its endpoints. -/
theorem segmentBlend_eq_smul_add {d : ℕ} (x y : Vec d) (t : ℝ) :
    segmentBlend x t y = (1 - t) • y + t • x := by
  simpa [segmentBlend] using
    (AffineMap.lineMap_apply_module y x t)

theorem segmentBlend_sub_right {d : ℕ} (x y : Vec d) (t : ℝ) :
    segmentBlend x t y - y = t • (x - y) := by
  ext i
  simp [segmentBlend, AffineMap.lineMap_apply_module']

theorem norm_segmentBlend_sub_right {d : ℕ} (x y : Vec d) (t : ℝ) :
    ‖segmentBlend x t y - y‖ = |t| * ‖x - y‖ := by
  rw [segmentBlend_sub_right, norm_smul, Real.norm_eq_abs]


theorem segmentBlend_mem_of_isOpenBoundedConvexDomain {d : ℕ}
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    segmentBlend x t y ∈ U  := by
  simpa [segmentBlend] using hU.convex.lineMap_mem hy hx ⟨ht0, ht1⟩


/-- A nonempty bounded open convex domain contains a positive-radius closed
ball for the inherited native-vector metric. Since that metric is the
finite-product supremum metric, this is an internal base cube, not a round
Euclidean ball. -/
theorem
    exists_metricClosedBall_subset_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)}
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

/-- The affine sample point used by the convex-domain smoothing operator. -/
def convexApproxSample {d : ℕ}
    (x0 z : Vec d) (r ε : ℝ) (x : Vec d) : Vec d :=
  (1 - ε) • x + ε • (x0 - r • z)

@[simp]
theorem convexApproxSample_apply {d : ℕ}
    (x0 z : Vec d) (r ε : ℝ) (x : Vec d) :
    convexApproxSample x0 z r ε x =
      (1 - ε) • x + ε • (x0 - r • z) :=
  rfl

theorem convexApproxSample_eq_segmentBlend {d : ℕ}
    (x0 z : Vec d) (r ε : ℝ) (x : Vec d) :
    convexApproxSample x0 z r ε x =
      segmentBlend (x0 - r • z) ε x := by
  rw [convexApproxSample, segmentBlend_eq_smul_add]


theorem sub_smul_mem_of_closedBall_subset {d : ℕ}
    {U : Set (Vec d)} {x0 z : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1) :
    x0 - r • z ∈ U  := by
  have sub_smul_mem_closedBall :
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
  exact hball (sub_smul_mem_closedBall)

/-- The base-ball sample point remains in the convex domain. -/
theorem convexApproxSample_mem_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {x x0 z : Vec d} {r ε : ℝ} (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    convexApproxSample x0 z r ε x ∈ U := by
  rw [convexApproxSample_eq_segmentBlend]
  exact
    segmentBlend_mem_of_isOpenBoundedConvexDomain
      hU (sub_smul_mem_of_closedBall_subset hball hr hz) hx hε0 hε1

/-- The base-ball sampling map sends the whole convex domain to itself. -/
theorem convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Set.MapsTo (convexApproxSample x0 z r ε) U U := by
  intro x hx
  exact
    convexApproxSample_mem_of_isOpenBoundedConvexDomain
      hU hx hball hr hz hε0 hε1

theorem norm_convexApproxSample_sub {d : ℕ}
    (x0 z : Vec d) (r ε : ℝ) (x : Vec d) :
    ‖convexApproxSample x0 z r ε x - x‖ =
      |ε| * ‖(x0 - r • z) - x‖ := by
  rw [convexApproxSample_eq_segmentBlend,
    norm_segmentBlend_sub_right]

theorem norm_convexApproxSample_sub_le {d : ℕ}
    (x0 z : Vec d) (r ε : ℝ) (x : Vec d)
    (hε0 : 0 ≤ ε) :
    ‖convexApproxSample x0 z r ε x - x‖ ≤
      ε * ‖(x0 - r • z) - x‖ := by
  rw [norm_convexApproxSample_sub, abs_of_nonneg hε0]

private theorem IsBoundedDomain.norm_sub_le_two_mul_choose'
    {d : ℕ} {U : Set (Vec d)} (hU : IsBoundedDomain U)
    {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) :
    ‖x - y‖ ≤ 2 * Classical.choose hU := by
  have hRPos :=
    (Classical.choose_spec hU).1
  have hR :=
    (Classical.choose_spec hU).2
  have hxNorm : ‖x‖ ≤ Classical.choose hU := by
    refine (pi_norm_le_iff_of_nonneg hRPos.le).2 ?_
    intro i
    simpa using hR x hx i
  have hyNorm : ‖y‖ ≤ Classical.choose hU := by
    refine (pi_norm_le_iff_of_nonneg hRPos.le).2 ?_
    intro i
    simpa using hR y hy i
  calc
    ‖x - y‖ ≤ ‖x‖ + ‖y‖ :=
      norm_sub_le x y
    _ ≤ Classical.choose hU + Classical.choose hU :=
      add_le_add hxNorm hyNorm
    _ = 2 * Classical.choose hU := by
      ring

theorem norm_convexApproxSample_sub_le_two_mul_choose
    {d : ℕ} {U : Set (Vec d)} (hU : IsBoundedDomain U)
    {x x0 z : Vec d} {r ε : ℝ} (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1) (hε0 : 0 ≤ ε) :
    ‖convexApproxSample x0 z r ε x - x‖ ≤
      ε * (2 * Classical.choose hU) := by
  calc
    ‖convexApproxSample x0 z r ε x - x‖ ≤
        ε * ‖(x0 - r • z) - x‖ :=
      norm_convexApproxSample_sub_le x0 z r ε x hε0
    _ ≤ ε * (2 * Classical.choose hU) :=
      mul_le_mul_of_nonneg_left
        (hU.norm_sub_le_two_mul_choose' (sub_smul_mem_of_closedBall_subset hball hr hz) hx) hε0

theorem
    norm_convexApproxSample_sub_le_two_mul_choose_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {x x0 z : Vec d} {r ε : ℝ} (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1) (hε0 : 0 ≤ ε) :
    ‖convexApproxSample x0 z r ε x - x‖ ≤
      ε * (2 * Classical.choose hU.isBoundedDomain) :=
  norm_convexApproxSample_sub_le_two_mul_choose
    hU.isBoundedDomain hx hball hr hz hε0

open scoped Pointwise Convolution

/-- Cache smooth-bump existence on native vectors for this module and its
transitive importers. -/
private instance instHasContDiffBumpVec (d : ℕ) :
    HasContDiffBump (Vec d) :=
  inferInstance

/-- A nonnegative smooth unit-mass kernel supported in the closed unit ball
for the inherited native-vector norm. -/
structure IsConvexApproxKernel {d : ℕ} (ρ : Vec d → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) ρ
  compactSupport : HasCompactSupport ρ
  support_subset_closedBall :
    tsupport ρ ⊆ Metric.closedBall (0 : Vec d) 1
  nonneg : ∀ z, 0 ≤ ρ z
  setIntegral_one : ∫ z in tsupport ρ, ρ z = 1

namespace IsConvexApproxKernel

theorem continuous {d : ℕ} {ρ : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) :
    Continuous ρ :=
  hρ.smooth.continuous

end IsConvexApproxKernel

namespace ContDiffBump

theorem isConvexApproxKernel_normed {d : ℕ}
    (φ : ContDiffBump (0 : Vec d)) (hφ : φ.rOut ≤ 1) :
    IsConvexApproxKernel (φ.normed MeasureTheory.volume) := by
  refine
    { smooth := by
        simpa using
          (φ.contDiff_normed (μ := MeasureTheory.volume))
      compactSupport := by
        simpa using
          (φ.hasCompactSupport_normed
            (μ := MeasureTheory.volume))
      support_subset_closedBall := by
        rw [φ.tsupport_normed_eq (μ := MeasureTheory.volume)]
        exact Metric.closedBall_subset_closedBall hφ
      nonneg := by
        intro z
        simpa using
          (φ.nonneg_normed (μ := MeasureTheory.volume) z)
      setIntegral_one := by
        calc
          ∫ z in tsupport (φ.normed MeasureTheory.volume),
              φ.normed MeasureTheory.volume z =
              ∫ z, φ.normed MeasureTheory.volume z := by
            exact
              MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
                (fun z hz =>
                  image_eq_zero_of_notMem_tsupport
 hz)
          _ = 1 :=
            φ.integral_normed (μ := MeasureTheory.volume) }

end ContDiffBump

/-- A concrete smooth bump centered at the origin with outer radius `1`. -/
noncomputable def unitContDiffBump {d : ℕ} :
    ContDiffBump (0 : Vec d) :=
  ⟨(1 / 2 : ℝ), 1, by positivity, by norm_num⟩

/-- The normalized kernel associated with `unitContDiffBump`. -/
noncomputable def unitConvexApproxKernel {d : ℕ} :
    Vec d → ℝ :=
  (unitContDiffBump (d := d)).normed MeasureTheory.volume

theorem isConvexApproxKernel_unitConvexApproxKernel {d : ℕ} :
    IsConvexApproxKernel
      (unitConvexApproxKernel (d := d)) := by
  simpa only [unitConvexApproxKernel, unitContDiffBump] using
    (ContDiffBump.isConvexApproxKernel_normed
      (φ := unitContDiffBump)
      (by norm_num [unitContDiffBump]))

/-- The standard positive scale sequence for convex approximation. -/
noncomputable def unitConvexApproxScale (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

theorem unitConvexApproxScale_pos (n : ℕ) :
    0 < unitConvexApproxScale n := by
  dsimp only [unitConvexApproxScale]
  positivity

theorem tendsto_unitConvexApproxScale_zero :
    Filter.Tendsto unitConvexApproxScale
      Filter.atTop (nhds 0) := by
  simpa using!
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- The integrand defining convex approximation at a point. -/
def convexApproxIntegrand {d : ℕ}
    (ρ u : Vec d → ℝ) (x0 : Vec d) (r ε : ℝ)
    (x z : Vec d) : ℝ :=
  ρ z * u (convexApproxSample x0 z r ε x)

@[simp]
theorem convexApproxIntegrand_apply {d : ℕ}
    (ρ u : Vec d → ℝ) (x0 : Vec d) (r ε : ℝ)
    (x z : Vec d) :
    convexApproxIntegrand ρ u x0 r ε x z =
      ρ z * u (convexApproxSample x0 z r ε x) :=
  rfl

/-- The convex-domain smoothing operator attached to a kernel `ρ`. -/
noncomputable def convexApproxSmoothing {d : ℕ}
    (ρ u : Vec d → ℝ) (x0 : Vec d) (r ε : ℝ)
    (x : Vec d) : ℝ :=
  ∫ z in tsupport ρ, convexApproxIntegrand ρ u x0 r ε x z

@[simp]
theorem convexApproxSmoothing_apply {d : ℕ}
    (ρ u : Vec d → ℝ) (x0 : Vec d) (r ε : ℝ)
    (x : Vec d) :
    convexApproxSmoothing ρ u x0 r ε x =
      ∫ z in tsupport ρ,
        convexApproxIntegrand ρ u x0 r ε x z :=
  rfl

/-- The concrete convex smoothing sequence using the unit kernel and scale. -/
noncomputable def unitConvexApproxSequence {d : ℕ}
    (u : Vec d → ℝ) (x0 : Vec d) (r : ℝ) (n : ℕ) :
    Vec d → ℝ :=
  fun x =>
    convexApproxSmoothing
      (unitConvexApproxKernel (d := d)) u x0 r
        (unitConvexApproxScale n) x

/-- Rescale a kernel by a positive length `a`, displaying the exact
dimension-`d` Jacobian factor. -/
noncomputable def scaledConvexApproxKernel {d : ℕ}
    (ρ : Vec d → ℝ) (a : ℝ) : Vec d → ℝ :=
  fun y => (a ^ d)⁻¹ * ρ (a⁻¹ • y)

theorem continuous_scaledConvexApproxKernel {d : ℕ}
    {ρ : Vec d → ℝ} (hρ : Continuous ρ) (a : ℝ) :
    Continuous (scaledConvexApproxKernel ρ a) := by
  unfold scaledConvexApproxKernel
  fun_prop

theorem contDiff_scaledConvexApproxKernel {d : ℕ}
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (scaledConvexApproxKernel ρ a) := by
  have hscale :
      ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => a⁻¹ • y) := by
    fun_prop
  simpa using!
    contDiff_const.mul (hρ.smooth.comp hscale)

theorem measurable_scaledConvexApproxKernel {d : ℕ}
    {ρ : Vec d → ℝ} (hρ : Continuous ρ) (a : ℝ) :
    Measurable (scaledConvexApproxKernel ρ a) :=
  (continuous_scaledConvexApproxKernel hρ a).measurable

theorem hasCompactSupport_scaledConvexApproxKernel {d : ℕ}
    {ρ : Vec d → ℝ} (hρ : HasCompactSupport ρ)
    {a : ℝ} (ha : 0 < a) :
    HasCompactSupport (scaledConvexApproxKernel ρ a) := by
  have hcomp :
      HasCompactSupport (fun y => ρ (a⁻¹ • y)) := by
    simpa using
      hρ.comp_smul (inv_ne_zero ha.ne')
  simpa using!
    (hcomp.mul_left :
      HasCompactSupport
        (fun y => (a ^ d)⁻¹ * ρ (a⁻¹ • y)))

theorem integrable_scaledConvexApproxKernel {d : ℕ}
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {a : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable
      (scaledConvexApproxKernel ρ a) := by
  exact
    (continuous_scaledConvexApproxKernel hρ.continuous a).integrable_of_hasCompactSupport
      (hasCompactSupport_scaledConvexApproxKernel
        hρ.compactSupport ha)

theorem scaledConvexApproxKernel_nonneg {d : ℕ}
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {a : ℝ} (_ha : 0 < a) (y : Vec d) :
    0 ≤ scaledConvexApproxKernel ρ a y := by
  have hpowNonneg : 0 ≤ (a ^ d)⁻¹ := by
    positivity
  exact mul_nonneg hpowNonneg (hρ.nonneg _)

theorem integral_scaledConvexApproxKernel {d : ℕ}
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {a : ℝ} (ha : 0 < a) :
    ∫ y, scaledConvexApproxKernel ρ a y = 1 := by
  have haNe :=
    ha.ne'
  have hzero :
      ∀ y, y ∉ a • tsupport ρ →
        scaledConvexApproxKernel ρ a y = 0 := by
    intro y hy
    have hy' : a⁻¹ • y ∉ tsupport ρ := by
      intro hmem
      apply hy
      exact Set.mem_smul_set.mpr
        ⟨a⁻¹ • y, hmem, by
          rw [smul_smul, mul_inv_cancel₀ haNe, one_smul]⟩
    simp [scaledConvexApproxKernel, image_eq_zero_of_notMem_tsupport hy']
  rw [←
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      hzero]
  calc
    ∫ y in a • tsupport ρ,
        scaledConvexApproxKernel ρ a y
        ∂MeasureTheory.volume =
        (a ^ d)⁻¹ *
          ∫ y in a • tsupport ρ, ρ (a⁻¹ • y)
            ∂MeasureTheory.volume := by
      simp only [scaledConvexApproxKernel,
        MeasureTheory.integral_const_mul]
    _ = ∫ z in tsupport ρ, ρ z
          ∂MeasureTheory.volume := by
      simpa [smul_eq_mul, smul_smul,
        inv_mul_cancel₀ haNe, mul_inv_cancel₀ haNe] using
        (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
          (μ := MeasureTheory.volume)
          (f := fun y => ρ (a⁻¹ • y))
          (s := tsupport ρ) ha).symm
    _ = 1 :=
      hρ.setIntegral_one

theorem translateSet_smul_subset_of_convexApproxSample_mapsTo
    {d : ℕ} {U : Set (Vec d)}
    {x0 z : Vec d} {r ε : ℝ}
    (hmap :
      Set.MapsTo (convexApproxSample x0 z r ε) U U) :
    translateSet (ε • (x0 - r • z)) ((1 - ε) • U) ⊆
      U := by
  intro y hy
  rcases hy with ⟨w, hw, hyw⟩
  rcases Set.mem_smul_set.mp hw with ⟨x, hx, rfl⟩
  have hx' :=
    hmap hx
  rw [hyw]
  simpa using hx'

theorem setIntegral_comp_smul_add_of_pos
    {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a : ℝ} (ha : 0 < a) (b : Vec d) (U : Set (Vec d))
    (f : Vec d → E) :
    ∫ x in U, f (a • x + b) ∂MeasureTheory.volume =
      (a ^ d)⁻¹ •
        ∫ y in translateSet b (a • U), f y
          ∂MeasureTheory.volume := by
  calc
    ∫ x in U, f (a • x + b) ∂MeasureTheory.volume =
        (a ^ d)⁻¹ •
          ∫ z in a • U, f (z + b)
            ∂MeasureTheory.volume := by
      simpa [Vec] using
        (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
          (μ := MeasureTheory.volume)
          (f := fun z => f (z + b))
          (s := U) ha)
    _ = (a ^ d)⁻¹ •
          ∫ y in translateSet b (a • U), f y
            ∂MeasureTheory.volume := by
      rw [setIntegral_comp_addRight_translateSet
 b (a • U) f]

theorem convolution_scaledConvexApproxKernel_indicator_eq_setIntegral
    {d : ℕ} {ρ u : Vec d → ℝ} {U : Set (Vec d)}
    {x0 x : Vec d} {r ε : ℝ}
    (hr : 0 < r) (hε0 : 0 < ε) :
    (scaledConvexApproxKernel ρ (ε * r) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume]
      Set.indicator U u) ((1 - ε) • x + ε • x0) =
      ∫ z in tsupport ρ,
        ρ z * Set.indicator U u
          (((1 - ε) • x + ε • x0) - (ε * r) • z)
          ∂MeasureTheory.volume := by
  let a : ℝ :=
    ε * r
  let A :=
    (1 - ε) • x + ε • x0
  have ha : 0 < a := by
    positivity
  have haNe :=
    ha.ne'
  change
    ∫ t, scaledConvexApproxKernel ρ a t *
        Set.indicator U u (A - t) ∂MeasureTheory.volume =
      ∫ z in tsupport ρ,
        ρ z * Set.indicator U u (A - a • z)
          ∂MeasureTheory.volume
  simp only [scaledConvexApproxKernel]
  have hzero :
      ∀ y, y ∉ a • tsupport ρ →
        ((a ^ d)⁻¹ * ρ (a⁻¹ • y)) *
          Set.indicator U u (A - y) = 0 := by
    intro y hy
    have hy' : a⁻¹ • y ∉ tsupport ρ := by
      intro hmem
      apply hy
      exact Set.mem_smul_set.mpr
        ⟨a⁻¹ • y, hmem, by
          rw [smul_smul, mul_inv_cancel₀ haNe, one_smul]⟩
    simp [image_eq_zero_of_notMem_tsupport hy']
  rw [←
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      hzero]
  have hmul :
      (fun y =>
        ((a ^ d)⁻¹ * ρ (a⁻¹ • y)) *
          Set.indicator U u (A - y)) =
        fun y =>
          (a ^ d)⁻¹ *
            (ρ (a⁻¹ • y) * Set.indicator U u (A - y)) := by
    funext y
    ring
  calc
    ∫ y in a • tsupport ρ,
        ((a ^ d)⁻¹ * ρ (a⁻¹ • y)) *
          Set.indicator U u (A - y) ∂MeasureTheory.volume =
        (a ^ d)⁻¹ *
          ∫ y in a • tsupport ρ,
            ρ (a⁻¹ • y) * Set.indicator U u (A - y)
              ∂MeasureTheory.volume := by
      rw [hmul, MeasureTheory.integral_const_mul]
    _ = ∫ z in tsupport ρ,
          ρ z * Set.indicator U u (A - a • z)
            ∂MeasureTheory.volume := by
      simpa [smul_eq_mul, mul_assoc, mul_left_comm,
        mul_comm, sub_eq_add_neg, smul_smul,
        inv_mul_cancel₀ haNe, mul_inv_cancel₀ haNe,
        zero_smul, add_zero] using
        (setIntegral_comp_smul_add_of_pos
 ha (b := 0)
          (U := tsupport ρ)
          (f := fun y =>
            ρ (a⁻¹ • y) * Set.indicator U u (A - y))).symm

theorem
    convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
    {d : ℕ} {ρ u : Vec d → ℝ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ)
    {x0 x : Vec d} {r ε : ℝ} (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε0 : 0 < ε) (hε1 : ε < 1) :
    convexApproxSmoothing ρ u x0 r ε x =
      (scaledConvexApproxKernel ρ (ε * r) ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ,
          MeasureTheory.volume]
        Set.indicator U u) ((1 - ε) • x + ε • x0) := by
  rw [
    convolution_scaledConvexApproxKernel_indicator_eq_setIntegral
      hr hε0,
    convexApproxSmoothing]
  apply MeasureTheory.integral_congr_ae
  change
    ∀ᵐ z ∂MeasureTheory.volume.restrict (tsupport ρ),
      convexApproxIntegrand ρ u x0 r ε x z =
        ρ z * Set.indicator U u
          (((1 - ε) • x + ε • x0) - (ε * r) • z)
  rw [MeasureTheory.ae_restrict_iff' ((isClosed_tsupport (f := ρ)).measurableSet)]
  filter_upwards with z hz
  have hzNorm : ‖z‖ ≤ 1 := by
    simpa using
      hρ.support_subset_closedBall hz
  have hsampleEq :
      ((1 - ε) • x + ε • x0) - (ε * r) • z =
        convexApproxSample x0 z r ε x := by
    simp [convexApproxSample, sub_eq_add_neg, smul_smul,
      add_assoc, add_left_comm, add_comm]
  have hind :
      Set.indicator U u (convexApproxSample x0 z r ε x) =
        u (convexApproxSample x0 z r ε x) := by
    rw [Set.indicator_of_mem (convexApproxSample_mem_of_isOpenBoundedConvexDomain hU hx hball hr.le hzNorm hε0.le (le_of_lt hε1))]
  calc
    convexApproxIntegrand ρ u x0 r ε x z =
        ρ z * u (convexApproxSample x0 z r ε x) :=
      convexApproxIntegrand_apply ρ u x0 r ε x z
    _ = ρ z *
        Set.indicator U u
          (convexApproxSample x0 z r ε x) := by
      rw [hind]
    _ = ρ z *
        Set.indicator U u
          (((1 - ε) • x + ε • x0) -
            (ε * r) • z) := by
      rw [hsampleEq]

end PDE

