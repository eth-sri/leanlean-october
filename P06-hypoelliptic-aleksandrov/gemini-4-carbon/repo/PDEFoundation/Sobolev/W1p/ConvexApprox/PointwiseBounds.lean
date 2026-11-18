module

public import PDEFoundation.Sobolev.W1p.ConvexApprox.WeakDerivSmoothing.Integral

@[expose] public noncomputable section

namespace PDE
open scoped Pointwise Convolution

/-- The classical coordinate derivative of the smooth representative agrees
almost everywhere with the correspondingly smoothed weak derivative, including
the exact affine factor `1 - ε`. -/
theorem ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {i : Fin d} {u gi ρ : Vec d → ℝ} {p : ENNReal}
    (hρ : IsConvexApproxKernel ρ) (hp : 1 ≤ p)
    (huMem : MemLpOn U p u) (hgiMem : MemLpOn U p gi)
    (huWeak : HasWeakPartialDerivOn U i u gi)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    (fun x =>
        (fderiv ℝ
          (convexApproxSmoothRepresentative U ρ u x0 r ε) x)
          (basisVec i)) =ᵐ[MeasureTheory.volume.restrict U]
      fun x =>
        (1 - ε) *
          convexApproxSmoothRepresentative U ρ gi x0 r ε x := by
  have huLoc :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      (huMem.locallyIntegrable hp)
  have hgiLoc :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      (hgiMem.locallyIntegrable hp)
  have huSmooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (convexApproxSmoothRepresentative U ρ u x0 r ε) :=
    contDiff_convexApproxSmoothRepresentative
      hU.measurableSet hρ hp huMem hr hε
  have hgiSmooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (convexApproxSmoothRepresentative U ρ gi x0 r ε) :=
    contDiff_convexApproxSmoothRepresentative
      hU.measurableSet hρ hp hgiMem hr hε
  have hClassicalWeak :=
    HasWeakPartialDerivOn.of_contDiff
      (U := U) (i := i)

      (huSmooth.of_le (by simp))
  have hSmoothedWeak :=
    HasWeakPartialDerivOn.convexApproxSmoothRepresentative
      (i := i) hU huLoc hgiLoc huWeak hρ
      hball hr hε hεOne
  have hClassicalContinuous :
      Continuous
        (fun x =>
          (fderiv ℝ
            (convexApproxSmoothRepresentative U ρ u x0 r ε) x)
            (basisVec i)) := by
    simpa only using
      (huSmooth.continuous_fderiv (by simp)).clm_apply
        continuous_const
  have hSmoothedContinuous :
      Continuous
        (fun x =>
          (1 - ε) *
            convexApproxSmoothRepresentative U ρ gi x0 r ε x) := by
    simpa only using!
      continuous_const.mul hgiSmooth.continuous
  have hClassicalLoc :
      MeasureTheory.LocallyIntegrableOn
        (fun x =>
          (fderiv ℝ
            (convexApproxSmoothRepresentative U ρ u x0 r ε) x)
            (basisVec i))
        U MeasureTheory.volume :=
    hClassicalContinuous.continuousOn.locallyIntegrableOn
      hU.measurableSet
  have hSmoothedLoc :
      MeasureTheory.LocallyIntegrableOn
        (fun x =>
          (1 - ε) *
            convexApproxSmoothRepresentative U ρ gi x0 r ε x)
        U MeasureTheory.volume :=
    hSmoothedContinuous.continuousOn.locallyIntegrableOn
      hU.measurableSet
  exact
    HasWeakPartialDerivOn.ae_eq
      hU.isOpen hClassicalLoc hSmoothedLoc
      hClassicalWeak hSmoothedWeak

theorem continuous_convexApproxSample_right
    {d : ℕ} (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    Continuous
      (fun z : Vec d =>
        convexApproxSample x0 z r ε x) := by
  unfold convexApproxSample
  fun_prop


theorem continuous_convexApproxIntegrand_right
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    Continuous
      (fun z =>
        convexApproxIntegrand ρ u x0 r ε x z) := by
  simpa using!
    hρ.mul
      (hu.comp
        (continuous_convexApproxSample_right x0 r ε x))

theorem continuous_convexApproxIntegrand_prod
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) :
    Continuous
      (fun xz : Vec d × Vec d =>
        convexApproxIntegrand
          ρ u x0 r ε xz.1 xz.2)  := by
  have continuous_convexApproxSample_prod (r ε : ℝ) :
      Continuous
      (fun xz : Vec d × Vec d =>
        convexApproxSample x0 xz.2 r ε xz.1) := by
    unfold convexApproxSample
    fun_prop
  have hρProd :
      Continuous
        (fun xz : Vec d × Vec d => ρ xz.2) :=
    hρ.comp continuous_snd
  have huProd :=
    hu.comp
      (continuous_convexApproxSample_prod r ε)
  simpa using!
    hρProd.mul huProd

theorem hasCompactSupport_convexApproxIntegrand
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : HasCompactSupport ρ)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    HasCompactSupport
      (fun z =>
        convexApproxIntegrand ρ u x0 r ε x z) := by
  simpa using!
    (hρ.mul_right :
      HasCompactSupport
        (fun z =>
          ρ z *
            u (convexApproxSample x0 z r ε x)))

theorem integrable_convexApproxIntegrand
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ)
    (hρCompact : HasCompactSupport ρ)
    (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    MeasureTheory.Integrable
      (fun z =>
        convexApproxIntegrand ρ u x0 r ε x z) :=
  (continuous_convexApproxIntegrand_right
      hρ hu x0 r ε x).integrable_of_hasCompactSupport
    (hasCompactSupport_convexApproxIntegrand
      hρCompact x0 r ε x)

theorem continuous_convexApproxWeightedOscillation
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    Continuous
      (fun z =>
        ρ z *
          |u (convexApproxSample x0 z r ε x) - u x|) :=
  hρ.mul
    (((hu.comp
      (continuous_convexApproxSample_right
        x0 r ε x)).sub continuous_const).abs)

theorem hasCompactSupport_convexApproxWeightedOscillation
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρCompact : HasCompactSupport ρ)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    HasCompactSupport
      (fun z =>
        ρ z *
          |u (convexApproxSample x0 z r ε x) - u x|) := by
  simpa only using!
    (hρCompact.mul_right :
      HasCompactSupport
        (fun z =>
          ρ z *
            |u (convexApproxSample x0 z r ε x) - u x|))

theorem integrable_convexApproxWeightedOscillation
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ)
    (hρCompact : HasCompactSupport ρ)
    (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    MeasureTheory.Integrable
      (fun z =>
        ρ z *
          |u (convexApproxSample x0 z r ε x) - u x|) :=
  (continuous_convexApproxWeightedOscillation
      hρ hu x0 r ε x).integrable_of_hasCompactSupport
    (hasCompactSupport_convexApproxWeightedOscillation
      hρCompact x0 r ε x)

theorem integrable_convexApproxKernelMulConst
    {d : ℕ} {ρ : Vec d → ℝ}
    (hρ : Continuous ρ)
    (hρCompact : HasCompactSupport ρ)
    (c : ℝ) :
    MeasureTheory.Integrable
      (fun z => ρ z * c) := by
  have hContinuous :
      Continuous (fun z => ρ z * c) :=
    hρ.mul continuous_const
  have hCompact :
      HasCompactSupport (fun z => ρ z * c) := by
    simpa only using!
      (hρCompact.mul_right :
        HasCompactSupport (fun z => ρ z * c))
  exact
    hContinuous.integrable_of_hasCompactSupport hCompact

theorem continuous_convexApproxSmoothing
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ)
    (hρCompact : HasCompactSupport ρ)
    (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) :
    Continuous
      (convexApproxSmoothing ρ u x0 r ε) := by
  have hIntegrand :
      Continuous
        (Function.uncurry
          (fun x z =>
            convexApproxIntegrand ρ u x0 r ε x z)) := by
    simpa using!
      continuous_convexApproxIntegrand_prod
        hρ hu x0 r ε
  simpa using!
    (continuous_parametric_integral_of_continuous
      (μ := MeasureTheory.volume)

      hIntegrand hρCompact.isCompact)


/-- Membership in the closed unit ball centered at zero gives the expected
norm bound. -/
theorem norm_le_one_of_mem_closedBall_zero_one
    {d : ℕ} {z : Vec d}
    (hz : z ∈ Metric.closedBall (0 : Vec d) 1) :
    ‖z‖ ≤ 1 := by
  simpa using hz

/-- Kernel support points produce samples that remain in the convex domain. -/
theorem convexApproxSample_mem_of_tsupport_subset_closedBall
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {ρ : Vec d → ℝ} {x x0 z : Vec d} {r ε : ℝ}
    (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U)
    (hρSub :
      tsupport ρ ⊆ Metric.closedBall (0 : Vec d) 1)
    (hz : z ∈ tsupport ρ)
    (hr : 0 ≤ r) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    convexApproxSample x0 z r ε x ∈ U := by
  exact
    convexApproxSample_mem_of_isOpenBoundedConvexDomain
      hU hx hball hr
      (norm_le_one_of_mem_closedBall_zero_one (hρSub hz))
      hε0 hε1

/-- The smoothing error is the kernel-weighted average of pointwise
differences. -/
theorem convexApproxSmoothing_sub_eq_setIntegral_weightedDiff
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    convexApproxSmoothing ρ u x0 r ε x - u x =
      ∫ z in tsupport ρ,
        ρ z *
          (u (convexApproxSample x0 z r ε x) - u x) := by
  have hInt1 :
      MeasureTheory.IntegrableOn
        (fun z =>
          convexApproxIntegrand ρ u x0 r ε x z)
        (tsupport ρ) :=
    (integrable_convexApproxIntegrand
      hρ.continuous hρ.compactSupport hu
      x0 r ε x).integrableOn
  have hInt2 :
      MeasureTheory.IntegrableOn
        (fun z => ρ z * u x) (tsupport ρ) :=
    (integrable_convexApproxKernelMulConst
      hρ.continuous hρ.compactSupport (u x)).integrableOn
  have hconst :
      (∫ z in tsupport ρ, ρ z * u x) = u x := by
    rw [MeasureTheory.integral_mul_const,
      hρ.setIntegral_one, one_mul]
  calc
    convexApproxSmoothing ρ u x0 r ε x - u x =
        (∫ z in tsupport ρ,
            convexApproxIntegrand ρ u x0 r ε x z) -
          ∫ z in tsupport ρ, ρ z * u x := by
      rw [convexApproxSmoothing]
      conv_lhs => rw [← hconst]
    _ = ∫ z in tsupport ρ,
          convexApproxIntegrand ρ u x0 r ε x z -
            ρ z * u x := by
      rw [MeasureTheory.integral_sub hInt1 hInt2]
    _ = ∫ z in tsupport ρ,
          ρ z *
            (u (convexApproxSample x0 z r ε x) - u x) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      simp
      ring

/-- The absolute smoothing error is bounded by the weighted average of the
pointwise oscillation. -/
theorem
    abs_convexApproxSmoothing_sub_le_setIntegral_weightedOscillation
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    |convexApproxSmoothing ρ u x0 r ε x - u x| ≤
      ∫ z in tsupport ρ,
        ρ z *
          |u (convexApproxSample x0 z r ε x) - u x| := by
  rw [
    convexApproxSmoothing_sub_eq_setIntegral_weightedDiff
      hρ hu x0 r ε x]
  calc
    |∫ z in tsupport ρ,
        ρ z *
          (u (convexApproxSample x0 z r ε x) - u x)| ≤
        ∫ z in tsupport ρ,
          |ρ z *
            (u (convexApproxSample x0 z r ε x) - u x)| := by
      simpa only using
        (MeasureTheory.abs_integral_le_integral_abs
          (μ :=
            MeasureTheory.volume.restrict (tsupport ρ))
)
    _ = ∫ z in tsupport ρ,
          ρ z *
            |u (convexApproxSample x0 z r ε x) - u x| := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      rw [abs_mul, abs_of_nonneg (hρ.nonneg z)]

/-- A pointwise oscillation bound on every kernel sample controls the
smoothing error with the same constant. -/
theorem abs_convexApproxSmoothing_sub_le_of_pointwiseOscillation
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) {δ : ℝ}
    (hosc :
      ∀ z ∈ tsupport ρ,
        |u (convexApproxSample x0 z r ε x) - u x| ≤ δ) :
    |convexApproxSmoothing ρ u x0 r ε x - u x| ≤ δ := by
  have hIntLeft :
      MeasureTheory.IntegrableOn
        (fun z =>
          ρ z *
            |u (convexApproxSample x0 z r ε x) - u x|)
        (tsupport ρ) :=
    (integrable_convexApproxWeightedOscillation
      hρ.continuous hρ.compactSupport hu
      x0 r ε x).integrableOn
  have hIntRight :
      MeasureTheory.IntegrableOn
        (fun z => ρ z * δ) (tsupport ρ) :=
    (integrable_convexApproxKernelMulConst
      hρ.continuous hρ.compactSupport δ).integrableOn
  calc
    |convexApproxSmoothing ρ u x0 r ε x - u x| ≤
        ∫ z in tsupport ρ,
          ρ z *
            |u (convexApproxSample x0 z r ε x) - u x| :=
      abs_convexApproxSmoothing_sub_le_setIntegral_weightedOscillation
        hρ hu x0 r ε x
    _ ≤ ∫ z in tsupport ρ, ρ z * δ := by
      refine MeasureTheory.setIntegral_mono_on
        hIntLeft hIntRight
        (isClosed_tsupport ρ).measurableSet ?_
      intro z hz
      exact
        mul_le_mul_of_nonneg_left
          (hosc z hz) (hρ.nonneg z)
    _ = δ := by
      rw [MeasureTheory.integral_mul_const,
        hρ.setIntegral_one, one_mul]

/-- A modulus bound at the explicit domain scale
`ε * (2 * Classical.choose hU.isBoundedDomain)` controls the smoothing
error. -/
theorem abs_convexApproxSmoothing_sub_le_of_modulus
    {d : ℕ} {U : Set (Vec d)}
    {ρ u : Vec d → ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)
    {x x0 : Vec d} {r ε : ℝ}
    (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) {δ : ℝ}
    (hmod :
      ∀ y ∈ U,
        ‖y - x‖ ≤
            ε *
              (2 *
                Classical.choose hU.isBoundedDomain) →
          |u y - u x| ≤ δ) :
    |convexApproxSmoothing ρ u x0 r ε x - u x| ≤ δ := by
  apply
    abs_convexApproxSmoothing_sub_le_of_pointwiseOscillation
      hρ hu x0 r ε x
  intro z hz
  have hy :=
    convexApproxSample_mem_of_tsupport_subset_closedBall
      hU hx hball hρ.support_subset_closedBall hz
      hr hε0 hε1
  have hdist :=
    norm_convexApproxSample_sub_le_two_mul_choose_of_isOpenBoundedConvexDomain
      hU hx hball hr
      (norm_le_one_of_mem_closedBall_zero_one
        (hρ.support_subset_closedBall hz))
      hε0
  exact hmod _ hy hdist

/-- Uniform continuity on the closure supplies a positive scale that controls
the smoothing error uniformly over the whole domain. -/
theorem
    exists_pos_forall_abs_convexApproxSmoothing_sub_le_of_continuous
    {d : ℕ} {U : Set (Vec d)}
    {ρ u : Vec d → ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0,
      ∀ ⦃x : Vec d⦄, x ∈ U →
        ∀ ⦃ε : ℝ⦄,
          0 ≤ ε →
            ε ≤ 1 →
              ε *
                  (2 *
                    Classical.choose hU.isBoundedDomain) ≤
                η →
                |convexApproxSmoothing
                    ρ u x0 r ε x - u x| ≤
                  δ := by
  have hcompact :
      IsCompact (closure U) :=
    hU.isBoundedDomain.isBounded.isCompact_closure
  have huc :
      UniformContinuousOn u (closure U) :=
    hcompact.uniformContinuousOn_of_continuous
      hu.continuousOn
  rcases
      (Metric.uniformContinuousOn_iff_le.mp huc) δ hδ with
    ⟨η, hηpos, hη⟩
  refine ⟨η, hηpos, ?_⟩
  intro x hx ε hε0 hε1 hεη
  apply
    abs_convexApproxSmoothing_sub_le_of_modulus
      hU hρ hu hx hball hr hε0 hε1
  intro y hy hyx
  have hxcl : x ∈ closure U :=
    subset_closure hx
  have hycl : y ∈ closure U :=
    subset_closure hy
  have hdist :
      dist (u y) (u x) ≤ δ := by
    apply hη y hycl x hxcl
    calc
      dist y x = ‖y - x‖ := by
        simpa only using (dist_eq_norm y x)
      _ ≤ ε *
          (2 *
            Classical.choose hU.isBoundedDomain) :=
        hyx
      _ ≤ η :=
        hεη
  simpa [Real.dist_eq] using hdist


/-- Along any nonnegative scale sequence tending to zero and eventually at
most one, convex approximation converges uniformly on the domain. -/
theorem
    eventually_forall_abs_convexApproxSmoothing_sub_le_of_continuous
    {d : ℕ} {U : Set (Vec d)}
    {ρ u : Vec d → ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r)
    {ε : ℕ → ℝ}
    (hε :
      Filter.Tendsto ε Filter.atTop (nhds 0))
    (hεNonneg :
      ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ ε n)
    (hεLeOne :
      ∀ᶠ n : ℕ in Filter.atTop, ε n ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ ⦃x : Vec d⦄, x ∈ U →
        |convexApproxSmoothing
            ρ u x0 r (ε n) x - u x| ≤
          δ  := by
  have two_mul_choose_isBoundedDomain_nonneg {U : Set (Vec d)} (hU : IsBoundedDomain U) :
      0 ≤ 2 * Classical.choose hU := by
    have hchooseNonneg :
        0 ≤ Classical.choose hU :=
      (Classical.choose_spec hU).1.le
    positivity
  obtain ⟨η, hηpos, hη⟩ :=
    exists_pos_forall_abs_convexApproxSmoothing_sub_le_of_continuous
      hU hρ hu hball hr hδ
  let C : ℝ :=
    2 * Classical.choose hU.isBoundedDomain
  have hCnonneg : 0 ≤ C := by
    simpa only [C] using
      two_mul_choose_isBoundedDomain_nonneg
        hU.isBoundedDomain
  have hscaled :
      Filter.Tendsto
        (fun n => ε n * C)
        Filter.atTop (nhds 0) := by
    simpa using hε.mul_const C
  filter_upwards
      [Metric.tendsto_nhds.mp hscaled η hηpos,
        hεNonneg, hεLeOne] with
    n hn hε0 hε1 x hx
  have hlt : ε n * C < η := by
    have hn' :
        |ε n| * |C| < η := by
      simpa using hn
    simpa only [abs_of_nonneg hε0,
      abs_of_nonneg hCnonneg] using hn'
  exact hη hx hε0 hε1 hlt.le

end PDE

