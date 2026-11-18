module

public import PDEFoundation.Sobolev.W1p.ConvexApprox.PointwiseBounds
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import PDEFoundation.Measure.FiniteVectorConvergence
public import PDEFoundation.Measure.LpTendsto
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Sobolev.W1p.EuclideanGradient
public import PDEFoundation.Sobolev.W1p.Mean
public import PDEFoundation.Sobolev.W1p.Smooth

@[expose] public noncomputable section

namespace PDE
open Filter MeasureTheory
open scoped ENNReal Pointwise Convolution Topology


/-- Convex approximation of continuous input converges in `L^p` on the
bounded domain for every finite exponent. -/
theorem
    tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_continuous
    {d : ℕ} {U : Set (Vec d)}
    {ρ u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ) (hp : p ≠ ∞)
    (hu : Continuous u)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r)
    {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hεNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ ε n)
    (hεOne : ∀ᶠ n : ℕ in atTop, ε n ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        eLpNorm
          (fun x =>
            convexApproxSmoothing ρ u x0 r (ε n) x - u x)
          p (volumeOn U))
      atTop (𝓝 0) := by
  let f : ℕ → Vec d → ℝ :=
    fun n x =>
      convexApproxSmoothing ρ u x0 r (ε n) x - u x
  let μ : Measure (Vec d) :=
    volumeOn U
  let : IsFiniteMeasure μ :=
    hU.isFiniteMeasure_volumeOn
  have hUMeas :=
    hU.isOpen.measurableSet
  have hpowTop :
      μ Set.univ ^ (1 / p.toReal) ≠ ∞ := by
    refine
      (ENNReal.rpow_lt_top_of_nonneg
        (by positivity) ?_).ne
    exact (measure_lt_top μ Set.univ).ne
  let cμ : ℝ :=
    (μ Set.univ ^ (1 / p.toReal)).toReal
  have hcμNonneg : 0 ≤ cμ :=
    ENNReal.toReal_nonneg
  have hpow :
      ENNReal.ofReal cμ =
        μ Set.univ ^ (1 / p.toReal) := by
    exact ENNReal.ofReal_toReal hpowTop
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  by_cases hηTop : η = ∞
  · exact
      Eventually.of_forall fun n => by
        simp only [hηTop, le_top]
  let δ : ℝ :=
    η.toReal / (cμ + 1)
  have hηReal : 0 < η.toReal :=
    ENNReal.toReal_pos hη.ne' hηTop
  have hδ : 0 < δ := by
    positivity
  filter_upwards
    [eventually_forall_abs_convexApproxSmoothing_sub_le_of_continuous
      hU hρ hu hball hr hε hεNonneg hεOne hδ] with n hn
  have hdist :
      ∀ x,
        dist (Set.indicator U (f n) x) 0 ≤ δ := by
    intro x
    by_cases hx : x ∈ U
    · simpa [f, hx, Real.dist_eq] using hn hx
    · simp [hx, δ, hδ.le]
  let g :=
    Set.indicator U (f n)
  have hsupport : Function.support g ⊆ U := by
    simp [g]
  have hnormIndicatorSub :
      eLpNorm (g - fun _ => 0)
          p volume ≤
        ENNReal.ofReal δ *
          volume U ^ (1 / p.toReal) := by
    exact
      eLpNorm_sub_le_of_dist_bdd
        (μ := volume)
        hp hUMeas.nullMeasurableSet hδ.le
        (((((continuous_convexApproxSmoothing hρ.continuous
          hρ.compactSupport hu x0 r (ε n)).sub hu).measurable.indicator
            hUMeas).sub measurable_const).aestronglyMeasurable)
        hdist hsupport
        (by
          intro x hx
          exact (hx rfl).elim)
  have hsubZero :
      (g - fun _ => 0) = g := by
    ext x
    simp
  have hnormIndicator :
      eLpNorm g p volume ≤
        ENNReal.ofReal δ *
          volume U ^ (1 / p.toReal) := by
    rw [← hsubZero]
    exact hnormIndicatorSub
  have hnorm :
      eLpNorm (f n) p μ ≤
        ENNReal.ofReal δ *
          μ Set.univ ^ (1 / p.toReal) := by
    calc
      eLpNorm (f n) p μ =
          eLpNorm g p volume := by
        symm
        simpa using
          (eLpNorm_indicator_eq_eLpNorm_restrict
            (μ := volume) hUMeas)
      _ ≤
          ENNReal.ofReal δ *
            volume U ^ (1 / p.toReal) :=
        hnormIndicator
      _ =
          ENNReal.ofReal δ *
            μ Set.univ ^ (1 / p.toReal) := by
        simp only [μ, volumeOn,
          Measure.restrict_apply_univ]
  have hδMul : δ * cμ ≤ η.toReal := by
    have hfrac :
        cμ / (cμ + 1) ≤ 1 := by
      have hcμ : cμ ≤ cμ + 1 := by
        linarith
      have hdenom : 0 ≤ cμ + 1 := by
        linarith
      simpa only using
        div_le_one_of_le₀ hcμ hdenom
    calc
      δ * cμ =
          η.toReal * (cμ / (cμ + 1)) := by
        dsimp only [δ]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      _ ≤ η.toReal * 1 :=
        mul_le_mul_of_nonneg_left hfrac hηReal.le
      _ = η.toReal := by
        ring
  calc
    eLpNorm (f n) p μ ≤
        ENNReal.ofReal δ *
          μ Set.univ ^ (1 / p.toReal) :=
      hnorm
    _ = ENNReal.ofReal (δ * cμ) := by
      rw [← hpow, ← ENNReal.ofReal_mul]
      exact hδ.le
    _ ≤ η := by
      rw [← ENNReal.ofReal_toReal hηTop]
      exact ENNReal.ofReal_le_ofReal hδMul

/-- Convex approximation converges in `L^p` for every finite exponent
`p ≥ 1` and every `MemLpOn` input. -/
theorem
    tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn
    {d : ℕ} {U : Set (Vec d)}
    {ρ u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ)
    (hpOne : 1 ≤ p) (hpTop : p ≠ ∞)
    (hu : MemLpOn U p u)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r)
    {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hεPos : ∀ᶠ n : ℕ in atTop, 0 < ε n)
    (hεOne : ∀ᶠ n : ℕ in atTop, ε n < 1) :
    Tendsto
      (fun n : ℕ =>
        eLpNorm
          (fun x =>
            convexApproxSmoothing ρ u x0 r (ε n) x - u x)
          p (volumeOn U))
      atTop (𝓝 0) := by
  let μ : Measure (Vec d) :=
    volumeOn U
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  by_cases hηTop : η = ∞
  · exact
      Eventually.of_forall fun n => by
        simp only [hηTop, le_top]
  obtain ⟨η₁, hη₁Pos, hη₁⟩ :=
    exists_Lp_half
      (μ := μ) (ε := ℝ) (p := p) hη.ne'
  obtain ⟨η₂, hη₂Pos, hη₂⟩ :=
    exists_Lp_half
      (μ := μ) (ε := ℝ) (p := p) hη₁Pos.ne'
  have hεNonneg :
      ∀ᶠ n : ℕ in atTop, 0 ≤ ε n :=
    hεPos.mono fun _ hn => hn.le
  have hεLeOne :
      ∀ᶠ n : ℕ in atTop, ε n ≤ 1 :=
    hεOne.mono fun _ hn => hn.le
  have hεHalf :
      ∀ᶠ n : ℕ in atTop, ε n < (1 / 2 : ℝ) :=
    (tendsto_order.1 hε).2 _ (by positivity)
  let C : ENNReal :=
    ENNReal.ofReal (((1 / 2 : ℝ) ^ d)⁻¹) ^
      (1 / p).toReal
  have hCPos : 0 < C := by
    positivity
  have hCZero :=
    hCPos.ne'
  have hCTop : C ≠ ∞ := by
    exact
      (ENNReal.rpow_lt_top_of_nonneg
        (by positivity) ENNReal.ofReal_ne_top).ne
  let δ : ENNReal :=
    min η₂ (η₁ / C)
  have hδPos : 0 < δ := by
    have hquotient :=
      ENNReal.div_pos hη₁Pos.ne' hCTop
    exact lt_min hη₂Pos hquotient
  have huMem : MemLp u p μ := by
    simpa using hu
  obtain ⟨g, happrox, hgMem⟩ :=
    huMem.exists_boundedContinuous_eLpNorm_sub_le
      hpTop (ε := δ) hδPos.ne'
  have hthirdMem :=
    hgMem.sub huMem
  have hthirdNorm :
      eLpNorm
          (fun x => (g : Vec d → ℝ) x - u x)
          p μ ≤
        η₂ := by
    calc
      eLpNorm
          (fun x => (g : Vec d → ℝ) x - u x)
          p μ =
        eLpNorm
          (fun x => u x - (g : Vec d → ℝ) x)
          p μ := by
        exact
          eLpNorm_sub_comm
            (g : Vec d → ℝ) u p μ
      _ ≤ δ :=
        happrox
      _ ≤ η₂ :=
        min_le_left _ _
  have hmiddleTendsto :=
    tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_continuous
      hU hρ hpTop g.continuous hball hr.le
      hε hεNonneg hεLeOne
  have hmiddleEventually :=
    ENNReal.tendsto_nhds_zero.1
      hmiddleTendsto η₂ hη₂Pos
  have hcomboEventually :
      ∀ᶠ n : ℕ in atTop,
        eLpNorm
            (fun x =>
              (convexApproxSmoothing ρ
                    (g : Vec d → ℝ) x0 r (ε n) x -
                  g x) +
                ((g : Vec d → ℝ) x - u x))
            p μ <
          η₁ := by
    filter_upwards [hmiddleEventually] with n hmiddle
    exact
      hη₂ _ _ hmiddle hthirdNorm
  have hfirstEventually :
      ∀ᶠ n : ℕ in atTop,
        eLpNorm
            (fun x =>
              convexApproxSmoothing ρ u x0 r (ε n) x -
                convexApproxSmoothing ρ
                  (g : Vec d → ℝ) x0 r (ε n) x)
            p μ ≤
          η₁ := by
    filter_upwards [hεPos, hεHalf] with
      n hεnPos hεnHalf
    have hfactor :
        ENNReal.ofReal (((1 - ε n) ^ d)⁻¹) ^
            (1 / p).toReal ≤
          C := by
      have hhalf :
          (1 / 2 : ℝ) ≤ 1 - ε n := by
        linarith
      have hpow :=
        pow_le_pow_left₀ (by positivity) hhalf d
      have hpowPos : 0 < (1 / 2 : ℝ) ^ d := by
        positivity
      have hinv :
          ((1 - ε n) ^ d)⁻¹ ≤
            ((1 / 2 : ℝ) ^ d)⁻¹ := by
        simpa using
          one_div_le_one_div_of_le hpowPos hpow
      have hofReal :=
        ENNReal.ofReal_le_ofReal hinv
      exact
        ENNReal.rpow_le_rpow hofReal (by positivity)
    have hεnOne : ε n < 1 := by
      linarith
    have happrox' :
        eLpNorm
            (fun x => u x - (g : Vec d → ℝ) x)
            p μ ≤
          δ :=
      happrox
    calc
      eLpNorm
          (fun x =>
            convexApproxSmoothing ρ u x0 r (ε n) x -
              convexApproxSmoothing ρ
                (g : Vec d → ℝ) x0 r (ε n) x)
          p μ ≤
        ENNReal.ofReal (((1 - ε n) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm
            (fun x => u x - (g : Vec d → ℝ) x)
            p μ := by
        exact
          eLpNorm_sub_convexApproxSmoothing_le
            hU hρ hpOne hpTop hu hgMem
            hball hr hεnPos hεnOne
      _ ≤
          ENNReal.ofReal (((1 - ε n) ^ d)⁻¹) ^
              (1 / p).toReal *
            δ := by
        gcongr
      _ ≤ C * δ := by
        gcongr
      _ ≤ C * (η₁ / C) := by
        gcongr
        exact min_le_right _ _
      _ = η₁ := by
        rw [ENNReal.mul_div_cancel hCZero hCTop]
  filter_upwards
    [hεPos, hεHalf, hfirstEventually,
      hcomboEventually] with
    n hεnPos hεnHalf hfirst hcombo
  let F : Vec d → ℝ :=
    fun x =>
      convexApproxSmoothing ρ u x0 r (ε n) x -
        convexApproxSmoothing ρ
          (g : Vec d → ℝ) x0 r (ε n) x
  let G : Vec d → ℝ :=
    fun x =>
      (convexApproxSmoothing ρ
            (g : Vec d → ℝ) x0 r (ε n) x -
          g x) +
        ((g : Vec d → ℝ) x - u x)
  have hεnOne : ε n < 1 := by
    linarith
  have hsum :=
    hη₁ _ _ hfirst hcombo.le
  have hdecomposition :
      eLpNorm
          (fun x =>
            convexApproxSmoothing ρ u x0 r (ε n) x - u x)
          p μ =
        eLpNorm (F + G) p μ := by
    apply eLpNorm_congr_ae
    filter_upwards with x
    dsimp only [F, G, Pi.add_apply]
    ring
  calc
    eLpNorm
        (fun x =>
          convexApproxSmoothing ρ u x0 r (ε n) x - u x)
        p μ =
      eLpNorm (F + G) p μ :=
        hdecomposition
    _ ≤ η :=
      hsum.le

/-- The affine derivative weight `1 - ε` does not change the `L^p` limit of
convex approximation. -/
theorem
    tendsto_eLpNorm_sub_zero_one_sub_mul_convexApproxSmoothing_of_memLpOn
    {d : ℕ} {U : Set (Vec d)}
    {ρ u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ)
    (hpOne : 1 ≤ p) (hpTop : p ≠ ∞)
    (hu : MemLpOn U p u)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r)
    {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hεPos : ∀ᶠ n : ℕ in atTop, 0 < ε n)
    (hεOne : ∀ᶠ n : ℕ in atTop, ε n < 1) :
    Tendsto
      (fun n : ℕ =>
        eLpNorm
          (fun x =>
            (1 - ε n) *
                convexApproxSmoothing ρ u x0 r (ε n) x -
              u x)
          p (volumeOn U))
      atTop (𝓝 0) := by
  let μ : Measure (Vec d) :=
    volumeOn U
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  by_cases hηTop : η = ∞
  · exact
      Eventually.of_forall fun n => by
        simp only [hηTop, le_top]
  obtain ⟨η₁, hη₁Pos, hη₁⟩ :=
    exists_Lp_half
      (μ := μ) (ε := ℝ) (p := p) hη.ne'
  have hvalueTendsto :=
    tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn
      hU hρ hpOne hpTop hu hball hr
      hε hεPos hεOne
  have hvalueEventually :=
    ENNReal.tendsto_nhds_zero.1
      hvalueTendsto η₁ hη₁Pos
  have hεHalf :
      ∀ᶠ n : ℕ in atTop, ε n < (1 / 2 : ℝ) :=
    (tendsto_order.1 hε).2 _ (by positivity)
  let C : ENNReal :=
    ENNReal.ofReal (((1 / 2 : ℝ) ^ d)⁻¹) ^
      (1 / p).toReal
  let B : ENNReal :=
    C * eLpNorm u p μ
  have hCTop : C ≠ ∞ := by
    exact
      (ENNReal.rpow_lt_top_of_nonneg
        (by positivity) ENNReal.ofReal_ne_top).ne
  have huMem : MemLp u p μ := by
    simpa using hu
  have hBTop : B ≠ ∞ := by
    exact
      ENNReal.mul_ne_top hCTop huMem.eLpNorm_ne_top
  let M : ℝ :=
    B.toReal
  have hM :
      ENNReal.ofReal M = B := by
    exact ENNReal.ofReal_toReal hBTop
  have hscaledTendsto :
      Tendsto
        (fun n => |ε n| * M)
        atTop (𝓝 0) := by
    simpa using
      hε.norm.mul_const M
  have hsmallTendsto :
      Tendsto
        (fun n =>
          ENNReal.ofReal (|ε n| * M))
        atTop (𝓝 0) := by
    simpa using
      ENNReal.tendsto_ofReal hscaledTendsto
  have hsmallEventually :=
    ENNReal.tendsto_nhds_zero.1
      hsmallTendsto η₁ hη₁Pos
  have hconvBoundEventually :
      ∀ᶠ n : ℕ in atTop,
        eLpNorm
            (convexApproxSmoothing ρ u x0 r (ε n))
            p μ ≤
          B := by
    filter_upwards [hεPos, hεHalf] with
      n hεnPos hεnHalf
    have hfactor :
        ENNReal.ofReal (((1 - ε n) ^ d)⁻¹) ^
            (1 / p).toReal ≤
          C := by
      have hhalf :
          (1 / 2 : ℝ) ≤ 1 - ε n := by
        linarith
      have hpow :=
        pow_le_pow_left₀ (by positivity) hhalf d
      have hpowPos : 0 < (1 / 2 : ℝ) ^ d := by
        positivity
      have hinv :
          ((1 - ε n) ^ d)⁻¹ ≤
            ((1 / 2 : ℝ) ^ d)⁻¹ := by
        simpa using
          one_div_le_one_div_of_le hpowPos hpow
      have hofReal :=
        ENNReal.ofReal_le_ofReal hinv
      exact
        ENNReal.rpow_le_rpow hofReal (by positivity)
    have hεnOne : ε n < 1 := by
      linarith
    calc
      eLpNorm
          (convexApproxSmoothing ρ u x0 r (ε n))
          p μ ≤
        ENNReal.ofReal (((1 - ε n) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm u p μ :=
        eLpNorm_convexApproxSmoothing_le
          hU hρ hpOne hpTop hu hball
          hr hεnPos hεnOne
      _ ≤ C * eLpNorm u p μ := by
        gcongr
      _ = B :=
        rfl
  filter_upwards
    [hvalueEventually, hconvBoundEventually,
      hsmallEventually, hεPos, hεHalf] with
    n hvalue hconvBound hsmall hεnPos hεnHalf
  let F : Vec d → ℝ :=
    fun x =>
      convexApproxSmoothing ρ u x0 r (ε n) x - u x
  let G : Vec d → ℝ :=
    fun x =>
      (-ε n) *
        convexApproxSmoothing ρ u x0 r (ε n) x
  have hεnOne : ε n < 1 := by
    linarith
  have hGNorm :
      eLpNorm G p μ ≤ η₁ := by
    calc
      eLpNorm G p μ =
          ENNReal.ofReal |ε n| *
            eLpNorm
              (convexApproxSmoothing ρ u x0 r (ε n))
              p μ := by
        change
          eLpNorm
              ((-ε n) •
                convexApproxSmoothing ρ u x0 r (ε n))
              p μ =
            ENNReal.ofReal |ε n| *
              eLpNorm
                (convexApproxSmoothing ρ u x0 r (ε n))
                p μ
        simpa only [Real.enorm_eq_ofReal_abs, abs_neg] using
          (eLpNorm_const_smul
            (-ε n)
            (convexApproxSmoothing ρ u x0 r (ε n))
            p μ)
      _ ≤ ENNReal.ofReal |ε n| * B := by
        gcongr
      _ = ENNReal.ofReal (|ε n| * M) := by
        rw [← hM, ← ENNReal.ofReal_mul]
        exact abs_nonneg _
      _ ≤ η₁ :=
        hsmall
  have hsum :=
    hη₁ _ _ hvalue hGNorm
  have hdecomposition :
      eLpNorm
          (fun x =>
            (1 - ε n) *
                convexApproxSmoothing ρ u x0 r (ε n) x -
              u x)
          p μ =
        eLpNorm (F + G) p μ := by
    apply eLpNorm_congr_ae
    filter_upwards with x
    dsimp only [F, G, Pi.add_apply]
    ring
  calc
    eLpNorm
        (fun x =>
          (1 - ε n) *
              convexApproxSmoothing ρ u x0 r (ε n) x -
            u x)
        p μ =
      eLpNorm (F + G) p μ :=
        hdecomposition
    _ ≤ η :=
      hsum.le

/-- The unit convex-approximation sequence converges in `L^p` for arbitrary
`MemLpOn` input. -/
theorem
    tendsto_eLpNorm_sub_zero_unitConvexApproxSequence_of_memLpOn
    {d : ℕ} {U : Set (Vec d)}
    {u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U)
    (hpOne : 1 ≤ p) (hpTop : p ≠ ∞)
    (hu : MemLpOn U p u)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) :
    Tendsto
      (fun n : ℕ =>
        eLpNorm
          (fun x =>
            unitConvexApproxSequence u x0 r n x - u x)
          p (volumeOn U))
      atTop (𝓝 0) := by
  simpa only [unitConvexApproxSequence] using
    (tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn
      hU
      (isConvexApproxKernel_unitConvexApproxKernel
)
      hpOne hpTop hu hball hr
      tendsto_unitConvexApproxScale_zero
      (Eventually.of_forall fun n => by
        exact unitConvexApproxScale_pos n)
      (((tendsto_order.1
        tendsto_unitConvexApproxScale_zero).2
          1 zero_lt_one).mono fun _ hn => hn))

/-- The affine-weighted unit convex-approximation sequence converges in
`L^p`; this is the form used for smoothed weak gradients. -/
theorem
    tendsto_eLpNorm_sub_zero_one_sub_mul_unitConvexApproxSequence_of_memLpOn
    {d : ℕ} {U : Set (Vec d)}
    {u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U)
    (hpOne : 1 ≤ p) (hpTop : p ≠ ∞)
    (hu : MemLpOn U p u)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) :
    Tendsto
      (fun n : ℕ =>
        eLpNorm
          (fun x =>
            (1 - unitConvexApproxScale n) *
                unitConvexApproxSequence u x0 r n x -
              u x)
          p (volumeOn U))
      atTop (𝓝 0) := by
  simpa only [unitConvexApproxSequence] using
    (tendsto_eLpNorm_sub_zero_one_sub_mul_convexApproxSmoothing_of_memLpOn
      hU
      (isConvexApproxKernel_unitConvexApproxKernel
)
      hpOne hpTop hu hball hr
      tendsto_unitConvexApproxScale_zero
      (Eventually.of_forall fun n => by
        exact unitConvexApproxScale_pos n)
      (((tendsto_order.1
        tendsto_unitConvexApproxScale_zero).2
          1 zero_lt_one).mono fun _ hn => hn))



namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

/-- The smooth `W^{1,p}` representative obtained from the standard convex
approximation kernel and scale. -/
noncomputable def convexApproxSmoothW1p
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (u : W1pFunction U p)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r)
    (n : ℕ) : W1pFunction U p :=
  W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU
    ((contDiff_convexApproxSmoothRepresentative
      (U := U)
      (ρ := unitConvexApproxKernel (d := d))
      (u := u.toFun) (p := p)
      (x0 := x0) (r := r)
      (ε := unitConvexApproxScale n)
      hU.measurableSet
      (isConvexApproxKernel_unitConvexApproxKernel
        (d := d))
      hp u.memLp hr
      (unitConvexApproxScale_pos n)).of_le (by simp))

@[simp]
theorem convexApproxSmoothW1p_toFun
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (u : W1pFunction U p)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r)
    (n : ℕ) :
    (convexApproxSmoothW1p hU hp u x0 hr n).toFun =
      convexApproxSmoothRepresentative U
        (unitConvexApproxKernel (d := d))
        u.toFun x0 r (unitConvexApproxScale n) :=
  rfl

@[simp]
theorem convexApproxSmoothW1p_grad
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (u : W1pFunction U p)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r)
    (n : ℕ) :
    (convexApproxSmoothW1p hU hp u x0 hr n).grad =
      classicalGradient
        (convexApproxSmoothRepresentative U
          (unitConvexApproxKernel (d := d))
          u.toFun x0 r (unitConvexApproxScale n)) :=
  rfl

@[simp]
theorem convexApproxSmoothW1p_grad_apply
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (u : W1pFunction U p)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r)
    (n : ℕ) (x : Vec d) (i : Fin d) :
    (convexApproxSmoothW1p hU hp u x0 hr n).grad x i =
      (fderiv ℝ
        (convexApproxSmoothRepresentative U
          (unitConvexApproxKernel (d := d))
          u.toFun x0 r (unitConvexApproxScale n)) x)
        (basisVec i) := by
  rw [convexApproxSmoothW1p_grad,
    classicalGradient_apply]

/-- Every member of the convex approximation sequence has a globally smooth
value representative. -/
theorem contDiff_convexApproxSmoothW1p_toFun
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (u : W1pFunction U p)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r)
    (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (convexApproxSmoothW1p hU hp u x0 hr n).toFun := by
  rw [convexApproxSmoothW1p_toFun]
  exact
    contDiff_convexApproxSmoothRepresentative
      hU.measurableSet
      (isConvexApproxKernel_unitConvexApproxKernel
)
      hp u.memLp hr (unitConvexApproxScale_pos n)

/-- The values of the smooth convex approximants converge in
`L^p(U)` for every finite `p ≥ 1`. -/
theorem tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) :
    Tendsto
      (fun n =>
        eLpNorm
          (fun x =>
            (convexApproxSmoothW1p hU hp u x0 hr n).toFun x -
              u.toFun x)
          p (volumeOn U))
      atTop (𝓝 0) := by
  let ρ : Vec d → ℝ :=
    unitConvexApproxKernel
  have hρ : IsConvexApproxKernel ρ := by
    simpa only [ρ] using
      isConvexApproxKernel_unitConvexApproxKernel

  have hScaleOne :=
    (((tendsto_order.1
      tendsto_unitConvexApproxScale_zero).2
        1 zero_lt_one).mono fun _ hn => hn)
  have hRaw :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x =>
              convexApproxSmoothing ρ u.toFun x0 r
                  (unitConvexApproxScale n) x -
                u.toFun x)
            p (volumeOn U))
        atTop (𝓝 0) := by
    simpa only [ρ, unitConvexApproxSequence] using
      tendsto_eLpNorm_sub_zero_unitConvexApproxSequence_of_memLpOn
        hU hp hpTop u.memLp hball hr
  have hRepresentative :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x =>
              convexApproxSmoothRepresentative U ρ u.toFun
                  x0 r (unitConvexApproxScale n) x -
                u.toFun x)
            p (volumeOn U))
        atTop (𝓝 0) := by
    refine hRaw.congr' ?_
    filter_upwards [hScaleOne] with n hScale
    apply eLpNorm_congr_ae
    filter_upwards
      [ae_restrict_mem hU.measurableSet] with x hx
    rw [
      convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
 hU hρ hx hball hr
        (unitConvexApproxScale_pos n) hScale]
  simpa only [convexApproxSmoothW1p_toFun, ρ] using
    hRepresentative

/-- Every coordinate of the weak gradient of the smooth convex approximants
converges in `L^p(U)`. -/
theorem tendsto_convexApproxSmoothW1p_grad_coord_eLpNorm_sub
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (i : Fin d) :
    Tendsto
      (fun n =>
        eLpNorm
          (fun x =>
            (convexApproxSmoothW1p hU hp u x0 hr n).grad x i -
              u.grad x i)
          p (volumeOn U))
      atTop (𝓝 0) := by
  let ρ : Vec d → ℝ :=
    unitConvexApproxKernel
  have hρ : IsConvexApproxKernel ρ := by
    simpa only [ρ] using
      isConvexApproxKernel_unitConvexApproxKernel

  have hScaleOne :=
    (((tendsto_order.1
      tendsto_unitConvexApproxScale_zero).2
        1 zero_lt_one).mono fun _ hn => hn)
  have hRaw :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x =>
              (1 - unitConvexApproxScale n) *
                  convexApproxSmoothing ρ
                    (fun y => u.grad y i)
                    x0 r (unitConvexApproxScale n) x -
                u.grad x i)
            p (volumeOn U))
        atTop (𝓝 0) := by
    simpa only [ρ, unitConvexApproxSequence] using
      tendsto_eLpNorm_sub_zero_one_sub_mul_unitConvexApproxSequence_of_memLpOn
        hU hp hpTop (u.grad_memLp i) hball hr
  have hRepresentative :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x =>
              (fderiv ℝ
                (convexApproxSmoothRepresentative U ρ u.toFun
                  x0 r (unitConvexApproxScale n)) x)
                  (basisVec i) -
                u.grad x i)
            p (volumeOn U))
        atTop (𝓝 0) := by
    refine hRaw.congr' ?_
    filter_upwards [hScaleOne] with n hScale
    apply eLpNorm_congr_ae
    have hBridge :=
      ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec
        (U := U) (ρ := ρ)


        hU hρ hp u.memLp (u.grad_memLp i)
        (u.hasWeakPartialDerivOn i)
        hball hr (unitConvexApproxScale_pos n) hScale
    filter_upwards
      [hBridge, ae_restrict_mem hU.measurableSet] with
      x hxBridge hxU
    rw [hxBridge]
    rw [
      convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem

        hU hρ hxU hball hr
        (unitConvexApproxScale_pos n) hScale]
  simpa only [convexApproxSmoothW1p_grad_apply, ρ] using
    hRepresentative










end W1pFunction

end PDE

