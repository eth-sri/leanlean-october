module

public import PDEFoundation.Sobolev.W1p.ConvexApprox.PointwiseBounds
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# `L^p` convergence of convex-domain smoothing

This file proves value convergence for convex approximation. Continuous input
is handled first by uniform convergence on the bounded domain. Density of
bounded continuous functions then gives convergence for arbitrary
`MemLpOn U p` input when `1 ≤ p < ∞`.

The final weighted statements show that
`(1 - ε) * convexApproxSmoothing ...` has the same `L^p` limit. This is the
form consumed by the weak-gradient approximation layer.

The classical-input derivative route is deliberately absent: weak derivatives
are handled separately without making that route a dependency of value
convergence.
-/

@[expose] public section

open scoped ENNReal Pointwise Convolution Topology

namespace PDE

open Filter MeasureTheory

variable {d : ℕ} {U : Set (Vec d)} {ρ u : Vec d → ℝ} {p : ENNReal}

/-- Convex approximation of continuous input converges in `L^p` on the
bounded domain for every finite exponent. -/
theorem
    tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_continuous
    
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
  let f  :=
    fun n x =>
      convexApproxSmoothing ρ u x0 r (ε n) x - u x
  let μ : Measure (Vec d) :=
    volumeOn U
  let : IsFiniteMeasure μ :=
    hU.isFiniteMeasure_volumeOn
  have hUMeas  :=
    hU.isOpen.measurableSet
  have hpowTop :
      μ Set.univ ^ (1 / p.toReal) ≠ ∞ := by
    simp
  let cμ  :=
    (μ Set.univ ^ (1 / p.toReal)).toReal
  have hcμNonneg : 0 ≤ cμ :=
    ENNReal.toReal_nonneg
  have hpow :
      ENNReal.ofReal cμ =
        μ Set.univ ^ (1 / p.toReal) := by
    aesop
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  by_cases hηTop : η = ∞
  · simp_all
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
    · aesop
    · simp [hx, hδ.le]
  let g  :=
    Set.indicator U (f n)
  have hsupport : Function.support g ⊆ U := by
    simp [g]
  have hnormIndicatorSub :
      eLpNorm (g - fun _ : Vec d => (0))
          p volume ≤
        ENNReal.ofReal δ *
          volume U ^ (1 / p.toReal) := by
    exact
      eLpNorm_sub_le_of_dist_bdd
        (μ := volume) (p := p) (s := U)
        hp hUMeas.nullMeasurableSet hδ.le
        (((((continuous_convexApproxSmoothing hρ.continuous
          hρ.compactSupport hu x0 r _).sub hu).measurable.indicator
            hUMeas).sub measurable_const).aestronglyMeasurable)
        hdist hsupport
        (by
          simp)
  have hsubZero :
      (g - fun _ : Vec d => (0)) = g := by
    aesop
  have hnormIndicator :
      eLpNorm g p volume ≤
        ENNReal.ofReal δ *
          volume U ^ (1 / p.toReal) := by
    simp_all
  have hnorm :
      eLpNorm (f n) p μ ≤
        ENNReal.ofReal δ *
          μ Set.univ ^ (1 / p.toReal) := by
    calc
      eLpNorm _ p μ =
          eLpNorm g p volume := by
        symm
        simpa using
          (eLpNorm_indicator_eq_eLpNorm_restrict
            (μ := volume) (p := p) (f := f n) hUMeas)
      _ ≤
          ENNReal.ofReal δ *
            volume U ^ (1 / p.toReal) :=
        hnormIndicator
      _ =
          ENNReal.ofReal δ *
            μ Set.univ ^ (1 / p.toReal) := by
        aesop
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
        ring
      _ ≤ η.toReal * 1 :=
        mul_le_mul_of_nonneg_left hfrac hηReal.le
      _ = η.toReal := by
        ring
  calc
    eLpNorm _ p μ ≤
        ENNReal.ofReal δ *
          μ Set.univ ^ (1 / p.toReal) :=
      hnorm
    _ = ENNReal.ofReal _ := by
      rw [← hpow, ← ENNReal.ofReal_mul]
      linarith
    _ ≤ η := by
      rw [← ENNReal.ofReal_toReal hηTop]
      exact ENNReal.ofReal_le_ofReal hδMul

/-- Convex approximation converges in `L^p` for every finite exponent
`p ≥ 1` and every `MemLpOn` input. -/
theorem
    tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn
    
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
  · simp_all
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
  have hCZero : C ≠ 0 :=
    hCPos.ne'
  have hCTop : C ≠ ∞ := by
    aesop
  let δ : ENNReal :=
    min η₂ (η₁ / C)
  have hδPos : 0 < δ := by
    aesop
  have huMem : MemLp u p μ := by
    omega
  obtain ⟨g, happrox, hgMem⟩ :=
    huMem.exists_boundedContinuous_eLpNorm_sub_le
      hpTop (ε := δ) hδPos.ne'
  have hthirdNorm :
      eLpNorm
          (fun x => (g : Vec d → ℝ) x - u x)
          p μ ≤
        η₂ := by
    calc
      eLpNorm
          _
          p μ =
        eLpNorm
          _
          p μ := by
        exact
          eLpNorm_sub_comm
            _ u p μ
      _ ≤ δ :=
        happrox
      _ ≤ η₂ :=
        min_le_left _ _
  have hmiddleTendsto :
      Tendsto
        (fun n : ℕ =>
          eLpNorm
            (fun x =>
              convexApproxSmoothing ρ
                  (g : Vec d → ℝ) x0 r (ε n) x -
                g x)
            p μ)
        atTop (𝓝 0) :=
    tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_continuous
      hU hρ hpTop g.continuous hball hr.le
      hε hεNonneg hεLeOne
  have hmiddleEventually :
      ∀ᶠ n : ℕ in atTop,
        eLpNorm
            (fun x =>
              convexApproxSmoothing ρ
                  (g : Vec d → ℝ) x0 r (ε n) x -
                g x)
            p μ ≤
          η₂ :=
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
          (1 / 2) ≤ 1 - ε n := by
        linarith
      have hpow :
          (1 / 2) ^ d ≤ (1 - ε n) ^ d :=
        pow_le_pow_left₀ (by positivity) hhalf d
      have hpowPos : 0 < (1 / 2 : ℝ) ^ d := by
        positivity
      have hinv :
          ((1 - ε n) ^ d)⁻¹ ≤
            ((1 / 2) ^ d)⁻¹ := by
        simpa using
          one_div_le_one_div_of_le hpowPos hpow
      have hofReal  :=
        ENNReal.ofReal_le_ofReal hinv
      exact
        ENNReal.rpow_le_rpow hofReal (by positivity)
    have hεnOne : ε n < 1 := by
      linarith
    have happrox' :
        eLpNorm
            (fun x => u x - g x)
            p μ ≤
          δ :=
      happrox
    calc
      eLpNorm
          _
          p μ ≤
        ENNReal.ofReal _ ^
            (1 / p).toReal *
          eLpNorm
            _
            p μ := by
        exact
          eLpNorm_sub_convexApproxSmoothing_le
            hU hρ hpOne hpTop hu hgMem
            hball hr hεnPos hεnOne
      _ ≤
          ENNReal.ofReal _ ^
              (1 / p).toReal *
            δ := by
        gcongr
      _ ≤ C * δ := by
        gcongr
      _ ≤ C * (η₁ / C) := by
        gcongr
        grind
      _ = η₁ := by
        rw [ENNReal.mul_div_cancel hCZero hCTop]
  filter_upwards
    [hεPos, hεHalf, hfirstEventually,
      hcomboEventually] with
    n hεnPos hεnHalf hfirst hcombo
  let F  :=
    fun x =>
      convexApproxSmoothing ρ u x0 r (ε n) x -
        convexApproxSmoothing ρ
          g x0 r (ε n) x
  let G  :=
    fun x =>
      (convexApproxSmoothing ρ
            g x0 r (ε n) x -
          g x) +
        (g x - u x)
  have hsum :
      eLpNorm (F + G) p μ < η :=
    hη₁ _ _ hfirst hcombo.le
  have hdecomposition :
      eLpNorm
          (fun x =>
            convexApproxSmoothing ρ u x0 r (ε n) x - u x)
          p μ =
        eLpNorm (F + G) p μ := by
    apply eLpNorm_congr_ae
    filter_upwards with x
    aesop
  grind

/-- The affine derivative weight `1 - ε` does not change the `L^p` limit of
convex approximation. -/
theorem
    tendsto_eLpNorm_sub_zero_one_sub_mul_convexApproxSmoothing_of_memLpOn
    
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
  · simp_all
  obtain ⟨η₁, hη₁Pos, hη₁⟩ :=
    exists_Lp_half
      (μ := μ) (ε := ℝ) (p := p) hη.ne'
  have hvalueTendsto :
      Tendsto
        (fun n : ℕ =>
          eLpNorm
            (fun x =>
              convexApproxSmoothing ρ u x0 r (ε n) x - u x)
            p μ)
        atTop (𝓝 0) :=
    tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn
      hU hρ hpOne hpTop hu hball hr
      hε hεPos hεOne
  have hvalueEventually :
      ∀ᶠ n : ℕ in atTop,
        eLpNorm
            (fun x =>
              convexApproxSmoothing ρ u x0 r (ε n) x - u x)
            p μ ≤
          η₁ :=
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
    aesop
  have huMem : MemLp u p μ := by
    omega
  have hBTop : B ≠ ∞ := by
    exact
      ENNReal.mul_ne_top hCTop huMem.eLpNorm_ne_top
  let M : ℝ :=
    B.toReal
  have hM :
      ENNReal.ofReal M = B := ENNReal.ofReal_toReal hBTop
  have hscaledTendsto :
      Tendsto
        (fun n : ℕ => |ε n| * M)
        atTop (𝓝 0) := by
    simpa using
      hε.norm.mul_const M
  have hsmallTendsto :
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal (|ε n| * M))
        atTop (𝓝 0) := by
    simpa using
      ENNReal.tendsto_ofReal hscaledTendsto
  have hsmallEventually :
      ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (|ε n| * M) ≤ η₁ :=
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
          (1 / 2) ≤ 1 - ε n := by
        linarith
      have hpow :
          (1 / 2) ^ d ≤ (1 - ε n) ^ d :=
        pow_le_pow_left₀ (by positivity) hhalf d
      have hpowPos : 0 < (1 / 2 : ℝ) ^ d := by
        positivity
      have hinv :
          ((1 - ε n) ^ d)⁻¹ ≤
            ((1 / 2) ^ d)⁻¹ := by
        simpa using
          one_div_le_one_div_of_le hpowPos hpow
      have hofReal :
          ENNReal.ofReal (((1 - ε n) ^ d)⁻¹) ≤
            ENNReal.ofReal (((1 / 2) ^ d)⁻¹) :=
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
        simp_all
      _ ≤ η₁ :=
        hsmall
  have hsum :
      eLpNorm (F + G) p μ < η :=
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
    dsimp only [Pi.add_apply]
    ring
  grind

/-- The unit convex-approximation sequence converges in `L^p` for arbitrary
`MemLpOn` input. -/
theorem
    tendsto_eLpNorm_sub_zero_unitConvexApproxSequence_of_memLpOn
    
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
        (d := d))
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
        (d := d))
      hpOne hpTop hu hball hr
      tendsto_unitConvexApproxScale_zero
      (Eventually.of_forall fun n => by
        exact unitConvexApproxScale_pos n)
      (((tendsto_order.1
        tendsto_unitConvexApproxScale_zero).2
          1 zero_lt_one).mono fun _ hn => hn))

end PDE
