module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Tactic.NormNum



/-!
# Convergence consequences of `L^p` convergence

This file provides measure-generic limit lemmas for extended-real `L^p`
seminorms.

## Main results

- `tendsto_eLpNorm_of_tendsto_sub`: convergence in `L^p` implies convergence
  of the `L^p` seminorms when the limiting seminorm is finite.
- `tendsto_integral_of_tendsto_eLpNorm_sub`: on a probability measure,
  `L^p` convergence for `p ≥ 1` implies convergence of Bochner integrals.
- `tendsto_average_of_tendsto_eLpNorm_sub`: the corresponding statement for
  Mathlib's average notation.

The integral results include the endpoint `p = 1`. They first compare the
`L^1` and `L^p` seminorms and then use continuity of the Bochner integral in
`L^1`.
-/

 public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

variable {ι α E : Type*}

/-- The extended-real `L^p` seminorm is continuous along `L^p`-convergent
families when `p ≥ 1` and the limiting seminorm is finite. -/
theorem tendsto_eLpNorm_of_tendsto_sub
     [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α}
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {F : ι → α → E} {f : α → E} {l : Filter ι}
    (_hF : ∀ i, AEStronglyMeasurable (F i) μ)
    (_hf : AEStronglyMeasurable f μ)
    (hfin : eLpNorm f p μ ≠ ∞)
    (h :
      Tendsto
        (fun i => eLpNorm (F i - f) p μ)
        l (𝓝 0)) :
    Tendsto
      (fun i => eLpNorm (F i) p μ)
      l (𝓝 (eLpNorm f p μ)) := by


  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun i =>
        eLpNorm f p μ - eLpNorm (F i - f) p μ)
      (h := fun i =>
        eLpNorm f p μ + eLpNorm (F i - f) p μ)
      ?_ ?_ (by
          intro i
          rw [tsub_le_iff_right]
          calc
            eLpNorm f p μ =
                eLpNorm (F i + (f - F i)) p μ := by
              norm_num
            _ ≤
                eLpNorm (F i) p μ +
                  eLpNorm (f - F i) p μ :=
              eLpNorm_add_le hp
            _ =
                eLpNorm (F i) p μ +
                  eLpNorm (F i - f) p μ := by
              rw [eLpNorm_sub_comm]) (by
          intro i

          calc
            eLpNorm (F i) p μ =
                eLpNorm (f + (F i - f)) p μ :=
              congrArg (fun g => eLpNorm g p μ) (by
                  funext x
                  simp only [Pi.add_apply, Pi.sub_apply]
                  abel)
            _ ≤
                eLpNorm f p μ + eLpNorm (F i - f) p μ :=
              eLpNorm_add_le hp)
  · have hlowerTendsto :=
      ENNReal.Tendsto.sub
        (tendsto_const_nhds :
          Tendsto (fun _ : ι => eLpNorm f p μ)
            l (𝓝 (eLpNorm f p μ)))
        h (Or.inl hfin)
    simpa using hlowerTendsto
  ·
    simpa only [add_zero] using (Tendsto.const_add (eLpNorm f p μ) h)

/-- On a probability measure, `L^p` convergence with `p ≥ 1` implies
convergence of Bochner integrals.

Only integrability of the limit and strong measurability of the approximants
are assumed. The `L^p` convergence itself makes the approximants integrable
eventually. -/
theorem tendsto_integral_of_tendsto_eLpNorm_sub
     [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {F : ι → α → E} {f : α → E} {l : Filter ι}
    (_hF : ∀ i, AEStronglyMeasurable (F i) μ)
    (hf : Integrable f μ)
    (h :
      Tendsto
        (fun i => eLpNorm (F i - f) p μ)
        l (𝓝 0)) :
    Tendsto
      (fun i => ∫ x, F i x ∂μ)
      l (𝓝 (∫ x, f x ∂μ)) := by


  exact
    tendsto_integral_of_L1'
      f (by
          filter_upwards
            [(tendsto_order.1 h).2 1 zero_lt_one] with i hi


          simpa only [sub_add_cancel] using
            ((show MemLp (F i - f) p μ from (hi.trans ENNReal.one_lt_top)).integrable hp).add hf) (by
          refine
            tendsto_of_tendsto_of_tendsto_of_le_of_le'
              tendsto_const_nhds h
              (Eventually.of_forall fun _ => zero_le)
              ?_
          exact
            Eventually.of_forall fun i =>
              eLpNorm_le_eLpNorm_of_exponent_le hp)

/-- On a probability measure, centering an `L^p`-convergent sequence by its
integral preserves `L^p` convergence. This includes the endpoint `p = 1`. -/
theorem tendsto_eLpNorm_centered_sub_zero
    {ι α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    {F : ι → α → ℝ} {f : α → ℝ} {l : Filter ι}
    (hF : ∀ i, AEStronglyMeasurable (F i) μ)
    (hf : Integrable f μ)
    (h :
      Tendsto
        (fun i => eLpNorm (F i - f) p μ)
        l (𝓝 0)) :
    Tendsto
      (fun i =>
        eLpNorm
          (fun x =>
            (F i x - ∫ y, F i y ∂μ) -
              (f x - ∫ y, f y ∂μ))
          p μ)
      l (𝓝 0) := by
  have hpZero  :=
    ne_of_gt (zero_lt_one.trans_le hp)
  have hIntegral :=
    tendsto_integral_of_tendsto_eLpNorm_sub
      hp hF hf h
  have hIntegralDiff :
      Tendsto
        (fun i => (∫ y, f y ∂μ) - ∫ y, F i y ∂μ)
        l (𝓝 0) := by
    have hConst :
        Tendsto
          (fun _ : ι => ∫ y, f y ∂μ)
          l (𝓝 (∫ y, f y ∂μ)) :=
      tendsto_const_nhds
    simpa only [sub_self] using hConst.sub hIntegral



  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds (show Tendsto
        (fun i =>
          eLpNorm (F i - f) p μ +
            eLpNorm
              (fun _ : α =>
                (∫ y, f y ∂μ) - ∫ y, F i y ∂μ)
              p μ)
        l (𝓝 0) by
          simpa only [zero_add] using h.add (by
              have hEnorm :
                  Tendsto
                    (fun i =>
                      ‖(∫ y, f y ∂μ) - ∫ y, F i y ∂μ‖ₑ)
                    l (𝓝 0) := by
                simpa only [enorm_zero] using hIntegralDiff.enorm
              have hFormula :
                  (fun i =>
                    eLpNorm
                      (fun _ : α =>
                        (∫ y, f y ∂μ) - ∫ y, F i y ∂μ)
                      p μ) =
                    fun i =>
                      ‖(∫ y, f y ∂μ) - ∫ y, F i y ∂μ‖ₑ := by
                funext i
                rw [eLpNorm_const'
                  ((∫ y, f y ∂μ) - ∫ y, F i y ∂μ)
                  hpZero hpTop]
                simp only [measure_univ, ENNReal.one_rpow, mul_one]
              rw [hFormula]
              exact hEnorm))
      (fun _ => zero_le) (show _ by
          intro i
          let A  :=
            F i - f
          let B : α → ℝ :=
            fun _ =>
              (∫ y, f y ∂μ) - ∫ y, F i y ∂μ


          calc
            eLpNorm
                (fun x =>
                  (F i x - ∫ y, F i y ∂μ) -
                    (f x - ∫ y, f y ∂μ))
                p μ =
              eLpNorm (A + B) p μ := by
                apply eLpNorm_congr_ae
                filter_upwards with x
                dsimp only [A, B, Pi.sub_apply, Pi.add_apply]
                ring
            _ ≤ eLpNorm A p μ + eLpNorm B p μ :=
              eLpNorm_add_le hp
            _ =
                eLpNorm (F i - f) p μ +
                  eLpNorm
                    (fun _ : α =>
                      (∫ y, f y ∂μ) - ∫ y, F i y ∂μ)
                    p μ :=
              rfl)

end PDE
