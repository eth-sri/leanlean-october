module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Average

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

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

/-- The extended-real `L^p` seminorm is continuous along `L^p`-convergent
families when `p ≥ 1` and the limiting seminorm is finite. -/
theorem tendsto_eLpNorm_of_tendsto_sub
    {ι α E : Type*} [MeasurableSpace α]
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
  have hupper :
      ∀ i,
        eLpNorm (F i) p μ ≤
          eLpNorm f p μ + eLpNorm (F i - f) p μ := by
    intro i
    have heq : F i = f + (F i - f) := by
      simp
    calc
      eLpNorm (F i) p μ =
          eLpNorm (f + (F i - f)) p μ :=
        congrArg (fun g => eLpNorm g p μ) heq
      _ ≤
          eLpNorm f p μ + eLpNorm (F i - f) p μ :=
        eLpNorm_add_le hp
  have hlower :
      ∀ i,
        eLpNorm f p μ - eLpNorm (F i - f) p μ ≤
          eLpNorm (F i) p μ := by
    intro i
    rw [tsub_le_iff_right]
    calc
      eLpNorm f p μ =
          eLpNorm (F i + (f - F i)) p μ := by
        simp
      _ ≤
          eLpNorm (F i) p μ +
            eLpNorm (f - F i) p μ :=
        eLpNorm_add_le hp
      _ =
          eLpNorm (F i) p μ +
            eLpNorm (F i - f) p μ := by
        rw [eLpNorm_sub_comm]
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun i =>
        eLpNorm f p μ - eLpNorm (F i - f) p μ)
      (h := fun i =>
        eLpNorm f p μ + eLpNorm (F i - f) p μ)
      ?_ ?_ hlower hupper
  · have hlowerTendsto :=
      ENNReal.Tendsto.sub
        tendsto_const_nhds
        h (Or.inl hfin)
    simpa using hlowerTendsto
  · simpa only [add_zero] using (Tendsto.const_add (eLpNorm f p μ) h)

end PDE
