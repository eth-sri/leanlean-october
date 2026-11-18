module
public import MathCollab.Density.Stronger.Atkinson.FiniteWeightVariation
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCutoffVariation
public import MathCollab.Density.Stronger.Atkinson.ZetaBandSecondDerivatives
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFirstDerivative
public import MathCollab.Density.Stronger.Atkinson.FresnelEvaluation
public import MathCollab.Density.Stronger.Atkinson.ContinuousKernelPrimitive
public import MathCollab.Density.Stronger.Atkinson.IntervalSecondDerivativeBounds
public import MathCollab.Density.Stronger.Atkinson.SecondDerivativeComposition
public import MathCollab.Density.Stronger.PointMean.HorizontalEdges
public import MathCollab.Density.Stronger.Fourth.SquareTail
public import Mathlib
public import TaoTrudgianYang2025.BetaModelPoisson

@[expose] public section

/-!
# Smooth cutoffs agreeing exactly with an interior integer interval

Strict physical endpoint margins permit a smooth plateau with transitions
in lattice gaps. Its values on all scaled integers are the exact interval
indicator. No smoothing error or replacement-sum assumption is introduced.
Derivative bounds uniform in the margins remain a separate obligation.
-/

noncomputable section

open Set Expdb
open scoped ContDiff FourierTransform BigOperators

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

theorem exponentialSumAt_eq_int_sum (F : ℝ → ℝ) (T N : ℝ) (a b : ℕ) :
    exponentialSumAt F T N a b =
      ∑ n ∈ Finset.Icc (a : ℤ) (b : ℤ), (𝐞 (T*F ((n : ℝ)/N)) : ℂ) := by
  classical
  unfold exponentialSumAt oscillatory
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ℤ))
  · intro n hn
    have h := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast h.1,by exact_mod_cast h.2⟩
  · intro n _ m _ h
    exact_mod_cast h
  · intro n hn
    have h := Finset.mem_Icc.mp hn
    have hn₀ := (Int.natCast_nonneg a).trans h.1
    refine ⟨n.toNat,?_,Int.toNat_of_nonneg hn₀⟩
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  · intro n _
    simp

end TaoTrudgianYang2025
