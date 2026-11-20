module
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Totient
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.Real.Pi.Irrational
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Order.Interval.Set.Monotone
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import GuthMaynard.NativeSource.GuthMaynard.ArithmeticCoefficients
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.NumberTheory.ZetaValues

@[expose] public section

open Set Filter Function MeasureTheory
open scoped BigOperators ContDiff FourierTransform Interval Topology

namespace GuthMaynard.NativeMoment

/-!
# DFI equations (13)--(20): quantitative delta estimates

This module derives the scale-sensitive estimates following the exact delta
identity.  Constants are kept explicit and are never represented by an
assumed big-O proposition.
-/

/-- Restricting the domain can only decrease the integral of a nonnegative
integrable real function. -/
theorem setIntegral_le_integral_of_nonneg
    (g : ℝ → ℝ) (hg : Integrable g) (hgnonneg : ∀ x, 0 ≤ g x)
    (s : Set ℝ) :
    (∫ x in s, g x) ≤ ∫ x : ℝ, g x := by
  exact MeasureTheory.integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall hgnonneg) hg

end GuthMaynard.NativeMoment
