module
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalDensity
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.ConstantSpeed
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.Analysis.Complex.RealDeriv
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
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Order.Interval.Set.Monotone
public import GuthMaynard.NativeSource.GuthMaynard.ArithmeticCoefficients
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalLargeValues
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Int.Interval
public import Mathlib.Analysis.Complex.PhragmenLindelof

@[expose] public section

open Complex Finset Filter Topology
open scoped BigOperators

namespace GuthMaynard.NativeMoment

/-!
# Finite classical Type-I/Type-II dichotomy

This module formalizes the finite detector split in ANTEDB Lemma 11.5.
The Type-I branch is a long ordinary-zeta tail.  The Type-II branch is the
genuinely short tail obtained by multiplying a short zeta sum by a short
Möbius polynomial.  Medium reflection, the terminal estimate, and endpoint
exponent assembly remain downstream of the certificate constructed here.
-/

/-- The sharp finite partial-zeta sum through `A`. -/
noncomputable def classicalZetaPartialSum (A : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 A, (n : ℂ) ^ (-s)

/-- The ordinary-zeta tail strictly above `Y` and through `A`. -/
noncomputable def classicalZetaLongTail (Y A : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Ioc Y A, (n : ℂ) ^ (-s)





/-- Fixed-line coefficients of the ordinary Type-I tail, extended by zero
beyond the sharp upper cutoff. -/
noncomputable def classicalZetaLongLineCoeff
    (A : ℕ) (σ : ℝ) (n : ℕ) : ℂ :=
  if n ≤ A then (n : ℂ) ^ (-(σ : ℂ)) else 0

theorem classicalZetaLongLineCoeff_term
    (A n : ℕ) (σ t : ℝ) (hn : 0 < n) (hnA : n ≤ A) :
    classicalZetaLongLineCoeff A σ n * (n : ℂ) ^ (-(t : ℂ) * I) =
      (n : ℂ) ^ (-((σ : ℂ) + I * (t : ℂ))) := by
  rw [classicalZetaLongLineCoeff, ite_eq_left hnA,
    ← Complex.cpow_add _ _ (by exact_mod_cast hn.ne')]
  congr 2
  ring

/-- The fixed-line Type-I tail is one wide polynomial starting at `Y`. -/
theorem classicalZetaLongTail_eq_wideDirichletPoly
    (Y A : ℕ) (σ t : ℝ) (hY : 1 ≤ Y) :
    classicalZetaLongTail Y A ((σ : ℂ) + I * (t : ℂ)) =
      wideDirichletPoly Y (Nat.clog 2 A)
        (classicalZetaLongLineCoeff A σ) t := by
  have hCover : A ≤ 2 ^ Nat.clog 2 A :=
    (Nat.clog_le_iff_le_pow Nat.one_lt_two).mp le_rfl
  have hUpper : A ≤ 2 ^ Nat.clog 2 A * Y := by
    calc
      A ≤ 2 ^ Nat.clog 2 A := hCover
      _ ≤ 2 ^ Nat.clog 2 A * Y :=
        Nat.le_mul_of_pos_right _ (lt_of_lt_of_le Nat.zero_lt_one hY)
  have hSubset : Finset.Ioc Y A ⊆
      Finset.Ioc Y (2 ^ Nat.clog 2 A * Y) := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
      (Finset.mem_Ioc.mp hn).2.trans hUpper⟩
  rw [classicalZetaLongTail, wideDirichletPoly]
  have hExtend :
      (∑ n ∈ Finset.Ioc Y A,
          classicalZetaLongLineCoeff A σ n * (n : ℂ) ^ (-(t : ℂ) * I)) =
        ∑ n ∈ Finset.Ioc Y (2 ^ Nat.clog 2 A * Y),
          classicalZetaLongLineCoeff A σ n * (n : ℂ) ^ (-(t : ℂ) * I) := by
    apply Finset.sum_subset hSubset
    intro n hnBig hnSmall
    have hnA : A < n := by
      by_contra h
      exact hnSmall (Finset.mem_Ioc.mpr
        ⟨(Finset.mem_Ioc.mp hnBig).1, Nat.le_of_not_gt h⟩)
    rw [classicalZetaLongLineCoeff, ite_eq_right (by omega), zero_mul]
  rw [← hExtend]
  apply Finset.sum_congr rfl
  intro n hn
  exact (classicalZetaLongLineCoeff_term A n σ t
    (lt_of_le_of_lt (Nat.zero_le Y) (Finset.mem_Ioc.mp hn).1)
    (Finset.mem_Ioc.mp hn).2).symm


/-- Splitting a finite zeta sum at `Y` is an exact identity. -/
theorem classicalZetaPartialSum_eq_short_add_long
    (Y A : ℕ) (s : ℂ) (hYA : Y ≤ A) :
    classicalZetaPartialSum A s =
      classicalZetaPartialSum Y s + classicalZetaLongTail Y A s := by
  have hUnion : Finset.Icc 1 A = Finset.Icc 1 Y ∪ Finset.Ioc Y A := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  rw [classicalZetaPartialSum, classicalZetaPartialSum,
    classicalZetaLongTail, hUnion, sum_union]
  rw [disjoint_left]
  intro n hnShort hnLong
  exact (not_lt_of_ge (Finset.mem_Icc.mp hnShort).2)
    (Finset.mem_Ioc.mp hnLong).1



















end GuthMaynard.NativeMoment
