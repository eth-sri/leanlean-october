module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.Analytic.ZetaContinuation
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Algebra.Field.GeomSum
public import WeylPort.Analytic.NonstationaryFoundation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Sharp zeta truncation and the actual AFE power integrals

The continuation identity is consumed from the existing node-71 foundation:
`Zeta0EqZeta` and `ZetaBnd_aux1b`, without duplicating their analytic continuation proofs.
-/

namespace DhimanKadiriQuesadaHerrera2026

open MeasureTheory Filter
open scoped Topology

/-- The existing Euler--Maclaurin continuation controls the actual regularized Dirichlet sum. -/
theorem norm_zeta_sub_regularized_sum_le {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s - ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
      (N : ℂ) ^ (1 - s) / (s - 1))‖ ≤
      (N : ℝ) ^ (-s.re) * (1 / 2 + ‖s‖ / s.re) := by
  have he := Zeta0EqZeta hN hs hs1
  unfold riemannZeta0 at he
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hi := ZetaBnd_aux1b N hN (t := s.im) hs
  rw [Complex.re_add_im] at hi
  have hid : riemannZeta s - ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
      (N : ℂ) ^ (1 - s) / (s - 1)) = -(N : ℂ) ^ (-s) / 2 +
      s * ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) := by
    rw [← he]
    have hd : 1 - s = -(s - 1) := by ring
    rw [hd, neg_div_neg_eq]
    ring
  rw [hid]
  calc
    _ ≤ ‖-(N : ℂ) ^ (-s) / 2‖ +
        ‖s * ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ := norm_add_le _ _
    _ ≤ (N : ℝ) ^ (-s.re) / 2 + ‖s‖ * ((N : ℝ) ^ (-s.re) / s.re) := by
      rw [norm_div, norm_neg, Complex.norm_ofNat, norm_mul]
      have hp : ‖(N : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-s.re) := by
        simpa only [Complex.ofReal_natCast, Complex.neg_re] using
          Complex.norm_cpow_eq_rpow_re_of_pos hn (-s)
      rw [hp]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hi (norm_nonneg s))
    _ = _ := by ring











end DhimanKadiriQuesadaHerrera2026
