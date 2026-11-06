module
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import DensityEnergyGM.DFIWeight
public import GuthMaynard.NativeSource.GuthMaynard.QuadraticDivisor

@[expose] public section

open Complex Finset Set
open scoped BigOperators ContDiff Topology
open scoped ArithmeticFunction.Moebius
open Classical

namespace GuthMaynard.NativeMoment

/-!
# DFI equations (9)--(19): the delta symbol

The source chooses an even smooth function `w`, supported where
`Q ≤ |u| ≤ 2Q`, normalized by `∑_{r≥1} w(r)=1`, and satisfying
`w^(j)(u) ≪_j Q^(-j-1)`.  These are equations (9) and (13).

The support makes every series in the delta symbol finite at each argument.
The definitions below expose an explicit radius large enough to contain every
nonzero term; later identities can therefore use ordinary `Finset` algebra.
-/

/-- The source cutoff used in DFI equations (9)--(19). -/
structure DFIDeltaWeight (Q : ℝ) where
  /-- The `toFun` component of `DFIDeltaWeight`. -/
  toFun : ℝ → ℝ
  one_le_Q : 1 ≤ Q
  smooth : ContDiff ℝ ∞ toFun
  even : ∀ u : ℝ, toFun (-u) = toFun u
  support_annulus : Function.support toFun ⊆
    {u : ℝ | Q ≤ |u| ∧ |u| ≤ 2 * Q}
  normalized : ∑' r : ℕ, toFun (r + 1 : ℕ) = 1
  derivativeBound : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ,
    ‖iteratedDeriv j toFun u‖ ≤ C * (Q ^ (j + 1))⁻¹

instance {Q : ℝ} : CoeFun (DFIDeltaWeight Q) (fun _ => ℝ → ℝ) :=
  ⟨DFIDeltaWeight.toFun⟩

theorem DFIDeltaWeight.Q_pos {Q : ℝ} (w : DFIDeltaWeight Q) : 0 < Q :=
  lt_of_lt_of_le zero_lt_one w.one_le_Q

/-- The annular support forces the source weight to vanish close to zero. -/
theorem DFIDeltaWeight.eq_zero_of_abs_lt {Q u : ℝ} (w : DFIDeltaWeight Q)
    (hu : |u| < Q) : w u = 0 := by
  by_contra hne
  have hmem : u ∈ Function.support w.toFun := hne
  exact (not_le_of_gt hu) (w.support_annulus hmem).1

@[simp]
theorem DFIDeltaWeight.zero {Q : ℝ} (w : DFIDeltaWeight Q) : w 0 = 0 := by
  apply w.eq_zero_of_abs_lt
  simpa using w.Q_pos

end GuthMaynard.NativeMoment
