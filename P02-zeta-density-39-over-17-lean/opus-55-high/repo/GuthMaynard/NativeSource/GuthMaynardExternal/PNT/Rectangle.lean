module
/-
Adapted from the Lean 4.30 revision of PrimeNumberTheoremAnd/Rectangle.lean.
Copyright belongs to the upstream contributors.
Released under the Apache License 2.0:
https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/main/LICENSE
-/
public import Mathlib
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Order.Interval.Set.Monotone

@[expose] public section

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle

lemma symm : Rectangle z w = Rectangle w z := by
  simp [Rectangle, uIcc_comm]

end Rectangle

@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl
