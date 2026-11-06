module
import Mathlib
public import MathCollab.Density.DetectorTaylorFamily

@[expose] public section

open Complex Filter
open scoped BigOperators Topology
noncomputable section
namespace MathCollab.Density





theorem sum_dyadic_Ioc (f : ℕ → ℂ) (L : ℕ) :
    (∑ r ∈ Finset.range L, ∑ n ∈ Finset.Ioc (2^r) (2*2^r), f n) =
      ∑ n ∈ Finset.Ioc 1 (2^L), f n := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    have he : 2^(L+1) = 2*2^L := by ring
    rw [he]
    exact Finset.sum_Ioc_consecutive f (by exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))) (by omega)








