module
import Mathlib
public import GafniTao.WooleyWeightedComplexHolder
public import GafniTao.WooleyWeightedMean

@[expose] public section

/-!
# Wooley equations (3.9) and (3.10)

This file assembles the exact residue decomposition and the weighted finite
Hölder estimate.  The result is the source normalization with one inverse
global `L²` mass, rather than an unspecified constant.
-/

open Finset
open scoped BigOperators

namespace GafniTao



theorem wooley_sqrt_inverse_power_mul
    {M : ℝ} {s : ℕ} (hM : 0 < M) (hs : 1 ≤ s) :
    (Real.sqrt M)⁻¹ ^ (2 * s) * M ^ (s - 1) = M⁻¹ := by
  have hpow : M ^ s = M ^ (s - 1) * M := by
    conv_lhs => rw [← Nat.sub_add_cancel hs, pow_add, pow_one]
  rw [pow_mul, inv_pow, Real.sq_sqrt hM.le]
  rw [inv_pow, hpow]
  field_simp




