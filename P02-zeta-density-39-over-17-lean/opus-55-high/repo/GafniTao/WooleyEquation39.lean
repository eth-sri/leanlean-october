module
public import GafniTao.WooleyWeightedComplexHolder
public import GafniTao.WooleyWeightedMean
import WeylPort.Analytic.RealLaplace

public section

/-!
# Wooley equations (3.9) and (3.10)

This file assembles the exact residue decomposition and the weighted finite
Hölder estimate.  The result is the source normalization with one inverse
global `L²` mass, rather than an unspecified constant.
-/

open Finset

namespace GafniTao


theorem wooley_sqrt_inverse_power_mul
    {M : ℝ} {s : ℕ} (hM : 0 < M) (hs : 1 ≤ s) :
    (Real.sqrt M)⁻¹ ^ (2 * s) * M ^ (s - 1) = M⁻¹ := by
  have hsqrt : Real.sqrt M ≠ 0 := (Real.sqrt_pos.2 hM).ne'
  pm_645
  rw [pow_mul, inv_pow, Real.sq_sqrt hM.le]
  rw [inv_pow, hpow]
  field_simp


end GafniTao
