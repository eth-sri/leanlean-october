module
public import GafniTao.WooleySection7HardArithmetic
public import GafniTao.WooleyTwoFactorHolder
import WeylPort.Analytic.RealLaplace

public section

/-!
# Exponent identities for Wooley Section 8

The identities below are the exact exponent bookkeeping behind equations
(8.1) and (8.2).  They are stated separately from Hölder so that no
subtraction cast or endpoint case is implicit in the analytic proof.
-/

namespace GafniTao


theorem wooleyTriangular_cast (r : ℕ) :
    (wooleyTriangular r : ℝ) = (r : ℝ) * ((r : ℝ) + 1) / 2 := by
  unfold wooleyTriangular
  pm_2813 Nat.even_mul_succ_self r
  rfl

theorem wooleyTriangular_mono {a b : ℕ} (hab : a ≤ b) :
    wooleyTriangular a ≤ wooleyTriangular b := by
  unfold wooleyTriangular
  exact Nat.div_le_div_right
    (Nat.mul_le_mul hab (Nat.add_le_add_right hab 1))

theorem wooleyTriangular_sub_le (k r : ℕ) :
    wooleyTriangular (k - r) ≤ wooleyTriangular k :=
  wooleyTriangular_mono (Nat.sub_le k r)

theorem wooleyTriangular_pred_le {k r : ℕ} (hrk : r ≤ k) :
    wooleyTriangular (r - 1) ≤ wooleyTriangular k :=
  wooleyTriangular_mono ((Nat.sub_le r 1).trans hrk)

section
variable {k r : ℕ} (hr : 1 ≤ r) (hrk : r < k)
include k r hr hrk
/-- The exponent of the `b'`-residue factor in the Section 8 interpolation. -/
theorem wooley_section8_left_exponent :
    (1 / ((k - r + 1 : ℕ) : ℝ)) *
          (2 * ((wooleyTriangular k - wooleyTriangular (k - r) : ℕ) : ℝ)) +
        ((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ) *
          (2 * (wooleyTriangular (r - 1) : ℝ)) =
      2 * (wooleyTriangular r : ℝ) := by
  pm_6249
  rw [Nat.cast_sub hsub, wooleyTriangular_cast,
    wooleyTriangular_cast, wooleyTriangular_cast,
    wooleyTriangular_cast]
  pm_2834

/-- The exponent of the `b`-residue factor in the Section 8 interpolation. -/
theorem wooley_section8_right_exponent :
    (1 / ((k - r + 1 : ℕ) : ℝ)) *
          (2 * (wooleyTriangular (k - r) : ℝ)) +
        ((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ) *
          (2 * ((wooleyTriangular k - wooleyTriangular (r - 1) : ℕ) : ℝ)) =
      2 * ((wooleyTriangular k - wooleyTriangular r : ℕ) : ℝ) := by
  pm_6249
  pm_7114 hrTri
  rw [Nat.cast_sub hpred, Nat.cast_sub hrTri,
    wooleyTriangular_cast, wooleyTriangular_cast,
    wooleyTriangular_cast, wooleyTriangular_cast]
  pm_2834
end

theorem wooley_section8_weight_complement
    {k r : ℕ} (hrk : r < k) :
    1 - 1 / ((k - r + 1 : ℕ) : ℝ) =
      ((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ) := by grind



end GafniTao
