module
public import GafniTao.WooleyConditioningTower
import WeylPort.Analytic.RealLaplace

public section

/-!
# Scale arithmetic for Wooley Lemma 4.1

These lemmas formalize the ceiling and loss calculations in the paragraph
between equations (4.12) and (4.13).
-/

namespace GafniTao

/-- Removing `k*h` from the Fourier depth removes exactly `h` from the
ceiling scale. -/
theorem wooley_ceilDiv_sub_mul
    {B k h : ℕ} (hk : 1 ≤ k) (hkhB : k * h ≤ B) :
    (B - k * h) ⌈/⌉ k = B ⌈/⌉ k - h := by
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div]
  have heq : B + k - 1 = (B - k * h + k - 1) + k * h := by omega
  rw [heq, Nat.add_mul_div_left _ h (by omega)]
  grind

/-- The elementary ceiling estimate `k*ceil(B/k) < B+k`. -/
theorem wooley_mul_ceilDiv_lt_add
    {B k : ℕ} (hk : 1 ≤ k) :
    k * (B ⌈/⌉ k) < B + k := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have hdiv := Nat.div_mul_le_self (B + k - 1) k
  grind

/-- The source inequality `B-kh ≥ delta*B-k`, together with the resulting
non-truncation of the natural subtraction. -/
theorem wooley_section4_depth_margin
    {B k h : ℕ} {delta : ℝ}
    (hk : 1 ≤ k) (hdelta0 : 0 < delta)
    (hdelta1 : delta < 1)
    (hh : (h : ℝ) ≤ (1 - delta) * (B ⌈/⌉ k : ℕ))
    (hlarge : (k : ℝ) ≤ delta * B) :
    k * h ≤ B ∧
      delta * B - k ≤ ((B - k * h : ℕ) : ℝ) := by
  have hceilNat := wooley_mul_ceilDiv_lt_add (B := B) hk
  have hceil : (k : ℝ) * (B ⌈/⌉ k : ℕ) < B + k := by
    exact_mod_cast hceilNat
  pm_2847 hk0 k
  pm_5658
  have hkhReal : (k : ℝ) * h ≤ B := by
    pm_2787
  have hkhB : k * h ≤ B := by
    exact_mod_cast hkhReal
  refine ⟨hkhB, ?_⟩
  rw [Nat.cast_sub hkhB]
  push_cast
  pm_2787


end GafniTao
