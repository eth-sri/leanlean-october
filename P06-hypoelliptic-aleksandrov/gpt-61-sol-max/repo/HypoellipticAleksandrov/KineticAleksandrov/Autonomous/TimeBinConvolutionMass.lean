module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.MixtureDensity
import Mathlib.Algebra.Order.Floor.Ring

/-! # Disjoint source time bins and their q-power mass bound

Source: companion paper, Lemma 8.6. The bins use integer indices and retain their right endpoints.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped ENNReal

variable (r : ℝ)

variable (j : ℤ)

/-- The literal source time bin of length r² on the full integer grid. -/
def entranceTimeBin   : Set Point :=
  {p | p.time ∈ Ioc ((j : ℝ) * r ^ 2) (((j : ℝ) + 1) * r ^ 2)}

/-- Every full-grid source bin is Borel. -/
theorem measurableSet_entranceTimeBin   :
    MeasurableSet (entranceTimeBin r j) :=
  measurableSet_Ioc.preimage continuous_time.measurable

/-- Full-grid right-closed source bins are pairwise disjoint. -/
theorem entranceTimeBin_pairwise  :
    Pairwise (fun i j => Disjoint (entranceTimeBin r i) (entranceTimeBin r j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hi hj
  have hi' : (i : ℝ) * r ^ 2 < p.time ∧ p.time ≤ ((i : ℝ) + 1) * r ^ 2 := hi
  have hj' : (j : ℝ) * r ^ 2 < p.time ∧ p.time ≤ ((j : ℝ) + 1) * r ^ 2 := hj
  rcases lt_or_gt_of_ne hij with h | h
  ·
    have hm := mul_le_mul_of_nonneg_right (show (i : ℝ) + 1 ≤ (j : ℝ) by exact_mod_cast h) (sq_nonneg r)
    linarith
  ·
    have hm := mul_le_mul_of_nonneg_right (show (j : ℝ) + 1 ≤ (i : ℝ) by exact_mod_cast h) (sq_nonneg r)
    linarith

/-- Every real time lies in exactly one right-closed integer bin. -/
theorem iUnion_entranceTimeBin  (hr : 0 < r) :
    (⋃ j : ℤ, entranceTimeBin r j) = univ := by
  apply Set.eq_univ_of_forall
  intro p
  let a := p.time / r ^ 2
  let j := Int.ceil a - 1
  apply mem_iUnion.mpr
  refine ⟨j, ?_⟩
  have hl : (j : ℝ) < a := Int.lt_ceil.mp (by dsimp [j]; omega)

  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  exact ⟨(lt_div_iff₀ hr2).mp hl, (div_le_iff₀ hr2).mp (by
      simpa only [j, Int.cast_sub, Int.cast_one, sub_add_cancel] using Int.le_ceil a)⟩

variable (nu : Measure Point) (r : ℝ) (hr : 0 < r)

include hr
/-- Disjoint integer bin masses sum to the original total starting mass. -/
theorem entranceTimeBin_mass_sum  :
    (∑' j : ℤ, nu (entranceTimeBin r j)) = nu univ := by
  rw [← measure_iUnion (entranceTimeBin_pairwise r) (measurableSet_entranceTimeBin r),
    iUnion_entranceTimeBin r hr]

/-- Short-window mass control gives the exact source q-power sum estimate. -/
theorem entranceTimeBin_mass_rpow_sum
    (q : ℝ) (hq : 1 ≤ q) (M : ℝ≥0∞)
    (hM : ∀ j : ℤ, nu (entranceTimeBin r j) ≤ M) :
    (∑' j : ℤ, nu (entranceTimeBin r j) ^ q) ≤ nu univ * M ^ (q - 1) := by

  calc
    _ ≤ ∑' j : ℤ, nu (entranceTimeBin r j) * M ^ (q - 1) := by
      apply ENNReal.tsum_le_tsum
      intro j
      have he : nu (entranceTimeBin r j) ^ q =
          nu (entranceTimeBin r j) * nu (entranceTimeBin r j) ^ (q - 1) := by
        calc
          _ = nu (entranceTimeBin r j) ^ (1 + (q - 1)) := by congr 1; ring
          _ = _ := by
            rw [ENNReal.rpow_add_of_nonneg 1 (q - 1) zero_le_one (sub_nonneg.mpr hq), ENNReal.rpow_one]
      rw [he]
      gcongr
      exact hM j
    _ = (∑' j : ℤ, nu (entranceTimeBin r j)) * M ^ (q - 1) :=
      ENNReal.tsum_mul_right
    _ = _ := by rw [entranceTimeBin_mass_sum nu r hr]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
