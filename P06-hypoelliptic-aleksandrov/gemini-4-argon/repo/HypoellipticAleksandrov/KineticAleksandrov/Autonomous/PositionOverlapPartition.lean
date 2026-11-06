module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapMixture
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapCells
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsCells
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! # Canonical decomposition into disjoint time-position starting cells -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped ENNReal
open scoped Classical

/- The two-index source cells form a pairwise disjoint grid. -/
theorem enlargedStartCell_pairwiseDisjoint (c : Clock) (s x : ℝ) :
    Pairwise (fun a b : ℕ × ℤ =>
      Disjoint (enlargedStartCell c s x a.1 a.2) (enlargedStartCell c s x b.1 b.2)) := by
  intro a b hab
  apply disjoint_left.mpr
  intro p ha hb
  by_cases ht : a.1 = b.1
  · have hk : a.2 ≠ b.2 := by
      intro hk
      exact hab (Prod.ext ht hk)
    exact disjoint_left.mp (enlargedPositionCell_disjoint c.r x c.positive hk) ha.2 hb.2
  · exact disjoint_left.mp (enlargedTimeBin_disjoint c.r s c.positive ht) ha.1 hb.1

/- The time-position grid covers all starting points on and after its time origin. -/
theorem enlargedStartCell_iUnion (c : Clock) (s x : ℝ) :
    (⋃ a : ℕ × ℤ, enlargedStartCell c s x a.1 a.2) = {p | s ≤ p.time} := by
  ext p
  constructor
  · intro hp
    obtain ⟨a, ha⟩ := mem_iUnion.mp hp
    have h := (enlargedTimeBin_bounds c.r s p.time a.1 ha.1).1
    have hj : 0 ≤ (a.1 : ℝ) := Nat.cast_nonneg _
    change s ≤ p.time
    exact (le_add_of_nonneg_right (mul_nonneg hj (sq_nonneg c.r))).trans h
  · intro hp
    obtain ⟨j, hj⟩ : ∃ j : ℕ, p.time ∈ enlargedTimeBin c.r s j := by
      let r := c.r
      let t := p.time
      have hr := c.positive
      have hr2 := sq_pos_of_pos hr
      have hex : ∃ n : ℕ, t ≤ s + ((n : ℝ) + 1) * r ^ 2 := by
        obtain ⟨n, hn⟩ := exists_nat_gt ((t - s) / r ^ 2)
        refine ⟨n, ?_⟩
        have h := (div_lt_iff₀ hr2).mp hn
        linarith
      let j := Nat.find hex
      have hu : t ≤ s + ((j : ℝ) + 1) * r ^ 2 := Nat.find_spec hex
      refine ⟨j, ?_⟩
      by_cases hj : j = 0
      · have hu' : t ≤ s + r ^ 2 := by simpa only [hj, Nat.cast_zero, zero_add, one_mul] using hu
        simpa [enlargedTimeBin, hj] using ⟨hp, hu'⟩
      · have hjp : j.pred < j := Nat.pred_lt hj
        have hn := Nat.find_min hex hjp
        have he : j = j.pred + 1 := (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hj)).symm
        have hc : (j.pred : ℝ) + 1 = (j : ℝ) := by exact_mod_cast he.symm
        have hl : s + (j : ℝ) * r ^ 2 < t := by
          rw [hc] at hn
          exact not_le.mp hn
        simpa [enlargedTimeBin, hj] using ⟨hl, hu⟩
    obtain ⟨k, hk⟩ := enlargedPositionCell_covers c.r x (p.position 0) c.positive
    exact mem_iUnion.mpr ⟨(j, k), hj, hk⟩

/- A positive starting measure after the origin is the sum of its cell restrictions. -/
theorem enlargedStartCell_measure_sum (nu : Measure Point) (c : Clock) (s x : ℝ)
    (hnu : ∀ᵐ e ∂nu, s ≤ e.time) :
    nu = Measure.sum (fun a : ℕ × ℤ => nu.restrict (enlargedStartCell c s x a.1 a.2)) := by
  have he : nu.restrict (⋃ a : ℕ × ℤ, enlargedStartCell c s x a.1 a.2) = nu := by
    rw [enlargedStartCell_iUnion]
    exact Measure.restrict_eq_self_of_ae_mem hnu
  exact he.symm.trans (Measure.restrict_iUnion (enlargedStartCell_pairwiseDisjoint c s x)
    (fun a => measurableSet_enlargedStartCell c s x a.1 a.2))

/- The actual positive mixture density decomposes into the same source-cell mixtures. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
