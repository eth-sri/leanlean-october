module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Inflation
import Mathlib.Tactic
import Mathlib.Tactic.Ring



/-! # The time-centered kinetic differentiation basis

The distinguished point is in the interior, rather than on a backward cylinder's top
face. The sets shrink in the ordinary product topology; their volume eccentricity is
not compared with product-metric balls.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set

variable {d : ℕ}

variable (P : KineticPoint d) (r : ℝ)

/-- The top of a time-centered cylinder based at P. -/
def centeredTop   : KineticPoint d :=
  ⟨P.time + r ^ 2 / 2, P.position + (r ^ 2 / 2) • P.velocity, P.velocity⟩

/-- The literal time-centered cylinder used for differentiation. -/
def centeredCylinder   : Set (KineticPoint d) :=
  backwardCylinder (centeredTop P r) r

variable (P X : KineticPoint d)

/-- Centering preserves the free-transport position coordinate. -/
theorem relativePosition_centeredTop   (r : ℝ) :
    relativePosition (centeredTop P r) X = relativePosition P X := by
  ext <;> simp_all [relativePosition, centeredTop] <;> ring

/-- Membership in the centered basis is stated in its physical Euclidean coordinates. -/
theorem mem_centeredCylinder_iff   {r : ℝ}
    (hr : 0 < r) :
    X ∈ centeredCylinder P r ↔
      |X.time-P.time| < r ^ 2 / 2 ∧
      PDE.vecEuclideanNorm (X.velocity-P.velocity) < r ∧
      PDE.vecEuclideanNorm (relativePosition P X) < r ^ 3 := by
  rw [centeredCylinder, mem_backwardCylinder_iff,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hr 3),
    relativePosition_centeredTop, sub_zero]
  simp only [centeredTop, abs_lt]
  constructor
  · rintro ⟨h1, h2, hv, hx⟩
    exact ⟨⟨by linarith only [h1], by linarith only [h2]⟩, hv, hx⟩
  · rintro ⟨⟨h1, h2⟩, hv, hx⟩
    exact ⟨by linarith only [h1], by linarith only [h2], hv, hx⟩

/-- The distinguished point belongs to each positive centered cylinder. -/
theorem self_mem_centeredCylinder  (P : KineticPoint d) {r : ℝ}
    (hr : 0 < r) : P ∈ centeredCylinder P r := by
  rw [mem_centeredCylinder_iff P P hr]
  have hz : PDE.vecEuclideanNorm (0 : PDE.Vec d) = 0 :=
    PDE.vecEuclideanNorm_eq_zero_iff.mpr rfl
  simp_all

/-- Relative position plus transport displacement is the physical position difference. -/
theorem position_sub_eq_relative  (P X : KineticPoint d) :
    X.position-P.position = relativePosition P X + (X.time-P.time) • P.velocity := by
  simp only [relativePosition, sub_add_cancel]

variable (P : KineticPoint d)

/-- Small centered cylinders have uniformly small Euclidean coordinate displacements. -/
theorem centeredCylinder_coordinate_bounds   {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) {X : KineticPoint d}
    (hX : X ∈ centeredCylinder P r) :
    |X.time-P.time| < r ∧
      PDE.vecEuclideanNorm (X.velocity-P.velocity) < r ∧
      PDE.vecEuclideanNorm (X.position-P.position) <
        r*(1+PDE.vecEuclideanNorm P.velocity) := by
  obtain ⟨ht, hv, hx⟩ := (mem_centeredCylinder_iff P X hr).mp hX
  have hr2 : r ^ 2 ≤ r := by nlinarith only [hr, hr1]

  have ht' : |X.time-P.time| < r := by linarith only [ht, hr2, hr]
  refine ⟨ht', hv, ?_⟩
  rw [position_sub_eq_relative]
  calc
    _ ≤ PDE.vecEuclideanNorm (relativePosition P X) +
        PDE.vecEuclideanNorm ((X.time-P.time) • P.velocity) :=
      PDE.vecEuclideanNorm_add_le _ _
    _ = PDE.vecEuclideanNorm (relativePosition P X) +
        |X.time-P.time| *PDE.vecEuclideanNorm P.velocity := by
      rw [PDE.vecEuclideanNorm_smul]
    _ < r + r*PDE.vecEuclideanNorm P.velocity :=
      add_lt_add_of_lt_of_le (hx.trans_le (by
          calc
            r ^ 3 = r ^ 2 * r := by ring
            _ ≤ r * r := mul_le_mul_of_nonneg_right hr2 hr.le
            _ ≤ r := by nlinarith only [hr, hr1]))
        (mul_le_mul_of_nonneg_right ht'.le (PDE.vecEuclideanNorm_nonneg _))
    _ = r*(1+PDE.vecEuclideanNorm P.velocity) := by ring

/-- The centered kinetic basis eventually fits in every ordinary metric neighborhood. -/
theorem centeredCylinder_subset_ball   {eps : ℝ}
    (heps : 0 < eps) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r < r0 →
      centeredCylinder P r ⊆ Metric.ball P eps := by
  let L := 1 + PDE.vecEuclideanNorm P.velocity
  have hL : 0 < L := by dsimp [L]; linarith [PDE.vecEuclideanNorm_nonneg P.velocity]
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [PDE.vecEuclideanNorm_nonneg P.velocity]
  refine ⟨min 1 (eps/L), lt_min zero_lt_one (div_pos heps hL), ?_⟩
  intro r hr hrr X hX

  have hrL  := (lt_div_iff₀ hL).mp (hrr.trans_le (min_le_right _ _))
  obtain ⟨ht, hv, hx⟩ := centeredCylinder_coordinate_bounds P hr ((hrr.trans_le (min_le_left _ _)).le) hX
  have hrle : r ≤ r*L := by nlinarith only [hr.le, hL1]


  rw [Metric.mem_ball, ← (KineticPoint.isometryEquivProd d).dist_eq]
  change max (dist X.time P.time)
    (max (dist X.position P.position) (dist X.velocity P.velocity)) < eps
  rw [max_lt_iff, max_lt_iff, Real.dist_eq]
  exact ⟨ht.trans_le hrle |>.trans hrL, (by
      rw [dist_eq_norm]
      exact (PDE.norm_le_vecEuclideanNorm _).trans_lt (hx.trans hrL)), (by
      rw [dist_eq_norm]
      exact (PDE.norm_le_vecEuclideanNorm _).trans_lt (hv.trans_le hrle |>.trans hrL))⟩

/-- Every sufficiently small centered cylinder stays in a prescribed open neighborhood. -/
theorem centeredCylinder_eventually_subset_open  {U : Set (KineticPoint d)}
    (hU : IsOpen U) {P : KineticPoint d} (hP : P ∈ U) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r < r0 → centeredCylinder P r ⊆ U := by
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hU P hP
  obtain ⟨r0, hr0, hsmall⟩ := centeredCylinder_subset_ball P heps
  exact ⟨r0, hr0, fun r hr hrr => (hsmall r hr hrr).trans hball⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
