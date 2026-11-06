module

public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Geometry.Affine
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
import Aesop



/-!
# Round balls on native vectors

Round balls are defined through the explicit Euclidean squared distance, not
the inherited finite-product metric. The squared-radius convention agrees
with the established homogenization API. Consequently, norm-membership and
radius-monotonicity lemmas state the required radius sign assumptions.
-/

@[expose] public section

open scoped Pointwise

namespace PDE

/-- Euclidean squared distance on native vectors. -/
def euclideanSqDist {d : ℕ} (x y : Vec d) : ℝ :=
  vecNormSq (x - y)

variable {d : ℕ}

variable (x₀ : Vec d) (R : ℝ)

/-- The explicit round Euclidean open ball. -/
def euclideanBall   : Set (Vec d) :=
  {x | euclideanSqDist x x₀ < R ^ 2}

/-- The explicit round Euclidean closed ball. -/
def euclideanClosedBall   : Set (Vec d) :=
  {x | euclideanSqDist x x₀ ≤ R ^ 2}

/-- The explicit Euclidean sphere. -/
def euclideanSphere   : Set (Vec d) :=
  {x | euclideanSqDist x x₀ = R ^ 2}

@[simp]
theorem euclideanSqDist_self  (x : Vec d) :
    euclideanSqDist x x = 0 := by
  simp [euclideanSqDist, vecNormSq, vecDot]

theorem euclideanSqDist_nonneg  (x y : Vec d) :
    0 ≤ euclideanSqDist x y :=
  vecNormSq_nonneg _

theorem euclideanSqDist_add_right  (x y z : Vec d) :
    euclideanSqDist (x + z) (y + z) = euclideanSqDist x y := by
  simp_all [euclideanSqDist]

theorem euclideanSqDist_smul_smul
    (r : ℝ) (x y : Vec d) :
    euclideanSqDist (r • x) (r • y) =
      r ^ 2 * euclideanSqDist x y := by
  have hsub : r • x - r • y = r • (x - y) := by
    ext i
    simp [sub_eq_add_neg, mul_add]
  rw [euclideanSqDist, hsub, vecNormSq_smul]
  rfl

theorem euclideanSqDist_affine_center
    (x₀ y : Vec d) (r : ℝ) :
    euclideanSqDist (r • y + x₀) x₀ =
      r ^ 2 * euclideanSqDist y 0 := by
  calc
    euclideanSqDist (r • y + x₀) x₀ =
        euclideanSqDist (r • y) 0 := by
      simpa using euclideanSqDist_add_right (r • y) 0 x₀
    _ = r ^ 2 * euclideanSqDist y 0 := by
      simpa using euclideanSqDist_smul_smul r y 0

variable {x₀ x : Vec d} {R : ℝ}

theorem mem_euclideanBall_iff_vecEuclideanNorm_lt
     (hR : 0 < R) :
    x ∈ euclideanBall x₀ R ↔
      vecEuclideanNorm (x - x₀) < R := (id (Iff.symm (Real.sqrt_lt' hR)))

theorem mem_euclideanClosedBall_iff_vecEuclideanNorm_le
     (hR : 0 ≤ R) :
    x ∈ euclideanClosedBall x₀ R ↔
      vecEuclideanNorm (x - x₀) ≤ R := (id (Iff.symm (Real.sqrt_le_left hR)))

section
variable (x₀ y : Vec d) {r : ℝ} (hr : 0 < r)

include hr
theorem affine_mem_euclideanBall_iff_of_pos
     :
    r • y + x₀ ∈ euclideanBall x₀ r ↔
      y ∈ euclideanBall (0 : Vec d) 1 := by
  change euclideanSqDist (r • y + x₀) x₀ < r ^ 2 ↔
    euclideanSqDist y 0 < 1 ^ 2
  rw [euclideanSqDist_affine_center]
  have hr2  := sq_pos_of_pos hr
  norm_num
  constructor <;> intro h <;> nlinarith

theorem affine_mem_euclideanClosedBall_iff_of_pos
     :
    r • y + x₀ ∈ euclideanClosedBall x₀ r ↔
      y ∈ euclideanClosedBall (0 : Vec d) 1 := by
  change euclideanSqDist (r • y + x₀) x₀ ≤ r ^ 2 ↔
    euclideanSqDist y 0 ≤ 1 ^ 2
  rw [euclideanSqDist_affine_center]
  have hr2  := sq_pos_of_pos hr
  norm_num
  constructor <;> intro h <;> nlinarith
end


variable (x₀ : Vec d)

theorem euclideanBall_eq_translateSet_smul_unit_of_pos
     {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r =
      translateSet x₀ (r • euclideanBall (0 : Vec d) 1) := by
  ext z
  rw [mem_translateSet_iff_sub_mem]
  constructor
  · intro hz
    refine Set.mem_smul_set.2 ⟨r⁻¹ • (z - x₀), ?_, ?_⟩
    · have hpoint :
          r • (r⁻¹ • (z - x₀)) + x₀ ∈
            euclideanBall x₀ r := by
        have hpointEq :
            r • (r⁻¹ • (z - x₀)) + x₀ = z := by
          ext i
          simp [hr.ne', sub_eq_add_neg]
        simpa [hpointEq] using hz
      exact
        (affine_mem_euclideanBall_iff_of_pos
          x₀ (r⁻¹ • (z - x₀)) hr).1 hpoint
    · ext i
      simp [hr.ne']
  · intro hz
    rcases Set.mem_smul_set.1 hz with ⟨y, hy, hyEq⟩
    have hpoint  :=
      (affine_mem_euclideanBall_iff_of_pos x₀ y hr).2 hy
    simp_all

section
variable {R : ℝ} (hR : 0 < R)

include hR
theorem center_mem_euclideanBall
      :
    x₀ ∈ euclideanBall x₀ R := by
  change euclideanSqDist x₀ x₀ < R ^ 2
  rw [euclideanSqDist_self]
  exact sq_pos_of_pos hR

theorem euclideanBall_nonempty
      :
    (euclideanBall x₀ R).Nonempty :=
  ⟨x₀, center_mem_euclideanBall x₀ hR⟩
end


theorem euclideanBall_subset_euclideanClosedBall
     (R : ℝ) :
    euclideanBall x₀ R ⊆ euclideanClosedBall x₀ R := by
  intro x hx
  change euclideanSqDist x x₀ ≤ R ^ 2
  change euclideanSqDist x x₀ < R ^ 2 at hx
  exact le_of_lt hx

section
variable {x₀ : Vec d} {r R : ℝ} (hr : 0 ≤ r)

include hr
theorem euclideanBall_mono
     (hrR : r ≤ R) :
    euclideanBall x₀ r ⊆ euclideanBall x₀ R := by
  intro x hx
  change euclideanSqDist x x₀ < R ^ 2
  change euclideanSqDist x x₀ < r ^ 2 at hx
  nlinarith

theorem euclideanClosedBall_subset_euclideanBall
     (hrR : r < R) :
    euclideanClosedBall x₀ r ⊆ euclideanBall x₀ R := by
  intro x hx
  change euclideanSqDist x x₀ < R ^ 2
  change euclideanSqDist x x₀ ≤ r ^ 2 at hx
  nlinarith
end


theorem euclideanSqDist_weighted_add_le
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (x y x₀ : Vec d) :
    euclideanSqDist (a • x + b • y) x₀ ≤
      a * euclideanSqDist x x₀ +
        b * euclideanSqDist y x₀ := by
  have hsub :
      (a • x + b • y) - x₀ =
        a • (x - x₀) + b • (y - x₀) := by
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      a * x i + b * y i - x₀ i =
          a * x i + b * y i - (a + b) * x₀ i := by
        rw [hab]
        ring
      _ = a * (x i - x₀ i) + b * (y i - x₀ i) := by
        ring
  rw [euclideanSqDist, hsub, euclideanSqDist]
  exact vecNormSq_weighted_add_le ha hb hab (x - x₀) (y - x₀)

theorem convex_euclideanBall
    (x₀ : Vec d) (R : ℝ) :
    Convex ℝ (euclideanBall x₀ R) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  change euclideanSqDist (a • x + b • y) x₀ < R ^ 2

  by_cases ha_zero : a = 0
  · aesop
  ·




    exact (euclideanSqDist_weighted_add_le ha hb hab x y x₀).trans_lt ((add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx (lt_of_le_of_ne ha (Ne.symm ha_zero))) (mul_le_mul_of_nonneg_left (le_of_lt hy) hb)).trans_eq (by
        nlinarith))

end PDE
