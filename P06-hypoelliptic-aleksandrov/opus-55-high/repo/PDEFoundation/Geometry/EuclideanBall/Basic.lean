module

public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Geometry.Affine
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

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

/-- The explicit round Euclidean open ball. -/
def euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ < R ^ 2}

/-- The explicit round Euclidean closed ball. -/
def euclideanClosedBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ ≤ R ^ 2}

/-- The explicit Euclidean sphere. -/
def euclideanSphere {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ = R ^ 2}

variable {d : ℕ} (x₀ : Vec d) {R : ℝ}

@[simp]
theorem euclideanSqDist_self  (x : Vec d) :
    euclideanSqDist x x = 0 := by
  simp [euclideanSqDist, vecNormSq, vecDot]

theorem euclideanSqDist_nonneg  (x y : Vec d) :
    0 ≤ euclideanSqDist x y :=
  vecNormSq_nonneg _

theorem euclideanSqDist_add_right  (x y z : Vec d) :
    euclideanSqDist (x + z) (y + z) = euclideanSqDist x y := by
  have hsub : (x + z) - (y + z) = x - y := by
    simp
  simp [euclideanSqDist]

theorem euclideanSqDist_smul_smul 
    (r : ℝ) (x y : Vec d) :
    euclideanSqDist (r • x) (r • y) =
      r ^ 2 * euclideanSqDist x y := by
  have hsub : r • x - r • y = r • (x - y) := by
    simp [sub_eq_add_neg]
  rw [euclideanSqDist, hsub, vecNormSq_smul]
  rfl

theorem euclideanSqDist_affine_center 
    (x₀ y : Vec d) (r : ℝ) :
    euclideanSqDist (r • y + x₀) x₀ =
      r ^ 2 * euclideanSqDist y 0 := by
  calc
    euclideanSqDist _ x₀ =
        euclideanSqDist _ 0 := by
      simpa using euclideanSqDist_add_right _ 0 x₀
    _ = r ^ 2 * euclideanSqDist y 0 := by
      simpa using euclideanSqDist_smul_smul r y 0

theorem mem_euclideanBall_iff_vecEuclideanNorm_lt 
    {x₀ x : Vec d} {R : ℝ} (hR : 0 < R) :
    x ∈ euclideanBall x₀ R ↔
      vecEuclideanNorm (x - x₀) < R := (Real.sqrt_lt' hR).symm

theorem mem_euclideanClosedBall_iff_vecEuclideanNorm_le 
    {x₀ x : Vec d} {R : ℝ} (hR : 0 ≤ R) :
    x ∈ euclideanClosedBall x₀ R ↔
      vecEuclideanNorm (x - x₀) ≤ R := (Real.sqrt_le_left hR).symm

theorem affine_mem_euclideanBall_iff_of_pos 
    (x₀ y : Vec d) {r : ℝ} (hr : 0 < r) :
    r • y + x₀ ∈ euclideanBall x₀ r ↔
      y ∈ euclideanBall (0 : Vec d) 1 := by
  change euclideanSqDist _ x₀ < r ^ 2 ↔
    euclideanSqDist y 0 < 1 ^ 2
  rw [euclideanSqDist_affine_center]
  simp_all

theorem affine_mem_euclideanClosedBall_iff_of_pos 
    (x₀ y : Vec d) {r : ℝ} (hr : 0 < r) :
    r • y + x₀ ∈ euclideanClosedBall x₀ r ↔
      y ∈ euclideanClosedBall (0 : Vec d) 1 := by
  change euclideanSqDist _ x₀ ≤ r ^ 2 ↔
    euclideanSqDist y 0 ≤ 1 ^ 2
  rw [euclideanSqDist_affine_center]
  simp_all

theorem euclideanBall_eq_translateSet_smul_unit_of_pos  {r : ℝ} (hr : 0 < r) :
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
          simp [hr.ne']
        simp_all
      exact
        (affine_mem_euclideanBall_iff_of_pos
          x₀ _ hr).1 hpoint
    · simp [hr.ne']
  · intro hz
    rcases Set.mem_smul_set.1 hz with ⟨y, hy, hyEq⟩
    have hpoint :
        r • y + x₀ ∈ euclideanBall x₀ r :=
      (affine_mem_euclideanBall_iff_of_pos x₀ y hr).2 hy
    simp_all

theorem center_mem_euclideanBall  (hR : 0 < R) :
    x₀ ∈ euclideanBall x₀ R := by
  change euclideanSqDist x₀ x₀ < R ^ 2
  simp_all

theorem euclideanBall_nonempty  (hR : 0 < R) :
    (euclideanBall x₀ R).Nonempty :=
  ⟨x₀, center_mem_euclideanBall x₀ hR⟩

theorem euclideanBall_subset_euclideanClosedBall  (R : ℝ) :
    euclideanBall x₀ R ⊆ euclideanClosedBall x₀ R := by
  intro x hx
  change euclideanSqDist x x₀ ≤ R ^ 2
  exact le_of_lt hx

theorem euclideanBall_mono 
    {x₀ : Vec d} {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    euclideanBall x₀ r ⊆ euclideanBall x₀ R := by
  intro x hx
  change euclideanSqDist x x₀ < R ^ 2
  change euclideanSqDist x x₀ < r ^ 2 at hx
  nlinarith

theorem euclideanClosedBall_subset_euclideanBall 
    {x₀ : Vec d} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    euclideanClosedBall x₀ r ⊆ euclideanBall x₀ R := by
  intro x hx
  change euclideanSqDist x x₀ < R ^ 2
  change euclideanSqDist x x₀ ≤ r ^ 2 at hx
  nlinarith

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
    calc
      a * x i + b * y i - x₀ i =
          a * x i + b * y i - (a + b) * x₀ i := by
        simp_all
      _ = a * (x i - x₀ i) + b * (y i - x₀ i) := by
        ring
  rw [euclideanSqDist, hsub]
  exact vecNormSq_weighted_add_le ha hb hab _ _

theorem convex_euclideanBall  (R : ℝ) :
    Convex ℝ (euclideanBall x₀ R) := by
  intro x hx y hy a b ha hb hab
  have hconv :=
    euclideanSqDist_weighted_add_le ha hb hab x y x₀
  by_cases ha_zero : a = 0
  · simp_all
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_zero)
    have hx_strict :
        a * euclideanSqDist x x₀ < a * R ^ 2 :=
      mul_lt_mul_of_pos_left hx ha_pos
    have hy_le :
        b * euclideanSqDist y x₀ ≤ b * R ^ 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hy) hb
    have hweighted :
        a * euclideanSqDist x x₀ +
            b * euclideanSqDist y x₀ <
          a * R ^ 2 + b * R ^ 2 :=
      add_lt_add_of_lt_of_le hx_strict hy_le
    have hright : a * R ^ 2 + b * R ^ 2 = R ^ 2 := by
      nlinarith
    exact hconv.trans_lt (hweighted.trans_eq hright)

end PDE
