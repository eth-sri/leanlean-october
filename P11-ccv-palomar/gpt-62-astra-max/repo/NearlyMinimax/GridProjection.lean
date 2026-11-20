module

public import NearlyMinimax.CellProjection

@[expose] public section

open Matrix MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace NearlyMinimax

/-- A regular-grid cell index, with the cube's right endpoint assigned
to the last cell. -/
def regularGridIndex (k : ℕ) (hk : 0 < k) (x : ℝ) : Fin k :=
  ⟨min ⌊(k : ℝ) * x⌋₊ (k - 1), (min_le_right _ _).trans_lt (by omega)⟩

variable {d k : ℕ} (hk : 0 < k) (c : Fin d → Fin k)

/-- Product cell label of a covariate. -/
def regularGridCell (k : ℕ) (hk : 0 < k) (x : Covariate d) : Fin d → Fin k :=
  fun i => regularGridIndex k hk (x i)

/-- The regular-grid label at dyadic level `j`. -/
abbrev dyadicGridLabel (j : ℕ) {d : ℕ} : Covariate d → Fin d → Fin (2^j) :=
  regularGridCell (2^j) (by positivity)

/-- The lower corner of an actual regular-grid cell. -/
def regularGridCorner : Covariate d :=
  fun i => (c i : ℝ) / k

/-- The explicit floor-based label and corner have the claimed cell
radius, including observations on the cube's right boundary. -/
theorem regular_grid_index_radius {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |x - (regularGridIndex k hk x : ℝ) / k| ≤ 1 / k := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  let m := ⌊(k : ℝ) * x⌋₊
  have hfloor  := Nat.floor_le (mul_nonneg hkreal.le hx0)
  have hmin : ((min m (k - 1) : ℕ) : ℝ) ≤ m := by bound
  have hcorner : (regularGridIndex k hk x : ℝ) / k ≤ x := by
    apply (div_le_iff₀ hkreal).mpr
    change ((min m (k - 1) : ℕ) : ℝ) ≤ _
    nlinarith
  rw [abs_of_nonneg (sub_nonneg.mpr hcorner)]
  have hsub : x - (regularGridIndex k hk x : ℝ) / k =
      (x * k - (regularGridIndex k hk x : ℝ)) / k := by field_simp
  rw [hsub]
  apply (div_le_div_iff_of_pos_right hkreal).mpr
  change x * k - ((min m (k - 1) : ℕ) : ℝ) ≤ 1
  by_cases hm : m ≤ k - 1
  · rw [min_eq_left hm]
    have hlt : (k : ℝ) * x < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    nlinarith
  · have hm' : k - 1 ≤ m := by omega
    rw [min_eq_right hm', Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    nlinarith [mul_le_mul_of_nonneg_right hx1 hkreal.le]

include hk in
/-- Every chosen cell corner belongs to the model's design cube. -/
theorem regular_grid_corner_mem_cube : regularGridCorner c ∈ unitCube d := by
  intro i
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨div_nonneg (Nat.cast_nonneg _) hkreal.le, ?_⟩
  apply (div_le_iff₀ hkreal).mpr
  simp

/-- The regular-grid radius follows directly from the covariate's cube
membership, with no assumed approximation property. -/
theorem regular_grid_cell_radius
    {x : Covariate d} (hx : x ∈ unitCube d) (i : Fin d) :
    |x i - regularGridCorner (regularGridCell k hk x) i| ≤ 1 / k :=
  regular_grid_index_radius hk (hx i).1 (hx i).2

/-- Grid labels are Borel despite the floor discontinuities. -/
theorem regular_grid_index_measurable :
    Measurable (regularGridIndex k hk) := by
  let f : ℕ → Fin k := fun m => ⟨min m (k - 1), (min_le_right _ _).trans_lt (by omega)⟩
  exact (measurable_of_countable f).comp ((measurable_const.mul measurable_id).nat_floor)

theorem regular_grid_cell_measurable (k : ℕ) (hk : 0 < k) :
    Measurable (regularGridCell (d := d) k hk) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (regular_grid_index_measurable hk).comp (measurable_pi_apply i)

end NearlyMinimax
