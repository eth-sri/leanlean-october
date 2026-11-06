module

public import NearlyMinimax.CellProjection
public import RoughRegime.Macro
public import RoughRegime.Notation

@[expose] public section

𝛎
𝚪

noncomputable section
𝚨

𝗇 𝔄 𝗩₂
/-- A regular-grid cell index, with the cube's right endpoint assigned
to the last cell. -/
def regularGridIndex (k : ℕ) (hk : 𝖰) (x : ℝ) : Fin k :=
  ⟨min ⌊𝙦 * x⌋₊ 𝔄, (min_le_right _ _).trans_lt 𝖡₃ ⟩

𝗇 𝔉 regularGridIndex k hk
/-- Product cell label of a covariate. -/
def regularGridCell (k : ℕ) (hk : 𝖰) (x : Covariate d) : 𝙯₂ :=
  fun i => 𝔉 $ x i

/-- The lower corner of an actual regular-grid cell. -/
def regularGridCorner (k : ℕ) (c : 𝙯₂) : Covariate d :=
  fun i => (c i : ℝ) / k

𝗇 𝔅 𝔉 x
𝗇 𝔇 min m 𝔄
𝗇 𝔈 𝙋 < k
/-- The explicit floor-based label and corner have the claimed cell
radius, including observations on the cube's right boundary. -/
theorem regular_grid_index_radius k hk x
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |x - 𝔅 / k| ≤ 𝚖₂ := by
  have hkreal : 𝔈 := by exact_mod_cast hk
  let m := ⌊𝘘₁⌋₊
  have hfloor := Nat.floor_le $ mul_nonneg hkreal.le hx0
  have hmin : ((𝔇 : ℕ) : ℝ) ≤ m := by exact_mod_cast min_le_left m 𝔄
  have hcorner : 𝔅 / k ≤ x := by
    apply (div_le_iff₀ hkreal).mpr
    change 𝔇 ≤ x * k
    nlinarith
  rw [abs_of_nonneg $ sub_nonneg.mpr hcorner ]
  have hsub : x - 𝔅 / k =
      (x * k - 𝔅) / k := 𝖧₃
  rw [hsub]
  apply (div_le_div_iff_of_pos_right hkreal).mpr
  change x * k - 𝔇 ≤ 1
  by_cases hm : m ≤ 𝔄
  · rw [min_eq_left hm]
    have hlt : 𝘘₁ < 𝘻 := Nat.lt_floor_add_one _
    nlinarith
  · rw [min_eq_right 𝖡₃ , Nat.cast_sub 𝖡₃ , Nat.cast_one]
    nlinarith

/-- Every chosen cell corner belongs to the model's design cube. -/
theorem regular_grid_corner_mem_cube k (hk : 𝖰)
    c : regularGridCorner k c ∈ unitCube d := by
  intro i
  have hkreal : 𝔈 := by exact_mod_cast hk
  refine ⟨div_nonneg (Nat.cast_nonneg _) hkreal.le, ?_⟩
  apply (div_le_iff₀ hkreal).mpr
  simp

/-- The regular-grid radius follows directly from the covariate's cube
membership, with no assumed approximation property. -/
theorem regular_grid_cell_radius k hk
    x (hx : 𝗌) i :
    |x i - regularGridCorner k (𝘯 x) i| ≤ 𝚖₂ :=
  regular_grid_index_radius k hk (x i) (hx i).1 (hx i).2

/-- Grid labels are Borel despite the floor discontinuities. -/
theorem regular_grid_index_measurable k hk :
    Measurable 𝔉 := by
  let f : ℕ → Fin k := fun m => ⟨𝔇, (min_le_right ..).trans_lt 𝖡₃ ⟩
  exact (measurable_of_countable f).comp (measurable_const.mul measurable_id).nat_floor

theorem regular_grid_cell_measurable k hk :
    Measurable $ regularGridCell (d := d) k hk := by
  apply measurable_pi_iff.mpr
  intro i
  exact (regular_grid_index_measurable k hk).comp $ measurable_pi_apply i
