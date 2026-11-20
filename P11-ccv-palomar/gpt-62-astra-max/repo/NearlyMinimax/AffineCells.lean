module

public import NearlyMinimax.AnchoredMoments
public import NearlyMinimax.DyadicPilotFeatures


@[expose] public section

/-! Exact changes of variables for the actual regular-grid cells. -/

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators ENNReal
namespace NearlyMinimax

section
variable {d k : ℕ} (c : Fin d → Fin k)

def gridAffine (w : Covariate d) : Covariate d :=
  regularGridCorner c + (k : ℝ)⁻¹ • w

def gridClosedBox : Set (Covariate d) :=
  Icc (regularGridCorner c) (regularGridCorner c + fun _ => (k : ℝ)⁻¹)

end

section
variable {d : ℕ} (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k)
include hk

def gridAffineEquiv :
    Covariate d ≃ᵐ Covariate d :=
  ((Homeomorph.smul (Units.mk0 ((k : ℝ)⁻¹) (by positivity))).trans
    (Homeomorph.addLeft (regularGridCorner c))).toMeasurableEquiv

@[simp] theorem gridAffineEquiv_apply (w : Covariate d) : gridAffineEquiv k hk c w = gridAffine c w := rfl

theorem gridAffine_preimage_box :
    gridAffine c ⁻¹' gridClosedBox c = unitCube d := by
  ext w
  change ((∀ i, regularGridCorner c i ≤ regularGridCorner c i + (k : ℝ)⁻¹ * w i) ∧
    (∀ i, regularGridCorner c i + (k : ℝ)⁻¹ * w i ≤ regularGridCorner c i + (k : ℝ)⁻¹)) ↔
    ∀ i, 0 ≤ w i ∧ w i ≤ 1
  constructor <;> aesop

end

section
variable {d k : ℕ} (hk : 0 < k) (c : Fin d → Fin k)
include hk

theorem gridClosedBox_subset_cube : gridClosedBox c ⊆ unitCube d := by
  intro z hz i
  refine ⟨(regular_grid_corner_mem_cube hk c i).1.trans (hz.1 i), ?_⟩
  apply (hz.2 i).trans
  change (c i) / k + (k : ℝ)⁻¹ ≤ 1
  have hc : ((c i).val : ℝ) + 1 ≤ k := by exact_mod_cast (c i).isLt
  have he : (c i) / k + (k : ℝ)⁻¹ = ((c i) + 1) / k := by ring
  rw [he]
  bound

theorem gridAffine_map_volume :
    volume.map (gridAffine c) =
      ENNReal.ofReal (k ^ d) • volume := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  rw [show gridAffine c = (fun z => regularGridCorner c + z) ∘
    (fun w => (k : ℝ)⁻¹ • w) by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_addHaar_smul volume (inv_ne_zero hkr.ne'),
     map_add_left_eq_self]
  simp

/-- The Jacobian is the exact number of regular-grid cells. -/
theorem gridAffine_map_cubeVolume :
    (cubeVolume d).map (gridAffine c) =
      ENNReal.ofReal (k ^ d) • volume.restrict (gridClosedBox c) := by
  let e := gridAffineEquiv k hk c
  have hpre : e ⁻¹' gridClosedBox c = unitCube d := gridAffine_preimage_box k hk c
  have h := e.restrict_map volume (gridClosedBox c)
  rw [hpre] at h
  change ((volume.restrict (unitCube d)).map e) = _
  rw [← h]
  change (volume.map (gridAffine c)).restrict _ = _
  rw [gridAffine_map_volume hk c, Measure.restrict_smul]

theorem gridAffine_integral
    (f : Covariate d → ℝ) :
    (∫ w, f (gridAffine c w) ∂cubeVolume d) =
      k ^ d * ∫ z in gridClosedBox c, f z := by
  have h := integral_map_equiv (μ := cubeVolume d) (gridAffineEquiv k hk c) f
  simp at h
  rw [← h]
  change (∫ z, f z ∂(cubeVolume d).map (gridAffine c)) = _
  rw [gridAffine_map_cubeVolume hk c, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]
  rfl

end

section
variable {d : ℕ} (k : ℕ) (hk : 0 < k)
include hk

theorem gridAffine_ae_pullback (c : Fin d → Fin k)
    {P : Covariate d → Prop} (hP : ∀ᵐ z ∂cubeVolume d, P z) :
    ∀ᵐ w ∂cubeVolume d, P (gridAffine c w) := by
  apply ae_of_ae_map (gridAffineEquiv k hk c).measurable.aemeasurable
  change ∀ᵐ z ∂(cubeVolume d).map (gridAffine c), P z
  rw [gridAffine_map_cubeVolume hk c]
  exact Measure.ae_smul_measure
    (ae_restrict_of_ae_restrict_of_subset (gridClosedBox_subset_cube hk c) hP) _

def gridNormalizedAnchor (x : Covariate d) : Covariate d :=
  fun i => k * (x i - regularGridCorner (regularGridCell k hk x) i)

theorem gridNormalizedAnchor_mem_cube
    {x : Covariate d} (hx : x ∈ unitCube d) : gridNormalizedAnchor k hk x ∈ unitCube d := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  intro i
  constructor
  · exact mul_nonneg hkr.le (sub_nonneg.mpr (regular_grid_cell_corner_le hk hx i))
  · exact (mul_le_mul_of_nonneg_left ((abs_le.mp (regular_grid_cell_radius hk hx i)).2) hkr.le).trans_eq (by field_simp)

end

theorem dyadicAnchoredFeature_affine {d ℓ : ℕ} (j : ℕ) (x w : Covariate d)
    (γ : AnchoredIndex d ℓ) :
    dyadicAnchoredFeature j x
      (gridAffine (k := (2 ^ j)) (regularGridCell _ (by positivity) x) w) γ =
      anchoredFeature (gridNormalizedAnchor (2 ^ j) (by positivity) x) w γ := by
  unfold dyadicAnchoredFeature anchoredFeature
  congr 1
  funext i
  simp [gridAffine, gridNormalizedAnchor]
  field_simp
  ring

variable {d k : ℕ} (hk : 0 < k) (c : Fin d → Fin k)

theorem regular_grid_index_eq_of_box {c : Fin k} {z : ℝ}
    (hlo : c / k ≤ z) (hhi : z < c / k + (k : ℝ)⁻¹) :
    regularGridIndex k hk z = c := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hf : ⌊k * z⌋₊ = c.val := by
    apply (Nat.floor_eq_iff (mul_nonneg hkr.le ((div_nonneg (Nat.cast_nonneg _) hkr.le).trans hlo))).2
    constructor
    · have h := (div_le_iff₀ hkr).mp hlo
      nlinarith
    · have h := mul_lt_mul_of_pos_left hhi hkr
      have he : k * (c / k + (k : ℝ)⁻¹) = c + 1 := by field_simp
      bound
  apply Fin.ext
  change min _ _ = c.val
  omega

/-- Grid fibers and closed affine boxes differ only on coordinate faces. -/
theorem regular_grid_fiber_ae_box :
    ((regularGridCell k hk) ⁻¹' {c} ∩ unitCube d) =ᵐ[volume] gridClosedBox c := by
  have hfaces : ∀ᵐ z : Covariate d ∂volume,
      ∀ i, z i ≠ regularGridCorner c i + (k : ℝ)⁻¹ := by
    rw [ae_all_iff]
    intro i
    apply ae_iff.mpr
    simp
    exact Measure.pi_eval_preimage_null (fun _ => volume) (measure_singleton _)
  filter_upwards [hfaces] with z hz
  apply propext
  constructor
  · intro hzcell
    have hc : regularGridCell k hk z = c := hzcell.1
    constructor <;> intro i
    · simpa only [hc] using regular_grid_cell_corner_le hk hzcell.2 i
    · have h := (abs_le.mp (regular_grid_cell_radius hk hzcell.2 i)).2
      simp only [hc] at h
      simpa using (by linarith : z i ≤ regularGridCorner c i + 1 / k)
  · intro hzbox
    refine ⟨?_, gridClosedBox_subset_cube hk c hzbox⟩
    funext i
    apply regular_grid_index_eq_of_box hk (hzbox.1 i)
    exact lt_of_le_of_ne (hzbox.2 i) (hz i)

theorem regular_grid_fiber_restrict (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k) :
    (cubeVolume d).restrict ((regularGridCell k hk) ⁻¹' {c}) =
      volume.restrict (gridClosedBox c) := by
  rw [cubeVolume, Measure.restrict_restrict
    ((measurableSet_singleton c).preimage (regular_grid_cell_measurable k hk))]
  exact Measure.restrict_congr_set (regular_grid_fiber_ae_box hk c)

/-- The original cell integral, with the exact Jacobian and boundary convention. -/
theorem regular_grid_cell_integral
    (f : Covariate d → ℝ) :
    k ^ d * (∫ z in (regularGridCell k hk) ⁻¹' {c}, f z ∂cubeVolume d) =
      ∫ w, f (gridAffine c w) ∂cubeVolume d := by
  rw [regular_grid_fiber_restrict]
  exact (gridAffine_integral hk c f).symm

end NearlyMinimax
