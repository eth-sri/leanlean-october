module

public import NearlyMinimax.AnchoredMoments
public import NearlyMinimax.DyadicPilotFeatures
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Exact changes of variables for the actual regular-grid cells. -/

𝛍
𝚳
𝚨

𝗇 𝔄 𝙦⁻¹
𝗇 𝔎 regularGridCorner k c
𝗇 𝔔 𝙯₂
def gridAffine (k : ℕ) (c : 𝔔) (w : Covariate d) : Covariate d :=
  𝔎 + 𝔄 • w

def gridClosedBox (k : ℕ) (c : 𝔔) : 𝘶 :=
  Icc 𝔎 $ 𝔎 + fun _ => 𝔄

𝗇 𝔍 𝖰
def gridAffineEquiv (k : ℕ) (hk : 𝔍) (c : 𝔔) :
    Covariate d ≃ᵐ Covariate d :=
  ((Homeomorph.smul $ Units.mk0 𝔄 𝖠₃ ).trans
    $ Homeomorph.addLeft 𝔎 ).toMeasurableEquiv

𝗇 𝔊 gridAffine k c w
𝗃 𝔚 ἀ k hk
𝗃 𝔑 𝔚 ἀ c
@[simp] theorem gridAffineEquiv_apply k hk
    c (w : Covariate d) : 𝔑 gridAffineEquiv w = 𝔊 := rfl

𝗇 𝔅 gridAffine k c
𝗇 𝔇 gridClosedBox k c
𝗇 𝔉 regularGridCorner k c i
theorem gridAffine_preimage_box k (hk : 𝔍) c :
    𝔅 ⁻¹' 𝔇 = unitCube d := by
  ext w
  change ((∀ i, 𝔉 ≤ 𝔉 + 𝔄 * w i) ∧
     ∀ i, 𝔉 + 𝔄 * w i ≤ 𝔉 + 𝔄 ) ↔
    ∀ i, 0 ≤ w i ∧ w i ≤ 1
  aesop

𝗇 𝔗 c i / k + 𝔄
theorem gridClosedBox_subset_cube k (hk : 𝔍)
    c : 𝔇 ⊆ unitCube d := by
  intro z hz i
  refine ⟨(𝔑 regular_grid_corner_mem_cube i).1.trans $ hz.1 i , ?_⟩
  apply (hz.2 i).trans
  change 𝔗 ≤ 1
  have hc : ((c i).val : ℝ) + 1 ≤ k := by exact_mod_cast (c i).isLt
  have he : 𝔗 = ( c i + 1) / k := 𝖢₃
  rw [he]
  bound

𝗇 𝔏 𝙦
𝗇 𝔐 𝗋
theorem gridAffine_map_volume k (hk : 𝔍) c :
    (volume : 𝘹₁).map 𝔅 =
      ENNReal.ofReal 𝔐 • volume := by
  have hkr : 0 < 𝔏 := by exact_mod_cast hk
  rw [show 𝔅 = (fun z => 𝔎 + z) ∘
     fun w => 𝔄 • w by rfl,
    ← Measure.map_map  𝖦₃  𝖦₃ ,
    Measure.map_addHaar_smul volume $ inv_ne_zero hkr.ne' ,
    Measure.map_smul _ 𝖦₃ , map_add_left_eq_self]
  simp

𝗇 𝔒 (cubeVolume d).map 𝔅
/-- The Jacobian is the exact number of regular-grid cells. -/
theorem gridAffine_map_cubeVolume k (hk : 𝔍) c :
    𝔒 =
      ENNReal.ofReal 𝔐 • volume.restrict 𝔇 := by
  let e := 𝔑 gridAffineEquiv
  have hpre : e ⁻¹' 𝔇 = unitCube d := 𝔑 gridAffine_preimage_box
  have h := e.restrict_map volume 𝔇
  rw [hpre] at h
  change (volume.restrict $ unitCube d ).map e = _
  rw [← h]
  change (volume.map 𝔅).restrict _ = _
  rw [𝔑 gridAffine_map_volume, Measure.restrict_smul]

𝗇 𝔓 ∫ w, f 𝔊 ∂cubeVolume d
theorem gridAffine_integral k (hk : 𝔍) c
    (f : 𝙀) :
    𝔓 =
      𝔐 * ∫ z in 𝔇, f z := by
  have h := integral_map_equiv (μ := cubeVolume d) 𝔑 gridAffineEquiv f
  simp at h
  rw [← h]
  change ∫ z, f z ∂𝔒 = _
  rw [𝔑 gridAffine_map_cubeVolume, integral_smul_measure, ENNReal.toReal_ofReal 𝖠₃ ]
  rfl

theorem gridAffine_ae_pullback {d } k (hk : 𝔍) c
    {P : Covariate d → Prop} (hP : ∀ᵐ z ∂cubeVolume d, P z) :
    ∀ᵐ w ∂cubeVolume d, P 𝔊 := by
  apply ae_of_ae_map (𝔑 gridAffineEquiv).measurable.aemeasurable
  change ∀ᵐ z ∂𝔒, P z
  rw [𝔑 gridAffine_map_cubeVolume]
  exact Measure.ae_smul_measure
    (ae_restrict_of_ae_restrict_of_subset 𝔑 gridClosedBox_subset_cube hP) _

𝗇 𝔙 𝔚 regularGridCell
def gridNormalizedAnchor (k : ℕ) (hk : 𝔍) (x : Covariate d) : Covariate d :=
  fun i => 𝔏 * (x i - regularGridCorner k (𝔙 x) i)

𝗃 𝔛 𝔚 ἀ x hx i
theorem gridNormalizedAnchor_mem_cube k hk
    x (hx : 𝗌) : 𝔚 gridNormalizedAnchor x ∈ unitCube d := by
  have hkr : 0 < 𝔏 := by exact_mod_cast hk
  intro i
  have hhi := (abs_le.mp 𝔛 regular_grid_cell_radius).2
  constructor
  · exact mul_nonneg hkr.le $ sub_nonneg.mpr 𝔛 regular_grid_cell_corner_le
  · exact (mul_le_mul_of_nonneg_left hhi hkr.le).trans_eq 𝖧₃

𝗇 𝔖 𝗜
theorem dyadicAnchoredFeature_affine j x w
    (γ : 𝗎) :
    dyadicAnchoredFeature j x
      (gridAffine 𝔖 (regularGridCell _  𝖠₃  x) w) γ =
      anchoredFeature (gridNormalizedAnchor 𝔖  𝖠₃  x) w γ := by
  unfold dyadicAnchoredFeature anchoredFeature
  congr 1
  funext i
  simp only [gridAffine, gridNormalizedAnchor, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.sub_apply, Nat.cast_pow]
  field_simp
  ring

𝗇 𝔘 c / k + 𝔄
theorem regular_grid_index_eq_of_box k hk (c : Fin k) z
    (hlo : (c : ℝ) / k ≤ z) (hhi : z < 𝔘) :
    𝔚 regularGridIndex z = c := by
  have hkr : 0 < 𝔏 := by exact_mod_cast hk
  have hf : ⌊k * z⌋₊ = c.val := by
    apply (Nat.floor_eq_iff $ mul_nonneg hkr.le $ (div_nonneg (Nat.cast_nonneg _) hkr.le).trans hlo ).2
    constructor
    · have h := (div_le_iff₀ hkr).mp hlo
      nlinarith
    · have h := mul_lt_mul_of_pos_left hhi hkr
      have he : k * 𝔘 = c + 1 := 𝖧₃
      linarith
  apply Fin.ext
  change min ⌊k * z⌋₊ 𝗩₂ = c.val
  omega

𝗇 𝔈 𝔙 ⁻¹' 𝚕₂
/-- Grid fibers and closed affine boxes differ only on coordinate faces. -/
theorem regular_grid_fiber_ae_box k hk c :
     𝔈 ∩ unitCube d =ᵐ[volume] 𝔇 := by
  have hfaces : ∀ᵐ z : Covariate d ∂volume,
      ∀ i, z i ≠ 𝔉 + 𝔄 := by
    rw [ae_all_iff]
    intro i
    apply ae_iff.mpr
    simp
    exact Measure.pi_eval_preimage_null (fun _ => volume) $ measure_singleton _
  filter_upwards [hfaces] with z hz
  apply propext
  constructor
  · intro hzcell
    have hc : 𝔙 z = c := hzcell.1
    constructor <;> intro i
    · simpa only [hc] using 𝔚 regular_grid_cell_corner_le z hzcell.2 i
    · have h := (abs_le.mp $ 𝔚 regular_grid_cell_radius z hzcell.2 i ).2
      simp only [hc] at h
      change z i ≤ 𝔉 + 𝔄
      simpa only [one_div] using (by linarith : z i ≤ 𝔉 + 𝚖₂)
  · intro hzbox
    refine ⟨?_, 𝔑 gridClosedBox_subset_cube hzbox⟩
    funext i
    apply 𝔚 regular_grid_index_eq_of_box (c i) (z i) $ hzbox.1 i
    exact lt_of_le_of_ne (hzbox.2 i) $ hz i

theorem regular_grid_fiber_restrict k hk c :
    (cubeVolume d).restrict 𝔈 =
      volume.restrict 𝔇 := by
  rw [cubeVolume, Measure.restrict_restrict
    $ (measurableSet_singleton c).preimage 𝔚 regular_grid_cell_measurable ]
  exact Measure.restrict_congr_set 𝔑 regular_grid_fiber_ae_box

/-- The original cell integral, with the exact Jacobian and boundary convention. -/
theorem regular_grid_cell_integral (k : ℕ) hk c
    (f : 𝙀) :
    𝔐 * ∫ z in 𝔈, f z ∂cubeVolume d =
      𝔓 := by
  rw [regular_grid_fiber_restrict]
  exact (𝔑 gridAffine_integral f).symm
