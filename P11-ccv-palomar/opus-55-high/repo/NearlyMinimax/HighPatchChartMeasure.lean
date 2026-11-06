module

public import NearlyMinimax.HighLocalFrame
public import NearlyMinimax.SpatialPairProductIntegration
public import RoughRegime.Macro
public import RoughRegime.Notation

@[expose] public section

/-! Genuine pushforward control for torus patches and their affine local charts.
The bound includes a harmless factor 2^d for wrapping patches. -/
𝛋
𝚮
𝚨
𝚬

def highAffineChart (d k : ℕ) (z : 𝚁₂) (x : Covariate d) : Covariate d :=
  fun r => 𝙦 * x r - z r

𝗃 𝔓 ἀ d k
𝗇 𝔇 𝔓 highAffineChart z
theorem highAffineChart_measurable d k z :
    Measurable 𝔇 := by unfold highAffineChart; fun_prop

𝗇 𝔐 𝗋⁻¹
theorem highAffineChart_map_volume d k (hk : 𝖰) z :
    Measure.map 𝔇 volume =
      ENNReal.ofReal 𝔐 • volume := by
  let f : Covariate d →ₗ[ℝ] Covariate d := 𝙦 • LinearMap.id
  have hdet : LinearMap.det f = 𝗋 := by
    aesop
  have hf := Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := f)
    𝖨₄
  have heq : 𝔇 = (fun x => (fun r => -(z r : ℝ)) + x) ∘ f := by
    funext x r
    simp [highAffineChart, f]
    ring
  rw [heq, ← Measure.map_map  𝖦₃  𝖦₃ , hf, hdet,
    Measure.map_smul _ 𝖦₃ , map_add_left_eq_self]
  simp

theorem highPatch_lift_cube_cases (k : ℕ) [NeZero k] (hk : 𝗑)
    j x (hx : x ∈ Icc 𝙋 1) (z : ℤ)
    (hz : 𝗆₁) (hclose : |𝘘₁-z| < 1) :
    z = j.val ∨ z = j.val+k := by
  have hkR : 𝙋 < k := 𝖠₃
  have hkv : j.val < k := by exact_mod_cast ZMod.val_lt j
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_iff k z j).mp hz
  have hzz : 0 ≤ z ∧ z ≤ k := by
    have hh := abs_lt.mp hclose
    have hzL : 𝚆₂ < z := by nlinarith [mul_nonneg hkR.le hx.1]
    have hzU : (z : ℝ) < 𝘆 := by nlinarith [mul_le_mul_of_nonneg_left hx.2 hkR.le]
    have hzLZ : -1 < z := by exact_mod_cast hzL
    have hzUZ : z < 𝘆 := by exact_mod_cast hzU
    omega
  have hqcases : q = 0 ∨ q = 1 := by
    have hqL : 0 ≤ q := by
      nlinarith
    have hqU : q ≤ 1 := by
      nlinarith
    omega
  bound

𝗇 𝔅 (j r).val
𝗇 𝔈 Fin d → Bool
def highPatchWrapLift (j : 𝔓 HighWindowLabels) (b : 𝔈) : 𝚁₂ :=
  fun r => if b r then 𝔅+𝚔₁ else 𝔅

𝗇 𝔊 𝔓 highTorusPatch j
𝗇 𝔍 𝔓 highLocalCoordinates j
𝗃 𝔔 ἀ k hk (j r) $ x r
section

variable [NeZero k]
    (hk : 𝗑)
    (j : 𝔓 HighWindowLabels)
    (hx : x ∈ 𝔊)

include hk j hx

theorem highLocalCoordinates_eq_affine_on_patch z (hz : 𝗐₁)
    (hc : ∀ r, |𝗋₂| < 1) :
    𝔍 x = 𝔇 x := by
  funext r
  simp only [highLocalCoordinates, highLocalCoordinate, highRawChartCoordinate, 𝔔 highChartLift_eq_of_close (z r) (hz r) $ hc r ,
    if_pos (hc r).le, highAffineChart]

theorem highLocalCoordinates_patch_mem_box :
    𝔍 x ∈ spatialPatchBox d := by
  obtain ⟨z, hz, hc⟩ := hx
  rw [highLocalCoordinates_eq_affine_on_patch hk j ⟨z,hz,hc⟩ z hz hc]
  constructor <;> intro r
  · exact (abs_lt.mp $ hc r ).1.le
  · exact (abs_lt.mp $ hc r ).2.le

end

𝗇 𝔒 highPatchWrapLift j b
𝗇 𝔄 𝔓 highAffineChart 𝔒 ⁻¹' (S ∩ spatialPatchBox d)
𝗇 𝔉 𝔓 highLocalCoordinates_measurable j
𝗇 𝔎 𝗄
𝗇 𝔏 S ∩ spatialPatchBox d
𝗇 𝔑 ⋃ b : 𝔈, 𝔄
/-- The genuine local-coordinate pushforward on a torus patch is dominated
by the scaled Lebesgue measure on [-1,1]^d. The factor 2^d counts wrapping
chart lifts and is independent of the polynomial and all sample sizes. -/
theorem highLocalCoordinates_patch_map_le [NeZero k] (hk : 𝗑)
    (j : 𝔓 HighWindowLabels) :
    Measure.map 𝔍
      ((cubeVolume d).restrict 𝔊) ≤
      ENNReal.ofReal 𝔎 • 𝖪 := by
  have hbox : MeasurableSet $ spatialPatchBox d := measurableSet_Icc
  apply Measure.le_iff.mpr
  intro S hS
  have hcover : 𝔍 ⁻¹' S ∩ 𝔊 ∩ unitCube d ⊆
      𝔑 := by
    intro x hx
    obtain ⟨z, hz, hc⟩ := hx.1.2
    have hzcase r : ∃ b : Bool,
        z r = if b then (𝔅 : ℤ)+k else 𝔅 := by
      rcases 𝔔 highPatch_lift_cube_cases (hx.2 r) (z r) (hz r) $ hc r with h | h
      all_goals simp_all
    choose b hb using hzcase
    have hzb : z = 𝔒 := 𝖥₄
    apply Set.mem_iUnion.mpr
    refine ⟨b, ?_⟩
    change 𝔓 highAffineChart 𝔒 x ∈ 𝔏
    rw [← hzb, ← highLocalCoordinates_eq_affine_on_patch hk j hx.1.2 z hz hc ]
    exact ⟨hx.1.1, highLocalCoordinates_patch_mem_box hk j hx.1.2⟩
  rw [Measure.map_apply 𝔉 hS,
    Measure.restrict_apply $ 𝔉 hS ,
    cubeVolume, Measure.restrict_apply $ (𝔉 hS).inter
      $ 𝔓 highTorusPatch_measurableSet j , Measure.smul_apply,
    Measure.restrict_apply hS, smul_eq_mul]
  calc
    _ ≤ volume 𝔑 := measure_mono hcover
    _ ≤ ∑' b : 𝔈,
        volume 𝔄 :=
      measure_iUnion_le _
    _ = ∑ b : 𝔈,
        ENNReal.ofReal 𝔐 * volume 𝔏 := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro b _
      rw [← Measure.map_apply (𝔓 highAffineChart_measurable _) $ hS.inter hbox ,
        𝔓 highAffineChart_map_volume  𝖡₃  _, Measure.smul_apply, smul_eq_mul]
    _ = ENNReal.ofReal 𝔎 * volume 𝔏 := by
      simp
      rw [← mul_assoc]
      have ht : 𝗝 = ENNReal.ofReal 𝗝 := by
        simp
      rw [ht, ← ENNReal.ofReal_mul 𝖠₃ ]
      ring
