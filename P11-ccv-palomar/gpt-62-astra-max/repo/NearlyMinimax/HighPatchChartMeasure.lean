module

public import NearlyMinimax.HighLocalFrame
public import NearlyMinimax.SpatialPairProductIntegration

@[expose] public section

/-! Genuine pushforward control for torus patches and their affine local charts.
The bound includes a harmless factor 2^d for wrapping patches. -/
noncomputable section
open Set MeasureTheory Function
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

def highAffineChart {d : ℕ} (k : ℕ) (z : Fin d → ℤ) (x : Covariate d) : Covariate d :=
  fun r => k * x r - z r

section
variable (d k : ℕ) (hk : 0 < k) (z : Fin d → ℤ)

theorem highAffineChart_measurable :
    Measurable (highAffineChart k z) := by unfold highAffineChart; fun_prop

include hk in
theorem highAffineChart_map_volume :
    Measure.map (highAffineChart k z) volume =
      ENNReal.ofReal (k^d)⁻¹ • volume := by
  let f : Covariate d →ₗ[ℝ] Covariate d := (k : ℝ) • LinearMap.id
  have hdet : LinearMap.det f = k^d := by
    simp [f, LinearMap.det_smul, LinearMap.det_id]
  have hf := Real.map_linearMap_volume_pi_eq_smul_volume_pi
    (by rw [hdet]; positivity)
  have heq : highAffineChart k z = (fun x => (fun r => -(z r : ℝ)) + x) ∘ f := by
    funext x r
    simp [highAffineChart, f]
    ring
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop), hf, hdet,
     map_add_left_eq_self]
  simp

end

theorem highPatch_lift_cube_cases {k : ℕ} [NeZero k] (hk : 4 ≤ k)
    {j : ZMod k} {x : ℝ} (hx : x ∈ Icc 0 1) {z : ℤ}
    (hz : z = j) (hclose : |k*x-z| < 1) :
    z = j.val ∨ z = j.val+k := by
  have hkR : (0 : ℝ) < k := by positivity
  have hkv : j.val < k := by exact_mod_cast ZMod.val_lt j
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_iff k z j).mp hz
  have hzz : 0 ≤ z ∧ z ≤ k := by
    have hh := abs_lt.mp hclose
    have hzL : (-1 : ℝ) < z := by nlinarith [mul_nonneg hkR.le hx.1]
    have hzU : (z : ℝ) < k+1 := by nlinarith [mul_le_mul_of_nonneg_left hx.2 hkR.le]
    have hzLZ : (-1) < z := by exact_mod_cast hzL
    have hzUZ : z < k+1 := by exact_mod_cast hzU
    omega
  have hqcases : q = 0 ∨ q = 1 := by
    have hqL : 0 ≤ q := by
      by_contra h
      nlinarith
    have hqU : q ≤ 1 := by
      by_contra h
      nlinarith
    omega
  grind

def highPatchWrapLift {d k : ℕ} (j : HighWindowLabels d k) (b : Fin d → Bool) : Fin d → ℤ :=
  fun r => if b r then (j r).val+k else (j r).val

variable {d k : ℕ} [NeZero k] (hk : 4 ≤ k) {j : HighWindowLabels d k}
include hk

theorem highLocalCoordinates_eq_affine_on_patch {x : Covariate d} (hx : x ∈ highTorusPatch j)
    {z : Fin d → ℤ} (hz : ∀ r, (z r)=j r)
    (hc : ∀ r, |k*x r-z r| < 1) :
    highLocalCoordinates j x = highAffineChart k z x := by
  funext r
  simp only [highLocalCoordinates, highLocalCoordinate, highRawChartCoordinate, (highChartLift_eq_of_close hk (hz r) (hc r)),
    if_pos (hc r).le, highAffineChart]

theorem highLocalCoordinates_patch_mem_box {x : Covariate d} (hx : x ∈ highTorusPatch j) :
    highLocalCoordinates j x ∈ spatialPatchBox d := by
  obtain ⟨z, hz, hc⟩ := hx
  rw [highLocalCoordinates_eq_affine_on_patch hk ⟨z,hz,hc⟩ hz hc]
  constructor <;> intro r
  · exact LT.lt.le (abs_lt.mp (hc r)).left
  · exact LT.lt.le (abs_lt.mp (hc r)).right

/-- The genuine local-coordinate pushforward on a torus patch is dominated
by the scaled Lebesgue measure on [-1,1]^d.  The factor 2^d counts wrapping
chart lifts and is independent of the polynomial and all sample sizes. -/
theorem highLocalCoordinates_patch_map_le
    (j : HighWindowLabels d k) :
    Measure.map (highLocalCoordinates j)
      ((cubeVolume d).restrict (highTorusPatch j)) ≤
      ENNReal.ofReal ((2 / k)^d) • volume.restrict (spatialPatchBox d) := by
  have hbox : MeasurableSet (spatialPatchBox d) := measurableSet_Icc
  apply Measure.le_iff.mpr
  intro S hS
  have hcover : (highLocalCoordinates j ⁻¹' S ∩ highTorusPatch j) ∩ unitCube d ⊆
      ⋃ b, highAffineChart k (highPatchWrapLift j b) ⁻¹' (S ∩ spatialPatchBox d) := by
    intro x hx
    obtain ⟨z, hz, hc⟩ := hx.1.2
    have hzcase r : ∃ b : Bool,
        z r = if b then (j r).val+(k : ℤ) else (j r).val := by
      rcases highPatch_lift_cube_cases hk (hx.2 r) (hz r) (hc r) with h | h
      · tauto
      · aesop
    choose b hb using hzcase
    have hzb : z = highPatchWrapLift j b := by funext r; exact hb r
    have he := highLocalCoordinates_eq_affine_on_patch hk hx.1.2 hz hc
    apply Set.mem_iUnion.mpr
    refine ⟨b, ?_⟩
    grind [highLocalCoordinates_patch_mem_box]
  rw [Measure.map_apply (highLocalCoordinates_measurable j) hS,
    Measure.restrict_apply ((highLocalCoordinates_measurable j) hS),
    cubeVolume, Measure.restrict_apply (((highLocalCoordinates_measurable j) hS).inter
      (highTorusPatch_measurableSet ..)), Measure.smul_apply,
    Measure.restrict_apply hS, smul_eq_mul]
  calc
    _ ≤ _ := measure_mono hcover
    _ ≤ _ :=
      measure_iUnion_le _
    _ = ∑ b,
        ENNReal.ofReal ((k^d)⁻¹) * volume (S ∩ spatialPatchBox d) := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro b _
      rw [← Measure.map_apply (highAffineChart_measurable ..) (hS.inter hbox),
        highAffineChart_map_volume d k (by omega) _, Measure.smul_apply, smul_eq_mul]
    _ = _ := by
      simp
      rw [← mul_assoc]
      congr 1
      have ht : 2^d = ENNReal.ofReal (2^d) := by
        simp
      rw [ht, ← ENNReal.ofReal_mul (by positivity)]
      ring

end NearlyMinimax
