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

def highAffineChart (d k : ℕ) (z : Fin d → ℤ) (x : Covariate d) : Covariate d :=
  fun r => (k : ℝ) * x r - z r

section
variable (d k : ℕ)

theorem highAffineChart_measurable (z : Fin d → ℤ) :
    Measurable (highAffineChart d k z) := by unfold highAffineChart; fun_prop

theorem highAffineChart_map_volume (hk : 0 < k) (z : Fin d → ℤ) :
    Measure.map (highAffineChart d k z) volume =
      ENNReal.ofReal ((k : ℝ)^d)⁻¹ • (volume : Measure (Covariate d)) := by
  let f : Covariate d →ₗ[ℝ] Covariate d := (k : ℝ) • LinearMap.id
  have hdet : LinearMap.det f = (k : ℝ)^d := by
    simp [f, LinearMap.det_smul, LinearMap.det_id]
  have hf := Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := f)
    (by rw [hdet]; positivity)
  have heq : highAffineChart d k z = (fun x : Covariate d => (fun r => -(z r : ℝ)) + x) ∘ f := by
    funext x r
    simp [highAffineChart, f]
    ring
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop), hf, hdet,
    Measure.map_smul _ (by fun_prop), map_add_left_eq_self]
  rw [abs_of_nonneg (by positivity)]

end

def highPatchWrapLift {d k : ℕ} (j : HighWindowLabels d k) (b : Fin d → Bool) : Fin d → ℤ :=
  fun r => if b r then (j r).val+(k : ℤ) else (j r).val

section
variable {d k : ℕ} [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k)
include hk

section
variable {x : Covariate d} (hx : x ∈ highTorusPatch d k j)
include hx

omit hx in
theorem highLocalCoordinates_eq_affine_on_patch
    (z : Fin d → ℤ) (hz : ∀ r, (z r : ZMod k)=j r)
    (hc : ∀ r, |(k : ℝ)*x r-z r| < 1) :
    highLocalCoordinates d k j x = highAffineChart d k z x := by
  funext r
  have he := highChartLift_eq_of_close k hk (j r) (x r) (z r) (hz r) (hc r)
  simp only [highLocalCoordinates, highLocalCoordinate, highRawChartCoordinate, he,
    if_pos (hc r).le, highAffineChart]

theorem highLocalCoordinates_patch_mem_box :
    highLocalCoordinates d k j x ∈ spatialPatchBox d := by
  obtain ⟨z, hz, hc⟩ := hx
  rw [highLocalCoordinates_eq_affine_on_patch hk j z hz hc]
  change (∀ r, -1 ≤ highAffineChart d k z x r) ∧ (∀ r, highAffineChart d k z x r ≤ 1)
  grind [highAffineChart]

end

/-- The genuine local-coordinate pushforward on a torus patch is dominated
by the scaled Lebesgue measure on [-1,1]^d.  The factor 2^d counts wrapping
chart lifts and is independent of the polynomial and all sample sizes. -/
theorem highLocalCoordinates_patch_map_le :
    Measure.map (highLocalCoordinates d k j)
      ((cubeVolume d).restrict (highTorusPatch d k j)) ≤
      ENNReal.ofReal ((2 / (k : ℝ))^d) • volume.restrict (spatialPatchBox d) := by
  have hbox : MeasurableSet (spatialPatchBox d) := measurableSet_Icc
  apply Measure.le_iff.mpr
  intro S hS
  have hcover : (highLocalCoordinates d k j ⁻¹' S ∩ highTorusPatch d k j) ∩ unitCube d ⊆
      ⋃ b : Fin d → Bool, highAffineChart d k (highPatchWrapLift j b) ⁻¹' (S ∩ spatialPatchBox d) := by
    intro x hx
    obtain ⟨z, hz, hc⟩ := hx.1.2
    have hzcase (r : Fin d) : ∃ b : Bool,
        z r = if b then ((j r).val : ℤ)+(k : ℤ) else ((j r).val : ℤ) := by
      rcases highPatch_lift_cube_cases k (j r) (x r) (hx.2 r) (z r) (hz r) (hc r) with h | ⟨hj, h⟩
      · exact ⟨false, h⟩
      · exact ⟨true, by simpa [hj] using h⟩
    choose b hb using hzcase
    have hzb : z = highPatchWrapLift j b := by funext r; exact hb r
    have he := highLocalCoordinates_eq_affine_on_patch hk j z hz hc
    apply Set.mem_iUnion.mpr
    refine ⟨b, ?_⟩
    simpa [← hzb, ← he] using ⟨hx.1.1, highLocalCoordinates_patch_mem_box hk j hx.1.2⟩
  rw [Measure.map_apply (highLocalCoordinates_measurable d k j) hS,
    Measure.restrict_apply ((highLocalCoordinates_measurable d k j) hS),
    cubeVolume, Measure.restrict_apply (((highLocalCoordinates_measurable d k j) hS).inter
      (highTorusPatch_measurableSet d k j)), Measure.smul_apply,
    Measure.restrict_apply hS, smul_eq_mul]
  calc
    _ ≤ volume (⋃ b : Fin d → Bool,
        highAffineChart d k (highPatchWrapLift j b) ⁻¹' (S ∩ spatialPatchBox d)) := measure_mono hcover
    _ ≤ ∑' b : Fin d → Bool,
        volume (highAffineChart d k (highPatchWrapLift j b) ⁻¹' (S ∩ spatialPatchBox d)) :=
      measure_iUnion_le _
    _ = ∑ b : Fin d → Bool,
        ENNReal.ofReal (((k : ℝ)^d)⁻¹) * volume (S ∩ spatialPatchBox d) := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro b _
      rw [← Measure.map_apply (highAffineChart_measurable d k _) (hS.inter hbox),
        highAffineChart_map_volume d k (by omega) _, Measure.smul_apply, smul_eq_mul]
    _ = ENNReal.ofReal ((2 / (k : ℝ))^d) * volume (S ∩ spatialPatchBox d) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [← mul_assoc]
      congr 1
      have ht : (2 : ℝ≥0∞)^d = ENNReal.ofReal ((2 : ℝ)^d) := by
        simp
      rw [ht, ← ENNReal.ofReal_mul (by positivity)] <;> ring

end

end NearlyMinimax
