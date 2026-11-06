module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationScalingNorm
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensity
import HypoellipticAleksandrov.Parabolic.ScalingMeasure

/-! # Lebesgue pairing under occupation density scaling -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped ENNReal

/- Pairing after inverse dilation picks up exactly the time length. -/
theorem occupation_integral_scaled_pullback {d T} (hT : 0 < T)
    (f : TimeVelocity d → ℝ) :
    ∫ q in Ioo (0 : ℝ) T ×ˢ univ,
      T ^ (-(d : ℝ) / 2) * f (parabolicAffine 0 0 (Real.sqrt T)⁻¹ q) =
      T * ∫ q in Ioo (0 : ℝ) 1 ×ˢ univ, f q := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have _h_xinl_0 : T ^ (-(d : ℝ) / 2) * ((Real.sqrt T)⁻¹ ^ (d + 2))⁻¹ = T := by
    have hh := occupation_scaling_factor (d := d) (γ := 1) hT
    have hb : occupationBeta d 1 = 1 := by unfold occupationBeta; ring
    simpa only [div_one, Real.rpow_one, hb] using hh
  rw [integral_const_mul, ← (parabolicAffine_measurableEmbedding (d := d) (t₀ := 0) (v₀ := 0) (inv_pos.mpr hs)).integral_map,
    occupation_map_restrict_parabolicAffine 0 0 (inv_pos.mpr hs),
    occupation_inverseScaling_image_slab hT, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg (inv_nonneg.mpr hs.le) _)),
    smul_eq_mul, ← mul_assoc, _h_xinl_0]

/- Forward and inverse parabolic dilations cancel with radius sqrt(T). -/
theorem occupation_forward_inverse {d T} (hT : 0 < T)
    (q : TimeVelocity d) :
    parabolicAffine 0 0 (Real.sqrt T)
      (parabolicAffine 0 0 (Real.sqrt T)⁻¹ q) = q := by
  have hs : Real.sqrt T ≠ 0 := (Real.sqrt_pos.mpr hT).ne'
  apply Prod.ext
  · change 0 + (Real.sqrt T) ^ 2 * (0 + (Real.sqrt T)⁻¹ ^ 2 * q.1) = q.1
    rw [inv_pow]
    field_simp
    simp only [zero_add, zero_mul]
  · ext j
    change 0 + Real.sqrt T * (0 + (Real.sqrt T)⁻¹ * q.2 j) = q.2 j
    field_simp
    simp only [zero_add, zero_mul]

/- The density pairing transforms with exactly one factor of T. -/
theorem occupation_scaledDensity_pairing {d T} (hT : 0 < T)
    (φ g : TimeVelocity d → ℝ) :
    ∫ q in Ioo (0 : ℝ) T ×ˢ univ,
      φ q * (T ^ (-(d : ℝ) / 2) *
        g (parabolicAffine 0 0 (Real.sqrt T)⁻¹ q)) =
      T * ∫ q in Ioo (0 : ℝ) 1 ×ˢ univ,
        φ (parabolicAffine 0 0 (Real.sqrt T) q) * g q := by
  have hh := occupation_integral_scaled_pullback hT
    (fun q => φ (parabolicAffine 0 0 (Real.sqrt T) q) * g q)
  convert hh using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun q => by
    dsimp only
    rw [occupation_forward_inverse hT]
    ring

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
