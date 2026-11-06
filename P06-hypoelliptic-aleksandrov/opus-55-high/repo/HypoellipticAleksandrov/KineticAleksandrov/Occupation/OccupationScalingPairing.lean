module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationScalingNorm
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Lebesgue pairing under occupation density scaling -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov.Parabolic MeasureTheory Set

variable {d : ℕ} {T : ℝ}

/-- Pairing after inverse dilation picks up exactly the time length. -/
theorem occupation_integral_scaled_pullback  (hT : 0 < T)
    (f : TimeVelocity d → ℝ) :
    ∫ q in Ioo (0 : ℝ) T ×ˢ univ,
      T ^ (-(d : ℝ) / 2) * f (parabolicAffine 0 0 (Real.sqrt T)⁻¹ q) =
      T * ∫ q in Ioo (0 : ℝ) 1 ×ˢ univ, f q := by
  have hs  := Real.sqrt_pos.mpr hT
  have he := parabolicAffine_measurableEmbedding (d := d) (t₀ := 0) (v₀ := 0)
    (inv_pos.mpr hs)
  rw [integral_const_mul, ← he.integral_map,
    occupation_map_restrict_parabolicAffine 0 0 (inv_pos.mpr hs),
    occupation_inverseScaling_image_slab hT, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg (inv_nonneg.mpr hs.le) _)),
    smul_eq_mul, ← mul_assoc, occupation_density_jacobian hT]

/-- Forward and inverse parabolic dilations cancel with radius sqrt(T). -/
theorem occupation_forward_inverse  (hT : 0 < T)
    (q : TimeVelocity d) :
    parabolicAffine 0 0 (Real.sqrt T)
      (parabolicAffine 0 0 (Real.sqrt T)⁻¹ q) = q := by
  apply Prod.ext
  · change 0 + (Real.sqrt T) ^ 2 * (0 + (Real.sqrt T)⁻¹ ^ 2 * q.1) = q.1
    grind
  · ext j
    change 0 + Real.sqrt T * (0 + (Real.sqrt T)⁻¹ * q.2 j) = q.2 j
    grind

/-- The density pairing transforms with exactly one factor of T. -/
theorem occupation_scaledDensity_pairing  (hT : 0 < T)
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
