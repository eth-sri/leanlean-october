module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockQuadraticScaling
import Mathlib.Tactic

/-! # Native inverse quadratic bounds used by positivity sets and overlap -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Matrix
open scoped MatrixOrder

variable {d : ℕ} {M : Matrix (Fin 2) (Fin 2) ℝ} {lam h sigma : ℝ} (hM : M.PosDef) (hlam : 0 < lam)
    {c : ℝ} (hh : 0 < h) (hc : 0 < c) (hs : -(h / 128) ≤ sigma) (hs0 : -(h / 128) ≤ sigma)
    (hu : M ≤ c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (hl : c • (1 : Matrix (Fin 2) (Fin 2) ℝ) ≤ M)
    (ht : |sigma / h| ≤ 1) (hs1 : sigma ≤ 0) (y V : PDE.Vec d)

include hM hc hu in
/-- A positive scalar covariance upper bound gives the exact inverse quadratic lower bound. -/
theorem blockQuadratic_inv_lower :
    PDE.vecNormSq y + PDE.vecNormSq V ≤ c * blockQuadratic M⁻¹ y V := by
  have hscalar : (c • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef := Matrix.PosDef.one.smul hc
  have he := blockQuadratic_mono (hscalar.inv.isHermitian.isSymm)
    (hM.inv.isHermitian.isSymm) (covariance_inv_antitone hM hscalar hu) y V
  rw [covariance_scalar_one_inv hc, blockQuadratic_smul, blockQuadratic_one] at he
  have hm := mul_le_mul_of_nonneg_left he hc.le
  simpa [← mul_assoc, mul_inv_cancel₀ hc.ne'] using hm

include hM hc hl in
/-- A positive scalar covariance lower bound gives the exact inverse quadratic upper bound. -/
theorem blockQuadratic_inv_upper :
    blockQuadratic M⁻¹ y V ≤ c⁻¹ * (PDE.vecNormSq y + PDE.vecNormSq V) := by
  have hscalar : (c • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef := Matrix.PosDef.one.smul hc
  have he := blockQuadratic_mono hM.inv.isHermitian.isSymm hscalar.inv.isHermitian.isSymm (covariance_inv_antitone hscalar hM hl) y V
  rw [covariance_scalar_one_inv hc, blockQuadratic_smul, blockQuadratic_one] at he
  exact he

include hlam hh hs ht in
/-- The upper covariance bound controls the native squared size of scaled position and velocity. -/
theorem qform_scaled_normSq_le :
    PDE.vecNormSq ((h ^ (3 / 2 : ℝ))⁻¹ • y) +
      PDE.vecNormSq ((h ^ (1 / 2 : ℝ))⁻¹ • V) ≤ 2 * lam * qform lam h sigma y V := by
  have hstrip : -(1 / 128) ≤ sigma / h := by
    apply (le_div_iff₀ hh).mpr
    linarith only [hs]
  rw [qform_eq_dimensionless lam hh]
  exact blockQuadratic_inv_lower (posDef_ghat hlam hstrip) (mul_pos (by norm_num) hlam)
    (ghat_upper hlam ht) _ _

/-- The endpoint covariance lower bound has the exact source constant sixteen. -/
theorem qform_endpoint_upper {lam h : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (y V : PDE.Vec d) :
    qform lam h h y V ≤ (16 / lam) *
      (PDE.vecNormSq ((h ^ (3 / 2 : ℝ))⁻¹ • y) +
        PDE.vecNormSq ((h ^ (1 / 2 : ℝ))⁻¹ • V)) := by
  rw [qform_eq_dimensionless lam hh, div_self hh.ne']
  have he := blockQuadratic_inv_upper (posDef_ghat hlam (show -(1 / 128) ≤ 1 by norm_num))
    (show 0 < lam / 16 by positivity) (ghat_one_lower hlam)
    ((h ^ (3 / 2 : ℝ))⁻¹ • y) ((h ^ (1 / 2 : ℝ))⁻¹ • V)
  convert he using 1
  field_simp

include hlam hh hs0 hs1 in
/-- The source covariance overlap gives the same quadratic contraction in physical coordinates. -/
theorem qform_overlap :
    qform lam h (sigma + h) y V ≤ (13 / 50 : ℝ) * qform lam h sigma y V := by
  have ht0 : -(1 / 128) ≤ sigma / h := by
    apply (le_div_iff₀ hh).mpr
    linarith only [hs0]
  have ht1 := div_nonpos_of_nonpos_of_nonneg hs1 hh.le
  have hn : -(1 / 128) ≤ sigma / h + 1 := by linarith only [ht0]
  have hM := posDef_ghat hlam ht0
  have hN := posDef_ghat hlam hn
  have hc : (0 : ℝ) < 13 / 50 := by norm_num
  have hscaled := hN.smul hc
  have he := blockQuadratic_mono hscaled.inv.isHermitian.isSymm hM.inv.isHermitian.isSymm (covariance_inv_antitone hM hscaled (ghat_overlap hlam ht0 ht1))
    ((h ^ (3 / 2 : ℝ))⁻¹ • y) ((h ^ (1 / 2 : ℝ))⁻¹ • V)
  rw [covariance_inv_smul hN hc, blockQuadratic_smul] at he
  have hm := mul_le_mul_of_nonneg_left he hc.le
  simp only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at hm
  rw [qform_eq_dimensionless lam hh, qform_eq_dimensionless lam hh]
  have ht : (sigma + h) / h = sigma / h + 1 := by field_simp
  rw [ht]
  exact hm

end HypoellipticAleksandrov.KineticAleksandrov.Holder
