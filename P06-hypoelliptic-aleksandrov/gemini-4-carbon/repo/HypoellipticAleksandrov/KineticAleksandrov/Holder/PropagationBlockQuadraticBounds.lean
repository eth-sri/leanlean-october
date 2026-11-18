module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.CovarianceBoundsFinal
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.CovariancePhysical
import HypoellipticAleksandrov.KineticAleksandrov.Holder.QuadraticCalculus

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder
open Matrix
open scoped BigOperators MatrixOrder


/-- Evaluation of a symmetric scalar block matrix on native Euclidean position and velocity. -/
def blockQuadratic {d : ℕ} (M : Matrix (Fin 2) (Fin 2) ℝ) (y V : PDE.Vec d) : ℝ :=
  M 0 0 * PDE.vecDot y y + 2 * M 0 1 * PDE.vecDot y V + M 1 1 * PDE.vecDot V V

/-- Block evaluation is the sum of its literal two-dimensional coordinate evaluations. -/
theorem blockQuadratic_eq_sum {d : ℕ} (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : M.IsSymm) (y V : PDE.Vec d) :
    blockQuadratic M y V = ∑ i, dotProduct ![y i, V i] (M.mulVec ![y i, V i]) := by
  have h10 : M 1 0 = M 0 1 := hM.apply 0 1
  unfold blockQuadratic PDE.vecDot
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, h10]
  ring

/-- Scalar block Loewner order gives the actual native Euclidean quadratic order. -/
theorem blockQuadratic_mono {d : ℕ} {A B : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm) (h : A ≤ B) (y V : PDE.Vec d) :
    blockQuadratic A y V ≤ blockQuadratic B y V := by
  rw [blockQuadratic_eq_sum A hA, blockQuadratic_eq_sum B hB]
  apply Finset.sum_le_sum
  intro i _
  have hp := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg ![y i, V i]
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at hp
  exact sub_nonneg.mp hp

/-- Positive definite block matrices have nonnegative native quadratic evaluations. -/
theorem blockQuadratic_nonneg {d : ℕ} {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : M.PosSemidef) (y V : PDE.Vec d) : 0 ≤ blockQuadratic M y V := by
  rw [blockQuadratic_eq_sum M hM.isHermitian.isSymm]
  exact Finset.sum_nonneg fun i _ => by
    simpa only [star_trivial] using hM.dotProduct_mulVec_nonneg ![y i, V i]

/-- Inversion reverses the exact scalar block Loewner order on the definite cone. -/
theorem covariance_inv_antitone {A B : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hAB : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  let X := B⁻¹ - A⁻¹
  have hX : Xᴴ = X := by
    dsimp only [X]
    rw [Matrix.conjTranspose_sub, hB.inv.isHermitian, hA.inv.isHermitian]
  have hBinv : (B⁻¹)ᴴ = B⁻¹ := hB.inv.isHermitian
  have hp := (hA.posSemidef.conjTranspose_mul_mul_same X).add
    ((Matrix.le_iff.mp hAB).conjTranspose_mul_mul_same B⁻¹)
  rw [hX, hBinv] at hp
  have ha : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hb : IsUnit B.det := isUnit_iff_ne_zero.mpr hB.det_pos.ne'
  have he : X * A * X + B⁻¹ * (B - A) * B⁻¹ = A⁻¹ - B⁻¹ := by
    simp only [X, sub_mul, mul_sub, Matrix.mul_assoc, Matrix.mul_nonsing_inv A ha,
      Matrix.nonsing_inv_mul_cancel_left A _ ha, Matrix.mul_nonsing_inv B hb,
      Matrix.mul_one]
    abel_nf
  exact Matrix.le_iff.mpr (he ▸ hp)

/-- The actual physical covariance quadratic is nonnegative on the source cutoff strip. -/
theorem qform_nonneg {d : ℕ} {lam h sigma : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (hs : -(h / 128) ≤ sigma) (y V : PDE.Vec d) : 0 ≤ qform lam h sigma y V :=
  blockQuadratic_nonneg (posDef_gramian hlam hh hs).inv.posSemidef y V

/-- Native block evaluation commutes with scalar multiplication. -/
theorem blockQuadratic_smul {d : ℕ} (M : Matrix (Fin 2) (Fin 2) ℝ)
    (c : ℝ) (y V : PDE.Vec d) : blockQuadratic (c • M) y V = c * blockQuadratic M y V := by
  unfold blockQuadratic
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

/-- Evaluation of the identity is the sum of the two native squared Euclidean norms. -/
theorem blockQuadratic_one {d : ℕ} (y V : PDE.Vec d) :
    blockQuadratic (1 : Matrix (Fin 2) (Fin 2) ℝ) y V =
      PDE.vecNormSq y + PDE.vecNormSq V := by
  simp [blockQuadratic, PDE.vecNormSq]




/-- The source quadratic is exactly the dimensionless inverse quadratic at scaled coordinates. -/
theorem qform_eq_dimensionless {d : ℕ} (lam : ℝ) {h : ℝ} (hh : 0 < h)
    (sigma : ℝ) (y V : PDE.Vec d) :
    qform lam h sigma y V = blockQuadratic (ghat lam (sigma / h))⁻¹
      ((h ^ (3 / 2 : ℝ))⁻¹ • y) ((h ^ (1 / 2 : ℝ))⁻¹ • V)  := by
  have covarianceDilation_inv :
      (covarianceDilation h)⁻¹ =
      !![(h ^ (3 / 2 : ℝ))⁻¹, 0; 0, (h ^ (1 / 2 : ℝ))⁻¹] := by
    have h3 := (Real.rpow_pos_of_pos hh (3 / 2 : ℝ)).ne'
    have h1 := (Real.rpow_pos_of_pos hh ((2 : ℝ)⁻¹)).ne'
    rw [Matrix.inv_def, Matrix.adjugate_fin_two, Matrix.det_fin_two, Ring.inverse_eq_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [covarianceDilation, Matrix.smul_apply, h3]
    field_simp [h1]
  unfold qform gramian
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, covarianceDilation_inv]
  unfold blockQuadratic
  rw [vecDot_smul_smul, vecDot_smul_smul, vecDot_smul_smul]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, zero_mul, add_zero, zero_add]
  ring

/-- Scalar multiplication of a definite block inverse has the expected reciprocal factor. -/
theorem covariance_inv_smul {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.PosDef)
    {c : ℝ} (hc : 0 < c) : (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  let u : ℝˣ := Units.mk0 c hc.ne'
  have hu : (u : ℝ) = c := rfl
  have h := Matrix.inv_smul' M u (isUnit_iff_ne_zero.mpr hM.det_pos.ne')
  simpa only [Units.smul_def, hu, Units.val_inv_eq_inv_val] using h

/-- Multiplying the inverse of a positive scalar identity cancels that scalar. -/
theorem covariance_scalar_one_inv {c : ℝ} (hc : 0 < c) :
    (c • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ = c⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  simpa only [inv_one] using covariance_inv_smul Matrix.PosDef.one hc



/-- A positive scalar covariance upper bound gives the exact inverse quadratic lower bound. -/
theorem blockQuadratic_inv_lower {d : ℕ} {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : M.PosDef) {c : ℝ} (hc : 0 < c)
    (hu : M ≤ c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (y V : PDE.Vec d) :
    PDE.vecNormSq y + PDE.vecNormSq V ≤ c * blockQuadratic M⁻¹ y V := by
  have hscalar : (c • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef := Matrix.PosDef.one.smul hc
  have hi := covariance_inv_antitone hM hscalar hu
  have he := blockQuadratic_mono (hscalar.inv.isHermitian.isSymm)
    (hM.inv.isHermitian.isSymm) hi y V
  rw [covariance_scalar_one_inv hc, blockQuadratic_smul, blockQuadratic_one] at he
  simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using (mul_le_mul_of_nonneg_left he hc.le)

/-- A positive scalar covariance lower bound gives the exact inverse quadratic upper bound. -/
theorem blockQuadratic_inv_upper {d : ℕ} {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : M.PosDef) {c : ℝ} (hc : 0 < c)
    (hl : c • (1 : Matrix (Fin 2) (Fin 2) ℝ) ≤ M) (y V : PDE.Vec d) :
    blockQuadratic M⁻¹ y V ≤ c⁻¹ * (PDE.vecNormSq y + PDE.vecNormSq V) := by
  have hscalar : (c • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef := Matrix.PosDef.one.smul hc
  have he := blockQuadratic_mono hM.inv.isHermitian.isSymm hscalar.inv.isHermitian.isSymm (covariance_inv_antitone hscalar hM hl) y V
  rw [covariance_scalar_one_inv hc, blockQuadratic_smul, blockQuadratic_one] at he
  exact he

/-- The upper covariance bound controls the native squared size of scaled position and velocity. -/
theorem qform_scaled_normSq_le {d : ℕ} {lam h sigma : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (hs : -(h / 128) ≤ sigma) (ht : |sigma / h| ≤ 1)
    (y V : PDE.Vec d) :
    PDE.vecNormSq ((h ^ (3 / 2 : ℝ))⁻¹ • y) +
      PDE.vecNormSq ((h ^ (1 / 2 : ℝ))⁻¹ • V) ≤ 2 * lam * qform lam h sigma y V := by
  have hstrip : -(1 / 128 : ℝ) ≤ sigma / h := by
    apply (le_div_iff₀ hh).mpr
    linarith only [hs]
  rw [qform_eq_dimensionless lam hh]
  exact blockQuadratic_inv_lower (posDef_ghat hlam hstrip) (mul_pos (by norm_num) hlam)
    (ghat_upper hlam ht) _ _

/-- The endpoint covariance lower bound has the exact source constant sixteen. -/
theorem qform_endpoint_upper {d : ℕ} {lam h : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (y V : PDE.Vec d) :
    qform lam h h y V ≤ (16 / lam) *
      (PDE.vecNormSq ((h ^ (3 / 2 : ℝ))⁻¹ • y) +
        PDE.vecNormSq ((h ^ (1 / 2 : ℝ))⁻¹ • V))  := by
  have ghat_one_lower :
      (lam / 16 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ≤ ghat lam 1 := by
    have hunit : (1 / 16 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ≤ ghat 1 1 := by
      apply Matrix.le_iff.mpr
      convert (posDef_two_of_det (a := (29 / 96 : ℝ)) (b := (61 / 64 : ℝ)) (c := (33 / 64 : ℝ)) (by norm_num) (by norm_num)).posSemidef using 1
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [ghat, Matrix.sub_apply, Matrix.smul_apply]
    have h := covariance_smul_le hunit hlam.le
    rw [ghat_smul lam 1]
    simpa only [smul_smul, div_eq_mul_inv, one_mul] using h
  rw [qform_eq_dimensionless lam hh, div_self hh.ne']
  convert (blockQuadratic_inv_upper (posDef_ghat hlam (show -(1 / 128 : ℝ) ≤ 1 by norm_num)) (show 0 < lam / 16 by positivity) (ghat_one_lower) ((h ^ (3 / 2 : ℝ))⁻¹ • y) ((h ^ (1 / 2 : ℝ))⁻¹ • V)) using 1
  field_simp

/-- The source covariance overlap gives the same quadratic contraction in physical coordinates. -/
theorem qform_overlap {d : ℕ} {lam h sigma : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (hs0 : -(h / 128) ≤ sigma) (hs1 : sigma ≤ 0) (y V : PDE.Vec d) :
    qform lam h (sigma + h) y V ≤ (13 / 50 : ℝ) * qform lam h sigma y V := by
  have ht0 : -(1 / 128 : ℝ) ≤ sigma / h := by
    apply (le_div_iff₀ hh).mpr
    linarith only [hs0]
  have ht1 : sigma / h ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs1 hh.le
  have hn : -(1 / 128 : ℝ) ≤ sigma / h + 1 := by linarith only [ht0]
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

