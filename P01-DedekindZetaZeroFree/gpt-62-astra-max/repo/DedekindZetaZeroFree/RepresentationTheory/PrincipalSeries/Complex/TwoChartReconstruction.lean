module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.MatrixSmoothness

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxPrincipalSeriesReconstruction
open KPCplxCharacterHaar KPCplxPrincipalSeriesMatrixSmooth
open scoped Matrix.Norms.Elementwise
local notation "Mat₂ℂ" => Matrix (Fin 2) (Fin 2) ℂ

noncomputable def chartWeight (s : ℝ) (g : ComplexGL2) (j : Fin 2) : ℝ :=
  Real.rpow (‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ / ‖(g : Mat₂ℂ) 1 j‖ ^ 2) (1 + 2*s)
noncomputable def reconstruct (s : ℝ) (F H : ℂ → ℂ) (g : ComplexGL2) : ℂ :=
  if (g : Mat₂ℂ) 1 0 ≠ 0 then
    (chartWeight s g 0 : ℂ) * F ((g : Mat₂ℂ) 1 1 / (g : Mat₂ℂ) 1 0)
  else (chartWeight s g 1 : ℂ) * H ((g : Mat₂ℂ) 1 0 / (g : Mat₂ℂ) 1 1)
lemma row_upper (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) (j : Fin 2) :
    (upperTriangular a d b * g : Mat₂ℂ) 1 j =
      (d : ℂ) * (g : Mat₂ℂ) 1 j := by
  simp [upperTriangular, Matrix.mul_apply, Fin.sum_univ_two]
lemma weight_upper (s : ℝ) (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) (j : Fin 2) :
    chartWeight s (upperTriangular a d b * g) j = inductionWeight s a d * chartWeight s g j := by
  have hdet : ‖(Matrix.GeneralLinearGroup.det (upperTriangular a d b * g) : ℂ)‖ =
      ‖(a : ℂ)‖ * ‖(d : ℂ)‖ * ‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ := by
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_mul, upperTriangular, Matrix.det_fin_two, norm_mul]
  have hw : inductionWeight s a d = (‖(a : ℂ)‖ / ‖(d : ℂ)‖) ^ (1+2*s) := by
    unfold inductionWeight
    rw [norm_div]
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_two, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  unfold chartWeight
  simp only [Matrix.GeneralLinearGroup.coe_mul]
  rw [row_upper, hdet, norm_mul, mul_pow, hw]
  simp only [Real.rpow_eq_pow]
  have he : ‖(a : ℂ)‖ * ‖(d : ℂ)‖ * ‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ /
      (‖(d : ℂ)‖ ^ 2 * ‖g 1 j‖ ^ 2) =
      (‖(a : ℂ)‖ / ‖(d : ℂ)‖) *
      (‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ / ‖g 1 j‖ ^ 2) := by
    field_simp
  rw [he, Real.mul_rpow (by positivity) (by positivity)]
variable (s : ℝ) (F H : ℂ → ℂ)

lemma reconstruct_covariance (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) :
    reconstruct s F H (upperTriangular a d b * g) = (inductionWeight s a d : ℂ) * reconstruct s F H g := by
  unfold reconstruct
  simp only [Matrix.GeneralLinearGroup.coe_mul]
  simp only [row_upper]
  simp only [mul_ne_zero_iff, d.ne_zero, true_and, weight_upper, Complex.ofReal_mul]
  split_ifs <;> simp_all [mul_div_mul_left, d.ne_zero, mul_assoc]

lemma reconstruct_open : openCoordinate (reconstruct s F H) = F := by
  ext <;> simp [openCoordinate, reconstruct, chartWeight, weyl, upperUnipotent, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_mul, Matrix.det_fin_two, Matrix.mul_apply]
lemma reconstruct_infinity
    (htrans : ∀ u : ℂ, u ≠ 0 → H u = (Real.rpow ‖u‖ (-2 * (1 + 2*s)) : ℂ) * F u⁻¹) :
    infinityCoordinate (reconstruct s F H) = H := by
  funext u
  by_cases hu : u = 0
  · simp_all [infinityCoordinate, reconstruct, chartWeight, lowerUnipotent, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  · simp_all [Real.inv_rpow, Real.rpow_neg, Real.rpow_two, Real.rpow_mul, infinityCoordinate, reconstruct, chartWeight, lowerUnipotent, Matrix.GeneralLinearGroup.val_det_apply]
end DedekindZetaZeroFree.KPCplxPrincipalSeriesReconstruction
