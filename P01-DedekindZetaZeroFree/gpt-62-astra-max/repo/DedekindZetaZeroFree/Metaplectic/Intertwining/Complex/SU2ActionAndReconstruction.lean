module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.ComplexParameterMajorants

@[expose] public section

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPComplexStandardIntertwinerGermProve
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open DedekindZetaZeroFree.KPComplexIntertwinerParameterMajorant MeasureTheory Set
open scoped ContDiff Matrix.Norms.Elementwise

lemma rowRatio_mul_su2 (g : ComplexGL2) (k : ComplexSU2) :
    rowRatio (g * complexSU2Embedding k) = rowRatio g := by
  have hrow (A : Matrix (Fin 2) (Fin 2) ℂ) :
      ‖(A * k) 1 0‖ ^ 2 +
        ‖(A * k) 1 1‖ ^ 2 =
      ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2 := by
    have h : ((A * k) *
        star (A * k)) 1 1 = (A * star A) 1 1 := by
      rw [star_mul, ← mul_assoc, mul_assoc A, (Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup k.property)), mul_one]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.star_def] at h
    simp_rw [Complex.mul_conj'] at h
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact_mod_cast h
  have hdet : Matrix.GeneralLinearGroup.det (complexSU2Embedding k) = 1 := by
    apply Units.ext
    exact (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
  unfold rowRatio bottomRowNormSq
  simp only [map_mul, hdet, mul_one, Matrix.GeneralLinearGroup.coe_mul]
  exact congrArg (fun r : ℝ => ‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ / r)
    (hrow g)

lemma rowRatio_su2 (k : ComplexSU2) : rowRatio (complexSU2Embedding k) = 1 := by
  simpa [rowRatio, bottomRowNormSq] using rowRatio_mul_su2 1 k

lemma rowRatio_upper_mul (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) :
    rowRatio (upperTriangular a d b * g) = ‖(a : ℂ) / (d : ℂ)‖ * rowRatio g := by
  have hdet : ((Matrix.GeneralLinearGroup.det (upperTriangular a d b) : ℂˣ) : ℂ) =
      (a : ℂ) * (d : ℂ) := by
    change Matrix.det !![(a : ℂ), b; 0, (d : ℂ)] = _
    simp [Matrix.det_fin_two]
  have hrow : bottomRowNormSq (upperTriangular a d b * g) =
      ‖(d : ℂ)‖ ^ 2 * bottomRowNormSq g := by
    unfold bottomRowNormSq
    change ‖(!![(a : ℂ), b; 0, (d : ℂ)] * g) 1 0‖ ^ 2 +
      ‖(!![(a : ℂ), b; 0, (d : ℂ)] * g) 1 1‖ ^ 2 = _
    simp [Matrix.mul_apply, Fin.sum_univ_two, norm_mul, mul_pow, mul_add]
  unfold rowRatio
  rw [hrow]
  simp only [map_mul, Units.val_mul, hdet, norm_mul, norm_div]
  field_simp
  <;> ring

alias rowRatio_positive := DedekindZetaZeroFree.KPComplexIntertwinerParameterMajorant.ComplexParameterMajorants.rowRatio_pos

lemma bottomRow_nonzero (g : ComplexGL2) :
    (fun j : Fin 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) 1 j) ≠ 0 := by
  intro he
  have hd := (Matrix.GeneralLinearGroup.det g).ne_zero
  change Matrix.det (g : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 at hd
  apply hd
  simp [Matrix.det_fin_two, (congrFun he 0), (congrFun he 1)]

lemma bottomRowLine_eq_mk (g : ComplexGL2) :
    bottomRowLine g = Projectivization.mk ℂ
      (fun j : Fin 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) 1 j) (bottomRow_nonzero g) := by
  unfold bottomRowLine
  split_ifs with h0
  · unfold projectiveInfinity
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨(g 1 1)⁻¹, ?_⟩
    have h1 : g 1 1 ≠ 0 := by
      intro he
      apply bottomRow_nonzero g
      funext j
      fin_cases j <;> simp [h0, he]
    funext j
    fin_cases j <;> simp [h0, h1]
  · unfold projectiveOpen
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨(g 1 0)⁻¹, ?_⟩
    funext j
    fin_cases j <;> simp [h0, div_eq_mul_inv, mul_comm]

lemma same_line_upper (g h : ComplexGL2) (he : bottomRowLine g = bottomRowLine h) :
    ∃ (a d : ℂˣ) (b : ℂ), g = upperTriangular a d b * h := by
  rw [bottomRowLine_eq_mk, bottomRowLine_eq_mk] at he
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp he
  let m := g * h⁻¹
  let Matrix₀ := Matrix (Fin 2) (Fin 2) ℂ
  have hm10 : m 1 0 = 0 := by
    have hr := congrArg (fun k : ComplexGL2 => k 1 0) (mul_inv_cancel h)
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at hr
    have hc0 := congrFun hc 0
    have hc1 := congrFun hc 1
    change c * h 1 0 = _ at hc0
    change c * h 1 1 = _ at hc1
    change ((g * h⁻¹ : ComplexGL2) : Matrix₀) 1 0 = 0
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rw [← hc0, ← hc1, mul_assoc, mul_assoc, ← mul_add, hr]
    simp
  have hdet : (m : Matrix₀) 0 0 *
      (m : Matrix₀) 1 1 ≠ 0 := by
    have hd := (Matrix.GeneralLinearGroup.det m).ne_zero
    change Matrix.det (m : Matrix₀) ≠ 0 at hd
    simpa [Matrix.det_fin_two, hm10] using hd
  let a := Units.mk0 (m 0 0) (left_ne_zero_of_mul hdet)
  let d := Units.mk0 (m 1 1) (right_ne_zero_of_mul hdet)
  refine ⟨a, d, m 0 1, ?_⟩
  have hm : m = upperTriangular a d (m 0 1) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [upperTriangular, a, d, hm10]
  rw [← hm]
  simp [m, mul_assoc]

end DedekindZetaZeroFree.RepresentationTheory.KPComplexStandardIntertwinerGermProve

end
