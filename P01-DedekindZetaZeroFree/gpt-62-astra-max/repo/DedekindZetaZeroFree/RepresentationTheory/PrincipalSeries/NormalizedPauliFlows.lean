module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RankOne.RightDerivedAction

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.MatrixPaths
open KPCplxCharacterHaar KPCplxIntertwinerEigenvalues
open scoped Matrix Matrix.Norms.Elementwise

def rawRowNormSq (m : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ‖m 1 0‖ ^ 2 + ‖m 1 1‖ ^ 2

 def liftRowSU2 (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : ComplexSU2 :=
  ⟨!![star b, -star a; a, b], by
    have h' : ‖b‖ ^ 2 + ‖a‖ ^ 2 = 1 := by linarith
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
          Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow,
          ← Complex.ofReal_add, h, h', mul_comm]
    · simp [Matrix.det_fin_two, Complex.star_def, Complex.mul_conj',
        mul_comm, ← Complex.ofReal_pow, ← Complex.ofReal_add, h, h']⟩

end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.MatrixPaths

end

end

section

noncomputable section
open scoped BigOperators
namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.PolynomialDerivatives

open KPCplxIntertwinerEigenvalues

open KPCplxCharacterHaar
open scoped Matrix Matrix.Norms.Elementwise
def normalizedNoncompactRowNormSq (m : (Matrix (Fin 2) (Fin 2) ℂ)) : ℝ := ‖m 1 0‖ ^ 2 + ‖m 1 1‖ ^ 2

open KPCplxPrincipalSeriesCharts
theorem normalizedNoncompactRowNormSq_pos (g : ComplexGL2) : 0 < normalizedNoncompactRowNormSq g := by apply @DedekindZetaZeroFree.KPCplxHarmonicPropagation.RaisingCalculation.rowB_pos <;> assumption
 def noncompactRowSU2 (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : ComplexSU2 :=
  ⟨!![star b, -star a; a, b], by
    have h' : ‖b‖ ^ 2 + ‖a‖ ^ 2 = 1 := by linarith
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
          Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow,
          ← Complex.ofReal_add, h, h', mul_comm]
    · simp [Matrix.det_fin_two, Complex.star_def, Complex.mul_conj',
        mul_comm, ← Complex.ofReal_pow, ← Complex.ofReal_add, h, h']⟩
def noncompactNormalizedSU2 (g : ComplexGL2) : ComplexSU2 :=
  noncompactRowSU2 ((g : (Matrix (Fin 2) (Fin 2) ℂ)) 1 0 / Real.sqrt (normalizedNoncompactRowNormSq g))
    ((g : (Matrix (Fin 2) (Fin 2) ℂ)) 1 1 / Real.sqrt (normalizedNoncompactRowNormSq g)) (by
      have hp := normalizedNoncompactRowNormSq_pos g
      simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]
      rw [Real.sq_sqrt hp.le, ← add_div]
      exact div_self hp.ne')

theorem noncompactNormalizedSU2_factor (g : ComplexGL2) :
    ∃ (a d : ℂˣ) (b : ℂ), g = upperTriangular a d b * complexSU2Embedding (noncompactNormalizedSU2 g) := by
  let r : ℝ := Real.sqrt (normalizedNoncompactRowNormSq g)
  have hr : 0 < r := Real.sqrt_pos.mpr (normalizedNoncompactRowNormSq_pos g)
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  let Matrix₀ := Matrix (Fin 2) (Fin 2) ℂ
  have hr2 : (r : ℂ)^2 = (g : (Matrix₀)) 1 0 * star ((g : (Matrix₀)) 1 0) +
      (g : (Matrix₀)) 1 1 * star ((g : (Matrix₀)) 1 1) := by
    simp only [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_add]
    congr 1
    exact Real.sq_sqrt (normalizedNoncompactRowNormSq_pos g).le
  let d : ℂˣ := Units.mk0 (r : ℂ) hrc
  let a : ℂˣ := Matrix.GeneralLinearGroup.det g / d
  let b := ((g : (Matrix₀)) 0 0 * star ((g : (Matrix₀)) 1 0) + (g : (Matrix₀)) 0 1 * star ((g : (Matrix₀)) 1 1)) / r
  refine ⟨a, d, b, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change (g : (Matrix₀)) i j = ((!![(a : ℂ), b; 0, (d : ℂ)] : (Matrix₀)) * (noncompactNormalizedSU2 g : (Matrix₀))) i j
  fin_cases i <;> fin_cases j <;>
    simp [noncompactNormalizedSU2, noncompactRowSU2,
      Matrix.mul_apply, Fin.sum_univ_two, a, d, b,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, map_div₀, r]
  all_goals rw [show Real.sqrt (normalizedNoncompactRowNormSq g) = r from rfl]
  all_goals field_simp [hrc]
  all_goals simp only [Complex.star_def] at hr2
  · linear_combination (g : (Matrix₀)) 0 0 * hr2
  · linear_combination (g : (Matrix₀)) 0 1 * hr2
end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.PolynomialDerivatives

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.MatrixPaths
open KPCplxCharacterHaar KPCplxIntertwinerEigenvalues
open DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction
open scoped Matrix Matrix.Norms.Elementwise

def rawNormalizedSphereCoordinate (m : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 3) : ℂ :=
  (![ (2 * (m 1 0 * star (m 1 1)).re : ℝ),
    (2 * (m 1 0 * star (m 1 1)).im : ℝ),
    (‖m 1 0‖ ^ 2 - ‖m 1 1‖ ^ 2 : ℝ)] i : ℂ) / (rawRowNormSq m : ℂ)

section

variable (j : Fin 3)

def rawNoncompactPath (k : ComplexSU2) (t : ℝ) : ComplexGL2 :=
  complexSU2Embedding k *
    KPSmoothActualFlowData.matrixExponential ((t : ℂ) • cartanMatrix (false, j))

def rawAxis : Fin 3 := ![2, 0, 1] j

def rawCoefficient : ℂ :=
  ![(Real.sqrt 2 : ℂ), (Real.sqrt 2 : ℂ), -(Real.sqrt 2 : ℂ)] j

end

private theorem rawRowNormSq_pos (g : ComplexGL2) : 0 < rawRowNormSq g := by apply @DedekindZetaZeroFree.KPCplxHarmonicPropagation.RaisingCalculation.rowB_pos <;> assumption

private def liftSU2 (g : ComplexGL2) : ComplexSU2 :=
  liftRowSU2 ((g : (Matrix (Fin 2) (Fin 2) ℂ)) 1 0 / Real.sqrt (rawRowNormSq g))
    ((g : (Matrix (Fin 2) (Fin 2) ℂ)) 1 1 / Real.sqrt (rawRowNormSq g)) (by
      have hp := rawRowNormSq_pos g
      simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]
      rw [Real.sq_sqrt hp.le, ← add_div]
      exact div_self hp.ne')
private theorem liftSU2_coordinate (g : ComplexGL2) :
    compactSphereCoordinate (liftSU2 g) = rawNormalizedSphereCoordinate g := by
  have hp := rawRowNormSq_pos g
  have hr : (Real.sqrt (rawRowNormSq g) : ℂ) ^ 2 = (rawRowNormSq g : ℂ) := by
    exact_mod_cast Real.sq_sqrt hp.le
  ext i
  fin_cases i <;>
    simp [compactSphereCoordinate, rawNormalizedSphereCoordinate, liftSU2,
      liftRowSU2, map_div₀, Complex.star_def, Complex.mul_re, Complex.mul_im, norm_div,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hp.le]
  all_goals push_cast
  all_goals field_simp [Complex.ofReal_ne_zero.mpr hp.ne', Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hp).ne']
  all_goals rw [hr]
  all_goals ring

open scoped Matrix.Norms.Operator in
private theorem exp_components (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) (i j : Fin 2) :
    HasDerivAt (fun u : ℝ => (NormedSpace.exp ((u : ℂ) • M)) i j)
      ((NormedSpace.exp ((t : ℂ) • M) * M) i j) t := by
  have hj := (ContinuousLinearMap.proj j : (Fin 2 → ℂ) →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt t ((ContinuousLinearMap.proj i : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Fin 2 → ℂ).hasFDerivAt.comp_hasDerivAt t (((hasDerivAt_exp_smul_const M (t : ℂ)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t Complex.ofRealCLM.hasDerivAt))
  change HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • M) i j)
    (((ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ
      (NormedSpace.exp ((t : ℂ) • M) * M))) 1) i j) t at hj
  simpa using hj
open scoped Matrix.Norms.Operator in
private theorem pauli_exp_det (j : Fin 3) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • noncompactMatrix j)).det = 1 := by
  let m := fun u : ℝ => NormedSpace.exp ((u : ℂ) • noncompactMatrix j)
  have hd : ∀ u, HasDerivAt (fun u => (m u).det) 0 u := by
    intro u
    have h := ((exp_components (noncompactMatrix j) u 0 0).mul
      (exp_components (noncompactMatrix j) u 1 1)).sub
      ((exp_components (noncompactMatrix j) u 0 1).mul
      (exp_components (noncompactMatrix j) u 1 0))
    convert h using 1
    · funext u; simp [m, Matrix.det_fin_two]
    · fin_cases j <;> simp [noncompactMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  simpa [m] using (is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) t 0)

open KPCplxPrincipalSeriesCharts
private theorem lift_section (g : ComplexGL2) (hdet : (g : Matrix (Fin 2) (Fin 2) ℂ).det = 1)
    (s : ℝ) (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    f g = ((rawRowNormSq g).rpow (-(1 + 2 * s)) : ℂ) * f (complexSU2Embedding (liftSU2 g)) := by
  let r : ℝ := Real.sqrt (rawRowNormSq g)
  have hr : 0 < r := Real.sqrt_pos.mpr (rawRowNormSq_pos g)
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  let Matrix₀ := Matrix (Fin 2) (Fin 2) ℂ
  have hr2 : (r : ℂ)^2 = (g : (Matrix₀)) 1 0 * star ((g : (Matrix₀)) 1 0) +
      (g : (Matrix₀)) 1 1 * star ((g : (Matrix₀)) 1 1) := by
    simp only [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_add]
    congr 1
    exact Real.sq_sqrt (rawRowNormSq_pos g).le
  let d : ℂˣ := Units.mk0 (r : ℂ) hrc
  let a : ℂˣ := Matrix.GeneralLinearGroup.det g / d
  let b := ((g : (Matrix₀)) 0 0 * star ((g : (Matrix₀)) 1 0) + (g : (Matrix₀)) 0 1 * star ((g : (Matrix₀)) 1 1)) / r
  have hf : g = upperTriangular a d b * complexSU2Embedding (liftSU2 g) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change (g : (Matrix₀)) i j = ((!![(a : ℂ), b; 0, (d : ℂ)] : (Matrix₀)) * (liftSU2 g : (Matrix₀))) i j
    fin_cases i <;> fin_cases j <;>
      simp [liftSU2, liftRowSU2,
        Matrix.mul_apply, Fin.sum_univ_two, a, d, b,
        Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, map_div₀, r]
    all_goals rw [show Real.sqrt (rawRowNormSq g) = r from rfl]
    all_goals field_simp [hrc]
    all_goals simp only [Complex.star_def] at hr2
    · linear_combination (g : (Matrix₀)) 0 0 * hr2
    · linear_combination (g : (Matrix₀)) 0 1 * hr2
  calc
    f g = (inductionWeight s a d : ℂ) * f (complexSU2Embedding (liftSU2 g)) := by
      conv_lhs => rw [hf, f.property.1]
    _ = _ := ?_
  congr 1
  apply congrArg Complex.ofReal
  unfold inductionWeight complexAbs
  have ha : (a : ℂ) = 1 / (r : ℂ) := by
    simp [a, d, Matrix.GeneralLinearGroup.val_det_apply, hdet]
  rw [ha]
  simp only [d, Units.val_mk0, norm_div, norm_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr]
  have hr2 : r ^ 2 = rawRowNormSq g := Real.sq_sqrt (rawRowNormSq_pos g).le
  rw [div_div, ← pow_two, hr2]
  change ((1 / rawRowNormSq g) ^ 2) ^ (1 / 2 + s) = (rawRowNormSq g) ^ (-(1 + 2 * s))
  rw [← Real.rpow_natCast_mul (one_div_nonneg.mpr (rawRowNormSq_pos g).le) 2]
  simp only [one_div]
  rw [← Real.rpow_neg_eq_inv_rpow]
  congr 1
  ring

theorem actual_noncompact_normalized_compact_lift (j : Fin 3) (k : ComplexSU2) :
    ∃ c : ℝ → ComplexSU2,
      c 0 = k ∧
      (∀ t i, compactSphereCoordinate (c t) i =
        rawNormalizedSphereCoordinate (rawNoncompactPath j k t) i) ∧
      (∀ (s : ℝ) (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) (t : ℝ),
        f (rawNoncompactPath j k t) =
          ((rawRowNormSq (rawNoncompactPath j k t)).rpow (-(1 + 2 * s)) : ℂ) *
            f (complexSU2Embedding (c t))) := by
  have hzero : rawNoncompactPath j k 0 = complexSU2Embedding k := by
    apply Units.ext
    change k *
      NormedSpace.exp (((0 : ℝ) : ℂ) • cartanMatrix (false, j)) = _
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one]
    rfl
  have hnorm : rawRowNormSq (complexSU2Embedding k) = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1
    rw [Matrix.mem_unitaryGroup_iff] at h
    simpa [rawRowNormSq, complexSU2Embedding, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_apply, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow] using (congrArg (fun m : Matrix (Fin 2) (Fin 2) ℂ => (m 1 1).re) h)
  refine ⟨fun t => if t = 0 then k else liftSU2 (rawNoncompactPath j k t), by simp, ?_, ?_⟩
  · intro t i
    dsimp only
    split_ifs with ht
    · subst t
      rw [hzero]
      simp only [rawNormalizedSphereCoordinate, hnorm, Complex.ofReal_one, div_one]
      fin_cases i <;> rfl
    · exact congrFun (liftSU2_coordinate (rawNoncompactPath j k t)) i
  · intro s f t
    dsimp only
    split_ifs with ht
    · subst t
      rw [hzero, hnorm]
      simp
    · apply lift_section
      change (k *
        NormedSpace.exp ((t : ℂ) • cartanMatrix (false, j))).det = 1
      rw [Matrix.det_mul, (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2, one_mul]
      exact pauli_exp_det j t

end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.MatrixPaths

end
end

section

noncomputable section
namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.MatrixPaths
open KPCplxCharacterHaar
open DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction
open scoped Matrix Matrix.Norms.Elementwise

open scoped Matrix.Norms.Operator in

theorem actual_noncompact_matrix_path_tangent (j : Fin 3) (k : ComplexSU2) :
    (rawNoncompactPath j k 0 : Matrix (Fin 2) (Fin 2) ℂ) = k ∧
      ∀ a b, HasDerivAt
        (fun t : ℝ => (rawNoncompactPath j k t : Matrix (Fin 2) (Fin 2) ℂ) a b)
        (((k : Matrix (Fin 2) (Fin 2) ℂ) * noncompactMatrix j) a b) 0 := by
  constructor
  · simp [rawNoncompactPath, KPSmoothActualFlowData.matrixExponential, complexSU2Embedding,
      IsUnit.unit_spec, cartanMatrix]
  · intro a b
    have hpoint : ∀ t : ℝ, (rawNoncompactPath j k t : Matrix (Fin 2) (Fin 2) ℂ) =
        k * NormedSpace.exp ((t : ℂ) • noncompactMatrix j) := by
      intro t
      have h1 : ((KPSmoothActualFlowData.matrixExponential ((t : ℂ) • cartanMatrix (false, j)) :
          Matrix (Fin 2) (Fin 2) ℂ)) = NormedSpace.exp ((t : ℂ) • cartanMatrix (false, j)) :=
        IsUnit.unit_spec _
      have hk : ((complexSU2Embedding k : ComplexGL2) : Matrix (Fin 2) (Fin 2) ℂ) =
          k := by simp [complexSU2Embedding]
      change (((complexSU2Embedding k : ComplexGL2) *
        KPSmoothActualFlowData.matrixExponential ((t : ℂ) • cartanMatrix (false, j))) :
          Matrix (Fin 2) (Fin 2) ℂ) = _
      rw [h1, hk]
      simp [cartanMatrix]
    have hgoal : (fun t : ℝ => (rawNoncompactPath j k t : Matrix (Fin 2) (Fin 2) ℂ) a b)
        = fun t : ℝ => (k *
            NormedSpace.exp ((t : ℂ) • noncompactMatrix j)) a b := by
      funext t
      rw [hpoint t]
    rw [hgoal]
    have h := ((hasDerivAt_exp_smul_const (noncompactMatrix j) ((0 : ℝ) : ℂ)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 Complex.ofRealCLM.hasDerivAt
    have hmat := h.const_mul (k : Matrix (Fin 2) (Fin 2) ℂ)
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, ContinuousLinearMap.coe_restrictScalars,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul, zero_smul, NormedSpace.exp_zero,
      mul_one, one_mul] at hmat
    have hj := (ContinuousLinearMap.proj b : (Fin 2 → ℂ) →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt 0 ((ContinuousLinearMap.proj a : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Fin 2 → ℂ).hasFDerivAt.comp_hasDerivAt 0 hmat)
    change HasDerivAt (fun t : ℝ => (k *
      NormedSpace.exp ((t : ℂ) • noncompactMatrix j)) a b)
      ((k *
        (ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ
          (NormedSpace.exp (((0 : ℝ) : ℂ) • noncompactMatrix j) * noncompactMatrix j))) 1) a b) 0 at hj
    simpa using hj

end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.MatrixPaths

end
end

section

noncomputable section
namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.MatrixPaths
open KPCplxCharacterHaar KPCplxIntertwinerEigenvalues
open DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction
open scoped Matrix Matrix.Norms.Elementwise

theorem normalized_induction_weight_tangent
    (s : ℝ) (j : Fin 3) (k : ComplexSU2)
    (m : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (hm : m 0 = k)
    (hd : ∀ a b, HasDerivAt (fun t => m t a b)
      (((k : Matrix (Fin 2) (Fin 2) ℂ) * noncompactMatrix j) a b) 0) :
    ((rawRowNormSq (m 0)).rpow (-(1 + 2 * s)) : ℂ) = 1 ∧
      HasDerivAt (fun t => ((rawRowNormSq (m t)).rpow (-(1 + 2 * s)) : ℂ))
        (-rawCoefficient j * (1 + 2 * (s : ℂ)) *
          compactSphereCoordinate k (rawAxis j)) 0 := by
  let Matrix₀ := Matrix (Fin 2) (Fin 2) ℂ
  have hrow : rawRowNormSq (k : Matrix₀) = 1 := by
    have hh := congrArg (fun B : Matrix₀ => (B 1 1).re)
      (Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1)
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Matrix.one_apply_eq] at hh
    change (((k : Matrix₀) 1 0 *
      (starRingEnd ℂ) ((k : Matrix₀) 1 0)) +
      ((k : Matrix₀) 1 1 *
      (starRingEnd ℂ) ((k : Matrix₀) 1 1))).re = 1 at hh
    simpa only [rawRowNormSq, Complex.mul_conj', Complex.add_re,
      ← Complex.ofReal_pow, Complex.ofReal_re] using hh
  have hB : rawRowNormSq (m 0) = 1 := by rw [hm, hrow]
  have hnorm : ∀ z : ℂ, ‖z‖ ^ 2 = (z * star z).re := by
    intro z
    simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply, Complex.star_def]
  have ha := hd 1 0
  have hb := hd 1 1
  have hderiv : HasDerivAt (fun t => rawRowNormSq (m t))
      (rawCoefficient j * compactSphereCoordinate k (rawAxis j)).re 0 := by
    convert (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (ha.mul ha.star)).add (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hb.mul hb.star)) using 1
    · simp [rawRowNormSq, hnorm, Function.comp_def]; rfl
    · fin_cases j <;>
        simp [hm, rawCoefficient, rawAxis, noncompactMatrix, Matrix.mul_apply,
          Fin.sum_univ_two, compactSphereCoordinate, hnorm, Complex.star_def,
          Complex.mul_re, Complex.mul_im] <;> ring
  refine ⟨by simp [hB], ?_⟩
  convert ((hderiv.rpow_const
    (Or.inl (by rw [hB]; norm_num))).ofReal_comp) using 1
  simp only [hB, Real.one_rpow, mul_one]
  fin_cases j <;> simp [rawCoefficient, rawAxis, compactSphereCoordinate,
    Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow] <;> ring

end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.MatrixPaths

end
end

section

noncomputable section
open scoped BigOperators
namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.PolynomialDerivatives

open KPCplxIntertwinerEigenvalues
open DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction

theorem polynomial_profile_curve_derivative
    (A : Fin 3 → MvPolynomial (Fin 3) ℂ) (x : Fin 3 → ℂ)
    (c : ℝ → Fin 3 → ℂ) (hc : c 0 = x)
    (hd : ∀ i, HasDerivAt (fun t => c t i) (MvPolynomial.eval x (A i)) 0)
    (p : MvPolynomial (Fin 3) ℂ) :
    HasDerivAt (fun t => MvPolynomial.eval (c t) p)
      (MvPolynomial.eval x (∑ i : Fin 3, A i * MvPolynomial.pderiv i p)) 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (0 : ℝ) a
  | add p q hp hq =>
    convert hp.add hq using 1
    · simp only [map_add]; rfl
    · simp only [map_add, mul_add, Finset.sum_add_distrib]
  | mul_X p i hp =>
    convert hp.mul (hd i) using 1
    · simp only [map_mul, MvPolynomial.eval_X]; rfl
    · simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, map_add,
        map_mul, MvPolynomial.eval_X, Finset.mul_sum, Finset.sum_mul, mul_add,
        Finset.sum_add_distrib, hc]
      simp only [map_sum, map_mul, MvPolynomial.eval_X, Pi.single_apply,
        apply_ite, map_one, map_zero, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Finset.sum_mul]
      simp only [mul_comm, mul_left_comm, mul_assoc, add_comm]

def noncompactAxis (j : Fin 3) : Fin 3 := ![2, 0, 1] j

def noncompactCoefficient (j : Fin 3) : ℂ :=
  ![(Real.sqrt 2 : ℂ), (Real.sqrt 2 : ℂ), -(Real.sqrt 2 : ℂ)] j

def noncompactVectorPolynomial (j i : Fin 3) : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.C (noncompactCoefficient j) *
    (MvPolynomial.C (if i = noncompactAxis j then 1 else 0) -
      MvPolynomial.X (noncompactAxis j) * MvPolynomial.X i)

def noncompactWeightPolynomial (s : ℝ) (j : Fin 3) : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.C (-noncompactCoefficient j * (1 + 2 * (s : ℂ))) *
    MvPolynomial.X (noncompactAxis j)

theorem noncompactVectorPolynomial_degree (j i : Fin 3) :
    (noncompactVectorPolynomial j i).totalDegree ≤ 2 := by
  unfold noncompactVectorPolynomial
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · simp only [MvPolynomial.totalDegree_C]; omega
  · simpa using
      MvPolynomial.totalDegree_mul
        (MvPolynomial.X (noncompactAxis j) : MvPolynomial (Fin 3) ℂ)
        (MvPolynomial.X i)

theorem noncompactWeightPolynomial_degree (s : ℝ) (j : Fin 3) :
    (noncompactWeightPolynomial s j).totalDegree ≤ 1 := by
  unfold noncompactWeightPolynomial
  simpa only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add]
    using MvPolynomial.totalDegree_mul
      (MvPolynomial.C (-noncompactCoefficient j * (1 + 2 * (s : ℂ))))
      (MvPolynomial.X (noncompactAxis j) : MvPolynomial (Fin 3) ℂ)

theorem weighted_polynomial_profile_curve_derivative
    (A : Fin 3 → MvPolynomial (Fin 3) ℂ) (B : MvPolynomial (Fin 3) ℂ)
    (x : Fin 3 → ℂ) (c : ℝ → Fin 3 → ℂ) (hc : c 0 = x)
    (hd : ∀ i, HasDerivAt (fun t => c t i) (MvPolynomial.eval x (A i)) 0)
    (w : ℝ → ℂ) (hw : w 0 = 1)
    (hwd : HasDerivAt w (MvPolynomial.eval x B) 0)
    (p : MvPolynomial (Fin 3) ℂ) :
    HasDerivAt (fun t => w t * MvPolynomial.eval (c t) p)
      (MvPolynomial.eval x (B * p + ∑ i : Fin 3, A i * MvPolynomial.pderiv i p)) 0 := by
  convert hwd.mul (polynomial_profile_curve_derivative A x c hc hd p) using 1
  simp only [hw, hc, one_mul, map_add, map_mul]

section

variable (s : ℝ) (j : Fin 3)

theorem noncompact_polynomial_profile_curve_derivative (x : Fin 3 → ℂ) (c : ℝ → Fin 3 → ℂ)
    (hc : c 0 = x)
    (hd : ∀ i, HasDerivAt (fun t => c t i)
      (MvPolynomial.eval x (noncompactVectorPolynomial j i)) 0)
    (w : ℝ → ℂ) (hw : w 0 = 1)
    (hwd : HasDerivAt w (MvPolynomial.eval x (noncompactWeightPolynomial s j)) 0)
    (p : MvPolynomial (Fin 3) ℂ) :
    deriv (fun t => w t * MvPolynomial.eval (c t) p) 0 =
      MvPolynomial.eval x (noncompactWeightPolynomial s j * p +
        ∑ i : Fin 3, noncompactVectorPolynomial j i * MvPolynomial.pderiv i p) :=
  (weighted_polynomial_profile_curve_derivative
    (noncompactVectorPolynomial j) (noncompactWeightPolynomial s j)
    x c hc hd w hw hwd p).deriv

theorem noncompact_derivative_polynomial_coefficients_of_curves
    (hcurve : ∀ k : KPCplxCharacterHaar.ComplexSU2,
      ∃ (c : ℝ → KPCplxCharacterHaar.ComplexSU2) (w : ℝ → ℂ),
        c 0 = k ∧ w 0 = 1 ∧
        (∀ i, HasDerivAt (fun t => compactSphereCoordinate (c t) i)
          (MvPolynomial.eval (compactSphereCoordinate k)
            (noncompactVectorPolynomial j i)) 0) ∧
        HasDerivAt w (MvPolynomial.eval (compactSphereCoordinate k)
          (noncompactWeightPolynomial s j)) 0 ∧
        (∀ (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) (t : ℝ),
          f (KPCplxCharacterHaar.complexSU2Embedding k *
            KPSmoothActualFlowData.matrixExponential ((t : ℂ) • cartanMatrix (false, j))) =
          w t * f (KPCplxCharacterHaar.complexSU2Embedding (c t)))) :
    ∃ (A : Fin 3 → MvPolynomial (Fin 3) ℂ) (B : MvPolynomial (Fin 3) ℂ),
      (∀ i, (A i).totalDegree ≤ 2) ∧ B.totalDegree ≤ 1 ∧
      ∀ (p : MvPolynomial (Fin 3) ℂ)
        (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s),
        compactRestriction s f = polynomialCompactRestriction p →
        compactRestriction s (localDerivative s (false, j) f) =
          polynomialCompactRestriction
            (B * p + ∑ i : Fin 3, A i * MvPolynomial.pderiv i p) := by
  refine ⟨noncompactVectorPolynomial j, noncompactWeightPolynomial s j,
    noncompactVectorPolynomial_degree j, noncompactWeightPolynomial_degree s j, ?_⟩
  intro p f hpf
  funext k
  obtain ⟨c, w, hc, hw, hd, hwd, hfactor⟩ := hcurve k
  have he : (fun t : ℝ => f (KPCplxCharacterHaar.complexSU2Embedding k *
      KPSmoothActualFlowData.matrixExponential ((t : ℂ) • cartanMatrix (false, j)))) =
      (fun t => w t * MvPolynomial.eval (compactSphereCoordinate (c t)) p) := by
    funext t
    rw [hfactor f t]
    congr 1
    exact congrFun hpf (c t)
  change deriv (fun t : ℝ => f (KPCplxCharacterHaar.complexSU2Embedding k *
      KPSmoothActualFlowData.matrixExponential ((t : ℂ) • cartanMatrix (false, j)))) 0 = _
  rw [he]
  exact noncompact_polynomial_profile_curve_derivative s j (compactSphereCoordinate k)
    (fun t => compactSphereCoordinate (c t)) (congrArg compactSphereCoordinate hc)
    hd w hw hwd p

theorem noncompact_derivative_polynomial_coefficients_of_coordinate_tangents
    (hcurve : ∀ k : KPCplxCharacterHaar.ComplexSU2,
      ∃ (c : ℝ → KPCplxCharacterHaar.ComplexSU2) (w : ℝ → ℂ),
        c 0 = k ∧ w 0 = 1 ∧
        (∀ i, HasDerivAt (fun t => compactSphereCoordinate (c t) i)
          (noncompactCoefficient j * ((if i = noncompactAxis j then 1 else 0) -
            compactSphereCoordinate k (noncompactAxis j) * compactSphereCoordinate k i)) 0) ∧
        HasDerivAt w (-noncompactCoefficient j * (1 + 2 * (s : ℂ)) *
          compactSphereCoordinate k (noncompactAxis j)) 0 ∧
        (∀ (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) (t : ℝ),
          f (KPCplxCharacterHaar.complexSU2Embedding k *
            KPSmoothActualFlowData.matrixExponential ((t : ℂ) • cartanMatrix (false, j))) =
          w t * f (KPCplxCharacterHaar.complexSU2Embedding (c t)))) :
    ∃ (A : Fin 3 → MvPolynomial (Fin 3) ℂ) (B : MvPolynomial (Fin 3) ℂ),
      (∀ i, (A i).totalDegree ≤ 2) ∧ B.totalDegree ≤ 1 ∧
      ∀ (p : MvPolynomial (Fin 3) ℂ)
        (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s),
        compactRestriction s f = polynomialCompactRestriction p →
        compactRestriction s (localDerivative s (false, j) f) =
          polynomialCompactRestriction
            (B * p + ∑ i : Fin 3, A i * MvPolynomial.pderiv i p) := by
  apply noncompact_derivative_polynomial_coefficients_of_curves s j
  intro k
  obtain ⟨c, w, hc, hw, hd, hwd, hf⟩ := hcurve k
  refine ⟨c, w, hc, hw, ?_, ?_, hf⟩
  · simpa [noncompactVectorPolynomial] using hd
  · simpa [noncompactWeightPolynomial] using hwd

end
open KPCplxCharacterHaar
open scoped Matrix Matrix.Norms.Elementwise

local notation "Mat₂ℂ" => Matrix (Fin 2) (Fin 2) ℂ

def normalizedNoncompactSphereCoordinate (m : Mat₂ℂ) (i : Fin 3) : ℂ :=
  (![ (2 * (m 1 0 * star (m 1 1)).re : ℝ),
    (2 * (m 1 0 * star (m 1 1)).im : ℝ),
    (‖m 1 0‖ ^ 2 - ‖m 1 1‖ ^ 2 : ℝ)] i : ℂ) / (normalizedNoncompactRowNormSq m : ℂ)
theorem normalizedNoncompactRowNormSq_compact (k : ComplexSU2) : normalizedNoncompactRowNormSq k = 1 := by apply @DedekindZetaZeroFree.KPCplxHarmonicPropagation.RaisingCalculation.rowB_compact <;> assumption

theorem noncompact_hopf_derivative_of_matrix_tangent (j : Fin 3) (k : ComplexSU2) (c : ℝ → Mat₂ℂ)
    (hc : c 0 = k)
    (hd : ∀ a b, HasDerivAt (fun t => c t a b) (((k : Mat₂ℂ) * noncompactMatrix j) a b) 0) :
    ∀ i, HasDerivAt (fun t => normalizedNoncompactSphereCoordinate (c t) i)
      (MvPolynomial.eval (compactSphereCoordinate k) (noncompactVectorPolynomial j i)) 0 := by
  have ha := hd 1 0
  have hb := hd 1 1
  have hab := ha.mul hb.star
  have haar := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (ha.mul ha.star)
  have hbbr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hb.mul hb.star)
  have hnorm : ∀ z : ℂ, ‖z‖ ^ 2 = (z * star z).re := by
    intro z
    simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply, Complex.star_def]
  let Matrix₀ := Mat₂ℂ
  have hB : HasDerivAt (fun t => normalizedNoncompactRowNormSq (c t))
      (((((k : (Matrix₀)) * noncompactMatrix j) 1 0) * star ((k : (Matrix₀)) 1 0) +
        (k : (Matrix₀)) 1 0 * star (((k : (Matrix₀)) * noncompactMatrix j) 1 0)).re +
       ((((k : (Matrix₀)) * noncompactMatrix j) 1 1) * star ((k : (Matrix₀)) 1 1) +
        (k : (Matrix₀)) 1 1 * star (((k : (Matrix₀)) * noncompactMatrix j) 1 1)).re) 0 := by
    convert haar.add hbbr using 1
    · simp [normalizedNoncompactRowNormSq, hnorm, Function.comp_def]; rfl
    · simp [hc]
  have hne : (normalizedNoncompactRowNormSq (c 0) : ℂ) ≠ 0 := by rw [hc, normalizedNoncompactRowNormSq_compact]; simp
  have hr : ((‖(k : (Matrix₀)) 1 0‖ ^ 2 + ‖(k : (Matrix₀)) 1 1‖ ^ 2 : ℝ) : ℂ) = 1 := by
    exact_mod_cast normalizedNoncompactRowNormSq_compact k
  simp only [hnorm, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im] at hr
  push_cast at hr
  intro i
  fin_cases i
  · convert (((Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hab).const_mul 2).ofReal_comp.div hB.ofReal_comp hne) using 1
    · simp [normalizedNoncompactSphereCoordinate, Function.comp_def, hnorm]; rfl
    · simp only [hc, normalizedNoncompactRowNormSq_compact, Complex.ofReal_one, one_pow, div_one]
      fin_cases j <;>
        simp [hc, noncompactVectorPolynomial, noncompactCoefficient, noncompactAxis,
          noncompactMatrix, Matrix.mul_apply, Fin.sum_univ_two,
          compactSphereCoordinate, hnorm, Complex.star_def, Complex.mul_re, Complex.mul_im]
      all_goals push_cast
      all_goals first | ring1 | linear_combination -(Real.sqrt 2 : ℂ) * hr | linear_combination (Real.sqrt 2 : ℂ) * hr
      all_goals first | ring1 | linear_combination -(Real.sqrt 2 : ℂ) * hr | linear_combination (Real.sqrt 2 : ℂ) * hr
  · convert (((Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hab).const_mul 2).ofReal_comp.div hB.ofReal_comp hne) using 1
    · simp [normalizedNoncompactSphereCoordinate, Function.comp_def, hnorm]; rfl
    · simp only [hc, normalizedNoncompactRowNormSq_compact, Complex.ofReal_one, one_pow, div_one]
      fin_cases j <;>
        simp [hc, noncompactVectorPolynomial, noncompactCoefficient, noncompactAxis,
          noncompactMatrix, Matrix.mul_apply, Fin.sum_univ_two,
          compactSphereCoordinate, hnorm, Complex.star_def, Complex.mul_re, Complex.mul_im]
      all_goals push_cast
      all_goals first | ring1 | linear_combination -(Real.sqrt 2 : ℂ) * hr | linear_combination (Real.sqrt 2 : ℂ) * hr
      all_goals first | ring1 | linear_combination -(Real.sqrt 2 : ℂ) * hr | linear_combination (Real.sqrt 2 : ℂ) * hr
  · convert ((haar.sub hbbr).ofReal_comp.div hB.ofReal_comp hne) using 1
    · simp [normalizedNoncompactSphereCoordinate, Function.comp_def, hnorm]; rfl
    · simp only [hc, normalizedNoncompactRowNormSq_compact, Complex.ofReal_one, one_pow, div_one]
      fin_cases j <;>
        simp [hc, noncompactVectorPolynomial, noncompactCoefficient, noncompactAxis,
          noncompactMatrix, Matrix.mul_apply, Fin.sum_univ_two,
          compactSphereCoordinate, hnorm, Complex.star_def, Complex.mul_re, Complex.mul_im]
      all_goals push_cast
      all_goals first | ring1 | linear_combination -(Real.sqrt 2 : ℂ) * hr | linear_combination (Real.sqrt 2 : ℂ) * hr

theorem noncompact_derivative_polynomial_coefficients (s : ℝ) (j : Fin 3) :
    ∃ (A : Fin 3 → MvPolynomial (Fin 3) ℂ) (B : MvPolynomial (Fin 3) ℂ),
      (∀ i, (A i).totalDegree ≤ 2) ∧ B.totalDegree ≤ 1 ∧
      ∀ (p : MvPolynomial (Fin 3) ℂ)
        (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s),
        compactRestriction s f = polynomialCompactRestriction p →
        compactRestriction s (localDerivative s (false, j) f) =
          polynomialCompactRestriction
            (B * p + ∑ i : Fin 3, A i * MvPolynomial.pderiv i p) := by
  apply noncompact_derivative_polynomial_coefficients_of_coordinate_tangents s j
  intro k
  obtain ⟨c, hc, hcoord, hfactor⟩ :=
    MatrixPaths.actual_noncompact_normalized_compact_lift j k
  obtain ⟨hm, hd⟩ := MatrixPaths.actual_noncompact_matrix_path_tangent j k
  obtain ⟨hw, hwd⟩ := MatrixPaths.normalized_induction_weight_tangent s j k
    (fun t => (MatrixPaths.rawNoncompactPath j k t : Mat₂ℂ)) hm hd
  refine ⟨c, (fun t => ((MatrixPaths.rawRowNormSq
    (MatrixPaths.rawNoncompactPath j k t)).rpow (-(1 + 2 * s)) : ℂ)), hc, hw, ?_, ?_, ?_⟩
  · intro i
    have he : (fun t => compactSphereCoordinate (c t) i) =
        (fun t => normalizedNoncompactSphereCoordinate (MatrixPaths.rawNoncompactPath j k t) i) := by
      funext t
      exact hcoord t i
    rw [he]
    simpa only [noncompactVectorPolynomial, map_mul, map_sub, MvPolynomial.eval_C,
      MvPolynomial.eval_X] using (noncompact_hopf_derivative_of_matrix_tangent j k
        (fun t => (MatrixPaths.rawNoncompactPath j k t : Mat₂ℂ)) hm hd i)
  · simpa only [MatrixPaths.rawCoefficient, MatrixPaths.rawAxis,
      noncompactCoefficient, noncompactAxis] using hwd
  · intro f t
    exact hfactor s f t

open KPCplxPrincipalSeriesCharts

end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.PolynomialDerivatives

end
end
