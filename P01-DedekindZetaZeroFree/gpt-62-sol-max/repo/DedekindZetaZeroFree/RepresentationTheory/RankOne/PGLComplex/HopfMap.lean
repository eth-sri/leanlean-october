module

public import DedekindZetaZeroFree.Analysis.HarmonicPolynomials.SphereRestriction
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicKTypes

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse
open KPCplxCharacterHaar KPCplxHarmonicIntertwinerSpectrum
open scoped BigOperators Matrix

theorem su2_bottomRow_norm_sq (k : ComplexSU2) :
    ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
    ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 = 1 := by
  have hu := Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup k.property)
  have hr := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 1 1).re) hu
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.star_def,
    Complex.mul_conj', ← Complex.ofReal_pow] using hr

noncomputable def hopfVector (k : ComplexSU2) : Ambient :=
  WithLp.toLp 2 (fun i => (compactSphereCoordinate k i).re)

theorem hopfVector_norm (k : ComplexSU2) : ‖hopfVector k‖ = 1 := by
  let m : Matrix (Fin 2) (Fin 2) ℂ := k
  have hr := su2_bottomRow_norm_sq k
  have hprod : (m 1 0 * star (m 1 1)).re ^ 2 +
      (m 1 0 * star (m 1 1)).im ^ 2 = ‖m 1 0‖ ^ 2 * ‖m 1 1‖ ^ 2 := by
    calc
      _ = Complex.normSq (m 1 0 * star (m 1 1)) := by
        simp only [Complex.normSq_apply, sq]
      _ = _ := by rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, norm_star]
  have hs : ‖hopfVector k‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [hopfVector, compactSphereCoordinate, Fin.sum_univ_three,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Complex.ofReal_re, Real.norm_eq_abs, sq_abs,
      ← Complex.ofReal_pow]
    change (2 * (m 1 0 * star (m 1 1)).re) ^ 2 +
      (2 * (m 1 0 * star (m 1 1)).im) ^ 2 +
      (‖m 1 0‖ ^ 2 - ‖m 1 1‖ ^ 2) ^ 2 = 1
    grind only
  nlinarith [norm_nonneg (hopfVector k)]

noncomputable def hopf (k : ComplexSU2) : Sphere :=
  ⟨hopfVector k, by simpa only [Metric.mem_sphere, dist_zero_right] using hopfVector_norm k⟩

def rowMatrix (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![star b, -star a; a, b]

def rowSU2 (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : ComplexSU2 :=
  ⟨rowMatrix a b, by
    have h' : ‖b‖ ^ 2 + ‖a‖ ^ 2 = 1 := by linarith
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [rowMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
          Complex.mul_conj', ← Complex.ofReal_pow,
          ← Complex.ofReal_add, h, h', mul_comm]
    · simp [rowMatrix, Matrix.det_fin_two, Complex.mul_conj',
        mul_comm, ← Complex.ofReal_pow, ← Complex.ofReal_add, h']⟩

theorem hopf_surjective : Function.Surjective hopf := by
  intro x
  have hs : (x : Ambient) 0 ^ 2 + (x : Ambient) 1 ^ 2 + (x : Ambient) 2 ^ 2 = 1 := by
    have hx : ‖(x : Ambient)‖ = 1 := by
      simp
    have := congrArg (fun r : ℝ => r ^ 2) hx
    simpa only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs,
      sq_abs, one_pow] using this
  have hz : (x : Ambient) 2 ≤ 1 := by
    nlinarith
  by_cases he : (x : Ambient) 2 = 1
  · have h0 : (x : Ambient) 0 = 0 := by nlinarith
    have h1 : (x : Ambient) 1 = 0 := by simp_all
    refine ⟨rowSU2 1 0 (by simp), ?_⟩
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [hopf, hopfVector, compactSphereCoordinate, rowSU2, rowMatrix, h0, h1, he]
  · let r : ℝ := Real.sqrt ((1 - (x : Ambient) 2) / 2)
    have hr : 0 < r := Real.sqrt_pos.2 (by have hz' : (x : Ambient) 2 < 1 := lt_of_le_of_ne hz he; linarith)
    have hr2 : r ^ 2 = (1 - (x : Ambient) 2) / 2 :=
      Real.sq_sqrt (by linarith)
    let a : ℂ := ⟨(x : Ambient) 0 / (2*r), (x : Ambient) 1 / (2*r)⟩
    let b : ℂ := r
    have ha : ‖a‖ ^ 2 = (1 + (x : Ambient) 2) / 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      dsimp [a]
      field_simp
      nlinarith [hr2]
    have hb : ‖b‖ ^ 2 = (1 - (x : Ambient) 2) / 2 := by
      simpa [b, Complex.norm_real, sq_abs] using hr2
    refine ⟨rowSU2 a b (by rw [ha, hb]; ring), ?_⟩
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [hopf, hopfVector, compactSphereCoordinate, rowSU2, rowMatrix,
      ha, a, b, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_div, hr2]
    all_goals field_simp
    all_goals ring

theorem hopf_complex_coordinates (k : ComplexSU2) :
    (fun i => (((hopf k : Ambient) i) : ℂ)) = compactSphereCoordinate k := by
  funext i
  fin_cases i <;> simp [hopf, hopfVector, compactSphereCoordinate, ← Complex.ofReal_pow]

end DedekindZetaZeroFree.ComplexFractionalInverse
