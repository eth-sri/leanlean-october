module

public import RadianRamsey.AlgebraicRamsey
public import OAI.Combinatorics.EuclideanRamsey.TensorNecessity

@[expose] public section

namespace OAI.EuclideanRamsey.Radian

open Real Algebra.TensorProduct
open scoped TensorProduct nonZeroDivisors Polynomial

noncomputable section

def radianConfig (θ : ℝ) (k : Fin 9) : Space 2 :=
  WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]
lemma radianConfig_on_circle (θ : ℝ) (k : Fin 9) : dist (radianConfig θ k) 0 = 1 := by
  rw [EuclideanSpace.dist_eq]
  simp [radianConfig,Fin.sum_univ_two]

private lemma algebraic_sin {θ : ℝ} (h : IsAlgebraic ℚ (cos θ)) : IsAlgebraic ℚ (sin θ) := by
  apply IsAlgebraic.of_pow (n := 2) (by decide)
  simpa [Real.sin_sq] using isAlgebraic_one.sub (h.pow 2)

private lemma algebraic_tan_iff_cos (θ : ℝ) :
    IsAlgebraic ℚ (tan (θ / 2)) ↔ IsAlgebraic ℚ (cos θ) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases hc : cos θ = -1
    · rw [hc]; exact isAlgebraic_one.neg
    rw [cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq θ hc,div_eq_mul_inv]
    exact (isAlgebraic_one.sub (h.pow 2)).mul ((isAlgebraic_one.add (h.pow 2)).inv)
  · have ch : IsAlgebraic ℚ (cos (θ/2)) := by
      apply IsAlgebraic.of_pow (n := 2) (by decide)
      rw [Real.cos_sq,mul_div_cancel₀ _ two_ne_zero,← add_div,div_eq_mul_inv]
      exact (isAlgebraic_one.add h).mul ((isAlgebraic_natCast 2).inv)
    rw [tan_eq_sin_div_cos, div_eq_mul_inv]
    exact (algebraic_sin ch).mul ch.inv

open Matrix

private lemma powers_injective {z : ℂ} (hz : Transcendental ℚ z) :
    Function.Injective (fun n : ℕ => z^n) := by
  intro a b h
  have h' : (Polynomial.X:ℚ[X])^a = Polynomial.X^b :=
    (transcendental_iff_injective.mp hz) (by simpa using h)
  simpa using congrArg Polynomial.natDegree h'

private def powLabel : Fin 9 ≃ Fin 3 × Fin 3 := (finProdFinEquiv (m:=3) (n:=3)).symm
private abbrev expRow (z : ℂ) (i : Fin 9) (j : Fin 3) := (z^(j:ℕ))^(i:ℕ)
private lemma exp_det_regular {z : ℂ} (hz : Transcendental ℚ z) :
    (Matrix.of (fun i => complexSqRow powLabel (expRow z i))).det ∈ ComplexTensor⁰ := by
  let g : ℚ[X] →ₐ[ℚ] ℂ := Polynomial.aeval z
  have hg : g.Flat := by
    let : Algebra ℚ[X] ℂ := g.toRingHom.toAlgebra
    let : Module.IsTorsionFree ℚ[X] ℂ := Module.isTorsionFree_iff_algebraMap_injective.mpr
      (transcendental_iff_injective.mp hz)
    exact (inferInstance : Module.Flat ℚ[X] ℂ)
  let e := polyEquivTensor ℚ ℂ
  let f := (lTensor ℂ g).comp e.toAlgHom
  let x (j : Fin 9) := Polynomial.monomial (powLabel j).2.val (z^(powLabel j).1.val)
  have hz₀ : z ≠ 0 := fun h => hz (h.symm ▸ isAlgebraic_zero)
  have hx : Function.Injective x := by
    intro i j h
    have H := (Polynomial.monomial_eq_monomial_iff.mp h).resolve_right (by simp [hz₀])
    exact powLabel.injective (Prod.ext (Fin.ext (powers_injective hz H.2)) (Fin.ext H.1))
  have hr : f ((vandermonde x).transpose.det) ∈ ComplexTensor⁰ := by
    let : Algebra ℂ[X] ComplexTensor := f.toRingHom.toAlgebra
    let : Module.Flat ℂ[X] ComplexTensor := (RingHom.Flat.of_bijective (f:=e.toRingHom) e.bijective).comp (hg.lTensor ℂ)
    apply isRegular_iff_mem_nonZeroDivisors.mp (isLeftRegular_iff_isRegular.mp (Module.Flat.isSMulRegular_of_nonZeroDivisors (R:=ℂ[X]) (M:=ComplexTensor) (r:=((vandermonde x).transpose.det)) ?_))
    rwa [mem_nonZeroDivisors_iff_ne_zero,det_transpose,det_vandermonde_ne_zero_iff]
  rw [f.map_det] at hr
  convert hr using 2
  ext i j
  simp [f,e,g,x,Matrix.vandermonde,tmul_pow,complexSqRow,← pow_mul]

private def turn (θ : ℝ) := Complex.exp ((θ:ℂ)*Complex.I)
private lemma turn_pow (θ : ℝ) (n : ℕ) : turn θ ^ n = turn (n*θ) := by
  simp [turn,Complex.exp_nat_mul,mul_assoc]
private lemma turn_transcendental (θ : ℝ) (h : Transcendental ℚ (cos θ)) : Transcendental ℚ (turn θ) := by
  intro hc
  apply h
  apply (isAlgebraic_algebraMap_iff (A := ℂ) Complex.ofReal_injective).mp
  change IsAlgebraic ℚ ((cos θ:ℝ):ℂ)
  rw [Complex.ofReal_cos,Complex.cos,neg_mul,Complex.exp_neg,div_eq_mul_inv]
  exact (hc.add (hc.inv)).mul ((isAlgebraic_natCast 2).inv)

private lemma span_expRow (θ : ℝ) (w : AffineRow 2) :
    ∃ v, ∀ i, expRow (turn θ) i ⬝ᵥ v = turn θ^(i:ℕ) * (evalRow (radianConfig θ) i w : ℝ) := by
  refine ⟨![(w (some 0):ℂ)/2+(w (some 1):ℂ)*Complex.I/2,
    (w none:ℂ),(w (some 0):ℂ)/2-(w (some 1):ℂ)*Complex.I/2],fun i => ?_⟩
  simp only [dotProduct,Fin.sum_univ_three,expRow]
  simp only [pow_right_comm (turn θ) _ (i:ℕ),turn_pow θ (i:ℕ)]
  simp [evalRow,Fin.sum_univ_two,radianConfig,
    turn,Complex.cos,Complex.sin,Complex.exp_neg]
  field_simp
  ring

/-- Transcendence of the half-angle tangent implies distinctness and obstructs Ramsey. -/
theorem radian_configuration (θ : ℝ) (ht : Transcendental ℚ (tan (θ / 2))) :
    Function.Injective (radianConfig θ) ∧ (∀ k, dist (radianConfig θ k) 0 = 1) ∧
      ¬ Ramsey (radianConfig θ) := by
  have hz := turn_transcendental θ ((algebraic_tan_iff_cos θ).not.mp ht)
  have hi : Function.Injective (radianConfig θ) := by
    intro i j hij
    refine Fin.ext (powers_injective hz (show turn θ ^ i.val = turn θ ^ j.val from ?_))
    rw [turn_pow,turn_pow]
    simp only [turn,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]
    simp_all [radianConfig]
  exact ⟨hi,radianConfig_on_circle θ,nonramsey_of_complex_matrix _ powLabel (expRow (turn θ)) _ (fun _ => pow_ne_zero _ (Complex.exp_ne_zero _))
    (hi.ne (by decide : (0 : Fin 9) ≠ 1)) (exp_det_regular hz) (span_expRow θ)⟩

theorem radian_not_ramsey (θ : ℝ) (ht : Transcendental ℚ (tan (θ / 2))) :
    ¬ Ramsey (radianConfig θ) := (radian_configuration θ ht).2.2

theorem radian_ramsey_iff_tan (θ : ℝ) (hinj : Function.Injective (radianConfig θ)) :
    Ramsey (radianConfig θ) ↔ IsAlgebraic ℚ (tan (θ / 2)) := by
  refine ⟨fun h => by_contradiction fun hn => radian_not_ramsey θ hn h, fun h => ?_⟩
  have hc := (algebraic_tan_iff_cos θ).mp h
  refine ramsey_of_algebraic _ (by decide) hinj ?_ (fun k => by simp [radianConfig,Fin.sum_univ_two])
  intro k j
  have h : IsAlgebraic ℚ (cos ((k:ℕ)*θ)) := by
    simpa [Polynomial.Chebyshev.T_real_cos] using
      (by_contradiction fun ht => (transcendental_aeval_iff.mp ht).1 hc : IsAlgebraic ℚ (Polynomial.aeval (cos θ) (Polynomial.Chebyshev.T ℚ k.val)))
  fin_cases j <;> first | exact h | exact algebraic_sin h

theorem radian_ramsey_iff (θ : ℝ) (hinj : Function.Injective (radianConfig θ)) :
    Ramsey (radianConfig θ) ↔ IsAlgebraic ℚ (cos θ) ∧ IsAlgebraic ℚ (sin θ) :=
  (radian_ramsey_iff_tan θ hinj).trans ((algebraic_tan_iff_cos θ).trans
    ⟨fun h => ⟨h, algebraic_sin h⟩, And.left⟩)

end
end OAI.EuclideanRamsey.Radian
