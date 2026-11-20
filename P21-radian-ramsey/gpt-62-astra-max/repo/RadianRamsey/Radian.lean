module

public import RadianRamsey.Projection
public import RadianRamsey.AlgebraicRamsey
public import OAI.Combinatorics.EuclideanRamsey.TensorNecessity

@[expose] public noncomputable section

/-!
# Theorem D: the radian 9-gon is non-Ramsey when `tan (θ/2)` is transcendental

Theorem D of the spherical-ramsey note (`note/spherical-ramsey.tex`,
doi:10.5281/zenodo.23396387). The nine points `(cos kθ, sin kθ)`, `k = 0, …, 8`.

In complex coordinates the rows are Fourier modes `-1,0,1`. After shifting
the exponents, their mixed evaluation matrix is a Vandermonde matrix. Its
nonsingularity gives coordinate potentials and a floor coloring obstruction.
The converse uses the algebraic circle trade and word construction.
-/

open scoped ComplexConjugate
open Real
namespace OAI.EuclideanRamsey.Radian

/-- The nine points at angles `0, θ, 2θ, …, 8θ` on the unit circle. -/
def radianConfig (θ : ℝ) (k : Fin 9) : Space 2 :=
  WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]

private abbrev phase (θ : ℝ) : ℂ := Circle.exp θ

private lemma trans_phase {θ : ℝ} (ht : Transcendental ℚ (tan (θ/2))) : Transcendental ℚ (phase θ) := by
  intro h
  let A := algebraicClosure ℚ ℂ
  have hw : phase (θ/2) ∈ A := by
    apply mem_algebraicClosure_iff.mpr ∘ IsAlgebraic.of_pow (n:=2) (by decide)
    rwa [sq,←Circle.coe_mul,←Circle.exp_add,add_halves]
  have hi : Complex.I ∈ A := mem_algebraicClosure_iff.mpr (Complex.isIntegral_I ℚ).isAlgebraic
  apply ht
  apply (isAlgebraic_algebraMap_iff (A:=ℂ) Complex.ofReal_injective).mp
  change IsAlgebraic ℚ ((tan (θ/2) : ℝ) : ℂ)
  rw [Complex.ofReal_tan,Complex.tan,Complex.sin,Complex.cos,neg_mul,Complex.exp_neg]
  apply mem_algebraicClosure_iff.mp
  apply_rules [A.div_mem,A.mul_mem,A.sub_mem,A.inv_mem,A.add_mem,A.natCast_mem 2]

private lemma image_point (θ) (i : Fin 9) : plane (radianConfig θ i) = phase θ^i.val := by
  rw [←Circle.coe_pow,←Circle.exp_natCast_mul]; simp [-Circle.exp_natCast_mul, plane, radianConfig, Complex.exp_mul_I]

theorem radian_configuration (θ : ℝ) (ht : Transcendental ℚ (tan (θ/2))) :
    Function.Injective (radianConfig θ) ∧ (∀ k, dist (radianConfig θ k) 0 = 1) ∧ ¬ Ramsey (radianConfig θ) := by
  have hz := trans_phase ht
  have hi : Function.Injective (radianConfig θ) := fun i j h => Fin.ext (pow_inj hz (by simpa [image_point] using congrArg plane h))
  let z := phase θ
  let w (j : Fin 3) := z^j.val/z-1
  obtain ⟨f,hf⟩ := projection (z:=z) hz w
  refine ⟨hi,fun k => ?_,obstruct (hi.ne (by decide)) (fun i b => f i (z^i.val*b)) ?_⟩
  · simp [← plane.norm_map, image_point]
  rintro b ⟨v,s,hb⟩
  let y := plane s
  let u : Fin 3 → ℂ := ![y/2,v,conj y/2]
  have eval (i : Fin 9) : form z u i = z^i.val*b i := by
    let p := z^i.val
    have hp : p*conj p=1 := by rw [Complex.mul_conj]; simp [p,z,←Complex.sq_norm]
    rw [hb i,inner_map_complex plane,image_point]
    change form z u i = p*((v+(y*conj p).re:ℝ):ℂ)
    rw [Complex.ofReal_add,Complex.re_eq_add_conj]
    simp [form,u,Fin.sum_univ_three,← show p=z^i.val from rfl]
    linear_combination -y*hp/2
  have chord : ∑ j, u j*w j = ((b 1-b 0 : ℝ):ℂ) := by
    have he : ∑ j, u j*w j = form z u 1/z-form z u 0 := by
      simp [w,form,Fin.sum_univ_three]; ring
    rw [he,eval,eval]; simp; field_simp [z,phase]
  simpa only [eval,chord,← Complex.ofReal_pow,Complex.ofReal_re] using hf u

theorem radian_not_ramsey (θ : ℝ) (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    ¬ Ramsey (radianConfig θ) :=
  (radian_configuration θ ht).2.2

/-! ## The converse and the iff -/

theorem algebraic_of_tan {θ : ℝ} (h : IsAlgebraic ℚ (Real.tan (θ / 2))) :
    IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ) := by
  rw [← mem_algebraicClosure_iff] at h
  simp [← mem_algebraicClosure_iff]
  rw [sin_eq_two_mul_tan_half_div_one_add_tan_half_sq θ]
  constructor
  · by_cases hc : cos θ = -1
    · aesop
    rw [cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq _ hc]
    aesop
  aesop

/-- **Theorem D.** For distinct radian points: Ramsey iff `cos θ` and `sin θ` are algebraic
(that is, iff `e^{iθ}` is algebraic). -/
theorem radian_ramsey_iff (θ : ℝ) (hinj : Function.Injective (radianConfig θ)) :
    Ramsey (radianConfig θ) ↔ IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ) := by
  constructor
  · exact algebraic_of_tan ∘ not_imp_not.mp (radian_not_ramsey θ)
  · rintro ⟨hc, hs⟩
    refine ramsey_from_strings
      ⟨plane.injective.comp hinj,?_,?_⟩ <;> intro i <;> simp only [Function.comp_apply,image_point]
    · simp [←Complex.sq_norm]
    · rw [phase,Circle.coe_exp,Complex.exp_ofReal_mul_I]
      exact (hc.algebraMap.isIntegral.add (hs.algebraMap.isIntegral.mul (Complex.isIntegral_I ℚ))).pow _

/-- The same, phrased with the half-angle tangent (Mathlib's junk value `tan (π/2) = 0` is
algebraic, and at `θ ≡ π` the points are `±1` with algebraic coordinates, so no case split
is needed in the statement). -/
theorem radian_ramsey_iff_tan (θ : ℝ) (hinj : Function.Injective (radianConfig θ)) :
    Ramsey (radianConfig θ) ↔ IsAlgebraic ℚ (Real.tan (θ / 2)) :=
  ⟨not_imp_not.mp (radian_not_ramsey θ),(radian_ramsey_iff θ hinj).2 ∘ algebraic_of_tan⟩

end OAI.EuclideanRamsey.Radian
