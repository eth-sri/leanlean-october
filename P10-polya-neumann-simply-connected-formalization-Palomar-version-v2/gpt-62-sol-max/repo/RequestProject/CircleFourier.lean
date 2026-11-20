module

public import Mathlib.Analysis.Fourier.AddCircle

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real Set MeasureTheory
open scoped ComplexConjugate

instance instTwoPiPeriod : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

theorem liftIco_zero_eqOn_Icc {T : ℝ} [hT : Fact (0 < T)] {β : Type*} {f : ℝ → β}
    (hf : f 0 = f T) : EqOn (fun t : ℝ => AddCircle.liftIco T 0 f (t : AddCircle T)) f (Icc 0 T) := by
  intro t ht
  rcases eq_or_lt_of_le ht.2 with rfl | htT
  · change AddCircle.liftIco t 0 f (t : AddCircle t) = f t
    rw [AddCircle.coe_period, ← hf]
    exact AddCircle.liftIco_zero_coe_apply ⟨le_rfl, hT.out⟩
  · exact AddCircle.liftIco_zero_coe_apply ⟨ht.1, htT⟩

lemma norm_fourier_coe (n : ℤ) (x : ℝ) : ‖fourier n (x : AddCircle (2 * π))‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

lemma fourier_coe_two_pi (n : ℤ) (x : ℝ) :
    fourier n (x : AddCircle (2 * π)) = Complex.exp (n * x * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

/-- Fourier coefficients of a conjugate are conjugates of the reflected sequence. -/
lemma fourierCoeffOn_conj (g : ℝ → ℂ) (m : ℤ) :
    fourierCoeffOn two_pi_pos (fun θ => conj (g θ)) m = conj (fourierCoeffOn two_pi_pos g (-m)) := by
  simp only [fourierCoeffOn_eq_integral, Complex.real_smul, map_mul, Complex.conj_ofReal,
    ← intervalIntegral.intervalIntegral_conj, smul_eq_mul, neg_neg, fourier_neg]

lemma liftIoc_circle_coe (f : AddCircle (2 * π) → ℂ) :
    AddCircle.liftIoc (2 * π) 0 (fun θ : ℝ => f θ) = f := by
  funext q
  change f ((AddCircle.equivIoc (2 * π) 0 q : ℝ) : AddCircle (2 * π)) = f q
  simp

lemma fourierCoeff_eq_on_circle (f : AddCircle (2 * π) → ℂ) :
    fourierCoeff f = fourierCoeffOn two_pi_pos (fun θ : ℝ => f θ) := by
  funext n
  simpa only [liftIoc_circle_coe, zero_add] using
    (fourierCoeff_liftIoc_eq (T := 2 * π) (a := 0) (fun θ : ℝ => f θ) n)

end PolyaNeumann

end
