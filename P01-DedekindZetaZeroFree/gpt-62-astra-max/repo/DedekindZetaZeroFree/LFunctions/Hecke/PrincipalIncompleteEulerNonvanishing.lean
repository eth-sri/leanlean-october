module

public import DedekindZetaZeroFree.Moments.Comparison.PoissonMellinKernelData
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterUnitarity

@[expose] public section

namespace DedekindZetaZeroFree.MellinZeroFree

open scoped NumberField

noncomputable section

open IsDedekindDomain

theorem norm_comparisonRealPower (Z : ℝ) (s : ℂ) :
    ‖comparisonRealPower Z s‖ = Real.exp (s.re * Real.log Z) := by
  rw [comparisonRealPower, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

variable (F : Type) [Field F] [NumberField F] (A : SArithmeticData F) (η : RayClassCharacter F A.modulus)

theorem comparisonPrincipalIncompleteL_eulerFactors_ne_zero (s : ℂ) (hs : 0 < s.re) :
    (∏ v ∈ A.Sf,
      (1 - η v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro v hv
  have hZ : 1 < idealNorm v.asIdeal := by
    have := NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
    simpa [idealNorm] using this
  have hlog := Real.log_pos hZ
  let comparisonRealPower₀ := comparisonRealPower (idealNorm v.asIdeal) (-s)
  have hnorm : ‖comparisonRealPower₀‖ < 1 := by
    rw [norm_comparisonRealPower, Real.exp_lt_one_iff]
    simp only [Complex.neg_re]
    nlinarith
  have hη :=
    RayUnitary.ray_character_norm_le_one F A.modulus A.modulus_ne_zero η v.asIdeal
  have hlt : ‖η v.asIdeal * comparisonRealPower₀‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (comparisonRealPower₀),
      norm_nonneg (η v.asIdeal)]
  intro h
  rw [((sub_eq_zero.mp h).symm), norm_one] at hlt
  exact lt_irrefl 1 hlt

theorem comparisonPrincipalIncompleteL_ne_zero_of_L_ne_zero (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F A.modulus η) (s : ℂ) (hs : 0 < s.re)
    (hL : P.L s ≠ 0) :
    comparisonPrincipalIncompleteL F A η hη P s ≠ 0 := by
  unfold comparisonPrincipalIncompleteL
  exact mul_ne_zero hL (comparisonPrincipalIncompleteL_eulerFactors_ne_zero F A η s hs)

end

end DedekindZetaZeroFree.MellinZeroFree
