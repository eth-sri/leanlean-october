module

public import DedekindZetaZeroFree.Theta.Profiles.RayParityKernels

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

open scoped NumberField

theorem conductor_real_pos
    (F : Type) [Field F] [NumberField F] (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    0 < (((|NumberField.discr F| : ℤ) : ℝ) * (Ideal.absNorm m : ℝ)) ∧
      (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) =
        ((((|NumberField.discr F| : ℤ) : ℝ) * (Ideal.absNorm m : ℝ)) : ℂ) := by
  have hd : 0 < ((|NumberField.discr F| : ℤ) : ℝ) := by
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero F)
  have hm' : 0 < (Ideal.absNorm m : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hm)
  exact ⟨mul_pos hd hm', by simp only [Complex.ofReal_intCast, Complex.ofReal_natCast]⟩

theorem completed_prefactor_eq_kappa
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (s : ℂ) :
    ((((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (s / 2) *
      Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F) =
      (4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces F *
        (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (s / 2) *
        DedekindZetaZeroFree.AbelianQuotient.RayParity.κδ F ∅ s := by
  classical
  letI : NumberField.IsTotallyComplex F := hF
  letI : IsEmpty (DedekindZetaZeroFree.AbelianQuotient.RayCoset.RealPlaces F) :=
    ⟨fun v => NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
      (NumberField.IsTotallyComplex.isComplex v.1) v.2⟩
  have hr : NumberField.InfinitePlace.nrRealPlaces F = 0 := 
    Fintype.card_eq_zero
  simp only [DedekindZetaZeroFree.AbelianQuotient.RayParity.κδ, hr, pow_zero,
    inv_one, one_mul, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  have h4 : (4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces F ≠ 0 :=
    by simp
  field_simp
  <;> ring

theorem completed_prefactor_ne_zero
    (F : Type) [Field F] [NumberField F] (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (s : ℂ) (hs : 1 < s.re) :
    (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (s / 2) *
      Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F ≠ 0 := by
  have hA := conductor_real_pos F m hm
  have hA0 : (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ≠ 0 := by
    rw [hA.2]
    exact_mod_cast ne_of_gt hA.1
  have hG : Complex.Gammaℂ s ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    apply mul_ne_zero
    · simp
    · exact Complex.Gamma_ne_zero_of_re_pos (by linarith)
  simp_all
