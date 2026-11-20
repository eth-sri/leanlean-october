module

public import DedekindZetaZeroFree.Arithmetic.Kummer.LocalHilbertSymbolComparison

@[expose] public section

namespace DedekindZetaZeroFree.RMKummerLocalSquareLaws

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

section

variable (F : Type) [Field F] [NumberField F] (h12 : (primitiveRoots 12 F).Nonempty)

theorem lambda_mul (x y : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    RMKummerLocalNormCharacter.lambda F h12 (x * y) v t =
      RMKummerLocalNormCharacter.lambda F h12 x v t *
        RMKummerLocalNormCharacter.lambda F h12 y v t := by
  letI : ValuativeRel (v.adicCompletion F) :=
    ClassFieldTheory.finitePlaceCompletionValuativeRel F v
  letI : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v
  rw [RMKummerLocalHilbertComparison.lambda_eq_inverse_localHilbertSymbol,
    RMKummerLocalHilbertComparison.lambda_eq_inverse_localHilbertSymbol,
    RMKummerLocalHilbertComparison.lambda_eq_inverse_localHilbertSymbol, map_mul]
  erw [ClassFieldTheory.localHilbertSymbol_mul_right, map_mul, mul_inv_rev]
  exact mul_comm _ _

private theorem lambda_at_one
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    RMKummerLocalNormCharacter.lambda F h12 1 v t = 1 := by
  have h := lambda_mul F h12 1 1 v t
  simp only [one_mul] at h
  exact mul_eq_left.mp h.symm

end

private alias lambda_square := DedekindZetaZeroFree.RMKummerLocalNormCharacter.lambda_pow_two

section

variable (F : Type) [Field F] [NumberField F] (h12 : (primitiveRoots 12 F).Nonempty) (x y : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ)

theorem lambda_div :
    RMKummerLocalNormCharacter.lambda F h12 (x / y) v t =
      RMKummerLocalNormCharacter.lambda F h12 x v t *
        (RMKummerLocalNormCharacter.lambda F h12 y v t)⁻¹ := by
  with_reducible exact eq_mul_inv_of_mul_eq ((lambda_mul F h12 (x / y) y v t).symm.trans (congrArg (fun z : Fˣ => RMKummerLocalNormCharacter.lambda F h12 z v t)
    (div_mul_cancel x y)))

theorem lambda_mul_sq :
    RMKummerLocalNormCharacter.lambda F h12 (x * y ^ 2) v t =
      RMKummerLocalNormCharacter.lambda F h12 x v t := by
  rw [lambda_mul, pow_two, lambda_mul, ← pow_two, lambda_square, mul_one]

end

alias lambda_one := lambda_at_one

variable (F : Type) [Field F] [NumberField F] (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ)

theorem lambda_eq_one_or_neg_one :
    RMKummerLocalNormCharacter.lambda F h12 x v t = 1 ∨
      RMKummerLocalNormCharacter.lambda F h12 x v t = -1 := by
  have h := congrArg (fun z : ℂˣ => (z : ℂ)) (lambda_square F h12 x v t)
  rcases sq_eq_one_iff.mp h with h | h
  · left; exact Units.ext h
  · right; exact Units.ext h

theorem lambda_inv_eq_conj :
    (((RMKummerLocalNormCharacter.lambda F h12 x v t)⁻¹ : ℂˣ) : ℂ) =
      star (RMKummerLocalNormCharacter.lambda F h12 x v t : ℂ) := by
  rcases lambda_eq_one_or_neg_one F h12 x v t with h | h <;>
    simp [h]

end
end DedekindZetaZeroFree.RMKummerLocalSquareLaws
