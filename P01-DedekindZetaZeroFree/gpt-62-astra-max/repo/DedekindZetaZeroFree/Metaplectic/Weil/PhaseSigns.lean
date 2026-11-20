module

public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData

@[expose] public section

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)

theorem weil_zeta12_cube_sq : (A.zeta12 ^ 3) ^ 2 = (-1 : F) := by
  simpa only [← pow_mul] using A.zeta12_pow_six

theorem weil_finite_minus_one_square
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    (algebraMap F (v.adicCompletion F) (A.zeta12 ^ 3)) ^ 2 =
      (-1 : v.adicCompletion F) := by
  simpa using
    congrArg (algebraMap F (v.adicCompletion F)) (weil_zeta12_cube_sq F A)

end DedekindZetaZeroFree
