module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section


namespace DedekindZetaZeroFree.Hecke

open scoped NumberField

noncomputable def normalizedHeckePrefactor (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (s : ℂ)  :=
  (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (s / 2) *
    Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F

end DedekindZetaZeroFree.Hecke
