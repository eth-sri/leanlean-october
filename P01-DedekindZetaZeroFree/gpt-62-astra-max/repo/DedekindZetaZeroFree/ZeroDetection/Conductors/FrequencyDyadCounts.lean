module

public import DedekindZetaZeroFree.Arithmetic.Ideals.ExteriorIdealAndRepresentativeCounting
public import DedekindZetaZeroFree.Arithmetic.Ideals.SIntegerPrincipalIdealIndex

@[expose] public section

open scoped NumberField
open IsDedekindDomain
namespace DedekindZetaZeroFree.Detector

noncomputable def frequencyNorm (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (u : S.integer F) : ℕ :=
  Nat.card ((S.integer F) ⧸ Ideal.span ({u} : Set (S.integer F)))

end DedekindZetaZeroFree.Detector
