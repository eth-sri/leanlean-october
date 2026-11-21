module

public import DedekindZetaZeroFree.Theta.Periods.UpperQuotientVanishing
public import DedekindZetaZeroFree.Theta.Unfolding.DyadicFactorizationAndSignedSeries

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def selectedMomentSource (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R}
    (C : JointUpperVanishingSources R N) : SelectedMomentSource R :=
  let U := SignedExpansion.signedUnfolding R C
  {
    Ur := U.Ur
    units := U.units
    psi := Characters.psi R
    primitive := Characters.primitive R
    L := Characters.L R
    norm_one := Characters.norm_one R
    characters_compatible := Characters.compatible R
    H := C.realization.H C.packet
    profiles := finite_profiles_of_same_residue R C.profiles
    reflected_domination := by
      intro u hu h d hh hd hc Z hZ
      refine ⟨U.row_class u, ?_⟩
      have he := U.identity R C.descent u hu h d hh hd hc Z hZ
      rw [mainTerm_eq_zero R C.upperZero, mainTerm_eq_zero R C.upperZero, add_zero, sub_zero] at he
      rw [he]
  }

end DedekindZetaZeroFree.ThetaExpansion

end
