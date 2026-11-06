module

public import DedekindZetaZeroFree.Theta.Unfolding.SignedAbsoluteUnfolding
public import DedekindZetaZeroFree.Moments.Comparison.CompatibleThetaMomentData

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources

theorem selected_certified_packet_exists
    {F : Type} [Field F] [NumberField F]
    (S : SArithmeticData F) (η : RayClassCharacter F S.modulus)
    (hη : η.IsPrincipal) (P : PrincipalRayHeckeData F S.modulus η) :
    ∃ R : PrincipalMellin.ActualRecipe S η, Nonempty (CertifiedPacket R) := by
  obtain ⟨R, hR⟩ := root_aligned_recipe_exists S η hη P
  obtain ⟨N⟩ := trace_haar_transport_exists R hR
  obtain ⟨A, hNative, ⟨D⟩⟩ := FourierContinuation.LiteralSource.current_native_transport_exists R hR N
  obtain ⟨B⟩ := first_root_cutoffs_exist R
  obtain ⟨Anew, hAnew⟩ := spherical_seed_exists_of_transport R N A D hNative
  obtain ⟨J, hJ⟩ := RootDerivatives.finite_projector_native R hR N Anew B hAnew
  obtain ⟨L⟩ := first_root_flat_lift_exists R hR N Anew B J hJ
  obtain ⟨hi, hd⟩ := first_root_derivative_period R N Anew B J
  have p9 := Nonempty.intro (L.toJointForwardIdentitySources hi hd)
  have p10 := residual_constant_term R hR N p9
  have p11 := mellin_gaussian R N p10
  have p12 := weighted_digits_descent R hR N p11
  have p13 := same_residue_profiles R N p12
  have p14 := reverse_joint_absolute R N p13
  have p15 := both_upper_averages_zero R N p14
  obtain ⟨C⟩ := signed_unfolding R hR N p15
  exact ⟨R, ⟨C.certified R⟩⟩

theorem selected_rank_one_expansion
    {F : Type} [Field F] [NumberField F]
    (S : SArithmeticData F) (η : RayClassCharacter F S.modulus)
    (hη : η.IsPrincipal) (P : PrincipalRayHeckeData F S.modulus η) :
    ∃ R : PrincipalMellin.ActualRecipe S η,
      RootAligned R ∧ Nonempty (SelectedMomentSource R) := by
  obtain ⟨R, ⟨C⟩⟩ := selected_certified_packet_exists S η hη P
  exact ⟨R, selected_moment_source_of_certified_packet R C⟩
end DedekindZetaZeroFree.ThetaExpansion
