module

public import DedekindZetaZeroFree.Theta.Unfolding.SignedAbsoluteUnfolding

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources

theorem selected_rank_one_expansion
    {F : Type} [Field F] [NumberField F]
    (S : SArithmeticData F) (η : RayClassCharacter F S.modulus)
    (hη : η.IsPrincipal) (P : PrincipalRayHeckeData F S.modulus η) :
    ∃ R : PrincipalMellin.ActualRecipe S η,
      RootAligned R ∧ Nonempty (SelectedMomentSource R) := by
  obtain ⟨R, hR⟩ := root_aligned_recipe_exists S η hη P
  obtain ⟨N⟩ := trace_haar_transport_exists R hR
  have p5 := admissible_flat_sources R hR N
  have p6 := common_smooth_laurent_germ_exists R hR N p5
  have p7 := detected_period_factorization R hR N p6
  have p8 := exterior_coefficients R hR N p7
  have p9 := first_root_packet R hR N p8
  have p10 := residual_constant_term R hR N p9
  have p11 := mellin_gaussian R N p10
  have p12 := weighted_digits_descent R hR N p11
  have p13 := same_residue_profiles R N p12
  have p14 := reverse_joint_absolute R N p13
  have p15 := both_upper_averages_zero R N p14
  obtain ⟨C⟩ := p15
  exact ⟨R, hR, ⟨selectedMomentSource R C⟩⟩
end DedekindZetaZeroFree.ThetaExpansion
