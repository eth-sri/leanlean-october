module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FixedData

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowNonprincipal

noncomputable section

open DedekindZetaZeroFree NumberField
open PrincipalMellinComparison.NonprincipalContinuation

variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (D : FixedData S η)

theorem inducers_nonprincipal (u : D.Row) (hu : u.u ≠ 1) :
    ¬ (D.inducers u).plus.character.IsPrincipal ∧ ¬ (D.omega u).character.IsPrincipal := by
  classical
  obtain ⟨h0, hmem⟩ := u.isRep
  let f : PrincipalMellinComparison.Frequency D.recipe := ⟨⟨u.u, h0⟩, hmem⟩
  let U : AllRowEuler.InitialSeparation.RawFrequency D.recipe.A :=
    { u := u.u, ideal := u.toFrequency.ideal, generates := u.toFrequency.generates,
      sixthFree := u.toFrequency.sixthFree }
  refine RawHeckeRows.actual_raw_inducers_nonprincipal D.recipe f U rfl ?_
    (D.inducers u).plus (D.inducers u).minus ?_ ?_
  · intro h
    apply hu
    have := congrArg (fun x : PrincipalMellinComparison.Frequency D.recipe => x.val.val) h
    simpa [f, PrincipalMellinComparison.principalFrequency] using this
  · intro I
    have h := (D.inducers u).plus_mask I.val
    unfold FrequencyCharacterMasks.plusCoefficient at h
    rw [dif_pos I.property] at h
    exact h
  · intro I
    have h := (D.inducers u).minus_mask I.val
    unfold FrequencyCharacterMasks.minusCoefficient FrequencyCharacterMasks.plusCoefficient at h
    rw [dif_pos I.property] at h
    exact h

end

end DedekindZetaZeroFree.Quantitative.RowNonprincipal
