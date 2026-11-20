module

public import DedekindZetaZeroFree.Metaplectic.Weil.QuadraticFourierOperatorsAndPhases

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.OddEvaluation

variable {F : Type} [Field F] [NumberField F]

abbrev Residue (v : HeightOneSpectrum (𝓞 F)) :=
  IsLocalRing.ResidueField (v.adicCompletionIntegers F)

abbrev residueFintype (v : HeightOneSpectrum (𝓞 F)) : Fintype (Residue v) :=
  @Fintype.ofFinite _ (SArithmeticData.exteriorLocalResidue_finite v)

attribute [local instance] residueFintype

variable (v : HeightOneSpectrum (𝓞 F))

abbrev localUnit :
    (v.adicCompletionIntegers F)ˣ →* (v.adicCompletion F)ˣ :=
  Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom

abbrev uniformizer
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) :
    (v.adicCompletion F)ˣ :=
  Units.mk0 (π : v.adicCompletion F) (fun h => hπ.ne_zero (Subtype.ext h))

abbrev conductor
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ) : Prop :=
  (∀ x : v.adicCompletionIntegers F,
    ResidueTrace.localTraceCharacter v
      (((uniformizer v π hπ)^c : (v.adicCompletion F)ˣ) *
        (x : v.adicCompletion F)) = 1) ∧
  ∃ x : v.adicCompletionIntegers F,
    ResidueTrace.localTraceCharacter v
      (((uniformizer v π hπ)^(c-1) : (v.adicCompletion F)ˣ) *
        (x : v.adicCompletion F)) ≠ 1

abbrev theta
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (x : Residue v) : Circle :=
  ((ResidueTrace.localTraceCharacter v).compAddMonoidHom
    (AddMonoidHom.mulLeft (((uniformizer v π hπ)^c :
      (v.adicCompletion F)ˣ) : v.adicCompletion F)))
    (((Classical.choose (IsLocalRing.residue_surjective x) :
      v.adicCompletionIntegers F) : v.adicCompletion F) / (π : v.adicCompletion F))

abbrev quadratic
    (x : Residue v) : ℂ := (quadraticChar (Residue v) x : ℂ)

abbrev epsilon
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ) : ℂ :=
  (∑ x : Residue v, (theta v π hπ c (x^2) : ℂ)) /
    (Real.sqrt (Fintype.card (Residue v)) : ℂ)

end DedekindZetaZeroFree.OddEvaluation

end
