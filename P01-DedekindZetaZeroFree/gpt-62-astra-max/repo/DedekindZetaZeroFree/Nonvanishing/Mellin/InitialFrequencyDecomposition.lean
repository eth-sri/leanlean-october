module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.NormalizedProbeArithmeticData

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison

noncomputable section
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

section

variable (R : PrincipalMellin.ActualRecipe S η)

abbrev Frequency :=
  {u // u ∈ R.probe.frequencies.reps}

def principalFrequency : Frequency R :=
  ⟨⟨1, one_ne_zero⟩, R.probe.frequencies.containsOne⟩

def frequencyNorm (u : Frequency R) : ℝ :=
  (FiniteTransform.exteriorNorm R.A.R.toSubring u.val.val : ℝ)

def separatedSeries
    (u : Frequency R) (ξ w z : ℂ) : ℂ :=
  NormalizedProbe.principalSeparatedMellinSeries R.A R.σ R.target R.traceBad
    R.probe u ξ w z

end

open MeasureTheory

end
end DedekindZetaZeroFree.PrincipalMellinComparison
