module

public import Mathlib

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.SIntegers.FundamentalDomainScaling
public import DedekindZetaZeroFree.Metaplectic.Weil.ExteriorQuadraticResidueGaussSums

@[expose] public section


noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.SArithmeticData

variable {F : Type} [Field F] [NumberField F]







def finiteTraceHaar (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) : Measure (v.adicCompletion F) := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  letI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let μ₀ : Measure (v.adicCompletion F) := Measure.addHaar
  exact (ENNReal.ofReal (PoissonS.integerVolume F v) /
    μ₀ {x | ‖x‖ ≤ (1 : ℝ)}) • μ₀

def finiteTraceFourier (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F))
    (f : v.adicCompletion F → ℂ) (y : v.adicCompletion F) : ℂ := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  letI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  exact ∫ x : v.adicCompletion F,
    f x * (ResidueTrace.localTraceCharacter v (-x * y) : ℂ) ∂A.finiteTraceHaar v

def finiteQuadraticMultiplier (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F)
    (f : v.adicCompletion F → ℂ) (x : v.adicCompletion F)  :=
  (ResidueTrace.localTraceCharacter v (a * x ^ 2) : ℂ) * f x

def finiteDilation (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F)
    (f : v.adicCompletion F → ℂ) (x : v.adicCompletion F)  :=
  f (c * x)

def finiteQuadraticCutoff (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ) (n : ℕ) : ℂ := (exteriorRawQuadraticCutoff v (A.finiteTraceHaar v) a n)

def FiniteQuadraticStabilizes (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)  :=
  ∃ z : ℂ, ∀ᶠ n : ℕ in Filter.atTop, A.finiteQuadraticCutoff v a n = z

def finiteGamma (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)  :=
  if h : A.FiniteQuadraticStabilizes v a then Classical.choose h else 0

theorem finiteQuadraticCutoff_eventually_eq_gamma (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (h : A.FiniteQuadraticStabilizes v a) :
    ∀ᶠ n : ℕ in Filter.atTop, A.finiteQuadraticCutoff v a n = A.finiteGamma v a := by
  simpa only [finiteGamma, dif_pos h] using Classical.choose_spec h

def finiteWeilPhase (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)  :=
  A.finiteGamma v a / A.finiteGamma v 1

def complexGamma (A : SArithmeticData F)
    (w : InfinitePlace F) (a : w.Completionˣ) : ℂ := 1

def complexWeilPhase (A : SArithmeticData F)
    (w : InfinitePlace F) (a : w.Completionˣ)  :=
  A.complexGamma w a / A.complexGamma w 1

end DedekindZetaZeroFree.SArithmeticData

end
