module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SIntegers.DilationAndTranslation
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalDifferentNormalization
public import DedekindZetaZeroFree.Metaplectic.Weil.QuadraticFourierOperatorsAndPhases

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.QuadraticRawProduct

variable (F : Type) [Field F] [NumberField F]

section

variable (T : Finset (HeightOneSpectrum (𝓞 F)))

def theta
    (f : PoissonS.Space F T → ℂ) : ℂ :=
  ∑' x : sIntegerRing F T, f (PoissonS.diagonalHom F T (x : F))

def chirp (b : F)
    (f : PoissonS.Space F T → ℂ) : PoissonS.Space F T → ℂ :=
  fun x => (sLocalTraceCharacter F T
    (sLocalDiagonal F T b * ((PoissonS.localProductToSpace F T).symm x) ^ 2) : ℂ) * f x

def dilation (c : F)
    (f : PoissonS.Space F T → ℂ) : PoissonS.Space F T → ℂ :=
  fun x => f (PoissonS.localProductToSpace F T
    (sLocalDiagonal F T c * (PoissonS.localProductToSpace F T).symm x))

end

local instance completionMeasurable (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance completionBorel (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

variable (T : Finset (HeightOneSpectrum (𝓞 F)))

abbrev fourier :=
  PoissonS.fourierIntegral F T (fun v : T => localFiniteCharacter F v.val)
    (fun v : T => localNormalizedHaar F v.val)

def testSpace :
    Submodule ℂ (PoissonS.Space F T → ℂ) :=
  Submodule.span ℂ {f | ∃ (fArch : SchwartzMap (PoissonArch.Space F) ℂ)
    (φ : (v : T) → v.val.adicCompletion F → ℂ),
    (∀ v, IsLocallyConstant (φ v)) ∧ (∀ v, HasCompactSupport (φ v)) ∧
    f = PoissonS.tensorFunction F T fArch φ}

theorem theta_const_mul
    (c : ℂ) (f : PoissonS.Space F T → ℂ) :
    theta F T (fun x => c * f x) = c * theta F T f := tsum_mul_left

end DedekindZetaZeroFree.QuadraticRawProduct

end
