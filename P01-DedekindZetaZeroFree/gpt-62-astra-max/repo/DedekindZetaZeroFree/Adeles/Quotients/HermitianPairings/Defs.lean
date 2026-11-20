module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.SmoothDescent
public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.DifferentialAndCodifferential
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Cusps.CutoffGraphApproximation

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCutoffTestPairingHolomorphy

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

local notation "cuspLevel" => KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U

abbrev Tests := KPCuspCutoffGraph.scalarTests F ζ hζ H.totallyComplex
  cuspLevel
  (H.atlas cuspLevel)

def testScalar (ψ : Tests F ζ hζ C R P H U) :
    KPContActualCutoffSmoothDescent.Covered F ζ hζ C R P H U → ℂ :=
  KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U ⟨ψ.val, ψ.property.1⟩

def testLaplacian (φ : Tests F ζ hζ C R P H U) :
    KPContActualCutoffSmoothDescent.Covered F ζ hζ C R P H U → ℂ :=
  ((KPContSectorScalarLineAlgebra.S F ζ hζ
    cuspLevel R P H).symm
    (KPCuspCutoffGraph.localLaplacianSection F ζ hζ H.totallyComplex
      cuspLevel
      (H.atlas cuspLevel)
      ⟨φ.val, φ.property.1⟩)).val

variable (w : KPContActualCutoffSmoothDescent.SmoothSections F ζ hζ C R P H U)
    (ψ : KPContActualCutoffSmoothDescent.Covered F ζ hζ C R P H U → ℂ)

def coveredPair :
    KPContActualCutoffSmoothDescent.Covered F ζ hζ C R P H U → ℂ :=
  fun x => KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U w x *
    star (ψ x)

def quotientPair :
    KPSmoothLocalQuotientCharts.X F ζ hζ → ℂ :=
  coveredPair F ζ hζ C R P H U w ψ ∘
    KPContSectorQuotientRelationsComparison.piTilde F ζ hζ
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U)

end DedekindZetaZeroFree.KPContActualCutoffTestPairingHolomorphy

end
