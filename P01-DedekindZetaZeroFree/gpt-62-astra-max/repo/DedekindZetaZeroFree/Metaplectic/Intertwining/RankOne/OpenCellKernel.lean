module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.NormalizedLevelNumerator
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.GlobalContinuationFromLevelIntegrals
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ZeroMapNonvanishing

@[expose] public section

section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory
namespace DedekindZetaZeroFree.KPRankOneOpenCellKernel
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPRankOneShellContinuation
open KPLocalExceptionalConstruction
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H D : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
    (P : Polarization T)

variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

abbrev multiplicativeMeasure (μ : Measure (LocalField F q)) :=
  KPCubicHaar.multiplicativeHaar (LocalField F q) μ

end

end DedekindZetaZeroFree.KPRankOneOpenCellKernel

end
