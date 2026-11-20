module

public import DedekindZetaZeroFree.Metaplectic.Torus.CenterInductionDiagonalAction
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.IteratedCenterKernelsAndCubeCosets

@[expose] public section

section

namespace DedekindZetaZeroFree.KPRankOneLiftedRegulatedDiagonalAlgebra

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H D : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
    (P : Polarization T)

local notation "LocalCompletion" => LocalField F q

def sourceTranslation (a b u v : LocalCompletionˣ) : LocalCompletion :=
  (a : LocalCompletion) * (u : LocalCompletion) ^ 3 +
    (b : LocalCompletion) * (v : LocalCompletion) ^ 3

def reverseIncrement (b v : LocalCompletionˣ) : LocalCompletionˣ := b * v ^ 3

def doubleKernel (B : Binding F ζ hζ q A P)
    (rep : D → H) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalCompletion → ℂ) (z lam : ℂ) (h : H)
    (a b u v : LocalCompletionˣ) : ℂ :=
  let ξ := a * u ^ 3
  let η := reverseIncrement F q b v
  (B.eta (kappa F ζ hζ q η 0) : ℂ) *
    (B.eta (kappa F ζ hζ q ξ (η : LocalCompletion)) : ℂ) *
    normPower LocalCompletion (η ^ 2) (-z) *
    normPower LocalCompletion (ξ ^ 2) z *
    ((centerTorus F ζ hζ q T A .minus (B.rootTorus η))
      ((centerTorus F ζ hζ q T A .plus (B.rootTorus ξ))
        ((centerCoordinates T rep hrep).symm
          (φ (sourceTranslation F q a b u v) • Pi.single d (1 : ℂ))))).val h *
    normPower LocalCompletion η lam

end

end DedekindZetaZeroFree.KPRankOneLiftedRegulatedDiagonalAlgebra

end
