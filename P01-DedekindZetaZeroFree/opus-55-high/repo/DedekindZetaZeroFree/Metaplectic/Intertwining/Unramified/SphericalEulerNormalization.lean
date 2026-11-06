module

public import DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.UnramifiedSphericalImage

@[expose] public section

namespace DedekindZetaZeroFree.KPGlobalGoodEulerFactor

open KPLocalStoneVonNeumann KPLocalPrincipalSeries MeasureTheory
open scoped Valued

noncomputable section

def convergenceChamber : Set ℂ := {s | -(1 / 6 : ℝ) < s.re}

def sphericalCoefficient (q m : ℝ) (s : ℂ) : ℂ :=
  (m : ℂ) *
    (1 - Complex.exp ((-2 - 6 * s) * (Real.log q : ℂ))) /
    (1 - Complex.exp ((-1 - 6 * s) * (Real.log q : ℂ)))
