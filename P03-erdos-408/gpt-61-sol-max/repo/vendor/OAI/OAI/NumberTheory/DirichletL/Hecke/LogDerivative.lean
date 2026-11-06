module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Hecke.BoundaryIntegration
public import OAI.NumberTheory.DirichletL.Hecke.Origin
public import OAI.NumberTheory.DirichletL.IdealLogDerivative

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical Topology
namespace SevenEighths.HeckeLogDerivative
open HeckeFamily

def coeff (χ : Character) : ℕ → ℂ := IdealLogDerivative.coeff (idealCoeff χ)

theorem coeff_LSeries_eq  χ   {s}  (hs : 1 < s.re) :
    LSeries (coeff χ) s = -deriv (LFunction χ) s / LFunction χ s :=
  OAI.SevenEighths.IdealLogDerivative.coeff_LSeries_eq_neg_logDeriv_of_eq (OAI.SevenEighths.HeckeFamily.idealCoeff χ) (OAI.SevenEighths.HeckeFamily.idealCoeff_norm_le_one χ) (OAI.SevenEighths.HeckeFamily.LFunction χ) (@OAI.SevenEighths.HeckeFamily.LFunction_eq_series χ) s hs

end SevenEighths.HeckeLogDerivative

end

end OAI
