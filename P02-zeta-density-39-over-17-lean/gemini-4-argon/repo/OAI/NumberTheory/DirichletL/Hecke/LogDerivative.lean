module
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

theorem coeff_LSeries_eq (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LSeries (coeff χ) s = -deriv (LFunction χ) s / LFunction χ s :=
  IdealLogDerivative.coeff_LSeries_eq_neg_logDeriv_of_eq _ (idealCoeff_norm_le_one χ)
    (LFunction χ) (fun _ hz => LFunction_eq_series χ hz) s hs
