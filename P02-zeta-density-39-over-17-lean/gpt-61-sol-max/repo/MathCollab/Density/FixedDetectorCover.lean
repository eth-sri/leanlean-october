module
import Mathlib
public import MathCollab.Density.DetectorBlockExpansion
public import MathCollab.Density.DetectorFamilyScales

@[expose] public section

open Complex Filter
open scoped BigOperators Topology
noncomputable section
namespace MathCollab.Density





section
variable {T : ℝ} {N : ℕ} {ρ : ℂ}
    (hT : 1 ≤ T) (hN : 0 < N) (hN' : (N : ℝ) ≤ T^2)
    (hβ : 0 ≤ ρ.re) (hβ' : ρ.re ≤ 1)
include T N ρ hT hN hN' hβ hβ'




end





