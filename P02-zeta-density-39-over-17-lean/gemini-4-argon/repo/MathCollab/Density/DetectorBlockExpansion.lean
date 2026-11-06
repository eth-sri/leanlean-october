module
public import MathCollab.Density.DetectorBinomial
public import MathCollab.Density.DetectorDyadic

@[expose] public section

open Complex Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density


theorem cpow_neg_eq_real_phase {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    (x : ℂ)^(-ρ) = ((x^(-ρ.re) : ℝ) : ℂ)*dirichletPhase x (-ρ.im) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le,
    Real.rpow_def_of_pos hx, Complex.ofReal_exp, dirichletPhase, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp
  ring





