module

public import Mathlib
public import RequestProject.Main

/-! The variational definitions are shared with the proof development. -/

@[expose] public section

open MeasureTheory
open scoped Real

attribute [-instance] PolyaNeumann.instIsTopologicalAddGroupComplex

namespace PalomarPolyaNeumann

/-- **Strict Neumann Pólya inequality.** For every bounded simply connected Lipschitz domain
`Ω ⊂ ℝ² = ℂ` and every integer `j ≥ 1`, `|Ω| μ_j(Ω) < 4πj`. -/
theorem strict_neumann_polya (Ω : Set ℂ) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) (j : ℕ) (hj : 1 ≤ j) :
    volume Ω * neumannEigenvalue Ω j < ENNReal.ofReal (4 * π * j) :=
  PolyaNeumann.strict_neumann_polya Ω hb hL hsc j hj

/-- **Strict Neumann Pólya inequality, counting form.** For every bounded simply connected
Lipschitz domain `Ω ⊂ ℝ² = ℂ` and every real `E > 0`, `N_N(E) > |Ω| E / (4π)`. -/
theorem strict_neumann_polya_count (Ω : Set ℂ) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) (E : ℝ) (hE : 0 < E) :
    volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) <
      (neumannCount Ω (ENNReal.ofReal E) : ENNReal) :=
  PolyaNeumann.strict_neumann_polya_count Ω hb hL hsc E hE

end PalomarPolyaNeumann
