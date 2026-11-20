module

public import QPBT.Games.Defs

/-!
# Quantitative state and operator distances

The blueprint uses asymptotic `approx` notation.  The skeleton records the
corresponding squared norm functionals explicitly, leaving universal-constant
estimates to later proof stages.

## References

These are blueprint `def:state-distance` and `def:povm-distance`; the paper origin is
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-271`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

section

variable {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X)
include X α ι μ

/--
Average squared state-dependent distance between two operator families.  This
is blueprint `def:povm-distance`,
with paper origin `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-271`.
-/
noncomputable def opFamilyDistSq (M N : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) : ℝ :=
  avgOver μ (fun x =>
    ∑ a : α, ‖applyOperatorToState (M x a - N x a) ψ‖ ^ 2)

/-- State-dependent squared distance between complete measurement families. -/
noncomputable abbrev measurementDistSq (M N : X → Quantum.Measurement α ι) (ψ : EuclideanSpace ℂ ι) : ℝ :=
  opFamilyDistSq μ (fun x a => (M x).effect a) (fun x a => (N x).effect a) ψ

end

end MIPStarRE.QPBT
