/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

public section

/-- Differentiate a scalar expression by the chain and arithmetic rules, leaving the
identification of its derivative as an algebraic goal. Brackets supply derivatives of
non-elementary terms or proofs of nonvanishing. -/
macro "scalar_deriv" hs:(Lean.Parser.Tactic.SolveByElim.args)? : tactic => `(tactic| (
  apply HasDerivAt.congr_deriv
  · repeat' first
      | assumption
      | solve_by_elim (maxDepth := 2) only $[$hs]?
      | apply hasDerivAt_const
      | apply hasDerivAt_id'
      | with_reducible apply HasDerivAt.fun_pow
      | with_reducible apply HasDerivAt.rpow_const
      | with_reducible apply HasDerivAt.fun_sub
      | with_reducible apply HasDerivAt.fun_add
      | with_reducible apply HasDerivAt.fun_mul
      | with_reducible apply HasDerivAt.div_const
      | with_reducible apply HasDerivAt.fun_div
      | with_reducible apply HasDerivAt.fun_neg
      | with_reducible apply HasDerivAt.sqrt
      | solve | positivity | left; positivity
  ))

namespace BergmanWeakType
open Set

abbrev radii := Ico (0 : ℝ) 1
abbrev unitInterval := Ioo (0 : ℝ) 1

theorem square_lt_one {r : ℝ} (hr : r ∈ radii) : r^2 < 1 := by nlinarith [hr.1, hr.2]

theorem inner_sq {r : ℝ} (hr : r ∈ unitInterval) : r^2 < 1 := square_lt_one (Ioo_subset_Ico_self hr)

/-- A scalar second-order jet along one line. Neither mixed partials nor
continuity in unrelated parameters are needed for the polar equation. -/
abbrev JetAt (f d : ℝ → ℝ) (e x : ℝ) := HasDerivAt f (d x) x ∧ HasDerivAt d e x

namespace JetAt
variable {f d g b : ℝ → ℝ} {e a x : ℝ}

theorem comp (h : JetAt f d e x) (hg : JetAt g b a (f x)) :
    JetAt (fun y ↦ g (f y)) (fun y ↦ b (f y)*d y) (a*d x*d x + b (f x)*e) x :=
  ⟨hg.1.comp x h.1, (hg.2.comp x h.1).mul h.2⟩

theorem sub_mul (h : JetAt f d e x) (hg : JetAt g b a x) (c : ℝ) :
    JetAt (fun y ↦ f y-c*g y) (fun y ↦ d y-c*b y) (e-c*a) x :=
  ⟨h.1.sub (hg.1.const_mul c), h.2.sub (hg.2.const_mul c)⟩
end JetAt

end BergmanWeakType
