module

public import MIPStarRE.LDT.Basic.DistributionAvg
public import QPBT.Games.Distance
public import QPBT.Games.DistributionAux
public import QPBT.State

/-! # State-dependent consistency and strategy closeness

The definitions are the finite-dimensional forms of blueprint
`def:consistency` and `def:strategy-distance`,
from `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-288`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

/-- The off-diagonal defect in blueprint
`def:consistency`, paper `06_nonlocal_games_and_mipstar.tex:232-248`. -/
noncomputable def consistencyDefect {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) : ℝ :=
  avgOver μ (fun x =>
    ∑ a : α, ∑ b : α,
      if a = b then 0 else
        (inner ℂ ψ ((EuclideanSpace.equiv ι ℂ).symm
          ((A x a * B x b).mulVec ψ))).re)

/-- A uniform consistency defect is invariant under a bijective relabeling of
its question type. -/
theorem consistencyDefect_uniform_question_equiv
    {X Y Outcome iota : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype iota] [DecidableEq iota]
    (e : X ≃ Y) (A B : Y → Outcome → Op iota)
    (psi : EuclideanSpace ℂ iota) :
    consistencyDefect (uniformDistribution X)
        (fun x a => A (e x) a) (fun x a => B (e x) a) psi =
      consistencyDefect (uniformDistribution Y) A B psi := by
  unfold consistencyDefect
  simpa using avgOver_uniform_equiv e (fun x =>
    ∑ a : Outcome, ∑ b : Outcome,
      if a = b then 0 else
        (inner ℂ psi ((EuclideanSpace.equiv iota ℂ).symm
          (((A (e x) a) * (B (e x) b)).mulVec psi))).re)

/-- A consistency defect is invariant under a bijective relabeling of both
outcome families. -/
theorem consistencyDefect_outcome_equiv
    {X Alpha Beta iota : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype Alpha] [DecidableEq Alpha]
    [Fintype Beta] [DecidableEq Beta]
    [Fintype iota] [DecidableEq iota]
    (mu : Distribution X) (e : Beta ≃ Alpha)
    (A B : X → Alpha → Op iota) (psi : EuclideanSpace ℂ iota) :
    consistencyDefect mu
        (fun x b => A x (e b)) (fun x b => B x (e b)) psi =
      consistencyDefect mu A B psi := by
  apply avgOver_congr
  intro x
  let term := fun a b =>
    if a = b then 0 else
      (inner ℂ psi ((EuclideanSpace.equiv iota ℂ).symm
        (((A x a) * (B x b)).mulVec psi))).re
  calc
    _ = ∑ a : Beta, ∑ b : Beta, term (e a) (e b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      unfold term
      simp
    _ =
        ∑ a : Beta, ∑ b : Alpha, term (e a) b := by
      simp [Equiv.sum_comp]
    _ = ∑ a : Alpha, ∑ b : Alpha, term a b :=
      Equiv.sum_comp e (fun a => ∑ b : Alpha, term a b)
    _ = _ := rfl

/-- Simultaneous bijective relabeling of uniform questions and outcomes leaves
the consistency defect unchanged. -/
theorem consistencyDefect_uniform_question_outcome_equiv
    {X Y Alpha Beta iota : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Alpha] [DecidableEq Alpha]
    [Fintype Beta] [DecidableEq Beta]
    [Fintype iota] [DecidableEq iota]
    (questionEquiv : X ≃ Y) (outcomeEquiv : Beta ≃ Alpha)
    (A B : Y → Alpha → Op iota) (psi : EuclideanSpace ℂ iota) :
    consistencyDefect (uniformDistribution X)
        (fun x b => A (questionEquiv x) (outcomeEquiv b))
        (fun x b => B (questionEquiv x) (outcomeEquiv b)) psi =
      consistencyDefect (uniformDistribution Y) A B psi := by
  calc
    consistencyDefect (uniformDistribution X)
        (fun x b => A (questionEquiv x) (outcomeEquiv b))
        (fun x b => B (questionEquiv x) (outcomeEquiv b)) psi =
      consistencyDefect (uniformDistribution X)
        (fun x a => A (questionEquiv x) a)
        (fun x a => B (questionEquiv x) a) psi :=
      consistencyDefect_outcome_equiv (uniformDistribution X)
        outcomeEquiv _ _ psi
    _ = consistencyDefect (uniformDistribution Y) A B psi :=
      consistencyDefect_uniform_question_equiv questionEquiv A B psi

/-- Pointwise equality of both operator families gives equality of their
consistency defects. -/
theorem consistencyDefect_congr
    {X Outcome iota : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype iota] [DecidableEq iota]
    (mu : Distribution X) (A A' B B' : X → Outcome → Op iota)
    (psi : EuclideanSpace ℂ iota)
    (hA : ∀ x a, A x a = A' x a) (hB : ∀ x a, B x a = B' x a) :
    consistencyDefect mu A B psi = consistencyDefect mu A' B' psi := by
  unfold consistencyDefect
  simp_all

variable {X ι : Type*} [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]

/-- Unit-alphabet specialization of blueprint
`def:povm-distance`, paper `06_nonlocal_games_and_mipstar.tex:258-271`. -/
noncomputable def opDistSq (μ : Distribution X) (M N : X → Op ι) (ψ : EuclideanSpace ℂ ι) : ℝ :=
  opFamilyDistSq μ (fun x (_ : Unit) => M x) (fun x (_ : Unit) => N x) ψ

end MIPStarRE.QPBT
