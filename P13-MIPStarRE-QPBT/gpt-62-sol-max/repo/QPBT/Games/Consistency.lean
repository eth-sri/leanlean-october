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
open DistanceCalculus

/-- Swapping both coordinates of a Kronecker product exchanges its factors. -/
theorem reindexOp_prodComm_heteroKron {ιA ιB : Type*} (A : Op ιA) (B : Op ιB) :
    reindexOp (Equiv.prodComm ιA ιB) (heteroKron B A) = heteroKron A B := by
  ext i j
  exact mul_comm _ _

section Reindex

open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Coordinate transport intertwines matrix action on a state. -/
theorem applyOperatorToState_reindexState (e : ι ≃ κ) (T : Op κ) (ψ : EuclideanSpace ℂ ι) :
    applyOperatorToState T (reindexState e ψ) =
      reindexState e (applyOperatorToState (reindexOp e T) ψ) := by
  ext k
  change (T *ᵥ (ψ.ofLp ∘ e.symm)) k = (T.submatrix e e *ᵥ ψ.ofLp) (e.symm k)
  rw [Matrix.submatrix_mulVec_equiv]
  simp [Function.comp_def]

/-- Simultaneous reindexing of a state and operator preserves the image norm. -/
theorem norm_applyOperatorToState_reindexState (e : ι ≃ κ) (T : Op κ)
    (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState T (reindexState e ψ)‖ =
      ‖applyOperatorToState (reindexOp e T) ψ‖ := by
  rw [applyOperatorToState_reindexState, reindexState_norm_eq]

/-- State-dependent distance is invariant under simultaneous reindexing. -/
theorem opFamilyDistSq_reindexState {X α : Type*} [Fintype α] (e : ι ≃ κ)
    (μ : Distribution X) (M N : X → α → Op κ) (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq μ M N (reindexState e ψ) =
      opFamilyDistSq μ (fun x a => reindexOp e (M x a)) (fun x a => reindexOp e (N x a)) ψ := by
  simp_rw [opFamilyDistSq, norm_applyOperatorToState_reindexState, reindexOp_sub]

end Reindex

/-- The off-diagonal defect in blueprint
`def:consistency`, paper `06_nonlocal_games_and_mipstar.tex:232-248`. -/
noncomputable def consistencyDefect {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) : ℝ :=
  avgOver μ (fun x =>
    ∑ a : α, ∑ b : α,
      if a = b then 0 else stateQForm ψ (A x a * B x b))

/-- The consistency defect of two complete measurements on one space. -/
noncomputable abbrev measurementDefect {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → Quantum.Measurement α ι) (ψ : EuclideanSpace ℂ ι) : ℝ :=
  consistencyDefect μ (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ

/-- The mismatch mass of local measurements on a bipartite state. -/
noncomputable abbrev bipartiteDefect {X α I J : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (μ : Distribution X) (A : X → Quantum.Measurement α I) (B : X → Quantum.Measurement α J)
    (ψ : EuclideanSpace ℂ (I × J)) : ℝ :=
  consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
    (fun x a => heteroKron 1 ((B x).effect a)) ψ

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
  rw [← uniformDistribution_map_equiv e, Distribution.avgOver_map]

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
  unfold consistencyDefect
  apply avgOver_congr
  intro x
  refine Fintype.sum_equiv e _ _ fun a => ?_
  exact Fintype.sum_equiv e _ _ fun b => by simp only [e.apply_eq_iff_eq]

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
      consistencyDefect (uniformDistribution Y) A B psi :=
  (consistencyDefect_outcome_equiv _ outcomeEquiv _ _ psi).trans
    (consistencyDefect_uniform_question_equiv questionEquiv A B psi)

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
  rw [funext fun x => funext (hA x), funext fun x => funext (hB x)]

/-- Unit-alphabet specialization of blueprint
`def:povm-distance`, paper `06_nonlocal_games_and_mipstar.tex:258-271`. -/
noncomputable def opDistSq {X ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (M N : X → Op ι) (ψ : EuclideanSpace ℂ ι) : ℝ :=
  opFamilyDistSq μ (fun x (_ : Unit) => M x) (fun x (_ : Unit) => N x) ψ

end MIPStarRE.QPBT
