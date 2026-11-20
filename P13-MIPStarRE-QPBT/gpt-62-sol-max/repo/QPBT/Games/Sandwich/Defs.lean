module

public import QPBT.Games.Defs
public import QPBT.Games.DistanceTheorems
public import QPBT.Games.ErrorFunctions

/-! # Definitions for sandwiched measurements

This module defines the palindromic operator products and the conditional
collision predicate used by the sandwich and pasting lemmas.

## References

Blueprint `lem:ld-sandwich` and `lem:pasting`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-525`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

namespace SandwichProduct

end SandwichProduct

/-- The two-family sandwiched product
`(G₂)_{g₂} (G₁)_{g₁} (G₂)_{g₂}` from blueprint
`eq:pasting-2a`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`. -/
def pastedMeasurement {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G₁ G₂ : Type*} (M₁ : G₁ → Op ι) (M₂ : G₂ → Op ι)
    (g₁ : G₁) (g₂ : G₂) : Op ι :=
  M₂ g₂ * M₁ g₁ * M₂ g₂

/-- The distinct-codeword collision bound on each conditional fiber. Null fibers
satisfy the unnormalized inequality with both sides zero. -/
def HasConditionalCollisionBound {X Y R Γ : Type*}
    [DecidableEq X] [Fintype Y] [DecidableEq R]
    (D : Distribution (X × Y)) (eval : Γ → Y → R) (η : ℝ) : Prop :=
  ∀ x g g', g ≠ g' →
    (∑ y, D.weight (x, y) * if eval g y = eval g' y then 1 else 0) ≤
      η * (D.map Prod.fst).weight x

/-! ### Tensor placements of measurements

The operator families compared in `lem:pasting` are placed on one factor of a
bipartite space. The two constructions below present such a placed family as a
measurement, so that the consistency calculus applies to it verbatim. -/

/-- An alias of `DistanceCalculus.leftPlacedMeasurement`, whose effects are the
left tensor placements of the effects of `M`. Formalization support for `lem:pasting`, blueprint
`ch12_qpbt_games.tex:960-990`. -/
noncomputable def Measurement.leftPlacement {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Measurement α ιA) : Measurement α (ιA × ιB) :=
  DistanceCalculus.leftPlacedMeasurement M

/-- An alias of `DistanceCalculus.rightPlacedMeasurement`, whose effects are the
right tensor placements of the effects of `M`. Formalization support for `lem:pasting`, blueprint
`ch12_qpbt_games.tex:960-990`. -/
noncomputable def Measurement.rightPlacement {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Measurement α ιB) : Measurement α (ιA × ιB) :=
  DistanceCalculus.rightPlacedMeasurement M

/-- The effects of the left placement. -/
@[simp] theorem Measurement.leftPlacement_effect {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Measurement α ιA) (a : α) :
    (Measurement.leftPlacement (ιB := ιB) M).effect a = heteroKron (M.effect a) 1 := rfl

/-- The effects of the right placement. -/
@[simp] theorem Measurement.rightPlacement_effect {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Measurement α ιB) (a : α) :
    (Measurement.rightPlacement (ιA := ιA) M).effect a = heteroKron 1 (M.effect a) := rfl

/-- The left placement of a projective measurement is projective.
Formalization support for `lem:pasting`, blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem Measurement.isProjective_leftPlacement {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Measurement α ιA) (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.QPBT.Measurement.IsProjective (Measurement.leftPlacement (ιB := ιB) M) :=
  Measurement.mapEffects_isProjective M hM DistanceCalculus.leftTensorAdd heteroKron_one_one
    (fun {_} h => kronecker_nonneg h Matrix.PosSemidef.one.nonneg) fun A => by
    change heteroKron (A * A) (1 : Op ιB) =
      heteroKron A (1 : Op ιB) * heteroKron A (1 : Op ιB)
    rw [heteroKron_mul, mul_one]

/-- The right placement of a projective measurement is projective. This is the
right-factor mirror of the preceding lemma and the second of the four
properties of the placement collected in the formalization-support node
`lem:pasting-tensor-placement`, blueprint `ch12_qpbt_games.tex:1063-1071`. -/
theorem Measurement.isProjective_rightPlacement {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Measurement α ιB) (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.QPBT.Measurement.IsProjective (Measurement.rightPlacement (ιA := ιA) M) :=
  Measurement.mapEffects_isProjective M hM DistanceCalculus.rightTensorAdd heteroKron_one_one
    (fun {_} h => kronecker_nonneg Matrix.PosSemidef.one.nonneg h) fun A => by
    change heteroKron (1 : Op ιA) (A * A) =
      heteroKron (1 : Op ιA) A * heteroKron (1 : Op ιA) A
    rw [heteroKron_mul, one_mul]

section

variable {α β ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
include α β ιA ιB

/-- Postprocessing commutes with the left tensor placement. This is one of the
four properties of the placement collected in the formalization-support node
`lem:pasting-tensor-placement`, blueprint `ch12_qpbt_games.tex:1063-1071`; it
records the compatibility of the placement of `lem:pasting` with the outcome
coarse-grainings its statement applies, and is stated for the left factor
alongside its right-factor mirror below. -/
theorem Measurement.leftPlacement_postprocess
    (M : Measurement α ιA) (f : α → β) (b : β) :
    (Measurement.leftPlacement (ιB := ιB) (M.postprocess f)).effect b =
      ((Measurement.leftPlacement (ιB := ιB) M).postprocess f).effect b := by
  classical
  simp only [Measurement.leftPlacement_effect, Measurement.postprocess_effect,
    heteroKron_finset_sum_left]

/-- Postprocessing commutes with the right tensor placement. This is the
right-factor mirror of the preceding compatibility, the fourth of the four
properties of the placement collected in the formalization-support node
`lem:pasting-tensor-placement`, blueprint `ch12_qpbt_games.tex:1063-1071`. -/
theorem Measurement.rightPlacement_postprocess
    (M : Measurement α ιB) (f : α → β) (b : β) :
    (Measurement.rightPlacement (ιA := ιA) (M.postprocess f)).effect b =
      ((Measurement.rightPlacement (ιA := ιA) M).postprocess f).effect b := by
  classical
  simp only [Measurement.rightPlacement_effect, Measurement.postprocess_effect,
    heteroKron_finset_sum_right]

end

end MIPStarRE.QPBT
