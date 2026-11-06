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

/-- The positive-mass conditional collision bound used by `lem:pasting`.
This is a formalization-only spelling of the conditional probability in
`lem:pasting`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`. -/
def HasConditionalCollisionBound {X Y₁ Y₂ R₂ Γ₂ : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₂] [DecidableEq R₂]
    [Fintype Γ₂]
    (D : Distribution ((X × Y₁) × Y₂)) (eval₂ : Γ₂ → Y₂ → R₂)
    (η : ℝ) : Prop :=
  ∀ x y₁, 0 < (D.map Prod.fst).weight (x, y₁) →
    ∀ g g' : Γ₂, g ≠ g' →
      (∑ y₂ : Y₂, D.weight ((x, y₁), y₂) *
        if eval₂ g y₂ = eval₂ g' y₂ then 1 else 0) ≤
        η * (D.map Prod.fst).weight (x, y₁)

/-! ### Tensor placements of measurements

The operator families compared in `lem:pasting` are placed on one factor of a
bipartite space. The two constructions below present such a placed family as a
measurement, so that the consistency calculus applies to it verbatim. -/

variable {α ιA ιB : Type*} [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]

/-- An alias of `DistanceCalculus.leftPlacedMeasurement`, whose effects are the
left tensor placements of the effects of `M`. Formalization support for `lem:pasting`, blueprint
`ch12_qpbt_games.tex:960-990`. -/
noncomputable def Measurement.leftPlacement (M : Measurement α ιA) : Measurement α (ιA × ιB) :=
  DistanceCalculus.leftPlacedMeasurement M

/-- An alias of `DistanceCalculus.rightPlacedMeasurement`, whose effects are the
right tensor placements of the effects of `M`. Formalization support for `lem:pasting`, blueprint
`ch12_qpbt_games.tex:960-990`. -/
noncomputable def Measurement.rightPlacement (M : Measurement α ιB) : Measurement α (ιA × ιB) :=
  DistanceCalculus.rightPlacedMeasurement M

/-- The effects of the left placement. -/
@[simp] theorem Measurement.leftPlacement_effect (M : Measurement α ιA) (a : α) :
    (Measurement.leftPlacement (ιB := ιB) M).effect a = heteroKron (M.effect a) 1 := rfl

/-- The effects of the right placement. -/
@[simp] theorem Measurement.rightPlacement_effect (M : Measurement α ιB) (a : α) :
    (Measurement.rightPlacement (ιA := ιA) M).effect a = heteroKron 1 (M.effect a) := rfl

/-- The left placement of a projective measurement is projective.
Formalization support for `lem:pasting`, blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem Measurement.isProjective_leftPlacement (M : Measurement α ιA) (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.QPBT.Measurement.IsProjective (Measurement.leftPlacement (ιB := ιB) M) := by
  intro a
  constructor
  · show heteroKron (M.effect a) 1 * heteroKron (M.effect a) 1 =
      heteroKron (M.effect a) 1
    rw [heteroKron_mul, (hM a).isIdempotentElem.eq, mul_one]
  · show (heteroKron (M.effect a) (1 : Op ιB))ᴴ = heteroKron (M.effect a) 1
    simp [heteroKron, Matrix.kronecker, Matrix.conjTranspose_kronecker, measurement_effect_hermitian, Matrix.conjTranspose_one]

/-- The right placement of a projective measurement is projective. This is the
right-factor mirror of the preceding lemma and the second of the four
properties of the placement collected in the formalization-support node
`lem:pasting-tensor-placement`, blueprint `ch12_qpbt_games.tex:1063-1071`. -/
theorem Measurement.isProjective_rightPlacement (M : Measurement α ιB) (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.QPBT.Measurement.IsProjective (Measurement.rightPlacement (ιA := ιA) M) := by
  intro a
  constructor
  · show heteroKron (1 : Op ιA) (M.effect a) * heteroKron 1 (M.effect a) =
      heteroKron 1 (M.effect a)
    rw [heteroKron_mul, (hM a).isIdempotentElem.eq, mul_one]
  · show (heteroKron (1 : Op ιA) (M.effect a))ᴴ = heteroKron 1 (M.effect a)
    simp [heteroKron, Matrix.kronecker, Matrix.conjTranspose_kronecker, measurement_effect_hermitian, Matrix.conjTranspose_one]

/-- Postprocessing commutes with the left tensor placement. This is one of the
four properties of the placement collected in the formalization-support node
`lem:pasting-tensor-placement`, blueprint `ch12_qpbt_games.tex:1063-1071`; it
records the compatibility of the placement of `lem:pasting` with the outcome
coarse-grainings its statement applies, and is stated for the left factor
alongside its right-factor mirror below. -/
theorem Measurement.leftPlacement_postprocess {α β ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Measurement α ιA) (f : α → β) (b : β) :
    (Measurement.leftPlacement (ιB := ιB) (M.postprocess f)).effect b =
      ((Measurement.leftPlacement (ιB := ιB) M).postprocess f).effect b := by
  grind [Measurement.leftPlacement_effect, Measurement.postprocess_effect, heteroKron_finset_sum_left]

/-- Postprocessing commutes with the right tensor placement. This is the
right-factor mirror of the preceding compatibility, the fourth of the four
properties of the placement collected in the formalization-support node
`lem:pasting-tensor-placement`, blueprint `ch12_qpbt_games.tex:1063-1071`. -/
theorem Measurement.rightPlacement_postprocess {α β ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Measurement α ιB) (f : α → β) (b : β) :
    (Measurement.rightPlacement (ιA := ιA) (M.postprocess f)).effect b =
      ((Measurement.rightPlacement (ιA := ιA) M).postprocess f).effect b := by
  grind [Measurement.rightPlacement_effect, Measurement.postprocess_effect, heteroKron_finset_sum_right]





end MIPStarRE.QPBT
