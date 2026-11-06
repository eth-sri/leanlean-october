import RequestProject.TruncatedCubePoset


/-! Dimension and coordinate indices of the actual truncated-cell incidence model. -/

namespace FiniteChains.Davis
open RACG
variable {V : Type} [DecidableEq V] {A : CommRel V}

def truncatedCellDimension : TruncatedCell A → ℕ
  | .inl c => c.1.spx.card
  | .inr σ => σ.1.card - 1

/-- Every proper face has strictly smaller dimension, including the new cut faces. -/
theorem truncatedCellDimension_strictMono : StrictMono (truncatedCellDimension (A := A)) := by
  intro c d hcd
  have hle := hcd.le
  have hne := hcd.ne
  cases c with
  | inl c =>
    cases d with
    | inl d =>
      change c.1.spx.card < d.1.spx.card
      by_contra hnot
      have hs :=
        Finset.eq_of_subset_of_card_le hle.1 (by omega)
      exact hne (congrArg Sum.inl (Subtype.ext (QCube.ext' hs hle.2)))
    | inr σ => exact hle.elim
  | inr σ =>
    cases d with
    | inl d =>
      change σ.1.card - 1 < d.1.spx.card
      have hc := Finset.card_le_card hle.1
      grind
    | inr τ =>
      change σ.1.card - 1 < τ.1.card - 1
      have hσ := Finset.card_pos.mpr σ.2.1
      by_contra hnot
      have hs := Finset.eq_of_subset_of_card_le hle (by omega)
      exact hne (congrArg Sum.inr (Subtype.ext hs))

theorem truncatedCellDimension_monotone : Monotone (truncatedCellDimension (A := A)) :=
  truncatedCellDimension_strictMono.monotone

theorem truncatedCell_eq_of_le_of_dimension_eq {c d : TruncatedCell A}
    (hcd : c ≤ d) (hd : truncatedCellDimension c = truncatedCellDimension d) : c = d := by
  by_contra hne
  have hlt := truncatedCellDimension_strictMono (lt_of_le_of_ne hcd hne)
  omega

/-- The same indices as the geometric and oriented collapse routines. -/
def truncatedFaceIndex : TruncatedCell A → Cube V ⊕ Finset V
  | .inl c => .inl (qCubeToCoordinate c.1)
  | .inr σ => .inr σ.1

variable [Fintype V]

theorem truncatedFaceIndex_injective : Function.Injective (truncatedFaceIndex (A := A)) := by
  intro c d he
  cases c with
  | inl c =>
    cases d with
    | inl d =>
      have hcoord := Sum.inl.inj he
      have hcube := qCubeCoordinateEquiv.injective (Subtype.ext hcoord)
      exact congrArg Sum.inl (Subtype.ext hcube)
    | inr σ => cases he
  | inr σ =>
    cases d with
    | inl d => cases he
    | inr τ => exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj he))
