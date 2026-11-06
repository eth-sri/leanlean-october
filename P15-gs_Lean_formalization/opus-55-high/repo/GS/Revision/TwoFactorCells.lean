module

public import GS.Core
public import Mathlib.Tactic.Choose

@[expose] public section


/-!
# Independent local factorization witnesses and global two-factor gluing

The permutation is absorbed into the two label maps on the intermediate slots.
An intermediate slot belongs to precisely one output block. This file proves
both directions of independent gluing for arbitrary finite index types.

The local characterization here uses a bounded number of outer-product
summands. `GS.Results.CellRank` proves its equivalence with the numerical
criterion `Matrix.rank ≤ card(cell)`, using an actual rank factorization.
No manifold theorem is claimed by this algebraic gluing result.

This module is included in the full build and axiom audit.
-/
noncomputable section
namespace GS.Revision.Cells

variable {α β ι κ τ : Type*}
variable [Fintype τ] [DecidableEq α] [DecidableEq β]

/-- Global row/column coordinates are pairs: block label, local coordinate.
Different local sizes can be embedded by zero padding; this theorem itself
uses a common row type ι and common column type κ. -/
def LeftSupport (left : τ → α) (L : Matrix (α × ι) τ ℝ) : Prop :=
  ∀ a i t, a ≠ left t → L (a, i) t = 0

def RightSupport (right : τ → β) (R : Matrix τ (β × κ) ℝ) : Prop :=
  ∀ t b j, b ≠ right t → R t (b, j) = 0

section
variable (left : τ → α) (right : τ → β)
def cellSum (a : α) (b : β)
    (U : Matrix ι τ ℝ) (V : Matrix τ κ ℝ) : Matrix ι κ ℝ :=
  fun i j => ∑ t, if a = left t ∧ b = right t then U i t * V t j else 0

/-- Each output block has its own witnesses; they need not agree between blocks. -/
def IndependentlyFactorable (A : Matrix (α × ι) (β × κ) ℝ) : Prop :=
  ∀ a b, ∃ U : Matrix ι τ ℝ, ∃ V : Matrix τ κ ℝ,
    ∀ i j, A (a, i) (b, j) = cellSum left right a b U V i j

def GloballyFactorable (A : Matrix (α × ι) (β × κ) ℝ) : Prop :=
  ∃ L : Matrix (α × ι) τ ℝ, ∃ R : Matrix τ (β × κ) ℝ,
    LeftSupport left L ∧ RightSupport right R ∧ A = L * R

/-- A genuine set-level characterization, not only a forward rank bound. -/
theorem global_iff_independent (A : Matrix (α × ι) (β × κ) ℝ) :
    GloballyFactorable left right A ↔ IndependentlyFactorable left right A := by
  constructor
  · rintro ⟨L, R, hL, hR, rfl⟩ a b
    refine ⟨(fun i t => L (a, i) t), (fun t j => R t (b, j)), fun i j => Finset.sum_congr rfl fun t _ => ?_⟩
    by_cases a = left t <;> aesop
  · intro h
    classical
    choose U V hUV using h
    refine ⟨fun ai t => if ai.1 = left t then U ai.1 (right t) ai.2 t else 0,
      fun t bj => if bj.1 = right t then V (left t) bj.1 t bj.2 else 0, fun _ _ _ h => by simp [h],
      fun _ _ _ h => by simp [h], ?_⟩
    ext ⟨a, i⟩ ⟨b, j⟩
    rw [hUV]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases hl : a = left t <;> by_cases hr : b = right t <;> simp [hl, hr]

end

end GS.Revision.Cells
