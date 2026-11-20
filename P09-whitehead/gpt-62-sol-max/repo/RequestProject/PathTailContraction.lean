module

public import Mathlib.Topology.Path
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Tactic

@[expose] public section

/-! A square filling obtained by sliding along a single concatenated path.
It extends an arbitrary contraction path at the initial end of an edge. -/

noncomputable section
namespace Path
open scoped unitInterval Topology

variable {X : Type*} [TopologicalSpace X] {a b z : X}

/-- Time runs vertically. At time zero the square is `p`; at time one it
is constant at `z`. Its left side is `q`, and its right side is `p.symm.trans q`. -/
def tailContraction (p : Path a b) (q : Path a z) : C(I × I, X) where
  toFun ts := (p.symm.trans q).extend
    ((1 - (ts.2 : ℝ) + (1 + (ts.2 : ℝ)) * (ts.1 : ℝ)) / 2)
  continuous_toFun := (p.symm.trans q).continuous_extend.comp (by fun_prop)

@[simp] theorem tailContraction_zero (p : Path a b) (q : Path a z) (s : I) :
    tailContraction p q (0, s) = p s := by
  change (p.symm.trans q).extend ((1 - s + (1 + s) * 0) / 2) = p s
  grind

@[simp] theorem tailContraction_one (p : Path a b) (q : Path a z) (s : I) :
    tailContraction p q (1, s) = z := by
  change (p.symm.trans q).extend ((1 - s + (1 + s) * 1) / 2) = z
  simp

@[simp] theorem tailContraction_left (p : Path a b) (q : Path a z) (t : I) :
    tailContraction p q (t, 0) = q t := by
  change (p.symm.trans q).extend ((1 - 0 + (1 + 0) * t) / 2) = q t
  rw [Path.extend_trans_of_half_le _ _ (by linarith [t.property.1])]
  grind

@[simp] theorem tailContraction_right (p : Path a b) (q : Path a z) (t : I) :
    tailContraction p q (t, 1) = (p.symm.trans q) t := by
  change (p.symm.trans q).extend ((1 - 1 + (1 + 1) * t) / 2) = _
  grind

end Path
