module

public import GradedNear.Defs

@[expose] public section

namespace GradedNear.Cert

-- The checker and the LP use the same defaults for missing row data.
scoped notation "rowAt " L:max k:max => List.getD (Leaf.rows L) k ⟨1, []⟩
scoped notation "featureAt " c:max k:max => List.getD (α := ℤ) (Col.v c) k 0
scoped notation "diagAt " c:max k:max => List.getD (α := ℤ) (Col.D c) k 1
scoped notation "familyAt " L:max k:max i:max => List.get (RowHead.fam (rowAt L k)) i
scoped notation "unscaled " z:max => (((z : ℤ) : ℝ) / S)

lemma S_pos : (0 : ℝ) < S := by norm_num [S]

lemma unscaled_nonneg {z : ℤ} (h : 0 ≤ z) : 0 ≤ unscaled z :=
  div_nonneg (by exact_mod_cast h) S_pos.le

end GradedNear.Cert
