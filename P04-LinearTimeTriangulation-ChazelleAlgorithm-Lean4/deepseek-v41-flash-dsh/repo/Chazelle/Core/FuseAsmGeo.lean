module

public import Chazelle.Golf

public import Chazelle.Core.FuseAsmPt
public import Chazelle.Core.SweepQueryL
public import Chazelle.Core.SweepPrimCapRam

/-!
# WP-F fusion assembly, part 9: where the point queries are

* The shared vertex is the walk vertex `6 + tpos C₁ m₁` of `C₁` and `6 + tpos C₂ 0` of `C₂`; the
  next walk vertices are its neighbours `u` (on `C₁`) and `w` (on `C₂`) (`left_next`,
  `right_next`).
* The cap origin is the point of the walk edge leaving the shared vertex towards the far arm, at
  the height code of the nearer neighbour (`capPos_left`, `capPos_right`).
-/

namespace Chazelle.Core

namespace FuseAsm

@[expose] public section

open WalkEmbed
open Chazelle.Chain (sideE)

variable (J : Merge.Junction)

theorem sideE_succ_m {m : ℕ} (hm : 1 ≤ m) : sideE m ((m + 1) % (2 * m)) = m - 1 := by
  unfold sideE
  rcases Nat.lt_or_ge (m + 1) (2 * m) with h | h
  · rw [Nat.mod_eq_of_lt h, ite_eq_right (⋄)]; omega
  · have : m = 1 := ⋄
    subst this; simp

/-- The walk vertex after the shared vertex in the walk of `C₁` is `u`. -/
theorem left_next : (chainModel J.left).W.vtx (6 + tpos J.left J.m₁ + 1) = sharedU J := by
  have hn := cm_n J.left
  have hτ := tpos_lt J.left J.m₁
  have := walk_tour J.left J.m₁ 1 (⋄)
  rw [Nat.mod_eq_of_lt (by rw [hn]; omega)] at this
  Ξ this
  unfold tourV
  ϴ Merge.Junction.left_m
  Ξ sideE_succ_m J.one_le_m₁
  rfl

/-- The walk vertex after the shared vertex in the walk of `C₂` is `w`. -/
theorem right_next : (chainModel J.right).W.vtx (6 + tpos J.right 0 + 1) = sharedW J := by
  have hn := cm_n J.right
  have hτ := tpos_lt J.right 0
  have := walk_tour J.right 0 1 (⋄)
  rw [Nat.mod_eq_of_lt (by rw [hn]; omega)] at this
  Ξ this
  unfold tourV
  ϴ Merge.Junction.right_m, zero_add
  have h1 : 1 % (2 * J.m₂) = 1 := Nat.mod_eq_of_lt (by have := J.one_le_m₂; omega)
  Ξ h1
  have h2 : sideE J.m₂ 1 = 1 := by unfold sideE; rw [ite_eq_left J.one_le_m₂]
  Ξ h2
  unfold sharedW
  Ξ Merge.Junction.whole_vertex_add

/-- The point of a walk position on the edge from `a` to `b` at the height of `h`. -/
theorem pos_edge {M : Model} {Q : Polygon} {e h : ℕ} {a b : Point} (ha : M.W.vtx e = a)
    (hb : M.W.vtx ((e + 1) % M.W.n) = b) (hne : a.2 ≠ b.2) :
    M.pos Q ⟨e, h + 1⟩ = Geometry.lerp a b (((Q.vtx h).2 - a.2) / (b.2 - a.2)) := by
  unfold Model.pos Model.param Model.wa Model.wb
  simp only
  Ξ ha, hb, ite_eq_right hne

end

end FuseAsm

end Chazelle.Core
