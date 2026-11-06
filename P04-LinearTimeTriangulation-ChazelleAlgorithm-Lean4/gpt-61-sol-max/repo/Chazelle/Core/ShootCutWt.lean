module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ShootCutPiece

/-!
# WP-G, part 3: the weights of the kind-0 pieces of the arc-cutter

A kind-0 piece must weigh at most `1` (`CutterOK`).  The cutter emits the following kind-0
pieces (walk positions `x`, `y` of the walk proper, `n = 2m + 7` walk edges of `chainModel C`):

* a piece inside one walk edge (`wt_within`: the rest of the edge of the start, the part of the
  edge of the end, a single edge, or a whole subarc inside one edge);
* a piece through the **uncounted block** `U` (walk edges `2m + 6, 0, …, 5`: up the slit, the box,
  down the slit): from a position of `U` to the walk vertex `6` (`wt_U_to_six`, weight `0`),
  from the walk vertex `2m + 5` to a position of `U` (`wt_last_to_U`, weight `≤ 1`: the edge
  `2m + 5` is counted), or between two positions of `U` in walk order (`wt_U_U`, weight `0`).
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sideE sideInArc)

namespace ShootCut

/-- **A piece within one walk edge** weighs at most `1`. -/
theorem wt_within (M : Model) {e : ℕ} {a b : ℝ} (hab : a < b) (ha : (e : ℝ) ≤ a)
    (hb : b ≤ e + 1) : M.arcWt a b ≤ 1 :=
  WalkEmbed.arcWt_le_one_of_within M hab ha hb

/-- The key of a position of the walk proper lies in `[edge, edge + 1)`. -/
theorem key_bounds {M : Model} {Q : Polygon} {n : ℕ} {x : WPos} (hx : ProperPos M Q n x) :
    (x.edge : ℝ) ≤ M.key Q x ∧ M.key Q x < x.edge + 1 := by
  unfold Model.key
  ram_grind

section
variable (M : Model) (Q : Polygon) {n : ℕ}
/-- **From a position to the end of its edge** (a walk vertex). -/
theorem wt_to_next {x : WPos} (hx : ProperPos M Q n x) :
    M.arcWt (M.key Q x) ((x.edge + 1 : ℕ) : ℝ) ≤ 1 := by
  have := key_bounds hx
  exact wt_within M (e := x.edge) (by simp_all) this.1 (by simp_all)

/-- **From the start vertex of an edge to a position strictly inside it.** -/
theorem wt_from_start {y : WPos} (hy : ProperPos M Q n y)
    (hpos : 0 < M.param Q y) : M.arcWt (y.edge : ℝ) (M.key Q y) ≤ 1 := by
  have := key_bounds hy
  exact wt_within M (e := y.edge) (by unfold Model.key; linarith) le_rfl this.2.le

/-- **Two positions of one edge, in order.** -/
theorem wt_same {x y : WPos} (hx : ProperPos M Q n x)
    (hy : ProperPos M Q n y) (he : x.edge = y.edge) (hlt : M.key Q x < M.key Q y) :
    M.arcWt (M.key Q x) (M.key Q y) ≤ 1 := by
  have h1 := key_bounds hx
  have h2 := key_bounds hy
  rw [← he] at h2
  exact wt_within M (e := x.edge) hlt h1.1 h2.2.le

/-! ## The uncounted block -/


end

variable (C : Chain)

/-- The walk edge `p` lies in the uncounted block `U` (`2m + 6` or `0 … 5`). -/
def InU (p : ℕ) : Prop := p ≤ 5 ∨ p = 2 * C.m + 6

/-- The weight of a chain model in closed form, for positions of the walk proper. -/
theorem arcWt_chain (Q : Polygon) {n : ℕ} {x y : WPos} (hx : ProperPos (chainModel C) Q n x)
    (hy : ProperPos (chainModel C) Q n y) :
    (chainModel C).arcWt ((chainModel C).key Q x) ((chainModel C).key Q y) =
      arcWtNat 6 (2 * C.m + 6) x.edge ((chainModel C).param Q x) y.edge
        ((chainModel C).param Q y) :=
  (chainModel C).arcWt_key (fun p hp => chainModel_counted_iff C p hp)
    (by grind [chainModel_n]) Q ⟨hx.1, hx.2.1⟩ ⟨hy.1, hy.2.1⟩

section
variable (e : ℕ) (f : ℝ)
theorem keyCeil_le : keyCeil e f ≤ e + 1 := by
  core_grind

theorem le_keyCeil : e ≤ keyCeil e f := by
  core_grind


end

/-- The vertex position `⟨p, 0⟩` is proper. -/
theorem proper_vtx (M : Model) (Q : Polygon) (n p : ℕ) : ProperPos M Q n ⟨p, 0⟩ :=
  ⟨le_rfl, by simp, Nat.zero_le _⟩

section
variable (Q : Polygon) {n : ℕ}
/-- **From a position of `U` to the walk vertex `6`**: weight `0`. -/
theorem wt_U_to_six {x : WPos} (hx : ProperPos (chainModel C) Q n x)
    (hU : InU C x.edge) :
    (chainModel C).arcWt ((chainModel C).key Q x) (6 : ℕ) = 0 := by
  have e6 : ((6 : ℕ) : ℝ) = (chainModel C).key Q ⟨6, 0⟩ := by simp
  rw [e6, arcWt_chain C Q hx (proper_vtx _ Q n 6)]
  
  
  have hk : keyCeil 6 ((chainModel C).param Q ⟨6, 0⟩) = 6 := by
    simp_all [keyCeil] <;> omega_nf
  unfold arcWtNat
  rw [hk]
  split_ifs with h
  · omega
  · rcases hU with hU | hU
    · exfalso
      apply h
      have : (x.edge : ℝ) + 1 ≤ 6 := by exact_mod_cast (by omega : x.edge + 1 ≤ 6)
      simp only [param_hgt0, add_zero]
      push_cast
      linarith [hx.2.1]
    omega

/-- **From the walk vertex `2m + 5` to a position of `U`**: weight at most `1`. -/
theorem wt_last_to_U {y : WPos} (hy : ProperPos (chainModel C) Q n y)
    (hU : InU C y.edge) :
    (chainModel C).arcWt ((2 * C.m + 5 : ℕ) : ℝ) ((chainModel C).key Q y) ≤ 1 := by
  have e5 : ((2 * C.m + 5 : ℕ) : ℝ) = (chainModel C).key Q ⟨2 * C.m + 5, 0⟩ := by simp
  rw [e5, arcWt_chain C Q (proper_vtx _ Q n _) hy]
  have hc := le_keyCeil y.edge ((chainModel C).param Q y)
  have hc' := keyCeil_le y.edge ((chainModel C).param Q y)
  have hm := C.one_le
  unfold arcWtNat
  dsimp only
  split_ifs with h
  · omega
  · rcases hU with hU | hU
    · omega
    · exfalso
      apply h
      simp only [param_hgt0, add_zero]
      rw [hU]
      push_cast
      linarith [hy.1]


end

/-- The order of the uncounted block: `2m + 6` first, then `0, …, 5`. -/
def uIdx (p : ℕ) : ℕ := if p = 2 * C.m + 6 then 0 else p + 1

/-- **Two positions of `U` in walk order** (on different edges, the second later in `U`):
weight `0`. -/
theorem wt_U_U (Q : Polygon) {n : ℕ} {x y : WPos} (hx : ProperPos (chainModel C) Q n x)
    (hy : ProperPos (chainModel C) Q n y) (hxU : InU C x.edge) (hyU : InU C y.edge)
    (hlt : uIdx C x.edge < uIdx C y.edge) :
    (chainModel C).arcWt ((chainModel C).key Q x) ((chainModel C).key Q y) = 0 := by
  rw [arcWt_chain C Q hx hy]
  
  have hc' := keyCeil_le y.edge ((chainModel C).param Q y)
  have hm := C.one_le
  have hx1 := hx.2.1
  have hy0 := hy.1
  unfold uIdx at hlt
  unfold arcWtNat
  rcases hxU with hxU | hxU <;> rcases hyU with hyU | hyU
  · rw [ite_eq_right (by omega : x.edge ≠ 2 * C.m + 6), ite_eq_right (by omega : y.edge ≠ 2 * C.m + 6)] at hlt
    have : (x.edge : ℝ) + 1 ≤ y.edge := by exact_mod_cast (by omega : x.edge + 1 ≤ y.edge)
    grind
  all_goals grind

end ShootCut

end

end Chazelle.Core
