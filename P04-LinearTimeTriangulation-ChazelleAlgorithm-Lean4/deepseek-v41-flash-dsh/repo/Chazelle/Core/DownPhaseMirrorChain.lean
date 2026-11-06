module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseMirrorModel

/-!
# Mirror symmetry (F-D7), part 6: mirrored chains and their chain models

`Chain.mir C`: the chain of the mirrored polygon `C.P.mir` with the same start edge and length.
Heights are preserved, so the least-index top vertex is the same (`topIdx_mir`); the box, the
slit and the domain are mirrored (`dom_mir`).  The corrected boundary walk of `C.mir` is the
mirror image of that of `C`, traversed backwards with shift `5` (`walkMir_sideWalk`): the box
block is traversed backwards and the tour of the double boundary is reversed, which flips the
turn `β` at the top vertex; and indeed `C.mir.sideBeta = !C.sideBeta` at an inner top vertex
(`sideBeta_mir`, from the asymmetry and coverage of the arcs of directions), while at an end top
vertex the turn does not matter.  Hence `chainModel C.mir` is the mirrored chain model
(`modelMir_chain`).
-/

namespace Chazelle.Core

namespace Mir

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (IsHChordIn sideCcw sideE)
open Chazelle.Visibility (hseg rayPt)

/-- **The mirrored chain.** -/
def _root_.Chazelle.Chain.mir (C : Chain) : Chain where
  P := C.P.mir
  s := C.s
  m := C.m
  one_le := C.one_le
  add_one_le := by rw [mir_n]; exact C.add_one_le

variable (C : Chain)

@[simp] theorem chainMir_P : C.mir.P = C.P.mir := rfl
@[simp] theorem chainMir_m : C.mir.m = C.m := rfl

theorem edgeIdx_mir (k : ℕ) : C.mir.edgeIdx k = C.edgeIdx k := by
  show (C.s + k) % C.P.mir.n = (C.s + k) % C.P.n
  Ξ mir_n

theorem vertex_mir (k : ℕ) : C.mir.vertex k = mir (C.vertex k) := by
  show C.P.mir.vtx (C.mir.edgeIdx k) = _
  rw [edgeIdx_mir, mir_vtx]; rfl

theorem set_mir : C.mir.set = mir '' C.set := by
  ext x
  Ξ mem_image_mir
  show (∃ k, k < C.m ∧ x ∈ C.mir.chainEdge k) ↔ ∃ k, k < C.m ∧ mir x ∈ C.chainEdge k
  ϴ Chazelle.Chain.chainEdge_eq, vertex_mir, ← mir_segment, mem_image_mir

theorem topIdx_mir : C.mir.topIdx = C.topIdx := by
  apply le_antisymm
  · refine C.mir.topIdx_min C.topIdx_le fun i hi => ?_
    Ξ vertex_mir, vertex_mir, mir_snd, mir_snd
    exact C.topIdx_spec.2 i hi
  · refine C.topIdx_min C.mir.topIdx_le fun i hi => ?_
    have := C.mir.topIdx_spec.2 i hi
    rwa [vertex_mir, vertex_mir, mir_snd, mir_snd] at this

theorem top_mir : C.mir.top = mir C.top := by
  show C.mir.vertex C.mir.topIdx = _
  rw [topIdx_mir, vertex_mir]; rfl

theorem coordBound_mir (P : Polygon) : Chazelle.Jordan.coordBound P.mir =
    Chazelle.Jordan.coordBound P := by
  unfold Chazelle.Jordan.coordBound
  Ξ mir_n
  refine Finset.sum_congr rfl fun i _ => ?_
  Ξ mir_vtx, mir_fst, mir_snd, abs_neg

theorem radius_mir : C.mir.radius = C.radius := by
  unfold Chazelle.Chain.radius; rw [chainMir_P, coordBound_mir]

theorem slitTop_mir : C.mir.slitTop = mir C.slitTop := by
  unfold Chazelle.Chain.slitTop; rw [top_mir, radius_mir]; rfl

theorem slit_mir : C.mir.slit = mir '' C.slit := by
  unfold Chazelle.Chain.slit; rw [top_mir, slitTop_mir, mir_segment]

theorem box_mir (r : ℝ) : mir '' Chazelle.Chain.box r = Chazelle.Chain.box r := by
  ext x
  Ξ mem_image_mir
  ϴ Chazelle.Chain.mem_box_iff, mir_fst, mir_snd, abs_neg

/-- **The domain of the mirrored chain.** -/
theorem dom_mir : C.mir.dom = mir '' C.dom := by
  unfold Chazelle.Chain.dom Chazelle.Chain.obstacle
  Ξ set_mir, slit_mir, radius_mir, ← image_union, image_sdiff mir_injective, box_mir

theorem sideTour_mir (β : Bool) (i : ℕ) : C.mir.sideTour β i = mir (C.sideTour β i) := by
  unfold Chazelle.Chain.sideTour Chazelle.Chain.sideIdx Chazelle.Chain.sideS
  rw [topIdx_mir, vertex_mir]; rfl

/-- The Euler tour index is symmetric. -/
theorem sideE_sym {m : ℕ} (hm : 0 < m) {x y : ℕ} (h : (x + y) % (2 * m) = 0) :
    sideE m (x % (2 * m)) = sideE m (y % (2 * m)) := by
  have hX := Nat.mod_lt x (show 0 < 2 * m by omega)
  have hY := Nat.mod_lt y (show 0 < 2 * m by omega)
  have h' : (x % (2 * m) + y % (2 * m)) % (2 * m) = 0 := by rw [← Nat.add_mod]; exact h
  have hs : x % (2 * m) + y % (2 * m) = 0 ∨ x % (2 * m) + y % (2 * m) = 2 * m := by
    by_cases hlt : x % (2 * m) + y % (2 * m) < 2 * m
    · rw [Nat.mod_eq_of_lt hlt] at h'; exact Or.inl h'
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h'
      right; omega
  unfold sideE
  split_ifs <;> omega

/-- **Reversing the tour flips the turn.** -/
theorem sideTour_not (β : Bool) {i : ℕ} (hi : i ≤ 2 * C.m) :
    C.sideTour (!β) i = C.sideTour β (2 * C.m - i) := by
  unfold Chazelle.Chain.sideTour Chazelle.Chain.sideIdx
  congr 1
  apply sideE_sym C.one_le
  have hT := C.topIdx_le
  rw [show C.sideS (!β) + i + (C.sideS β + (2 * C.m - i)) = 2 * C.m * 2 by
    unfold Chazelle.Chain.sideS; cases β <;> simp <;> omega]
  exact Nat.mul_mod_right _ _

/-- At an end top vertex, the turn does not matter. -/
theorem sideWalk_indep (hT : C.topIdx = 0 ∨ C.topIdx = C.m) (β β' : Bool) :
    C.sideWalk β = C.sideWalk β' := by
  have key : ∀ i, C.sideTour true i = C.sideTour false i := fun i => by
    unfold Chazelle.Chain.sideTour Chazelle.Chain.sideIdx Chazelle.Chain.sideS
    simp only [ite_true, Bool.false_eq_true, ite_false]
    rcases hT with h | h
    · rw [h, show 2 * C.m - 0 + i = i + 2 * C.m * 1 by omega, Nat.add_mul_mod_self_left,
        zero_add]
    · rw [h, show 2 * C.m - C.m = C.m by omega]
  have hf : C.sideTour β = C.sideTour β' := by
    funext i
    cases β <;> cases β' <;> simp [key]
  unfold Chazelle.Chain.sideWalk
  rw [hf]

/-- **The walk of the mirrored chain with the flipped turn is the mirrored walk, reversed.** -/
theorem walkMir_sideWalk_not (β : Bool) :
    WalkMir (C.sideWalk β) (C.mir.sideWalk (!β)) 5 := by
  have hn := C.sideWalk_n β
  have hn' := C.mir.sideWalk_n (!β)
  refine ⟨by rw [hn, hn']; rfl, by rw [hn]; omega, fun j hj => ?_⟩
  rw [hn] at hj ⊢
  rcases Nat.lt_or_ge j 6 with hj6 | hj6
  · rw [show 5 + (2 * C.m + 7) - j = (5 - j) + (2 * C.m + 7) * 1 by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    interval_cases j
    · show C.mir.slitTop = mir C.slitTop; exact slitTop_mir C
    · show ((-C.mir.radius, C.mir.radius) : Point) = mir (C.radius, C.radius)
      rw [radius_mir]; rfl
    · show ((-C.mir.radius, -C.mir.radius) : Point) = mir (C.radius, -C.radius)
      rw [radius_mir]; rfl
    · show ((C.mir.radius, -C.mir.radius) : Point) = mir (-C.radius, -C.radius)
      rw [radius_mir, mir_pt, neg_neg]
    · show ((C.mir.radius, C.mir.radius) : Point) = mir (-C.radius, C.radius)
      rw [radius_mir, mir_pt, neg_neg]
    · show C.mir.slitTop = mir C.slitTop; exact slitTop_mir C
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 6 := ⟨j - 6, by omega⟩
    rw [show (5 + (2 * C.m + 7) - (i + 6)) % (2 * C.m + 7) = (2 * C.m - i) + 6 by
      rw [Nat.mod_eq_of_lt (by omega)]; omega]
    rw [C.mir.sideWalk_vtx_tour _ (show i ≤ 2 * C.mir.m by simp; omega),
      C.sideWalk_vtx_tour _ (by omega), sideTour_mir, sideTour_not _ _ (by omega)]

/-- **The turn of the mirrored chain is flipped** (inner top vertex). -/
theorem sideBeta_mir (hP : C.P.Simple) (h0 : 0 < C.topIdx) (hm : C.topIdx < C.m) :
    C.mir.sideBeta = !C.sideBeta := by
  set T := C.topIdx with hT
  set A := C.vertex (T + 1) - C.top
  set B := C.vertex (T - 1) - C.top
  set X := C.slitTop - C.top
  have hA : A ≠ 0 := C.sideVertex_sub_top_ne hP (k := T + 1) (⋄) (by omega)
  have hB : B ≠ 0 := C.sideVertex_sub_top_ne hP (k := T - 1) (⋄) (by omega)
  have hns := C.sideChain_nonSpike hP h0 hm
  have hor : sideCcw A X B ∨ sideCcw B X A := Chazelle.Chain.sideCcw_or hA hB hns.1
    (C.sideUp_not_ray _ (⋄) hA) (C.sideUp_not_ray _ (by omega) hB)
  have hβ := C.sideBeta_eq_true_iff
  have e : C.mir.sideBeta = true ↔ sideCcw B X A := by
    rw [Chazelle.Chain.sideBeta_eq_true_iff, topIdx_mir, vertex_mir, vertex_mir, top_mir,
      slitTop_mir, mir_sub, mir_sub, mir_sub, sideCcw_mir]
  cases hb : C.sideBeta
  · show C.mir.sideBeta = true
    Ξ e
    refine hor.resolve_left fun h => ?_
    have := hβ.2 h
    rw [hb] at this
    exact Bool.false_ne_true this
  · show C.mir.sideBeta = false
    Ξ ← Bool.not_eq_true, e
    exact Chazelle.Chain.sideCcw_asymm hA hns.1 (hβ.1 hb)

/-- **The corrected walk of the mirrored chain is the mirrored walk, reversed.** -/
theorem walkMir_sideWalk (hP : C.P.Simple) :
    WalkMir (C.sideWalk C.sideBeta) (C.mir.sideWalk C.mir.sideBeta) 5 := by
  by_cases hT : C.topIdx = 0 ∨ C.topIdx = C.m
  · have hT' : C.mir.topIdx = 0 ∨ C.mir.topIdx = C.mir.m := by rw [topIdx_mir]; exact hT
    Ξ sideWalk_indep C.mir hT' C.mir.sideBeta (!C.sideBeta)
    exact walkMir_sideWalk_not C _
  · push Not at hT
    Ξ sideBeta_mir C hP (Nat.pos_of_ne_zero hT.1) (lt_of_le_of_ne C.topIdx_le hT.2)
    exact walkMir_sideWalk_not C _

/-! ### Chords -/

theorem hitSet_chain_mir (v : Point) (σ : ℝ) : C.mir.hitSet (mir v) (-σ) = C.hitSet v σ := by
  ext t
  simp only [Chazelle.Chain.hitSet, mem_ofPred_eq, ← mir_rayPt, dom_mir, mem_compl_iff,
    mem_image_mir, mir_mir]

theorem chordSet_chain_mir (k : ℕ) (σ : ℝ) :
    C.mir.chordSet k (-σ) = mir '' C.chordSet k σ := by
  unfold Chazelle.Chain.chordSet Chazelle.Chain.chordEnd Chazelle.Chain.chordParam
    Chazelle.Chain.hitParam
  Ξ vertex_mir, hitSet_chain_mir, mir_segment, mir_rayPt

theorem dirFree_mir (k : ℕ) (σ : ℝ) : C.mir.DirFree k (-σ) ↔ C.DirFree k σ := by
  unfold Chazelle.Chain.DirFree
  ϴ vertex_mir, ← mir_rayPt, dom_mir, mem_image_mir, mir_mir

/-- **The vertex chords of the mirrored chain.** -/
theorem chords_chain_mir : C.mir.chords = mirF C.chords := by
  ext c
  Ξ mem_mirF
  constructor
  · rintro ⟨k, σ, hk, hσ, hD, rfl⟩
    refine ⟨k, -σ, hk, by rcases hσ with rfl | rfl <;> norm_num, ?_, ?_⟩
    · rw [← dirFree_mir, neg_neg]; exact hD
    · Ξ ← neg_neg σ, chordSet_chain_mir, image_mir_image_mir, neg_neg
  · rintro ⟨k, σ, hk, hσ, hD, hc⟩
    refine ⟨k, -σ, hk, by rcases hσ with rfl | rfl <;> norm_num, (dirFree_mir C k σ).2 hD, ?_⟩
    Ξ chordSet_chain_mir, ← hc, image_mir_image_mir

/-- **The augmented chords of the mirrored chain.** -/
theorem augChords_mir : Merge.augChords C.mir = mirF (Merge.augChords C) := by
  have ht : C.mir.top.2 = C.top.2 := Ρ top_mir, mir_snd
  ext c
  Ξ mem_mirF
  unfold Merge.augChords
  ϴ mem_ofPred_eq
  Ξ dom_mir, ht
  constructor
  · rintro ⟨y, a, b, hch, hy, rfl⟩
    refine ⟨y, -b, -a, ?_, hy, hseg_mir y a b⟩
    rw [← isHChordIn_mir, neg_neg, neg_neg]; exact hch
  · rintro ⟨y, a, b, hch, hy, hc⟩
    refine ⟨y, -b, -a, isHChordIn_mir.2 hch, hy, ?_⟩
    Ξ ← hseg_mir, ← hc, image_mir_image_mir

/-- **The chain model of the mirrored chain is the mirrored chain model**, walk reversed with
shift `5`. -/
theorem modelMir_chain (hP : C.P.Simple) : ModelMir (chainModel C) (chainModel C.mir) 5 where
  D := dom_mir C
  walk := walkMir_sideWalk C hP
  counted p hp := by
    have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
    rw [hn] at hp ⊢
    rw [idx_q (⋄) hp]
    show (6 ≤ p ∧ p < 2 * C.m + 6) ↔ (6 ≤ _ ∧ _ < 2 * C.m + 6)
    split_ifs <;> omega
  Adm := augChords_mir C
  Full := chords_chain_mir C

end

end Mir

end Chazelle.Core
