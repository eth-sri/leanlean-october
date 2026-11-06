module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvStopRC
public import Chazelle.Core.RestoreTShot

/-!
# The sweep (WP-D), stage 2: mathematics for the per-origin step (part 4)

* `h6_of_abs`: a position strictly inside the height band at height code `0` is a tour position;
* `onCB_not_dom_left/right`: points of `C₁`, `C₂` or of the box are off the domain of `C`;
* `far_free`: the far end of a chord sees the origin back;
* `win_only2`, `win_min`: the first hit of `C` from the candidates of `C₁` and `C₂`;
* `right_v_pos`, `right_top_pos`, `top_not_left`: the origins of the shared and top codes in the
  walk of `C₂`;
* `parent_key_iff`: the parent of a shared or top chord from the keys of the walk of `C₂`.
-/

namespace Chazelle.Core

open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)
open WalkEmbed

@[expose] public section

namespace SweepStop

open Sweep SweepEv SweepIo

variable {J : Merge.Junction}

/-- **Height code `0` strictly inside the height band** is a tour position. -/
theorem h6_of_abs (C : Chain) (Q : Polygon) {x : WPos}
    (hy : |((chainModel C).pos Q x).2| < C.radius) (h0 : x.hgt = 0) : 6 ≤ x.edge := by
  obtain ⟨e, h⟩ := x
  simp only at h0
  subst h0
  by_contra hlt
  push Not at hlt
  have hv : (chainModel C).pos Q ⟨e, 0⟩ = (chainModel C).W.vtx e := by
    show sidePt _ e ((chainModel C).param Q ⟨e, 0⟩) = _
    simp_all [Chazelle.Chain.sidePt_zero] 
  rw [hv, Restore.chain_box_vtx_abs C hlt] at hy
  simp_all

/-- Points of `C₁` or of the box are off the domain of `C`. -/
theorem onCB_not_dom_left {z : Point} (h : OnCB J.left z) : z ∉ J.whole.dom := by
  intro hd
  have hb := J.whole.dom_subset_box hd
  rcases h with h | h | h
  · exact J.whole.not_mem_set_of_mem_dom hd (J.left_set_subset h)
  · have := hb.1; rw [h] at this; exact lt_irrefl _ this
  · have := hb.2; rw [h] at this; exact lt_irrefl _ this

/-- Points of `C₂` or of the box are off the domain of `C`. -/
theorem onCB_not_dom_right {z : Point} (h : OnCB J.right z) : z ∉ J.whole.dom := by
  intro hd
  have hb := J.whole.dom_subset_box hd
  rcases h with h | h | h
  · exact J.whole.not_mem_set_of_mem_dom hd (J.right_set_subset h)
  · have := hb.1; rw [h] at this; exact lt_irrefl _ this
  · have := hb.2; rw [h] at this; exact lt_irrefl _ this

/-- **The far end sees the origin back.** -/
theorem far_free (C : Chain) {a : Point} (ha : a.2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hf : FreeAt C a σ) : FreeAt C (farPt C a σ) (-σ) := by
  obtain ⟨hT, -, hin⟩ := Merge.hit_of_freeAt C ha hσ hf
  show ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (farPt C a σ) (-σ) s ∈ C.dom
  filter_upwards [Ioo_mem_nhdsGT hT] with s hs
  simp_all [farPt, Sweep.rayPt_back] 

section
variable {a : Point} (ha : a.2 ≤ J.right.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hf : FreeAt J.whole a σ)
include ha hσ hf
/-- **Only the candidate of `C₂`**: without a first hit of `C₁` it is the first hit of `C`. -/
theorem win_only2 (hno : ¬ (FreeAt J.left a σ ∧ a.2 ≤ J.left.top.2)) {τ₂ : ℝ}
    (h2 : τ₂ = J.right.hitParam a σ) : τ₂ = J.whole.hitParam a σ := by
  rcases hit_cases ha hσ with h | ⟨h1, h⟩
  · rw [h, h2]
  · exact absurd ⟨free_left hf h1, h1⟩ hno

/-- **The nearer candidate** is the first hit of `C`. -/
theorem win_min {τ₁ τ₂ τ : ℝ} (h1 : 0 < τ₁) (h1o : OnCB J.left (rayPt a σ τ₁))
    (h1g : FreeAt J.left a σ ∧ a.2 ≤ J.left.top.2 → τ₁ = J.left.hitParam a σ)
    (h2 : 0 < τ₂) (h2o : OnCB J.right (rayPt a σ τ₂)) (h2g : τ₂ = J.right.hitParam a σ)
    (hτ : τ = τ₁ ∨ τ = τ₂) (hτ1 : τ ≤ τ₁) (hτ2 : τ ≤ τ₂) : τ = J.whole.hitParam a σ := by
  have haW : a.2 ≤ J.whole.top.2 := le_trans ha J.right_top_le
  refine hit_min hσ haW hf (L := {τ₁, τ₂}) ?_ ?_ ?_ ?_
  · intro x hx
    rcases hx with rfl | hx
    · exact ⟨h1, onCB_not_dom_left h1o⟩
    · rw [mem_singleton_iff] at hx; subst hx
      exact ⟨h2, onCB_not_dom_right h2o⟩
  · rcases hit_cases ha hσ with h | ⟨hl, h⟩
    · simp_all
    · rw [h, ← h1g ⟨free_left hf hl, hl⟩]; simp_all
  all_goals simp_all

/-! ## The origins in the walk of `C₂` -/


end

theorem right_v_pos (Q : Polygon) :
    (chainModel J.right).pos Q ⟨6 + tpos J.right 0, 0⟩ = J.shared := by
  show sidePt _ _ ((chainModel J.right).param Q ⟨6 + tpos J.right 0, 0⟩) = _
  rw [show (chainModel J.right).param Q ⟨6 + tpos J.right 0, 0⟩ = 0 from rfl,
    Chazelle.Chain.sidePt_zero, vtx_tpos' J.right (Nat.zero_le _), J.right_vertex_zero]

theorem right_top_pos (Q : Polygon) : (chainModel J.right).pos Q ⟨6, 0⟩ = J.right.top := by
  show sidePt _ _ ((chainModel J.right).param Q ⟨6, 0⟩) = _
  rw [show (chainModel J.right).param Q ⟨6, 0⟩ = 0 from rfl]
  exact (sidePt_top_copies J.right).1

/-- The top of `C₂` is off `C₁` unless it is the shared vertex. -/
theorem top_not_left (hP : J.P.Simple) (ht : J.right.topIdx ≠ 0) : J.right.top ∉ J.left.set :=
  J.right_vertex_not_mem_left hP (Nat.pos_of_ne_zero ht) J.right.topIdx_le

/-! ## The parent of a shared or top chord -/

section
variable {P : Polygon} {N : NF} (hN : IsNF (chainModel J.right) (Qof P) N)
include hN
/-- The point of the end `1 - b` of a chord record. -/
theorem endPos_pt {i b : ℕ}
    (hi : i < N.nChords) (hb : b ≤ 1) :
    (chainModel J.right).pos (Qof P) (endPos N i (1 - b)) =
      (if b = 1 then Merge.lend ((N.chord i).toSet (chainModel J.right) (Qof P))
        else Merge.rend ((N.chord i).toSet (chainModel J.right) (Qof P))) := by
  have hj : 2 * i + (1 - b) < 2 * N.nChords := by omega
  obtain ⟨hEO, -⟩ := endOrigin_eq J hN hj
  grind [endOrigin]

/-- The attachment of a chord record at its end. -/
theorem endPos_attach {i : ℕ}
    (hi : i < N.nChords) (s : ℕ) :
    SideAttach (chainModel J.right).W ((N.chord i).toSet (chainModel J.right) (Qof P))
      (endPos N i s).edge ((chainModel J.right).param (Qof P) (endPos N i s)) := by
  have hA := hN.2.2.1 i hi
  unfold endPos; split_ifs
  · exact hA.1
  · exact hA.2


end

/-- **The parent of a shared or top chord**: the chord record `i` contains the chord of `a` in the
direction of code `b` iff its end `1 - b` has the key of the arrival position of `a` in the walk
of `C₂`. -/
theorem parent_key_iff (hP : J.P.Simple) {P : Polygon} {N : NF}
    (hN : IsNF (chainModel J.right) (Qof P) N) {a : Point} (haR : a ∈ J.right.set) {b : ℕ}
    (hb : b ≤ 1) (hf : FreeAt J.whole a (dirOf b)) {p h : ℕ}
    (hA : Arrival (chainModel J.right).W a (-dirOf b) p ((chainModel J.right).param (Qof P) ⟨p, h⟩))
    {i : ℕ} (hi : i < N.nChords) :
    (chainModel J.right).key (Qof P) (endPos N i (1 - b)) =
        (chainModel J.right).key (Qof P) ⟨p, h⟩ ↔
      Merge.shoot J.whole a (dirOf b) ⊆ (N.chord i).toSet (chainModel J.right) (Qof P) := by
  have hS₂ := hN.1.2.1
  have hc := chord_mem (M := chainModel J.right) (Q := Qof P) hi
  have hAt := endPos_attach hN hi (1 - b)
  have hpt := endPos_pt hN hi hb
  have hσ := dirOf_cases' b
  have hiff := parent_vt_iff hP hS₂ haR hb hf hc
  set c := (N.chord i).toSet (chainModel J.right) (Qof P) with hcdef
  unfold Model.key
  constructor
  · intro hk
    obtain ⟨he, ht⟩ := Chazelle.Chain.sideKey_inj hAt.2.1 hAt.2.2.1 hA.2.1 hA.2.2.1 hk
    have hpa : (chainModel J.right).pos (Qof P) (endPos N i (1 - b)) = a := by
      show sidePt _ _ _ = _
      rw [he, ht]; exact hA.2.2.2.1
    grind
  · intro hsub
    have hend := hiff.1 hsub
    -- the chord is the chord of `C₂` seen from `a`
    obtain ⟨y, l, r, hH, -, heq, hl, hr⟩ := Merge.augChords_spec (hS₂ hc)
    have hcs : c = Merge.shoot J.right a (dirOf b) := by
      rcases hend with ⟨rfl, h⟩ | ⟨rfl, h⟩
      · rw [dirOf_one, ← h, hl, heq]; exact Merge.hseg_eq_shoot J.right hH
      · rw [dirOf_zero, ← h, hr, heq]; exact Merge.hseg_eq_shoot_neg J.right hH
    have haD : a ∉ J.right.dom := fun hd => J.right.not_mem_set_of_mem_dom hd haR
    have hay := J.right.snd_le_top_of_mem_set haR
    have hfR := free_right hf hay
    have hA' := attach_of_origin (C := J.right) hP hay haD hσ hfR hA
    rw [← hcs] at hA'
    have hM : WalkAx (chainModel J.right) := FactsChain.walkAx J.right hP
    have hpa : sidePt (chainModel J.right).W (endPos N i (1 - b)).edge
        ((chainModel J.right).param (Qof P) (endPos N i (1 - b))) = a := by
      show (chainModel J.right).pos (Qof P) (endPos N i (1 - b)) = a
      grind
    obtain ⟨e1, e2⟩ := hM.attach_unique (hS₂ hc) hAt hA' (by rw [hpa, hA.2.2.2.1])
    rw [e1, e2]

end SweepStop

end

end Chazelle.Core
