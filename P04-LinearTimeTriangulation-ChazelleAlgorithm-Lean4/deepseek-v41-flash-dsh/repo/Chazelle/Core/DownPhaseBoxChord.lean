module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseBoxPos
public import Chazelle.Merge.Augmented

/-!
# WP-M (B3′, part 4): chords of twin chains

For twin chains `C`, `C'` and a chord record whose height and walk positions lie in the fixed
band of the box stretch:

* the walk edges are horizontal, vertical, or between two chain vertices (`edge_kind`);
* the points of band positions correspond (`pos_eq`);
* the chord of the record in the model of `C'` is the stretched chord (`toSet_eq`), and
  admissibility transfers (`augChords_transfer`).
-/

namespace Chazelle.Core

namespace BoxT

@[expose] public section

open Set Chazelle.Chain Chazelle.Visibility

variable {C C' : Chain}

/-! ## The walk of a chain model -/

theorem tour_mem (C : Chain) {j : ℕ} (hj6 : 6 ≤ j) (hj : j ≤ 2 * C.m + 6) :
    (C.sideWalk C.sideBeta).vtx j ∈ C.set := by
  have e : j = (j - 6) + 6 := ⋄
  rw [e, C.sideWalk_vtx_tour _ (⋄)]
  exact C.vertex_mem_set (C.sideIdx_le _ _)

theorem walk_last (C : Chain) : (C.sideWalk C.sideBeta).vtx (2 * C.m + 6) = C.top := by
  have := C.sideWalk_vtx_tour C.sideBeta (i := 2 * C.m) le_rfl
  rwa [C.sideTour_two_m] at this

/-- **The kinds of walk edges**: horizontal, vertical, or between two chain vertices. -/
theorem edge_kind (C : Chain) {p : ℕ} (hp : p < (C.sideWalk C.sideBeta).n) :
    ((C.sideWalk C.sideBeta).vtx p).2 =
        ((C.sideWalk C.sideBeta).vtx ((p + 1) % (C.sideWalk C.sideBeta).n)).2 ∨
      ((C.sideWalk C.sideBeta).vtx p).1 =
        ((C.sideWalk C.sideBeta).vtx ((p + 1) % (C.sideWalk C.sideBeta).n)).1 ∨
      ((C.sideWalk C.sideBeta).vtx p ∈ C.set ∧
        (C.sideWalk C.sideBeta).vtx ((p + 1) % (C.sideWalk C.sideBeta).n) ∈ C.set) := by
  have hn : (C.sideWalk C.sideBeta).n = 2 * C.m + 7 := C.sideWalk_n _
  rw [hn] at hp
  rcases Nat.lt_or_ge p 6 with h6 | h6
  · have hmod : (p + 1) % (C.sideWalk C.sideBeta).n = p + 1 := by
      rw [hn]; exact Nat.mod_eq_of_lt (⋄)
    Ξ hmod
    interval_cases p
    · left; rw [C.sideWalk_vtx_zero, C.sideWalk_vtx_one]; rfl
    · right; left; rw [C.sideWalk_vtx_one, C.sideWalk_vtx_two]
    · left; rw [C.sideWalk_vtx_two, C.sideWalk_vtx_three]
    · right; left; rw [C.sideWalk_vtx_three, C.sideWalk_vtx_four]
    · left; rw [C.sideWalk_vtx_four, C.sideWalk_vtx_five]; rfl
    · right; left; rw [C.sideWalk_vtx_five, C.sideWalk_vtx_six]; rfl
  · rcases Nat.lt_or_ge p (2 * C.m + 6) with h' | h'
    · right; right
      have hmod : (p + 1) % (C.sideWalk C.sideBeta).n = p + 1 := by
        rw [hn]; exact Nat.mod_eq_of_lt (⋄)
      Ξ hmod
      exact ⟨tour_mem C h6 (⋄), tour_mem C (by omega) (by omega)⟩
    · right; left
      have hp' : p = 2 * C.m + 6 := ⋄
      subst hp'
      rw [C.sideWalk_vtx_wrap, walk_last]; rfl

/-! ## Points of band positions -/

/-- Points of a segment between two points of the fixed band stay in it. -/
theorem abs_lerp_le {u v : Point} {c : ℝ} (hu : |u.1| ≤ c ∧ |u.2| ≤ c) (hv : |v.1| ≤ c ∧ |v.2| ≤ c)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |(Geometry.lerp u v t).1| ≤ c ∧ |(Geometry.lerp u v t).2| ≤ c := by
  ϴ Geometry.lerp
  have key : ∀ a b : ℝ, |a| ≤ c → |b| ≤ c → |a + t * (b - a)| ≤ c := by
    intro a b ha hb
    Ξ' abs_le at *
    constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]
  exact ⟨key _ _ hu.1 hv.1, key _ _ hu.2 hv.2⟩

namespace Twin

variable (h : Twin C C')
include h

/-- **Band positions correspond under the stretch.** -/
theorem pos_eq {Q : Polygon} {x : WPos} (hxn : x.edge < (chainModel C).W.n)
    (hx : BandPos C C' Q x) (hm : 0 ≤ (chainModel C).param Q x ∧ (chainModel C).param Q x < 1) :
    (chainModel C').pos Q x = phi C C' ((chainModel C).pos Q x) := by
  unfold Model.pos
  Ξ h.wa_eq, h.wb_eq
  set u := (chainModel C).wa x.edge with hu
  set v := (chainModel C).wb x.edge with hv
  rcases hx with h0 | ⟨k, hk, hy⟩
  · Θ Model.param, h0, Geometry.lerp_zero
  Ξ h.param'_eq hk hy, param_eq _ Q x k hk
  rw [param_eq _ Q x k hk] at hm
  by_cases hh : u.2 = v.2
  · ϴ ← hu, ← hv, hh, ↓reduceIte, Geometry.lerp_zero
  simp only [← hu, ← hv, hh, ↓reduceIte] at hm ⊢
  have hy' := sig_band hy (C := C) (C' := C')
  rcases edge_kind C hxn with hk2 | hk1 | ⟨hua, hvb⟩
  · exact absurd hk2 hh
  · -- a vertical edge
    have hk1' : u.1 = v.1 := hk1
    have hne : v.2 - u.2 ≠ 0 := sub_ne_zero.2 (Ne.symm hh)
    have hne' : (phi C C' v).2 - (phi C C' u).2 ≠ 0 := by
      simp only [phi, stretchPt]; exact sub_ne_zero.2 (fun e => hh (sig_inj.1 e).symm)
    apply Prod.ext
    · ϴ Geometry.lerp, phi, stretchPt, ← hk1', sub_self, mul_zero, add_zero
    · have hne2 : stretch (bnd C C') (kk C C') v.2 - stretch (bnd C C') (kk C C') u.2 ≠ 0 :=
        hne'
      have e1 : u.2 + ratio u.2 v.2 (Q.vtx k).2 * (v.2 - u.2) = (Q.vtx k).2 := by
        unfold ratio; field_simp; ring
      have e2 : stretch (bnd C C') (kk C C') u.2 + ratio (stretch (bnd C C') (kk C C') u.2)
          (stretch (bnd C C') (kk C C') v.2) (stretch (bnd C C') (kk C C') (Q.vtx k).2) *
          (stretch (bnd C C') (kk C C') v.2 - stretch (bnd C C') (kk C C') u.2) =
          stretch (bnd C C') (kk C C') (Q.vtx k).2 := by
        unfold ratio; field_simp; ring
      ϴ Geometry.lerp, phi, stretchPt
      Ξ e1, e2
  · -- an edge between two chain vertices: nothing moves
    have hu' : phi C C' u = u := h.phi_fix hua
    have hv' : phi C C' v = v := h.phi_fix hvb
    Ξ hu', hv'
    have hsu : stretch (bnd C C') (kk C C') u.2 = u.2 := by
      have := congrArg Prod.snd hu'; simpa [phi, stretchPt] using this
    have hsv : stretch (bnd C C') (kk C C') v.2 = v.2 := by
      have := congrArg Prod.snd hv'; simpa [phi, stretchPt] using this
    Ξ hsu, hsv, hy'
    have hb := abs_lerp_le (u := u) (v := v) (h.abs_le_of_mem hua) (h.abs_le_of_mem hvb) hm.1
      hm.2.le
    exact (stretchPt_of_le bnd_nonneg (by linarith [hb.1]) (by linarith [hb.2])).symm

/-! ## Chords -/

omit h in
/-- The stretch of a horizontal segment at a band height. -/
theorem image_hseg {y a b : ℝ} (hy : |y| < bnd C C') :
    phi C C' '' hseg y a b = hseg y (stretch (bnd C C') (kk C C') a)
      (stretch (bnd C C') (kk C C') b) := by
  have hy' := sig_band hy (C := C) (C' := C')
  ext z
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, rfl⟩
    refine ⟨?_, sig_le_iff.2 hw2, sig_le_iff.2 hw3⟩
    simp only [phi, stretchPt]; rw [hw1, hy']
  · rintro ⟨hz1, hz2, hz3⟩
    set w : Point := (stretch (bnd C C') (kk C C')⁻¹ z.1, y)
    have hinv : stretch (bnd C C') (kk C C') (stretch (bnd C C') (kk C C')⁻¹ z.1) = z.1 := by
      have := stretch_inv (B := bnd C C') (k := (kk C C')⁻¹) bnd_nonneg
        (inv_pos.2 kk_pos) z.1
      rwa [inv_inv] at this
    refine ⟨w, ⟨rfl, ?_, ?_⟩, ?_⟩
    · rw [← sig_le_iff (C := C) (C' := C')]; simp only [w]; rw [hinv]; exact hz2
    · rw [← sig_le_iff (C := C) (C' := C')]; simp only [w]; rw [hinv]; exact hz3
    · apply Prod.ext
      · simp only [phi, stretchPt, w]; exact hinv
      · simp only [phi, stretchPt, w]; rw [hy', hz1]

/-- **The chord of a band record in the model of `C'` is the stretched chord.** -/
theorem toSet_eq {Q : Polygon} {r : CRec} (hy : |(Q.vtx r.h).2| < bnd C C')
    (hl : r.lp < (chainModel C).W.n) (hr : r.rp < (chainModel C).W.n)
    (hml : 0 ≤ (chainModel C).param Q r.lpos ∧ (chainModel C).param Q r.lpos < 1)
    (hmr : 0 ≤ (chainModel C).param Q r.rpos ∧ (chainModel C).param Q r.rpos < 1) :
    r.toSet (chainModel C') Q = phi C C' '' r.toSet (chainModel C) Q := by
  have hbl : BandPos C C' Q r.lpos := Or.inr ⟨r.h, rfl, hy⟩
  have hbr : BandPos C C' Q r.rpos := Or.inr ⟨r.h, rfl, hy⟩
  unfold CRec.toSet
  Ξ image_hseg hy, h.pos_eq hl hbl hml, h.pos_eq hr hbr hmr
  rfl

/-- **Admissibility transfers**: the stretch of an augmented chord of `C` at a band height is an
augmented chord of `C'`. -/
theorem augChords_transfer {y a b : ℝ} (hy : |y| < bnd C C')
    (hc : hseg y a b ∈ Merge.augChords C) :
    hseg y (stretch (bnd C C') (kk C C') a) (stretch (bnd C C') (kk C C') b) ∈
      Merge.augChords C' := by
  obtain ⟨y', a', b', hh, hy'', he⟩ := hc
  -- the representation is unique: `hseg y a b = hseg y' a' b'` with `a' < b'`
  have hne : (hseg y' a' b').Nonempty := ⟨(a', y'), rfl, le_rfl, hh.lt.le⟩
  rw [← he] at hne
  obtain ⟨z, hz⟩ := hne
  have hz' : z ∈ hseg y' a' b' := he ▸ hz
  have hyy : y = y' := hz.1.symm.trans hz'.1
  subst hyy
  have hab : a = a' ∧ b = b' := by
    have hl : ((a', y) : Point) ∈ hseg y a b := by rw [he]; exact ⟨rfl, le_rfl, hh.lt.le⟩
    have hr : ((b', y) : Point) ∈ hseg y a b := by rw [he]; exact ⟨rfl, hh.lt.le, le_rfl⟩
    have ha : ((a, y) : Point) ∈ hseg y a' b' := by
      rw [← he]; exact ⟨rfl, le_rfl, le_trans hl.2.1 hl.2.2⟩
    have hb : ((b, y) : Point) ∈ hseg y a' b' := by
      rw [← he]; exact ⟨rfl, le_trans hl.2.1 hl.2.2, le_rfl⟩
    exact ⟨le_antisymm hl.2.1 ha.2.1, le_antisymm hb.2.2 hr.2.2⟩
  obtain ⟨rfl, rfl⟩ := hab
  have hy' := sig_band hy (C := C) (C' := C')
  refine ⟨y, _, _, ⟨sig_lt_iff.2 hh.lt, ?_, ?_, ?_⟩, ?_, rfl⟩
  · intro hm
    have : phi C C' (a, y) ∈ C'.dom := by simp only [phi, stretchPt, hy']; exact hm
    exact hh.left_not ((h.phi_mem_dom_iff _).1 this)
  · intro hm
    have : phi C C' (b, y) ∈ C'.dom := by simp only [phi, stretchPt, hy']; exact hm
    exact hh.right_not ((h.phi_mem_dom_iff _).1 this)
  · intro x hx1 hx2
    set w := stretch (bnd C C') (kk C C')⁻¹ x
    have hinv : stretch (bnd C C') (kk C C') w = x := by
      have := stretch_inv (B := bnd C C') (k := (kk C C')⁻¹) bnd_nonneg (inv_pos.2 kk_pos) x
      rwa [inv_inv] at this
    have hw := hh.open_mem w (by rw [← sig_lt_iff (C := C) (C' := C'), hinv]; exact hx1)
      (by rw [← sig_lt_iff (C := C) (C' := C'), hinv]; exact hx2)
    have := (h.phi_mem_dom_iff (w, y)).2 hw
    simpa only [phi, stretchPt, hinv, hy'] using this
  · rw [← h.top_eq]; exact hy''

end Twin

end

end BoxT

end Chazelle.Core
