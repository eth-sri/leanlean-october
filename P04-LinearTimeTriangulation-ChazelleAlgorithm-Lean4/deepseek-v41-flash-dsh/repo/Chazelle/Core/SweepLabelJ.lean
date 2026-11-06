module

public import Chazelle.Golf

public import Chazelle.Core.SweepLabelGap
public import Chazelle.Core.FuseMath

/-!
# The sweep (WP-D), part 5: label consistency for a junction

The generic lemma (K) (`Sweep.Corr.label_gen`) instantiated for the right side of a junction:
the walk of `C = J.whole`, read from the copy of the shared vertex left towards `C₂`, and the
walk of `C₂`, read from the shared vertex, with the families

  `F₂⁺ = J.fusion ∅ S₂`   (in the model of `C`)   and   `S₂`   (in the model of
  `C₂`).

* `pos_eq_vertex`: a walk position of a chain model whose point is a chain vertex is a tour
  vertex visiting it.
* `topChords₂`, `F₂plus`: the families.
* `TopStrict`: the top of `C₂` is the only point of `C₂` at its height (no longer assumed since
  F2; kept only for the side-1 mirror until it is regenerated).
* `rL1`, `rL2`, `rδ`: the constants of the correspondence for the right side, in the three cases
  of `FuseMath.side_pieces` (Sh: one piece with the box; N: one piece; G: two pieces around the
  box of `C₂`); the correspondence itself is `SweepLabelJG.corr_right0`.
* `RLabel`: the labels of a region of `F₂⁺` (the regions of `S₂` faced by the counterparts of the
  non-cut positions of the right stretch facing it); lemma (K3) is `SweepLabelJG.label_right3`.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideLeftOf sideE sidePrev sideNext)
open Chazelle.Visibility (rayPt)
open WalkEmbed

namespace Sweep

/-! ## Walk positions at chain vertices -/

section Vertex

variable (C : Chain)

/-- **A walk position at a chain vertex** is a tour vertex visiting it (the box, the slit and the
open tour edges contain no chain vertex). -/
theorem pos_eq_vertex (hP : C.P.Simple) (β : Bool) {p : ℕ} (hp : p < (C.sideWalk β).n) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) {k : ℕ} (hk : k ≤ C.m)
    (h : sidePt (C.sideWalk β) p t = C.vertex k) :
    t = 0 ∧ ∃ i, i ≤ 2 * C.m ∧ p = i + 6 ∧ C.sideIdx β i = k := by
  have hR := C.radius_pos
  have hvk := C.vertex_mem_set hk
  have hb := C.abs_le_coordBound_of_mem_set hvk
  have hcb := C.coordBound_lt_radius
  have hvtop := C.vertex_snd_le_top hk
  have htopR := C.top_snd_lt_radius
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := C.sidePt_box β t
  rcases C.sideWalk_pos_cases β hp ht with (hp5 | ⟨rfl, htp⟩) | ⟨i, hi, rfl, hit⟩
  · exfalso
    interval_cases p
    · rw [h0] at h; have := congrArg Prod.snd h; simp only at this
      have := (abs_le.1 hb.2).2; linarith
    · rw [h1] at h; have := congrArg Prod.fst h; simp only at this
      have := (abs_le.1 hb.1).1; linarith
    · rw [h2] at h; have := congrArg Prod.snd h; simp only at this
      have := (abs_le.1 hb.2).1; linarith
    · rw [h3] at h; have := congrArg Prod.fst h; simp only at this
      have := (abs_le.1 hb.1).2; linarith
    · rw [h4] at h; have := congrArg Prod.snd h; simp only at this
      have := (abs_le.1 hb.2).2; linarith
    · rw [h5] at h; have := congrArg Prod.snd h; simp only at this
      nlinarith
  · exfalso
    rw [h6] at h; have := congrArg Prod.snd h; simp only at this
    nlinarith
  · rcases ht.lt_or_eq with htp | rfl
    · exfalso
      have hi2 : i < 2 * C.m := by
        rcases lt_or_eq_of_le hi with h' | h'
        · exact h'
        · exact absurd (hit h') htp.ne'
      rw [C.sidePt_tour β hi2] at h
      unfold Chain.sideTour at h
      rcases C.sideTour_step β i with hs | hs
      · rw [hs] at h
        exact C.sideOpen_ne_vertex hP ⟨htp, ht1⟩ h
      · rw [← hs] at h
        have e : Geometry.lerp (C.vertex (C.sideIdx β (i + 1) + 1)) (C.vertex (C.sideIdx β (i + 1)))
            t = Geometry.lerp (C.vertex (C.sideIdx β (i + 1))) (C.vertex (C.sideIdx β (i + 1) + 1))
            (1 - t) := by
          apply Geometry.point_ext <;> simp [Geometry.lerp] <;> ring
        rw [e] at h
        exact C.sideOpen_ne_vertex hP ⟨⟡, by linarith⟩ h
    · refine ⟨rfl, i, hi, rfl, ?_⟩
      rw [Chazelle.Chain.sidePt_zero, C.sideWalk_vtx_tour β hi] at h
      exact C.sideVertex_inj hP (C.sideIdx_le β i) hk h

/-- Arithmetic of the tour positions at vertex `0`: offset `0`, or `2m` when the tour starts at
the box. -/
theorem vertex0_arith {m b i : ℕ} (hm : 0 < m) (hb : b ≤ 2 * m) (hi : i ≤ 2 * m)
    (h : (b + i) % (2 * m) = 0) :
    (i + 6 + (2 * m + 7) - (6 + (0 + 2 * m - b) % (2 * m))) % (2 * m + 7) = 0 ∨
      ((0 + 2 * m - b) % (2 * m) = 0 ∧
        (i + 6 + (2 * m + 7) - (6 + (0 + 2 * m - b) % (2 * m))) % (2 * m + 7) = 2 * m) := by
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h
  have hq2 : q ≤ 2 := by
    by_contra hc; push Not at hc; nlinarith
  have hτ : (0 + 2 * m - b) % (2 * m) = if b = 0 then 0 else 2 * m - b := by
    split_ifs with hb0
    · subst hb0; simp
    · rw [Nat.mod_eq_of_lt (show 0 + 2 * m - b < 2 * m by omega)]; omega
  rw [hτ]
  have key : ∀ x, x < 2 * (2 * m + 7) →
      x % (2 * m + 7) = if x < 2 * m + 7 then x else x - (2 * m + 7) := by
    intro x hx; split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  interval_cases q <;> split_ifs with hb0 <;> rw [key _ (by omega)] <;> split_ifs <;> omega

/-- **The positions at vertex `0`** of the walk of a chain model, read from the tour position `0`:
offset `0`, or offset `2m` when the tour position `0` is the box. -/
theorem off_vertex0 (hP : C.P.Simple) {p : ℕ} (hp : p < (chainModel C).W.n) {t : ℝ} (ht : 0 ≤ t)
    (ht1 : t < 1) (h : sidePt (chainModel C).W p t = C.vertex 0) :
    off (chainModel C).W.n ((6 + tpos C 0 : ℕ) : ℝ) (p + t) = 0 ∨
      (tpos C 0 = 0 ∧ off (chainModel C).W.n ((6 + tpos C 0 : ℕ) : ℝ) (p + t) = 2 * C.m) := by
  obtain ⟨rfl, i, hi, rfl, hidx⟩ := pos_eq_vertex C hP C.sideBeta hp ht ht1 (Nat.zero_le _) h
  have hn := cm_n C
  have hτ := tpos_lt C 0
  have hm := C.two_m_pos
  Ξ off_key' (by rw [hn]; omega) hp le_rfl zero_lt_one, add_zero
  have h0 : (bS C + i) % (2 * C.m) = 0 := by
    rw [Chain.sideIdx_eq] at hidx
    unfold Chain.sideE at hidx
    have := Nat.mod_lt (C.sideS C.sideBeta + i) hm
    split_ifs at hidx
    · exact hidx
    · omega
  have := vertex0_arith (m := C.m) (b := bS C) (i := i) (⋄) (bS_le C) hi h0
  unfold dOf
  Ξ hn
  unfold tpos
  rcases this with h | ⟨h1, h2⟩
  · left; rw [h]; simp
  · right; exact ⟨h1, by rw [h2]; push_cast; ring⟩

end Vertex

/-! ## The families -/

section Families

variable (J : Merge.Junction)

/-- **The top chords of `C` at the top of `C₂`** (the vertex chords of `C` at its vertex
`m₁ + topIdx C₂`). -/
def topChords₂ : Set (Set Point) :=
  {d | ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ J.whole.DirFree (J.m₁ + J.right.topIdx) σ ∧
    d = J.whole.chordSet (J.m₁ + J.right.topIdx) σ}

/-- **The family `F₂⁺`** of the sweep, in the model of `C`: the fusion of `∅` and `S₂` (the chords
of `C` seen from the endpoints of the chords of `S₂`, and the shared chords) and the top chords
at the top of `C₂`. -/
def F₂plus (S₂ : Set (Set Point)) : Set (Set Point) := J.fusion ∅ S₂ ∪ topChords₂ J

theorem topChords₂_subset_chords : topChords₂ J ⊆ J.whole.chords := by
  rintro d ⟨σ, hσ, hfree, rfl⟩
  have := J.right.topIdx_le
  exact ⟨_, σ, by simp only [Merge.Junction.whole_m, Merge.Junction.right_m] at this ⊢; omega,
    hσ, hfree, rfl⟩

theorem F₂plus_subset {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right) :
    F₂plus J S₂ ⊆ Merge.augChords J.whole := by
  rintro e (he | he)
  · exact J.fusion_subset_augChords (empty_subset _) hS₂ he
  · exact Merge.chords_subset_augChords _ (topChords₂_subset_chords J he)

theorem F₂plus_finite {S₂ : Set (Set Point)} (hS₂ : S₂.Finite) : (F₂plus J S₂).Finite :=
  (J.fusion_finite finite_empty hS₂).union (J.whole.chords_finite.subset (topChords₂_subset_chords J))

/-- Distinct augmented chords are not nested. -/
theorem augChords_nest {C : Chain} {e e' : Set Point} (he : e ∈ Merge.augChords C)
    (he' : e' ∈ Merge.augChords C) (h : e ⊆ e') : e = e' := by
  obtain ⟨y, a, b, hh, -, rfl⟩ := he
  obtain ⟨y', a', b', hh', -, rfl⟩ := he'
  have hab := hh.lt
  have hp : (((a + b) / 2, y) : Point) ∈ Visibility.hseg y a b :=
    ⟨rfl, by simp only; linarith, by simp only; linarith⟩
  rcases Chain.hchordIn_inter hh hh' hp (h hp) with ⟨rfl, rfl, rfl⟩ | ⟨h1, -⟩
  · rfl
  · exfalso
    rcases h1 with h1 | h1 <;> have := congrArg Prod.fst h1 <;> simp only at this <;> linarith

/-- **Endpoints of the chords of `S₂`** other than the shared vertex lie on chords of the fusion
inside them. -/
theorem trans_right (hP : J.P.Simple) {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right) :
    ∀ c ∈ S₂, ∀ q ∈ c, q ∉ J.right.dom → q ≠ J.shared → ∃ e ∈ F₂plus J S₂, q ∈ e ∧ e ⊆ c := by
  intro c hc q hq hqD hqv
  obtain ⟨hL, hR⟩ := J.end_mem_fusion hP (empty_subset _) hS₂ (Or.inr hc)
  obtain ⟨y, a, b, hH, -, rfl, hl, hr⟩ := Merge.augChords_spec (hS₂ hc)
  obtain ⟨hq2, hqa, hqb⟩ := hq
  rcases hqa.lt_or_eq with h1 | h1
  · rcases hqb.lt_or_eq with h2 | h2
    · exact absurd (by rw [show q = (q.1, y) from Prod.ext rfl hq2]; exact hH.open_mem q.1 h1 h2)
        hqD
    · have hqr : Merge.rend (Visibility.hseg y a b) = q := by rw [hr]; exact Prod.ext h2.symm hq2.symm
      rw [hqr] at hR
      obtain ⟨e, he, hqe, hec⟩ := hR hqv
      exact ⟨e, Or.inl he, hqe, hec⟩
  · have hql : Merge.lend (Visibility.hseg y a b) = q := by rw [hl]; exact Prod.ext h1 hq2.symm
    rw [hql] at hL
    obtain ⟨e, he, hqe, hec⟩ := hL hqv
    exact ⟨e, Or.inl he, hqe, hec⟩

end Families

/-! ## The correspondence for the right side of a junction -/

section CorrRight

variable (J : Merge.Junction)

/-- The length of the right stretch of the walk of `C` (read from the copy of the shared vertex
left towards `C₂`): the tour of `C₂`, and the box of `C` when it lies inside. -/
noncomputable def rlen : ℕ :=
  if 2 * J.whole.m - tpos J.whole J.m₁ < 2 * J.m₂ then 2 * J.m₂ + 7 else 2 * J.m₂

/-- The length of the first agreeing piece of the right correspondence (`Sweep.Corr`): the whole
stretch (with the box of `C`) in case Sh, the tour of `C₂` in case N, up to the box of `C₂` in
case G. -/
noncomputable def rL1 : ℕ :=
  if 2 * J.whole.m - tpos J.whole J.m₁ < 2 * J.m₂ then 2 * J.m₂ + 7
  else if 2 * J.m₂ ≤ 2 * J.right.m - tpos J.right 0 then 2 * J.m₂
  else 2 * J.right.m - tpos J.right 0

/-- The length of the second agreeing piece of the right correspondence (case G only). -/
noncomputable def rL2 : ℕ :=
  if 2 * J.whole.m - tpos J.whole J.m₁ < 2 * J.m₂ then 0
  else if 2 * J.m₂ ≤ 2 * J.right.m - tpos J.right 0 then 0
  else 2 * J.m₂ - (2 * J.right.m - tpos J.right 0)

/-- The gap of the right correspondence: the box block of `C₂` in case G. -/
noncomputable def rδ : ℕ :=
  if 2 * J.whole.m - tpos J.whole J.m₁ < 2 * J.m₂ then 0
  else if 2 * J.m₂ ≤ 2 * J.right.m - tpos J.right 0 then 0
  else 7

theorem rL1_add_rL2 : rL1 J + rL2 J = rlen J := by
  have := tpos_lt J.right 0
  have hm2 : J.right.m = J.m₂ := rfl
  unfold rL1 rL2 rlen
  split_ifs <;> omega

end CorrRight

/-! ## Lemma (K) for a junction -/

section LabelRight

variable (J : Merge.Junction)

/-- **The label of a region of `F₂⁺`**: `RLabel J S₂ G V` says that some position inside a walk
edge of the right stretch of the walk of `C`, not a cut of `F₂⁺`, faces `G`, and the corresponding
position of the walk of `C₂` faces `V`. -/
def RLabel (S₂ : Set (Set Point)) (G V : Set Point) : Prop :=
  ∃ d < rL1 J + rL2 J, ∃ t ∈ Ioo (0 : ℝ) 1,
    ¬ (chainModel J.whole).IsCut (F₂plus J S₂)
        ((((6 + tpos J.whole J.m₁) + d) % (chainModel J.whole).W.n : ℕ) + t) ∧
      (chainModel J.whole).Faces (((6 + tpos J.whole J.m₁) + d) % (chainModel J.whole).W.n) t G ∧
      (chainModel J.right).Faces
        (((6 + tpos J.right 0) + dq (rL1 J) (rδ J) d) % (chainModel J.right).W.n) t V

end LabelRight

end Sweep

end

end Chazelle.Core
