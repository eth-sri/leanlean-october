module

public import Chazelle.Core.SweepLabelJ

/-!
# The sweep (WP-D), mirror part 5: label consistency for the left side of a junction

The mirror of `SweepLabelJ` for the sweep with `i = 1` (points of `C₂` located in the regions of
`S₁`): the walk of `C = J.whole`, read from the copy of the shared vertex left towards `C₁` (tour
position `m₁ + 2 m₂`), and the walk of `C₁`, read from the shared vertex (its last vertex, tour
position `m₁`), with the families

  `F₁⁺ = J.fusion S₁ ∅ ∪ topChords₁ J`   (in the model of `C`)   and   `S₁`   (in the model of
  `C₁`).

* `off_vertexEnd`: the positions at the last vertex of a chain are at offset `0` from its tour
  position (or `2m` when that tour position is `0`).
* `topChords₁`, `F₁plus`, `trans_left`.
* `lL1`, `lL2`, `lδ`, `corr_left`: the correspondence in the three cases.
* `LLabel`, `label_left`: lemma (K) for the left side.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideLeftOf sideE sidePrev sideNext)
open Chazelle.Visibility (rayPt)
open WalkEmbed

namespace Sweep

/-! ## Walk positions at the last vertex of a chain -/

section VertexEnd

variable (C : Chain)

/-- Arithmetic of the tour positions at the last vertex `m`. -/
theorem vertexEnd_arith {m b i : ℕ} (hm : 0 < m) (hb : b ≤ 2 * m) (hi : i ≤ 2 * m)
    (h : (b + i) % (2 * m) = m) :
    (i + 6 + (2 * m + 7) - (6 + (m + 2 * m - b) % (2 * m))) % (2 * m + 7) = 0 ∨
      ((m + 2 * m - b) % (2 * m) = 0 ∧
        (i + 6 + (2 * m + 7) - (6 + (m + 2 * m - b) % (2 * m))) % (2 * m + 7) = 2 * m) := by
  have hq : b + i = (b + i) / (2 * m) * (2 * m) + m := by
    have := Nat.div_add_mod (b + i) (2 * m)
    rw [h] at this; linarith
  have hq2 : (b + i) / (2 * m) ≤ 1 := by
    by_contra hc; push Not at hc
    have : 2 * (2 * m) ≤ (b + i) / (2 * m) * (2 * m) := Nat.mul_le_mul_right _ hc
    omega
  have key : ∀ x, x < 2 * (2 * m + 7) →
      x % (2 * m + 7) = if x < 2 * m + 7 then x else x - (2 * m + 7) := by
    intro x hx; split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have key2 : ∀ x, x < 2 * (2 * m) → x % (2 * m) = if x < 2 * m then x else x - 2 * m := by
    intro x hx; split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [key2 _ (by omega)]
  interval_cases hq' : (b + i) / (2 * m) <;> split_ifs <;> rw [key _ (by omega)] <;>
    split_ifs <;> omega

/-- **The positions at the last vertex** of the walk of a chain model, read from its tour
position: offset `0`, or offset `2m` when that tour position is `0`. -/
theorem off_vertexEnd (hP : C.P.Simple) {p : ℕ} (hp : p < (chainModel C).W.n) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) (h : sidePt (chainModel C).W p t = C.vertex C.m) :
    off (chainModel C).W.n ((6 + tpos C C.m : ℕ) : ℝ) (p + t) = 0 ∨
      (tpos C C.m = 0 ∧ off (chainModel C).W.n ((6 + tpos C C.m : ℕ) : ℝ) (p + t) = 2 * C.m) := by
  obtain ⟨rfl, i, hi, rfl, hidx⟩ := pos_eq_vertex C hP C.sideBeta hp ht ht1 le_rfl h
  have hn := cm_n C
  have hτ := tpos_lt C C.m
  have hm := C.two_m_pos
  rw [off_key' (by rw [hn]; omega) hp le_rfl zero_lt_one, add_zero]
  have h0 : (bS C + i) % (2 * C.m) = C.m := by
    rw [Chain.sideIdx_eq] at hidx
    unfold Chain.sideE at hidx
    have := Nat.mod_lt (C.sideS C.sideBeta + i) hm
    split_ifs at hidx
    · exact hidx
    · omega
  have := vertexEnd_arith (m := C.m) (b := bS C) (i := i) (by omega) (bS_le C) hi h0
  unfold dOf
  rw [hn]
  unfold tpos
  rcases this with h | ⟨h1, h2⟩
  · left; rw [h]; simp
  · right; exact ⟨h1, by rw [h2]; push_cast; ring⟩

end VertexEnd

/-! ## The families -/

section FamiliesL

variable (J : Merge.Junction)

/-- **The top chords of `C` at the top of `C₁`** (the vertex chords of `C` at its vertex
`topIdx C₁`). -/
def topChords₁ : Set (Set Point) :=
  {d | ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ J.whole.DirFree J.left.topIdx σ ∧
    d = J.whole.chordSet J.left.topIdx σ}

/-- **The family `F₁⁺`** of the mirror sweep, in the model of `C`. -/
def F₁plus (S₁ : Set (Set Point)) : Set (Set Point) := J.fusion S₁ ∅ ∪ topChords₁ J

theorem topChords₁_subset_chords : topChords₁ J ⊆ J.whole.chords := by
  rintro d ⟨σ, hσ, hfree, rfl⟩
  have := J.left.topIdx_le
  exact ⟨_, σ, by simp only [Merge.Junction.whole_m, Merge.Junction.left_m] at this ⊢; omega,
    hσ, hfree, rfl⟩

theorem F₁plus_subset {S₁ : Set (Set Point)} (hS₁ : S₁ ⊆ Merge.augChords J.left) :
    F₁plus J S₁ ⊆ Merge.augChords J.whole := by
  rintro e (he | he)
  · exact J.fusion_subset_augChords hS₁ (empty_subset _) he
  · exact Merge.chords_subset_augChords _ (topChords₁_subset_chords J he)

theorem F₁plus_finite {S₁ : Set (Set Point)} (hS₁ : S₁.Finite) : (F₁plus J S₁).Finite :=
  (J.fusion_finite hS₁ finite_empty).union (J.whole.chords_finite.subset (topChords₁_subset_chords J))

/-- **Endpoints of the chords of `S₁`** other than the shared vertex lie on chords of the fusion
inside them. -/
theorem trans_left (hP : J.P.Simple) {S₁ : Set (Set Point)} (hS₁ : S₁ ⊆ Merge.augChords J.left) :
    ∀ c ∈ S₁, ∀ q ∈ c, q ∉ J.left.dom → q ≠ J.shared → ∃ e ∈ F₁plus J S₁, q ∈ e ∧ e ⊆ c := by
  intro c hc q hq hqD hqv
  obtain ⟨hL, hR⟩ := J.end_mem_fusion hP hS₁ (empty_subset _) (Or.inl hc)
  obtain ⟨y, a, b, hH, -, rfl, hl, hr⟩ := Merge.augChords_spec (hS₁ hc)
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

end FamiliesL

/-! ## The correspondence for the left side of a junction -/

section CorrLeft

variable (J : Merge.Junction)

/-- The length of the left stretch of the walk of `C` (read from the copy of the shared vertex
left towards `C₁`). -/
noncomputable def llen : ℕ :=
  if 2 * J.whole.m - tpos J.whole (J.m₁ + 2 * J.m₂) < 2 * J.m₁ then 2 * J.m₁ + 7 else 2 * J.m₁

/-- The length of the first agreeing piece of the left correspondence. -/
noncomputable def lL1 : ℕ :=
  if 2 * J.whole.m - tpos J.whole (J.m₁ + 2 * J.m₂) < 2 * J.m₁ then 2 * J.m₁ + 7
  else if 2 * J.m₁ ≤ 2 * J.left.m - tpos J.left J.m₁ then 2 * J.m₁
  else 2 * J.left.m - tpos J.left J.m₁

/-- The length of the second agreeing piece of the left correspondence (case G only). -/
noncomputable def lL2 : ℕ :=
  if 2 * J.whole.m - tpos J.whole (J.m₁ + 2 * J.m₂) < 2 * J.m₁ then 0
  else if 2 * J.m₁ ≤ 2 * J.left.m - tpos J.left J.m₁ then 0
  else 2 * J.m₁ - (2 * J.left.m - tpos J.left J.m₁)

/-- The gap of the left correspondence: the box block of `C₁` in case G. -/
noncomputable def lδ : ℕ :=
  if 2 * J.whole.m - tpos J.whole (J.m₁ + 2 * J.m₂) < 2 * J.m₁ then 0
  else if 2 * J.m₁ ≤ 2 * J.left.m - tpos J.left J.m₁ then 0
  else 7

theorem lL1_add_lL2 : lL1 J + lL2 J = llen J := by
  have := tpos_lt J.left J.m₁
  have hm1 : J.left.m = J.m₁ := rfl
  unfold lL1 lL2 llen
  split_ifs <;> omega

end CorrLeft

/-! ## Lemma (K) for the left side -/

section LabelLeft

variable (J : Merge.Junction)

end LabelLeft

end Sweep

end

end Chazelle.Core
