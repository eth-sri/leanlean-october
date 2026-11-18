module

public import Chazelle.Core.FactsWalk

/-!
# WP-B: the chain model satisfies the walk axioms

For a chain `C` of a simple polygon, the chain model `chainModel C` (box-and-slit domain, walk
`C.sideWalk C.sideBeta`, admissible chords `Merge.augChords C`) satisfies the walk axioms
`WalkAx` of `Chazelle.Core.FactsWalk` (`walkAx_chainModel`):

* openness, connectedness, the nondegenerate edges, the trace and the cleanness of the walk are
  `Chazelle.Chain.Sides` (`sideWalk_nd`, `sideWalk_trace`, `sideWalk_clean` with the correct
  turn at the top vertex `sideGood_sideBeta`);
* finite augmented families are chord systems (`Merge.augChordSystem`);
* the endpoints of an augmented chord are on the chain or on an open vertical side of the box, so
  the chord is attached there (`sideSees_chordEnd`, `sideAttach_of_left`) and the positions at an
  endpoint have disjoint left sectors (`sideWalk_disj`);
* **reach**: the first exit of an eastward ray from the domain is on the right side of the box
  (walk edge `3`, going up), on the slit above the top vertex (walk edge `2m + 6`, going up), or
  inside a chain edge, which the tour of the double boundary traverses in both directions, one
  of them upwards.

It also proves the generic first-exit lemma `exists_first_exit`.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext lerp_mem_segment)
open Chazelle.Visibility (hseg segment_horizontal_eq_hseg)

/-- **First exit of a horizontal ray** from an open set lying left of the line `x = R`: the ray
to the east from `z ∈ D` stays in `D` on `[0, s)` and leaves it at `s > 0`. -/
theorem exists_first_exit {D : Set Point} (hD : IsOpen D) {z : Point} (hz : z ∈ D) {R : ℝ}
    (hR : ∀ x ∈ D, x.1 < R) :
    ∃ s > (0 : ℝ), (∀ s' ∈ Ico (0 : ℝ) s, ((z.1 + s', z.2) : Point) ∈ D) ∧
      ((z.1 + s, z.2) : Point) ∉ D := by
  set T := {s : ℝ | 0 ≤ s ∧ ((z.1 + s, z.2) : Point) ∉ D} with hT
  have hcont : Continuous fun s : ℝ => ((z.1 + s, z.2) : Point) := by fun_prop
  have hTc : IsClosed T :=
    (isClosed_le continuous_const continuous_id).inter (hD.isClosed_compl.preimage hcont)
  have hz1 := hR z hz
  have hTne : T.Nonempty := ⟨R - z.1 + 1, by linarith, fun h => by
    have := hR _ h; simp only at this; linarith⟩
  have hbdd : BddBelow T := ⟨0, fun s hs => hs.1⟩
  have hmem := hTc.csInf_mem hTne hbdd
  refine ⟨sInf T, ?_, fun s' hs' => ?_, hmem.2⟩
  · rcases hmem.1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hmem.2; rw [← h, add_zero]; exact hz
  · by_contra hs
    exact absurd (csInf_le hbdd ⟨hs'.1, hs⟩) (not_le.2 hs'.2)

namespace FactsChain

variable (C : Chain)

/-- A horizontal segment as a segment. -/
theorem hseg_eq_segment {y a b : ℝ} (hab : a ≤ b) :
    hseg y a b = Chazelle.segment ((a, y) : Point) (b, y) := by
  rw [segment_horizontal_eq_hseg (a := ((a, y) : Point)) (b := ((b, y) : Point)) rfl]
  dsimp only
  rw [min_eq_left hab, max_eq_right hab]

/-- An endpoint of an augmented chord is on the chain or on an open vertical side of the box. -/
theorem end_cases {y a b : ℝ} (h : IsHChordIn C.dom y a b) (hy : y ≤ C.top.2) {e : Point}
    (he : C.Anchorable e) (he2 : e.2 = y) :
    e ∈ C.set ∨ (|e.1| = C.radius ∧ |e.2| < C.radius) := by
  have hmid := h.open_mem ((a + b) / 2) (by linarith [h.lt]) (by linarith [h.lt])
  have hyR : |y| < C.radius := (C.dom_subset_box hmid).2
  rcases he with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · left
    obtain ⟨e1, e2, -⟩ := C.mem_slit_iff.1 h1
    have : e = C.top := point_ext e1 (le_antisymm (he2 ▸ hy) e2)
    rw [this]; exact C.top_mem_set
  · exact Or.inr ⟨h1, he2 ▸ hyR⟩
  · exact absurd (he2 ▸ h1) (ne_of_lt hyR)

/-- The walk-end condition at an endpoint of an augmented chord. -/
theorem walkEnd (hP : C.P.Simple) {e e' : Point} (hee : e ≠ e') (hy : e.2 = e'.2)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp e e' s ∈ C.dom)
    (he : e ∈ C.set ∨ (|e.1| = C.radius ∧ |e.2| < C.radius)) :
    WalkEnd (C.sideWalk C.sideBeta) (Chazelle.segment e e') e := by
  refine ⟨?_, ?_⟩
  · obtain ⟨p, t, hp, ht, ht1, hpt, hl⟩ := C.sideSees_chordEnd hP C.sideBeta hee hy hopen he
    exact ⟨p, t, sideAttach_of_left hp ht ht1 hpt hl, hpt⟩
  · intro p p' t t' hp ht ht1 hp' ht' ht1' hne h1 h2
    refine ⟨1, one_pos, fun x _ hx hx' => ?_⟩
    exact C.sideWalk_disj hP (C.sideGood_sideBeta hP) hp ht ht1 hp' ht' ht1'
      (fun h => fun h' => hne h.symm h'.symm) (h2.trans h1.symm) (h1 ▸ he) x ⟨hx, hx'⟩

/-- Every chain vertex is a vertex of the corrected walk. -/
theorem vertex_mem_walk {k : ℕ} (hk : k ≤ C.m) :
    ∃ i < (C.sideWalk C.sideBeta).n, (C.sideWalk C.sideBeta).vtx i = C.vertex k := by
  have hm := C.one_le
  obtain ⟨i, hi, hidx, -⟩ := C.sideIdx_visit C.sideBeta (j := k) (by omega)
  refine ⟨i + 6, by rw [sideWalk_n]; omega, ?_⟩
  rw [C.sideWalk_vtx_tour _ hi.le, sideTour, hidx]
  congr 1; unfold sideE; split_ifs; omega

/-- The two traversals of a chain edge by the tour of the double boundary. -/
theorem tour_edges {k : ℕ} (hk : k < C.m) :
    (∃ i < 2 * C.m, C.sideIdx C.sideBeta i = k ∧ C.sideIdx C.sideBeta (i + 1) = k + 1) ∧
      (∃ i < 2 * C.m, C.sideIdx C.sideBeta i = k + 1 ∧ C.sideIdx C.sideBeta (i + 1) = k) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi, h1, h2, -⟩ := C.sideIdx_visit C.sideBeta (j := k) (by omega)
    refine ⟨i, hi, ?_, ?_⟩
    · rw [h1]; unfold sideE; split_ifs <;> omega
    · rw [h2]; unfold sideE; split_ifs <;> omega
  · obtain ⟨i, hi, h1, h2, -⟩ := C.sideIdx_visit C.sideBeta (j := 2 * C.m - 1 - k) (by omega)
    refine ⟨i, hi, ?_, ?_⟩
    · rw [h1]; unfold sideE; split_ifs <;> omega
    · rw [h2]; unfold sideE; split_ifs <;> omega

/-- **Reach for the chain model.** -/
theorem reach {z : Point} (hz : z ∈ C.dom)
    (hzv : ∀ i < (C.sideWalk C.sideBeta).n, z.2 ≠ ((C.sideWalk C.sideBeta).vtx i).2) :
    ∃ s > (0 : ℝ), (∀ s' ∈ Ico (0 : ℝ) s, ((z.1 + s', z.2) : Point) ∈ C.dom) ∧
      ∃ p < (C.sideWalk C.sideBeta).n, ∃ t ∈ Ioo (0 : ℝ) 1,
        sidePt (C.sideWalk C.sideBeta) p t = ((z.1 + s, z.2) : Point) ∧
        ((C.sideWalk C.sideBeta).vtx p).2 <
          ((C.sideWalk C.sideBeta).vtx ((p + 1) % (C.sideWalk C.sideBeta).n)).2 := by
  set W := C.sideWalk C.sideBeta with hW
  have hm := C.one_le
  have hn : W.n = 2 * C.m + 7 := C.sideWalk_n _
  have hR := C.radius_pos
  have hbox : ∀ x ∈ C.dom, |x.1| < C.radius ∧ |x.2| < C.radius := fun x hx => C.dom_subset_box hx
  obtain ⟨s, hs, hseg, hq⟩ := exists_first_exit C.isOpen_dom hz (R := C.radius)
    (fun x hx => (abs_lt.1 (hbox x hx).1).2)
  refine ⟨s, hs, hseg, ?_⟩
  have hz1 := abs_lt.1 (hbox z hz).1
  have hz2 := abs_lt.1 (hbox z hz).2
  -- `z.2` is not the height of the top of the box, nor of a chain vertex
  have hzR : z.2 ≠ C.radius := fun h => hzv 0 (by omega) (by rw [C.sideWalk_vtx_zero]; exact h)
  have hzv' : ∀ k ≤ C.m, z.2 ≠ (C.vertex k).2 := by
    intro k hk h
    obtain ⟨i, hi, hvi⟩ := vertex_mem_walk C hk
    exact hzv i hi (by rw [hvi]; exact h)
  -- the exit point is at abscissa at most `R`
  have hqR : z.1 + s ≤ C.radius := by
    by_contra hgt
    push Not at hgt
    have hs' : s - (z.1 + s - C.radius) / 2 ∈ Ico (0 : ℝ) s := ⟨by linarith, by linarith⟩
    have := (abs_lt.1 (hbox _ (hseg _ hs')).1).2
    simp only at this; linarith
  rw [C.mem_dom_iff] at hq
  by_cases hqbox : ((z.1 + s, z.2) : Point) ∈ box C.radius
  · by_cases hqset : ((z.1 + s, z.2) : Point) ∈ C.set
    · -- inside a chain edge
      obtain ⟨k, hk, hmem⟩ := hqset
      rw [C.chainEdge_eq] at hmem
      obtain ⟨s₀, hs₀0, hs₀1, he⟩ := Geometry.mem_segment_iff_lerp.1 hmem
      have he2 := congrArg Prod.snd he
      simp only [lerp_snd] at he2
      have hs₀0' : 0 < s₀ := by
        rcases hs₀0.lt_or_eq with h | h
        · exact h
        · exfalso; apply hzv' k hk.le; rw [he2, ← h]; ring
      have hs₀1' : s₀ < 1 := by
        rcases hs₀1.lt_or_eq with h | h
        · exact h
        · exfalso; apply hzv' (k + 1) hk; rw [he2, h]; ring
      have hne : (C.vertex k).2 ≠ (C.vertex (k + 1)).2 := by
        intro h; apply hzv' k hk.le; rw [he2, ← h]; ring
      obtain ⟨⟨i, hi, hi1, hi2⟩, ⟨i', hi', hi1', hi2'⟩⟩ := tour_edges C hk
      have hvi : W.vtx (i + 6) = C.vertex k := by
        rw [hW, C.sideWalk_vtx_tour _ hi.le, sideTour, hi1]
      have hvi1 : W.vtx ((i + 6 + 1) % W.n) = C.vertex (k + 1) := by
        rw [hW, C.sideWalk_next_tour _ hi, C.sideWalk_vtx_tour _ (by omega), sideTour, hi2]
      have hvi' : W.vtx (i' + 6) = C.vertex (k + 1) := by
        rw [hW, C.sideWalk_vtx_tour _ hi'.le, sideTour, hi1']
      have hvi1' : W.vtx ((i' + 6 + 1) % W.n) = C.vertex k := by
        rw [hW, C.sideWalk_next_tour _ hi', C.sideWalk_vtx_tour _ (by omega), sideTour, hi2']
      rcases lt_or_gt_of_ne hne with hup | hdn
      · refine ⟨i + 6, by omega, s₀, ⟨hs₀0', hs₀1'⟩, ?_, by rw [hvi, hvi1]; exact hup⟩
        unfold sidePt; rw [hvi, hvi1, he]
      · refine ⟨i' + 6, by omega, 1 - s₀, ⟨by linarith, by linarith⟩, ?_,
          by rw [hvi', hvi1']; exact hdn⟩
        unfold sidePt; rw [hvi', hvi1', he]
        apply point_ext <;> simp only [lerp_fst, lerp_snd] <;> ring
    · -- on the slit, above the top vertex
      have hslit : ((z.1 + s, z.2) : Point) ∈ C.slit := by
        by_contra h; exact hq ⟨hqbox, hqset, h⟩
      obtain ⟨e1, e2, e3⟩ := C.mem_slit_iff.1 hslit
      simp only at e1 e2 e3
      have htop : C.top.2 < z.2 := by
        rcases e2.lt_or_eq with h | h
        · exact h
        · exact absurd h.symm (hzv' C.topIdx C.topIdx_le)
      have hzR' : z.2 < C.radius := lt_of_le_of_ne e3 hzR
      have hv0 : W.vtx (2 * C.m + 6) = C.top := by
        rw [hW, C.sideWalk_vtx_tour _ le_rfl, C.sideTour_two_m]
      have hv1 : W.vtx ((2 * C.m + 6 + 1) % W.n) = C.slitTop := by
        rw [hW, C.sideWalk_next_last]; rfl
      have hpos : 0 < C.radius - C.top.2 := by linarith
      refine ⟨2 * C.m + 6, by omega, (z.2 - C.top.2) / (C.radius - C.top.2),
        ⟨div_pos (by linarith) hpos, (div_lt_one hpos).2 (by linarith)⟩, ?_, ?_⟩
      · rw [(C.sidePt_box _ _).2.2.2.2.2.2]
        apply point_ext
        · simp only; exact e1.symm
        · simp only; field_simp; ring
      · rw [hv0, hv1]; exact C.top_snd_lt_radius
  · -- on the right side of the box
    have hq1 : z.1 + s = C.radius := by
      by_contra hne
      apply hqbox
      refine ⟨abs_lt.2 ⟨by linarith, lt_of_le_of_ne hqR hne⟩, abs_lt.2 hz2⟩
    have hv3 : W.vtx 3 = (C.radius, -C.radius) := C.sideWalk_vtx_three _
    have hv4 : W.vtx ((3 + 1) % W.n) = (C.radius, C.radius) := by
      rw [hn, Nat.mod_eq_of_lt (by omega)]; exact C.sideWalk_vtx_four _
    refine ⟨3, by omega, (z.2 + C.radius) / (2 * C.radius),
      ⟨div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩, ?_, ?_⟩
    · rw [(C.sidePt_box _ _).2.2.2.1]
      apply point_ext
      · simp only; exact hq1.symm
      · simp only; field_simp; ring
    · rw [hv3, hv4]; simp only; linarith

/-- **The chain model satisfies the walk axioms.** -/
theorem walkAx (hP : C.P.Simple) : WalkAx (chainModel C) where
  isOpen := C.isOpen_dom
  preconn := C.dom_connected hP
  nonempty := C.dom_nonempty
  nd := C.sideWalk_nd hP _
  trace := C.sideWalk_trace _
  clean := C.sideWalk_clean hP (C.sideGood_sideBeta hP)
  sys := fun _ hF hfin => Merge.augChordSystem C hF hfin
  ends := by
    intro c hc
    obtain ⟨y, a, b, h, hy, rfl⟩ := hc
    have hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp ((a, y) : Point) (b, y) s ∈ C.dom := by
      intro s hs
      have e : lerp ((a, y) : Point) (b, y) s = ((a + s * (b - a), y) : Point) := by
        apply point_ext <;> simp [lerp]
      rw [e]
      exact h.open_mem _ (by nlinarith [h.lt, hs.1]) (by nlinarith [h.lt, hs.2])
    have hab : ((a, y) : Point) ≠ (b, y) := fun e => h.lt.ne (congrArg Prod.fst e)
    have hseg := hseg_eq_segment (y := y) h.lt.le
    have ha := end_cases C h hy (Merge.anchorable_left C h) rfl
    have hb := end_cases C h hy (Merge.anchorable_right C h) rfl
    refine ⟨(a, y), (b, y), hab, hseg, rfl, hopen, ?_, ?_⟩
    · rw [hseg]; exact walkEnd C hP hab rfl hopen ha
    · rw [hseg, Geometry.segment_comm]
      exact walkEnd C hP hab.symm rfl (WalkAx.open_rev hopen) hb
  reach := fun z hz hzv => reach C hz hzv

end FactsChain

end

end Chazelle.Core
