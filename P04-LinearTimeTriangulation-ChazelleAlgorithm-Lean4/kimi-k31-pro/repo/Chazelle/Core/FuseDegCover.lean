module

public import Chazelle.Core.FuseDegChain
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# The degree of the revised fusion, part 5: the pieces of the walk and the classification

* `side_two_pieces`: the stretch of the walk of `C` along one side chain is covered by (at most)
  two pieces, starting at a copy of the shared vertex or of the top of the side chain.
* `glue_subset_aug`: the glue chords are augmented chords of `C`.
* `classify`: an exit chord of `R` of the fusion, attached inside a piece next to a position
  faced by `R`, with all attachments on counted edges and not through the shared vertex, is of
  type (I) (a chord of `Sᵢ` is attached at the side position) or crosses out of the piece.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft TouchesIn freeIn
  regionsIn)
open Chazelle.Geometry (lerp)
open WalkEmbed FuseMath

namespace FuseDeg

variable (J : Merge.Junction)

/-- **The points of counted walk edges of a chain model are on the chain.** -/
theorem counted_mem_set (C : Chain) {p : ℕ} (hp : p < (chainModel C).W.n)
    (hc : (chainModel C).counted p) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sidePt (chainModel C).W p t ∈ C.set := by
  obtain ⟨h6, h2m⟩ : 6 ≤ p ∧ p < 2 * C.m + 6 := hc
  obtain ⟨i, rfl⟩ : ∃ i, p = i + 6 := ⟨p - 6, by omega⟩
  have hi : i < 2 * C.m := by omega
  rw [cm_W]
  unfold sidePt
  rw [C.sideWalk_next_tour _ hi, C.sideWalk_vtx_tour _ hi.le, C.sideWalk_vtx_tour _ (by omega)]
  unfold Chain.sideTour
  rcases C.sideTour_step C.sideBeta i with h | h
  · exact C.sideLerp_mem_set (Or.inl h) (C.sideIdx_le _ i) (C.sideIdx_le _ _) ht0 ht1
  · exact C.sideLerp_mem_set (Or.inr h) (C.sideIdx_le _ i) (C.sideIdx_le _ _) ht0 ht1

/-- **A chord containing an attached chord from its point is attached there too.** -/
theorem attach_sup {W : Polygon} {f c : Set Point} {p : ℕ} {t : ℝ} (hA : SideAttach W f p t)
    {e b : Point} (hfe : f = Chazelle.segment (sidePt W p t) e) (he : e ≠ sidePt W p t)
    (hcb : c = Chazelle.segment (sidePt W p t) b) (hec : e ∈ c) : SideAttach W c p t := by
  obtain ⟨hp, ht, ht1, -, r, hr, hl⟩ := hA
  set q := sidePt W p t with hq
  have hd  := dist_pos.2 he
  refine ⟨hp, ht, ht1, by rw [hcb]; exact Geometry.left_mem_segment _ _, min r (dist e q),
    lt_min hr hd, fun x hx hxq hxd => hl x ?_ hxq (lt_of_lt_of_le hxd (min_le_left _ _))⟩
  have hxd' : dist x q < dist e q := lt_of_lt_of_le hxd (min_le_right _ _)
  have hdist : ∀ u : ℝ, 0 ≤ u → dist (lerp q b u) q = u * dist b q := by
    intro u hu
    rw [dist_comm, dist_eq_norm, dist_eq_norm]
    have : q - lerp q b u = u • (q - b) := by
      apply Geometry.point_ext <;> simp [lerp] <;> ring
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu, norm_sub_rev]
  rw [hcb] at hx hec
  obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
  obtain ⟨se, hse0, hse1, hese⟩ := Geometry.mem_segment_iff_lerp.1 hec
  rw [hese] at hxd' hd
  rw [hdist s hs0, hdist se hse0] at hxd'
  rw [hdist se hse0] at hd
  have hbq : 0 < dist b q := by
    rcases (dist_nonneg : 0 ≤ dist b q).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hd; exact absurd hd (lt_irrefl _)
  have hsse  := lt_of_mul_lt_mul_right hxd' hbq.le
  have hse  := lt_of_le_of_lt hs0 hsse
  rw [hfe, hese]
  refine Geometry.mem_segment_iff_lerp.2 ⟨s / se, div_nonneg hs0 hse.le,
    (div_le_one hse).2 hsse.le, ?_⟩
  apply Geometry.point_ext <;> simp [Geometry.lerp_fst, Geometry.lerp_snd] <;>
    field_simp <;> ring

/-- An agreement with a side walk, with the lengths in range, is a piece. -/
theorem pieceAt_of_agree {C' : Chain} (hC'P : C'.P = J.P) {g g' L : ℕ}
    (hg : g < (chainModel J.whole).W.n) (hg' : g' < (chainModel C').W.n)
    (hL : L < (chainModel J.whole).W.n) (hL' : L ≤ (chainModel C').W.n)
    (hA : Agree (chainModel J.whole).W (chainModel C').W g g' L) : PieceAt J C' g g' L := by
  have hR := radius_of_P J hC'P
  refine ⟨hg, hg', hL, hL', hA, fun d hd hc => ?_⟩
  rw [counted_iff_box _ (Nat.mod_lt _ (by omega))] at hc
  rw [counted_iff_box _ (Nat.mod_lt _ (by omega))]
  rw [mod_succ_mod] at hc ⊢
  rw [hA d hd.le, hA (d + 1) hd] at hc
  rwx [hR]

/-- The offset from a later base of a stretch. -/
theorem dOf_shift {n g s p : ℕ} (hg : g < n) (hp : p < n) (hs : s ≤ dOf n g p) :
    dOf n ((g + s) % n) p = dOf n g p - s := by
  have h1 := off_shift hg hp hs le_rfl one_pos
  have h2 := off_key' (g := (g + s) % n) (Nat.mod_lt _ (by omega)) hp le_rfl one_pos
  rw [h1, add_zero, add_zero] at h2
  exact_mod_cast h2.symm

/-- **Two pieces along one side**: the stretch of the walk of `C` read from the copy of the shared
vertex left towards a side chain `C'` is covered by two pieces (equal, unless only the box of
`C'` lies inside the stretch), each starting at a copy of the shared vertex or of the top of
`C'`. -/
theorem side_two_pieces (_hP : J.P.Simple) {C' : Chain} (hC'P : C'.P = J.P)
    {J₀ J₀' ℓ : ℕ} (hT : ∀ e, e ≤ ℓ → tourV J.whole J₀ e = tourV C' J₀' e)
    (hv0 : tourV J.whole J₀ 0 = sharedV J) (hℓ' : ℓ ≤ 2 * C'.m) (hℓ : ℓ < 2 * J.whole.m)
    (hbox : 2 * J.whole.m - tpos J.whole J₀ < ℓ →
      2 * C'.m - tpos C' J₀' = 2 * J.whole.m - tpos J.whole J₀) :
    ∃ gA gA' LA gB gB' LB : ℕ, PieceAt J C' gA gA' LA ∧ PieceAt J C' gB gB' LB ∧
      ((chainModel J.whole).W.vtx gA = J.shared ∨ (chainModel J.whole).W.vtx gA = C'.top) ∧
      ((chainModel J.whole).W.vtx gB = J.shared ∨ (chainModel J.whole).W.vtx gB = C'.top) ∧
      ∀ p : ℕ, p < (chainModel J.whole).W.n →
        dOf (chainModel J.whole).W.n (6 + tpos J.whole J₀) p <
          (if 2 * J.whole.m - tpos J.whole J₀ < ℓ then ℓ + 7 else ℓ) →
        dOf (chainModel J.whole).W.n gA p < LA ∨ dOf (chainModel J.whole).W.n gB p < LB := by
  set C := J.whole with hC
  set W := (chainModel C).W with hW
  set W' := (chainModel C').W with hW'
  have hR := radius_of_P J hC'P
  have hn := cm_n C
  have hn' := cm_n C'
  set τ := tpos C J₀ with hτ
  set τ' := tpos C' J₀' with hτ'
  have hτlt := tpos_lt C J₀
  have hτ'lt := tpos_lt C' J₀'
  set g := 6 + τ with hg_def
  set g' := 6 + τ' with hg'_def
  have hg : g < W.n := by rwo [hn]
  have hg' : g' < W'.n := by rwo [hn']
  set s := 2 * C.m - τ with hs_def
  set s' := 2 * C'.m - τ' with hs'_def
  have hstart : W.vtx g = J.shared := by
    have := walk_tour C J₀ 0 (by omega)
    rw [add_zero, Nat.mod_eq_of_lt hg] at this
    rwr [this, hv0]
  by_cases hsl : s < ℓ
  · -- case Sh
    have hss  := (hbox hsl).symm
    have hA := agree_Sh hT hR.symm hℓ.le hℓ' hss hsl
    have hpc := pieceAt_of_agree J hC'P hg hg' (by rwo [hn]) (by rwo [hn']) hA
    refine ⟨g, g', ℓ + 7, g, g', ℓ + 7, hpc, hpc, Or.inl hstart, Or.inl hstart,
      fun p _ hin => Or.inl ?_⟩
    rw [ite_eq_left hsl] at hin; exact hin
  push Not at hsl
  by_cases hsl' : ℓ ≤ s'
  · -- case N
    have hA := agree_N hT hsl hsl'
    have hpc := pieceAt_of_agree J hC'P hg hg' (by rwo [hn]) (by rwo [hn']) hA
    refine ⟨g, g', ℓ, g, g', ℓ, hpc, hpc, Or.inl hstart, Or.inl hstart, fun p _ hin => Or.inl ?_⟩
    rw [ite_eq_right (not_lt.2 hsl)] at hin; exact hin
  -- case G
  push Not at hsl'
  have hA1 := agree_G1 hT hsl hsl'
  have hA2 := agree_G2 hT hℓ' hsl hsl'
  have hpc1 := pieceAt_of_agree J hC'P hg hg' (by rwo [hn]) (by rwo [hn']) hA1
  have hpc2 := pieceAt_of_agree J hC'P (Nat.mod_lt _ (by rwo [hn]))
    (Nat.mod_lt _ (by rwo [hn']))
    (by rwo [hn]) (by rwo [hn']) hA2
  have hpt : W.vtx ((g + s') % W.n) = C'.top := by
    rw [hA1 s' le_rfl]
    have := walk_box C' J₀' 0 (by omega)
    rw [add_zero] at this
    exact this
  refine ⟨g, g', s', _, _, ℓ - s', hpc1, hpc2, Or.inl hstart, Or.inr hpt, fun p hp hin => ?_⟩
  rw [ite_eq_right (not_lt.2 hsl)] at hin
  by_cases hD : dOf W.n g p < s'
  · exact Or.inl hD
  · push Not at hD
    right
    rw [dOf_shift hg hp hD]
    omega

/-- **The glue chords are augmented chords of `C`.** -/
theorem glue_subset_aug (hgen : SharedGeneric J) : glueChords J ⊆ Merge.augChords J.whole := by
  rintro d (hd | ⟨hext, hfree, rfl⟩)
  · exact Merge.chords_subset_augChords _ (topChords_subset_chords J hd)
  · obtain ⟨hτ0, hτ1, hnear, hnf⟩ := cap_param J hgen hext
    have hm₁ : 1 ≤ J.m₁ := J.one_le_m₁
    have hm₂ : 1 ≤ J.m₂ := J.one_le_m₂
    have hwm : J.whole.m = J.m₁ + J.m₂ := rfl
    have hmem : capOrigin J ∈ J.whole.set := by
      unfold capOrigin
      generalize (((capNear J).2 - (sharedV J).2) / ((capFar J).2 - (sharedV J).2)) = τ
        at hτ0 hτ1 ⊢
      rcases hnf with ⟨-, hf⟩ | ⟨-, hf⟩
      · rw [hf]
        exact J.whole.sideLerp_mem_set (a := J.m₁) (b := J.m₁ + 1) (Or.inl rfl) (by omega)
          (by omega) hτ0.le hτ1.le
      · rw [hf]
        exact J.whole.sideLerp_mem_set (a := J.m₁) (b := J.m₁ - 1) (Or.inr (by omega))
          (by omega) (by omega) hτ0.le hτ1.le
    have hy : (capOrigin J).2 ≤ J.whole.top.2 := by
      have : (capOrigin J).2 = (capNear J).2 := by
        unfold capOrigin
        simp [Geometry.lerp_snd]
        exact hnear.symm
      rw [this]
      rcases hnf with ⟨hn, -⟩ | ⟨hn, -⟩
      · rw [hn]; exact J.whole.vertex_snd_le_top (by omega)
      · rw [hn]; exact J.whole.vertex_snd_le_top (by omega)
    have hdir : capDir J = 1 ∨ capDir J = -1 := by
      unfold capDir; split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
    exact Merge.shoot_mem_augChords J.whole hy (fun h => J.whole.not_mem_set_of_mem_dom h hmem) hdir hfree


/-- **Classification of the exit chords faced inside a piece**: a chord of the fusion with a
parent chord `c` in `Sᵢ ∪ Sⱼ` (containing it and one of whose ends it contains), with all its
attachments on counted edges and not through the shared vertex, attached at an offset in
`(0, L)` of a piece of side `i` next to which `R` is faced, is of type (I) or crossing. -/
theorem classify (hP : J.P.Simple) {C' : Chain} {Q : Polygon} {Si Sj S' : Set (Set Point)}
    (hS : SideOK J C' Q Si S') {g g' L : ℕ} (hpc : PieceAt J C' g g' L)
    (hjend : ∀ c ∈ Sj, ∀ q : Point, (q = Merge.lend c ∨ q = Merge.rend c) → q ∈ C'.set →
      q = J.shared)
    (hjnd : ∀ c ∈ Sj, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom)
    {R : Set Point} {f : Set Point} (hf : f ∈ exits (chainModel J.whole) S' R)
    (hpar : ∃ c ∈ Si ∪ Sj, f ⊆ c ∧ (Merge.lend c ∈ f ∨ Merge.rend c ∈ f))
    (hcnt : ∀ (pb : ℕ) (tb : ℝ), SideAttach (chainModel J.whole).W f pb tb →
      (chainModel J.whole).counted pb)
    (hsh : J.shared ∉ f) {d : ℕ} {t : ℝ} (hd : d < L) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hdt : 0 < (d : ℝ) + t)
    (hA : SideAttach (chainModel J.whole).W f ((g + d) % (chainModel J.whole).W.n) t)
    (hadj : Adj (chainModel J.whole) S' R ((g + d) % (chainModel J.whole).W.n) t) :
    f ∈ TypeI J C' Si S' R g g' L ∨ f ∈ CrossX (chainModel J.whole) S' R g L := by
  obtain ⟨c, hc, hfc, hnear⟩ := hpar
  have hpc' := hpc
  obtain ⟨hg, hg', hLn, hLn', hAg, hcntP⟩ := hpc
  set M := chainModel J.whole with hMdef
  set M' := chainModel C' with hM'def
  have hM : WalkAx M := walkAx_chainModel hP
  have hM' : WalkAx M' := walkAx_chainModel hS.simple
  have hn : 0 < M.W.n := by omega
  have hn' : 0 < M'.W.n := by omega
  have hdt' : t = 0 → 1 ≤ d := fun h => by
    rw [h, add_zero] at hdt; exact_mod_cast hdt
  have hq' : sidePt M.W ((g + d) % M.W.n) t = sidePt M'.W ((g' + d) % M'.W.n) t :=
    hAg.sidePt_eq hd t
  have hAf' : SideAttach M'.W f ((g' + d) % M'.W.n) t :=
    (hAg.sideAttach_iff hn hn' hd hdt' f).1 hA
  have hfA := hS.adm hf.1
  rcases hc with hci | hcj
  · left
    refine ⟨hf.1, d, t, hd, ht0, ht1, hdt, hA, hadj, c, hci, ?_⟩
    set q := sidePt M'.W ((g' + d) % M'.W.n) t with hq
    have hqf : q ∈ f := hAf'.2.2.2.1
    have hqD : q ∉ M.D := by rw [← hq']; exact hM.trace _ hA.1 t ht0 ht1.le
    have hqD' : q ∉ C'.dom := hM'.trace _ hAf'.1 t ht0 ht1.le
    obtain ⟨e, hfe, he, -, -, -⟩ := chord_through hM hfA hqf hqD
    obtain ⟨y, a, b, hH, -, hceq, -, -⟩ := Merge.augChords_spec (hS.fam.2.1 hci)
    have hqc := hfc hqf
    rw [hceq] at hqc
    obtain ⟨hq2, hqa, hqb⟩ := hqc
    have hseg := FactsChain.hseg_eq_segment (y := y) hH.lt.le
    have hec : e ∈ c := hfc (by rw [hfe]; exact Geometry.right_mem_segment _ _)
    rcases hqa.lt_or_eq with h1 | h1
    · rcases hqb.lt_or_eq with h2 | h2
      · exact absurd (by rw [show q = (q.1, y) from Prod.ext rfl hq2]; exact hH.open_mem q.1 h1 h2)
          hqD'
      · have hqe : q = ((b, y) : Point) := Prod.ext h2 hq2
        refine attach_sup hAf' hfe he (b := ((a, y) : Point)) ?_ hec
        rw [hceq, hseg, Geometry.segment_comm, ← hqe]
    · have hqe : q = ((a, y) : Point) := Prod.ext h1.symm hq2
      refine attach_sup hAf' hfe he (b := ((b, y) : Point)) ?_ hec
      rw [hceq, hseg, ← hqe]
  · obtain ⟨pb, tb, hB, hBne⟩ := hM.other_attach hfA hA
    by_cases hX : off M.W.n g (pb + tb) = 0 ∨ (L : ℝ) ≤ off M.W.n g (pb + tb)
    · exact Or.inr ⟨hf, d, t, hd, ht0, ht1, hdt, hA, hadj, pb, tb, hB, hBne, hX⟩
    exfalso
    push Not at hX
    set dB := dOf M.W.n g pb with hdB
    have hpb : (g + dB) % M.W.n = pb := add_dOf hg hB.1
    have hoB : off M.W.n g (pb + tb) = dB + tb := off_key' hg hB.1 hB.2.1 hB.2.2.1
    have hdBL : dB < L := by
      have : (dB : ℝ) < L := by rw [hoB] at hX; linarith [hX.2, hB.2.1]
      exact_mod_cast this
    have hB' : SideAttach M.W f ((g + dB) % M.W.n) tb := by rwx [hpb]
    -- the two attachment points of `f` are on `C'`
    have hmemB : sidePt M.W pb tb ∈ C'.set := by
      rw [← hpb, hAg.sidePt_eq hdBL tb]
      exact counted_mem_set C' (Nat.mod_lt _ hn') (hcntP dB hdBL (by rw [hpb]; exact hcnt _ _ hB))
        hB.2.1 hB.2.2.1.le
    have hmemA : sidePt M.W ((g + d) % M.W.n) t ∈ C'.set := by
      rw [hq']
      exact counted_mem_set C' (Nat.mod_lt _ hn') (hcntP d hd (hcnt _ _ hA)) ht0 ht1.le
    -- the near end of `f` is one of them
    obtain ⟨u, w, -, hends⟩ := seg_end hM hfA
    have hA0 := hends _ hA.2.2.2.1 (hM.trace _ hA.1 t ht0 ht1.le)
    have hB0 := hends _ hB.2.2.2.1 (hM.trace _ hB.1 tb hB.2.1 hB.2.2.1.le)
    obtain ⟨q₀, hq₀, hq₀f⟩ : ∃ q₀, (q₀ = Merge.lend c ∨ q₀ = Merge.rend c) ∧ q₀ ∈ f := by
      rcases hnear with h | h
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
    have hq₀D : q₀ ∉ M.D := by
      rcases hq₀ with rfl | rfl
      · exact (hjnd c hcj).1
      · exact (hjnd c hcj).2
    have hq0 := hends _ hq₀f hq₀D
    have hq₀C : q₀ ∈ C'.set := by
      rcases hA0 with h1 | h1 <;> rcases hB0 with h2 | h2 <;> rcases hq0 with h3 | h3
      all_goals first
        | (rwx [h3, ← h1])
        | (rwx [h3, ← h2])
        | (exfalso; exact hBne (h2.trans h1.symm))
    exact hsh (hjend c hcj q₀ hq₀ hq₀C ▸ hq₀f)

end FuseDeg

end

end Chazelle.Core
