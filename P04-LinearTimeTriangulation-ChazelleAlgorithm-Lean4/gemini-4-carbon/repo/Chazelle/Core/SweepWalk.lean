module

public import Chazelle.Core.SweepLoop

/-!
# The sweep (WP-D), part 12: the walk along the `C₁` part (detection of the next event)

The event loop of the sweep walks the `C₁` part of the walk of `C` (offsets beyond the right
stretch) from event to event.  From a non-cut position `x₀` facing a region `G` with a valid label
`λ` (`Valid`), the next cut key `K` (no cut strictly between) that is not an attachment of a
bracket chord (a chord with both attachments on the `C₁` part: the wall pieces, precomputed
stops) carries a chord of the candidate set `Cand λ`: a piece of a chord of `S₂` touching `λ`, a
chord through the shared vertex, or a chord through the top of `C₂` (`next_event_detected`).

* `off_sub`, `before_faces_of_gap`: the positions just before the next cut key face `G`.
* `Cand`: the candidate chords of the sweep for the label `λ`.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideKey_inj)
open WalkEmbed

namespace Sweep

/-- Offsets of a key moved back by `s`. -/
theorem off_sub {n g k y s : ℝ} (hg0 : 0 ≤ g) (hgn : g < n) (_hk0 : 0 ≤ k) (_hkn : k < n)
    (hy : y = k - s ∨ y = k - s + n) (hy0 : 0 ≤ y) (hyn : y < n) (hs : 0 < s)
    (hso : s < off n g k) : off n g y = off n g k - s := by
  unfold off at *
  rcases hy with rfl | rfl <;> split_ifs at * <;> first | linarith

/-- **The positions just before the next cut key face the current region**: if `x₀` (non-cut,
inside a walk edge) faces `G` and no cut lies strictly between `x₀` and the key `K` (in offsets
from `g`, `o(x₀) < o(K)`), then `G` is faced just before `K`. -/
theorem before_faces_of_gap {M : Model} (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {g : ℝ} (hg0 : 0 ≤ g) (hgn : g < M.W.n) {G : Set Point}
    (hG : G ∈ M.regions F) {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < M.W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ M.IsCut F (p₀ + t₀)) (hfG₀ : M.Faces p₀ t₀ G) {pK : ℕ} {tK : ℝ}
    (hpK : pK < M.W.n) (htK0 : 0 ≤ tK) (htK1 : tK < 1)
    (ho : off M.W.n g (p₀ + t₀) < off M.W.n g (pK + tK))
    (hgap : ∀ x, M.IsCut F x → 0 ≤ x → x < M.W.n →
      ¬ (off M.W.n g (p₀ + t₀) < off M.W.n g x ∧ off M.W.n g x < off M.W.n g (pK + tK))) :
    BeforeFaces M pK tK G := by
  set n := M.W.n with hndef
  set o := off (n : ℝ) g with hodef
  have hn : 0 < n := by omega
  obtain ⟨x0, x1⟩ := Corr.key_mem hp₀ ht₀.1.le ht₀.2
  obtain ⟨k0, k1⟩ := Corr.key_mem hpK htK0 htK1
  have hx0o : 0 ≤ o ((p₀ : ℝ) + t₀) := off_nonneg x0 hgn
  set δ := o ((pK : ℝ) + tK) - o ((p₀ : ℝ) + t₀) with hδ
  have hδ0 : 0 < δ := by linarith
  -- a position just before `K` faces `G`
  have key : ∀ (q : ℕ) (u s : ℝ), q < n → u ∈ Ioo (0 : ℝ) 1 → 0 < s → s < δ →
      ((q : ℝ) + u = (pK : ℝ) + tK - s ∨ (q : ℝ) + u = (pK : ℝ) + tK - s + n) →
      M.Faces q u G := by
    intro q u s hq hu hs0 hs1 hqu
    obtain ⟨y0, y1⟩ := Corr.key_mem hq hu.1.le hu.2
    have hoy : o ((q : ℝ) + u) = o ((pK : ℝ) + tK) - s :=
      off_sub hg0 hgn k0 k1 hqu y0 y1 hs0 (by linarith)
    have hnc : ¬ M.IsCut F ((q : ℝ) + u) := by
      intro hc
      exact hgap _ hc y0 y1 ⟨by rw [hoy]; linarith, by rw [hoy]; linarith⟩
    obtain ⟨U, hU, hfU⟩ := hM.exists_faces_of_not_cut hF hfin hq hu hnc
    have heq : G = U := by
      refine (hM.eq_iff_not_separates hF hfin hG hU hp₀ hq ht₀ hu hnc₀ hnc hfG₀ hfU).2
        fun c hc ⟨qa, qb, sa, sb, hQA, hQB, hQAB, hsep⟩ => ?_
      obtain ⟨a0, a1⟩ := Corr.key_mem hQA.1 hQA.2.1 hQA.2.2.1
      obtain ⟨b0, b1⟩ := Corr.key_mem hQB.1 hQB.2.1 hQB.2.2.1
      have hxa : (p₀ : ℝ) + t₀ ≠ qa + sa := fun h => hnc₀ ⟨c, hc, qa, sa, hQA, h⟩
      have hxb : (p₀ : ℝ) + t₀ ≠ qb + sb := fun h => hnc₀ ⟨c, hc, qb, sb, hQB, h⟩
      have hya : (q : ℝ) + u ≠ qa + sa := fun h => hnc ⟨c, hc, qa, sa, hQA, h⟩
      have hyb : (q : ℝ) + u ≠ qb + sb := fun h => hnc ⟨c, hc, qb, sb, hQB, h⟩
      have hxy : (p₀ : ℝ) + t₀ ≠ q + u := by
        intro h; have := congrArg o h; rw [hoy] at this; linarith
      have hkab := WalkAx.key_ne_of_pt_ne hQA hQB hQAB
      have hsep' := (sep_iff_btw hg0 hgn a0 a1 b0 b1 x0 x1 y0 y1 hkab hxy hxa hxb hya hyb).1 hsep
      have hnot : ∀ {r : ℕ} {v : ℝ}, SideAttach M.W c r v →
          ¬ Btw (o ((p₀ : ℝ) + t₀)) (o ((q : ℝ) + u)) (o ((r : ℝ) + v)) := by
        intro r v hR hb
        obtain ⟨r0, r1⟩ := Corr.key_mem hR.1 hR.2.1 hR.2.2.1
        have hcut : M.IsCut F ((r : ℝ) + v) := ⟨c, hc, r, v, hR, rfl⟩
        unfold Btw at hb
        rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hgap _ hcut r0 r1 ⟨h1, by rw [hoy] at h2; linarith⟩
        · rw [hoy] at h1; linarith
      exact hnot hQA (hsep'.2 (hnot hQB))
    rw [heq]; exact hfU
  refine ⟨min δ 1, lt_min hδ0 one_pos, fun htp s hs0 hs1 hs2 => ?_, fun ht s hs0 hs1 => ?_⟩
  · refine key pK (tK - s) s hpK ⟨by linarith, by linarith⟩ hs0
      (lt_of_lt_of_le hs1 (min_le_left _ _)) (Or.inl (by ring))
  · subst ht
    have hs1' : s < 1 := lt_of_lt_of_le hs1 (min_le_right _ _)
    refine key _ (1 - s) s (Nat.mod_lt _ hn) ⟨by linarith, by linarith⟩ hs0
      (lt_of_lt_of_le hs1 (min_le_left _ _)) ?_
    rcases Nat.eq_zero_or_pos pK with h0 | h0
    · subst h0
      right
      rw [show (0 + n - 1) % n = n - 1 by rw [Nat.mod_eq_of_lt (by omega)]; omega,
        Nat.cast_sub (by omega)]
      push_cast; ring
    · left
      rw [show (pK + n - 1) % n = pK - 1 by
        rw [show pK + n - 1 = (pK - 1) + n by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)], Nat.cast_sub (by omega)]
      push_cast; ring

section Cand

variable (J : Merge.Junction)

/-- **The candidate chords** of the sweep for the label `λ`: pieces of chords of `S₂` touching `λ`
or a region at a side of the slit of `C₂` (the label triple, F2)
(the pieces seen from the endpoints of the exit chords of `λ`), the chords through the shared
vertex (the shared chords), and the chords through the top of `C₂` (the top chords). -/
def Cand (S₂ : Set (Set Point)) (L : Set Point) : Set (Set Point) :=
  {h | h ∈ F₂plus J S₂ ∧ ((∃ c ∈ S₂, h ⊆ c ∧ ∃ V, LabS J S₂ L V ∧
    Chazelle.Chain.TouchesIn (chainModel J.right).D c V) ∨ J.shared ∈ h ∨ J.right.top ∈ h)}

/-- The attachment at offset `0` of the stretch is the shared vertex. -/
theorem sidePt_off_zero (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {p : ℕ} {t : ℝ}
    (hp : p < (chainModel J.whole).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (h0 : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p + t) = 0) :
    sidePt (chainModel J.whole).W p t = J.shared := by
  have hC := corr_right0 J hP hS₂ hS₂f
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < (chainModel J.whole).W.n := by
    exact_mod_cast hC.hg
  obtain ⟨k0, k1⟩ := Corr.key_mem hp ht0 ht1
  have hk := off_inj hg0 hgn k0 k1 hg0 hgn (by rw [h0, off_self])
  obtain ⟨rfl, rfl⟩ := sideKey_inj ht0 ht1 le_rfl zero_lt_one
    (show (p : ℝ) + t = ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) + 0 by rw [add_zero]; exact hk)
  rw [Chazelle.Chain.sidePt_zero]
  have := hC.A1 0 (Nat.zero_le _)
  rw [add_zero, add_zero, Nat.mod_eq_of_lt hC.hg, Nat.mod_eq_of_lt hC.hg'] at this
  rw [this]
  exact right_vtx0 J

/-- The split vertex (offset `rL1` inside the stretch, case G) is the top of `C₂`. -/
theorem sidePt_split (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) (hlt : rL1 J < rL1 J + rL2 J) :
    sidePt (chainModel J.whole).W
      ((6 + tpos J.whole J.m₁ + rL1 J) % (chainModel J.whole).W.n) 0 = J.right.top := by
  have hC := corr_right0 J hP hS₂ hS₂f
  have hδ : 0 < rδ J := by
    by_contra h0
    have := hC.hδ (by omega)
    omega
  rw [Chazelle.Chain.sidePt_zero]
  have := hC.A2 0 (Nat.zero_le _)
  rw [add_zero, add_zero] at this
  rw [this, show 6 + tpos J.right 0 + rL1 J + rδ J = 6 + tpos J.right 0 + (rL1 J + rδ J) by ring]
  exact right_split_top J hδ

/-- **A chord of `F₂⁺` bounding a labelled region, with an attachment in the stretch, is a
candidate**: if `G` has a label and is on the side `σ` of `h`, and `h` has an attachment at an
offset below the length of the stretch, then `h ∈ Cand λ` for a valid `λ`. -/
theorem cand_of_side (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set (Set Point)} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {G L : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (_hL : L ∈ (chainModel J.right).regions S₂) (hvalid : Valid J S₂ G L)
    (hlab : ∃ V₀ ∈ (chainModel J.right).regions S₂, RLabel J S₂ G V₀)
    {h : Set Point} (hh : h ∈ F₂plus J S₂) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hS : SideOf (chainModel J.whole) σ h G) {pB : ℕ} {tB : ℝ}
    (hB : SideAttach (chainModel J.whole).W h pB tB)
    (hBL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pB + tB) <
      ((rL1 J + rL2 J : ℕ) : ℝ)) : h ∈ Cand J S₂ L := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < (chainModel J.whole).W.n := by
    exact_mod_cast hC.hg
  obtain ⟨k0, k1⟩ := Corr.key_mem hB.1 hB.2.1 hB.2.2.1
  have hBpt : sidePt (chainModel J.whole).W pB tB ∈ h := hB.2.2.2.1
  rcases F₂plus_cases J hS₂.2.1 hh with ⟨c, hc, hhc⟩ | ⟨hv, -⟩ | ⟨ht, -⟩
  · rcases (off_nonneg k0 hgn).lt_or_eq with hpos | hzero
    · -- a proper position of the stretch, or the split vertex
      obtain ⟨hpd, hoff⟩ := hC.decomp hB.1 hB.2.1 hB.2.2.1
      set dB := dOf (chainModel J.whole).W.n (6 + tpos J.whole J.m₁) pB with hdB
      rw [hoff] at hpos hBL
      have hdL : dB < rL1 J + rL2 J := by
        have : (dB : ℝ) < ((rL1 J + rL2 J : ℕ) : ℝ) := by linarith [hB.2.1]
        exact_mod_cast this
      rw [← hpd] at hB hBpt
      by_cases hsplit : tB = 0 ∧ dB = rL1 J
      · obtain ⟨rfl, hdr⟩ := hsplit
        rw [hdr] at hB hBpt hdL
        refine ⟨hh, Or.inr (Or.inr ?_)⟩
        rw [← sidePt_split J hP hS₂.2.1 hS₂.1 hdL]
        exact hBpt
      · have hsec : tB = 0 → dB ≠ 0 ∧ dB ≠ rL1 J := by
          intro ht0
          refine ⟨fun h0 => ?_, fun h1 => hsplit ⟨ht0, h1⟩⟩
          rw [h0, ht0] at hpos; simp at hpos
        obtain ⟨V', hV', hVs'⟩ := side_region_exists hC.hM₂ hC.hS hC.hSfin hc hσ
        obtain ⟨V₀, hV₀, hR⟩ := hlab
        have h1 := hvalid.1 V₀ hV₀ hR
        have h2 := label_side_gen2 J hP hS₂ hF hdL hB.2.1 hB.2.2.1 hsec hh hc hhc hB
          hσ hG hV' hV₀ hS hVs' hR
        exact ⟨hh, Or.inl ⟨c, hc, hhc, V', labS_trans J h1 h2,
          touches_of_sideOf J hS₂.2.1 hc hVs'⟩⟩
    · refine ⟨hh, Or.inr (Or.inl ?_)⟩
      rw [← sidePt_off_zero J hP hS₂.2.1 hS₂.1 hB.1 hB.2.1 hB.2.2.1 hzero.symm]
      exact hBpt
  · exact ⟨hh, Or.inr (Or.inl hv)⟩
  · exact ⟨hh, Or.inr (Or.inr ht)⟩

/-- **A labelled region has a label among the regions of `S₂`.** -/
theorem rlabel_region (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {G V : Set Point}
    (hR : RLabel J S₂ G V) : ∃ V' ∈ (chainModel J.right).regions S₂, RLabel J S₂ G V' := by
  have hC := corr_right0 J hP hS₂ hS₂f
  obtain ⟨d, hd, t, ht, hnc, hfG, -⟩ := hR
  set P₂ := (6 + tpos J.right 0 + dq (rL1 J) (rδ J) d) % (chainModel J.right).W.n with hP₂
  have hP₂n : P₂ < (chainModel J.right).W.n := Nat.mod_lt _ hC.n₂_pos
  have hnc₂ : ¬ (chainModel J.right).IsCut S₂ ((P₂ : ℝ) + t) := by
    rintro ⟨c, hc, q, u, hA, hk⟩
    obtain ⟨rfl, rfl⟩ := sideKey_inj hA.2.1 hA.2.2.1 ht.1.le ht.2 hk.symm
    obtain ⟨e, he, -, -, heA⟩ := hC.transfer hd ht.1.le ht.2 (fun h => absurd h ht.1.ne') hc hA
    exact hnc ⟨e, he, _, _, heA, rfl⟩
  obtain ⟨V', hV', hf⟩ := hC.hM₂.exists_faces_of_not_cut hC.hS hC.hSfin hP₂n ht hnc₂
  exact ⟨V', hV', d, hd, t, ht, hnc, hfG, hf⟩

/-- **Detection of the next event** (the loop over the walk).  Let the sweep be at a non-cut
position `x₀` of the `C₁` part facing `G`, with a valid label `λ`, and let `K` be the next cut key
(no cut strictly between), at which no bracket chord is attached (every chord at `K` has an
attachment inside the stretch) and some chord has an attachment strictly inside the stretch at
positive offset.  Then a candidate chord of `λ` is attached at `K`: the sweep's lazy test finds
the event. -/
theorem next_event_detected (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set (Set Point)} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {G L : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hL : L ∈ (chainModel J.right).regions S₂) (hvalid : Valid J S₂ G L)
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < (chainModel J.whole).W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (p₀ + t₀))
    (hfG₀ : (chainModel J.whole).Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀))
    {pK : ℕ} {tK : ℝ} (hpK : pK < (chainModel J.whole).W.n) (htK0 : 0 ≤ tK) (htK1 : tK < 1)
    (hoK : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pK + tK))
    (hgap : ∀ x, (chainModel J.whole).IsCut (F₂plus J S₂) x → 0 ≤ x →
      x < (chainModel J.whole).W.n →
      ¬ (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀) <
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) x ∧
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) x <
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pK + tK)))
    {e : Set Point} (he : e ∈ F₂plus J S₂) (heK : SideAttach (chainModel J.whole).W e pK tK)
    {pB : ℕ} {tB : ℝ} (heB : SideAttach (chainModel J.whole).W e pB tB)
    (heKB : sidePt (chainModel J.whole).W pK tK ≠ sidePt (chainModel J.whole).W pB tB)
    (hB0 : 0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pB + tB))
    (hBL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pB + tB) <
      ((rL1 J + rL2 J : ℕ) : ℝ))
    (hnobr : ∀ e' ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e' pK tK →
      ∃ (pb : ℕ) (tb : ℝ), SideAttach (chainModel J.whole).W e' pb tb ∧
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) <
          ((rL1 J + rL2 J : ℕ) : ℝ)) :
    ∃ h ∈ Cand J S₂ L, SideAttach (chainModel J.whole).W h pK tK := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hM := hC.hM
  have hFs : F₂plus J S₂ ⊆ (chainModel J.whole).Adm := hC.hF
  have hGM : GoodModel (chainModel J.whole) := Or.inl ⟨J.whole, hP, rfl⟩
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < (chainModel J.whole).W.n := by
    exact_mod_cast hC.hg
  set o := off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) with hodef
  obtain ⟨kK0, kK1⟩ := Corr.key_mem hpK htK0 htK1
  -- a chord of `F₂⁺` attached at a cut key of the `C₁` part after `x₀` is attached at `K`
  have hatK : ∀ {h : Set Point} {pz : ℕ} {tz : ℝ}, h ∈ F₂plus J S₂ →
      SideAttach (chainModel J.whole).W h pz tz → o (p₀ + t₀) < o (pz + tz) →
      o (pz + tz) ≤ o (pK + tK) → SideAttach (chainModel J.whole).W h pK tK := by
    intro h pz tz hh hZ h1 h2
    obtain ⟨z0, z1⟩ := Corr.key_mem hZ.1 hZ.2.1 hZ.2.2.1
    rcases h2.lt_or_eq with h2 | h2
    · exact absurd ⟨h1, h2⟩ (hgap _ ⟨h, hh, pz, tz, hZ, rfl⟩ z0 z1)
    · have hk := off_inj hg0 hgn z0 z1 kK0 kK1 h2
      obtain ⟨rfl, rfl⟩ := sideKey_inj hZ.2.1 hZ.2.2.1 htK0 htK1 hk
      exact hZ
  by_cases hlab : ∃ V₀ ∈ (chainModel J.right).regions S₂, RLabel J S₂ G V₀
  · -- a labelled region: the chord at `K` on the side of `G`
    have hW := before_faces_of_gap hM hFs hF.1 hg0 hgn hG hp₀ ht₀ hnc₀ hfG₀ hpK htK0 htK1 hoK
      hgap
    by_cases htie : ∃ e' ∈ F₂plus J S₂, e' ≠ e ∧ SideAttach (chainModel J.whole).W e' pK tK
    · obtain ⟨e', he', hne, hA'⟩ := htie
      have hside : ∃ h ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W h pK tK ∧
          ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ SideOf (chainModel J.whole) σ h G := by
        rcases hM.tie_pair hFs he he' (Ne.symm hne) heK hA' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · obtain ⟨-, hhor, -⟩ := hM.tie_shape hFs he he' heK hA' h1 h2
          have hs := after_side_tie hGM hF he he' hne heK hA' h1 h2 hG
          rcases lt_or_gt_of_ne hhor with hdn | hup
          · exact ⟨e', he', hA', -1, Or.inr rfl, hs.2.1 hdn hW⟩
          · exact ⟨e, he, heK, 1, Or.inl rfl, hs.2.2.2 hup hW⟩
        · obtain ⟨-, hhor, -⟩ := hM.tie_shape hFs he' he hA' heK h2 h1
          have hs := after_side_tie hGM hF he' he (Ne.symm hne) hA' heK h2 h1 hG
          rcases lt_or_gt_of_ne hhor with hdn | hup
          · exact ⟨e, he, heK, -1, Or.inr rfl, hs.2.1 hdn hW⟩
          · exact ⟨e', he', hA', 1, Or.inl rfl, hs.2.2.2 hup hW⟩
      obtain ⟨h, hh, hhK, σ, hσ, hS⟩ := hside
      obtain ⟨pb, tb, hb, hbL⟩ := hnobr h hh hhK
      exact ⟨h, cand_of_side J hP hS₂ hF hG hL hvalid hlab hh hσ hS hb hbL, hhK⟩
    · push Not at htie
      have huniq : ∀ e' ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e' pK tK → e' = e := by
        intro e' he' hA'
        by_contra hne
        exact htie e' he' hne hA'
      have hS : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ SideOf (chainModel J.whole) σ e G := by
        rcases hM.attach_dir (hFs he) heK with hd | hd
        · exact ⟨1, Or.inl rfl, before_side hGM hF he heK huniq (Or.inl ⟨rfl, hd⟩) hG hW⟩
        · exact ⟨-1, Or.inr rfl, before_side hGM hF he heK huniq (Or.inr ⟨rfl, hd⟩) hG hW⟩
      obtain ⟨σ, hσ, hS⟩ := hS
      exact ⟨e, cand_of_side J hP hS₂ hF hG hL hvalid hlab he hσ hS heB hBL, heK⟩
  · -- an unlabelled region
    have hU : ∀ V, ¬ RLabel J S₂ G V := by
      intro V hR
      exact hlab (rlabel_region J hP hS₂.2.1 hS₂.1 hR)
    rcases (detect_valid J hP hS₂ hF hG hL hvalid hp₀ ht₀ hnc₀ hfG₀ ho₀).2 hU with
      ⟨ρ, -, hZ, hhZ, pz, tz, hZA, htrack, hzpos, hfinal⟩ | hT
    · have hnot : ¬ (o (pz + tz) = 0 ∨ o (pK + tK) < o (pz + tz)) := fun h =>
        hfinal e he pK tK pB tB heK heB heKB hoK h hBL hB0.ne'
      push Not at hnot
      obtain ⟨hz0, hzK⟩ := hnot
      rcases hzpos with h | ⟨-, hz⟩
      · exact absurd h hz0
      have hZK := hatK hhZ hZA hz hzK
      refine ⟨hZ, ⟨hhZ, ?_⟩, hZK⟩
      rcases htrack with ⟨c, hc, hZc, V', -, hrel, hVs⟩ | hk | hk
      · refine Or.inl ⟨c, hc, hZc, V', ?_, touches_of_sideOf J hS₂.2.1 hc hVs⟩
        rcases hrel with rfl | ⟨-, h⟩
        · exact Or.inl rfl
        · exact Or.inr h
      · exact Or.inr (Or.inl hk)
      · exact Or.inr (Or.inr hk)
    · obtain ⟨e₁, e₂, d, pb, pb', tb, tb', ρ, he₁, he₂, hne, hd0, hd, hA₁, hA₂, hB₁, hB₂, hBne₁,
        hBne₂, hout₁, hout₂, hρ, hS₁, hS₂', ht₁, ht₂⟩ := hT
      set W := (chainModel J.whole).W with hWdef
      set A := (6 + tpos J.whole J.m₁ + d) % W.n with hAdef
      obtain ⟨-, hy₁, -⟩ := hM.attach_seg (hFs he₁) hA₁ hB₁ (Ne.symm hBne₁)
      obtain ⟨-, hy₂, -⟩ := hM.attach_seg (hFs he₂) hA₂ hB₂ (Ne.symm hBne₂)
      have hx₁ : (sidePt W pb tb).1 ≠ (sidePt W A 0).1 :=
        fun h => hBne₁ (Geometry.point_ext h hy₁.symm)
      have hx₂ : (sidePt W pb' tb').1 ≠ (sidePt W A 0).1 :=
        fun h => hBne₂ (Geometry.point_ext h hy₂.symm)
      have hopp := tie_opposite hM hFs he₁ he₂ hne hA₁ hA₂ hB₁.2.2.2.1 hB₂.2.2.2.1 hx₁ hx₂
      obtain ⟨θ, hθ, hori⟩ := exists_sign hρ (sub_ne_zero.2 (Ne.symm hx₁))
      have hθρ : θ * ρ * (θ * ρ) = 1 := by
        rcases hθ with rfl | rfl <;> rcases hρ with rfl | rfl <;> norm_num
      have hori' : 0 < -θ * ρ * ((sidePt W A 0).1 - (sidePt W pb' tb').1) := by
        have e1 : -θ * ρ * ((sidePt W A 0).1 - (sidePt W pb' tb').1) =
            θ * ρ * ((sidePt W pb' tb').1 - (sidePt W A 0).1) := by ring
        rw [e1]
        have hprod : 0 < (θ * ρ * ((sidePt W A 0).1 - (sidePt W pb tb).1)) *
            (θ * ρ * ((sidePt W pb' tb').1 - (sidePt W A 0).1)) := by
          have e2 : (θ * ρ * ((sidePt W A 0).1 - (sidePt W pb tb).1)) *
              (θ * ρ * ((sidePt W pb' tb').1 - (sidePt W A 0).1)) =
              (θ * ρ * (θ * ρ)) * (-(((sidePt W pb tb).1 - (sidePt W A 0).1) *
                ((sidePt W pb' tb').1 - (sidePt W A 0).1))) := by ring
          rw [e2, hθρ, one_mul]
          linarith
        exact pos_of_mul_pos_right hprod hori.le
      have hAL : o ((A : ℝ) + 0) < ((rL1 J + rL2 J : ℕ) : ℝ) := by
        have hoA : o ((A : ℝ) + 0) = d + 0 := hC.off_M hd le_rfl zero_lt_one
        rw [hoA]
        have : (d : ℝ) + 1 ≤ ((rL1 J + rL2 J : ℕ) : ℝ) := by exact_mod_cast hd
        linarith
      -- the forward chord of the tie and its far attachment
      obtain ⟨ff, hff, pf, tf, hfF, htf, hfe, hclear⟩ : ∃ ff ∈ F₂plus J S₂, ∃ (pf : ℕ) (tf : ℝ),
          SideAttach W ff pf tf ∧ J.right.top ∈ ff ∧
          (o (pf + tf) = 0 ∨ (((rL1 J + rL2 J : ℕ) : ℝ) ≤ o (pf + tf) ∧
            o (p₀ + t₀) < o (pf + tf))) ∧
          ∀ e ∈ F₂plus J S₂, ∀ (pw : ℕ) (tw : ℝ) (pb : ℕ) (tb : ℝ),
            SideAttach W e pw tw → SideAttach W e pb tb → sidePt W pw tw ≠ sidePt W pb tb →
            o (p₀ + t₀) < o (pw + tw) → (o (pf + tf) = 0 ∨ o (pw + tw) < o (pf + tf)) →
            o (pb + tb) < ((rL1 J + rL2 J : ℕ) : ℝ) → o (pb + tb) ≠ 0 → False := by
        rcases hθ with rfl | rfl
        · obtain ⟨h1, h2⟩ := bracket_tie J hP hS₂ hF hρ hG he₂ he₁ hne hAL hA₂ hA₁ hB₂ hB₁
            (Ne.symm hBne₂) (Ne.symm hBne₁) hS₂' hS₁ (by linarith) hori hout₂ hout₁ hp₀ ht₀ hnc₀
            hfG₀ ho₀
          exact ⟨e₁, he₁, pb, tb, hB₁, ht₁, h1, h2⟩
        · obtain ⟨h1, h2⟩ := bracket_tie J hP hS₂ hF hρ hG he₁ he₂ (Ne.symm hne) hAL hA₁ hA₂
            hB₁ hB₂ (Ne.symm hBne₁) (Ne.symm hBne₂) hS₁ hS₂' hori (by linarith) hout₁ hout₂ hp₀
            ht₀ hnc₀ hfG₀ ho₀
          exact ⟨e₂, he₂, pb', tb', hB₂, ht₂, h1, h2⟩
      have hnot : ¬ (o (pf + tf) = 0 ∨ o (pK + tK) < o (pf + tf)) := fun h =>
        hclear e he pK tK pB tB heK heB heKB hoK h hBL hB0.ne'
      push Not at hnot
      obtain ⟨hz0, hzK⟩ := hnot
      rcases hfe with h | ⟨-, hz⟩
      · exact absurd h hz0
      exact ⟨ff, ⟨hff, Or.inr (Or.inr htf)⟩, hatK hff hfF hz hzK⟩

/-! ## The loop invariant of the RAM -/

omit J in
/-- **No cut between two positions**: two non-cut positions inside walk edges with no cut strictly
between them (in offsets from `g`) face the same region. -/
theorem same_region_of_gap {M : Model} (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {g : ℝ} (hg0 : 0 ≤ g) (hgn : g < M.W.n) {U U' : Set Point}
    (hU : U ∈ M.regions F) (hU' : U' ∈ M.regions F) {p p' : ℕ} {t t' : ℝ} (hp : p < M.W.n)
    (hp' : p' < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (hc : ¬ M.IsCut F (p + t)) (hc' : ¬ M.IsCut F (p' + t')) (hf : M.Faces p t U)
    (hf' : M.Faces p' t' U') (hlt : off M.W.n g (p + t) < off M.W.n g (p' + t'))
    (hgap : ∀ x, M.IsCut F x → 0 ≤ x → x < M.W.n →
      ¬ (off M.W.n g (p + t) < off M.W.n g x ∧ off M.W.n g x < off M.W.n g (p' + t'))) :
    U = U' := by
  refine (hM.eq_iff_not_separates hF hfin hU hU' hp hp' ht ht' hc hc' hf hf').2
    fun c hcF ⟨qa, qb, sa, sb, hQA, hQB, hQAB, hsep⟩ => ?_
  obtain ⟨x0, x1⟩ := Corr.key_mem hp ht.1.le ht.2
  obtain ⟨y0, y1⟩ := Corr.key_mem hp' ht'.1.le ht'.2
  obtain ⟨a0, a1⟩ := Corr.key_mem hQA.1 hQA.2.1 hQA.2.2.1
  obtain ⟨b0, b1⟩ := Corr.key_mem hQB.1 hQB.2.1 hQB.2.2.1
  have hxa : (p : ℝ) + t ≠ qa + sa := fun h => hc ⟨c, hcF, qa, sa, hQA, h⟩
  have hxb : (p : ℝ) + t ≠ qb + sb := fun h => hc ⟨c, hcF, qb, sb, hQB, h⟩
  have hya : (p' : ℝ) + t' ≠ qa + sa := fun h => hc' ⟨c, hcF, qa, sa, hQA, h⟩
  have hyb : (p' : ℝ) + t' ≠ qb + sb := fun h => hc' ⟨c, hcF, qb, sb, hQB, h⟩
  have hxy : (p : ℝ) + t ≠ p' + t' := by
    intro h; rw [h] at hlt; exact lt_irrefl _ hlt
  have hkab := WalkAx.key_ne_of_pt_ne hQA hQB hQAB
  have hsep' := (sep_iff_btw hg0 hgn a0 a1 b0 b1 x0 x1 y0 y1 hkab hxy hxa hxb hya hyb).1 hsep
  have hnot : ∀ {r : ℕ} {v : ℝ}, SideAttach M.W c r v →
      ¬ Btw (off M.W.n g ((p : ℝ) + t)) (off M.W.n g ((p' : ℝ) + t')) (off M.W.n g ((r : ℝ) + v)) := by
    intro r v hR hb
    obtain ⟨r0, r1⟩ := Corr.key_mem hR.1 hR.2.1 hR.2.2.1
    have hcut : M.IsCut F ((r : ℝ) + v) := ⟨c, hcF, r, v, hR, rfl⟩
    unfold Btw at hb
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hgap _ hcut r0 r1 ⟨h1, h2⟩
    · linarith
  exact hnot hQA (hsep'.2 (hnot hQB))

end Cand

end Sweep

end

end Chazelle.Core
