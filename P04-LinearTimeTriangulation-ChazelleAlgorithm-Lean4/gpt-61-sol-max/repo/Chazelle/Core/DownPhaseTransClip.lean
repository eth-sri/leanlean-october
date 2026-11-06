module

public import Chazelle.Core.DownPhaseTransDom

/-!
# WP-M (T, part 3): clipping the chords of the top chain to the interior of `Q`

For the top chain `C` of a simple polygon `Q` whose last edge `e_{n-1}` is not horizontal:
* `cross_sides`: a horizontal line crossing an open non-horizontal edge has the interior on
  exactly one side of the crossing point;
* `sub_chord`: through every interior point of a chain chord there is an interior chord of `Q`
  inside it;
* `one_piece`: a chain chord contains at most one interior chord of `Q` (it meets `∂Q` at most
  once, on `e_{n-1}`, and crosses there);
* `pieces F₀`, the interior chords inside chords of `F₀`, form a chord family of the interior
  model with at most as many chords as `F₀` (`chordFamily_pieces`, `ncard_pieces_le`).
-/

namespace Chazelle.Core

namespace Trans

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (sidePt IsHChordIn)
open Chazelle.Geometry (lerp)
open Chazelle.Jordan (offset nrm)
open Chazelle.Visibility (hseg)

/-- **Crossing an open non-horizontal edge horizontally**: for small `ε`, exactly one of the two
horizontal neighbours of a point of the open edge is in the filled polygon. -/
theorem cross_sides {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hh : (P.vtx i).2 ≠ (P.vtx ((i + 1) % P.n)).2) :
    ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
      ((((lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t₀).1 - ε,
        (lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t₀).2) : Point) ∈ P.filled ↔
      (((lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t₀).1 + ε,
        (lerp (P.vtx i) (P.vtx ((i + 1) % P.n)) t₀).2) : Point) ∉ P.filled) := by
  set u := P.vtx i with hu
  set v := P.vtx ((i + 1) % P.n) with hv
  set w := lerp u v t₀ with hw
  obtain ⟨r, hr, hstrip⟩ := Chazelle.Jordan.strip hP hi ht₀
  have hcont1 : Continuous (fun δ : ℝ => offset u v t₀ δ) := by unfold offset; fun_prop
  have hcont2 : Continuous (fun δ : ℝ => offset u v t₀ (-δ)) := by unfold offset; fun_prop
  have h0 : offset u v t₀ 0 = w := by simp_all
  have h0' : offset u v t₀ (-0) = w := by simp_all
  have hev1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset u v t₀ δ ∈ ball w r :=
    (hcont1.tendsto 0).mono_left nhdsWithin_le_nhds (by rw [h0]; exact ball_mem_nhds w hr)
  have hev2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset u v t₀ (-δ) ∈ ball w r :=
    (hcont2.tendsto 0).mono_left nhdsWithin_le_nhds (by rw [h0']; exact ball_mem_nhds w hr)
  obtain ⟨δ, hδs, hδ1, hδ2, hδ0⟩ := ((Chazelle.Jordan.edge_sides hP hi ht₀).and
    (hev1.and (hev2.and self_mem_nhdsWithin))).exists
  
  have huv : u ≠ v := fun e => hh (by rw [e])
  have hsq := Chazelle.Jordan.sqLen_pos huv
  -- the two half-disks
  set Hp := ball w r ∩ {x | 0 < (1 : ℝ) * Chazelle.det u v x} with hHp
  set Hm := ball w r ∩ {x | 0 < (-1 : ℝ) * Chazelle.det u v x} with hHm
  have hpre : ∀ σ : ℝ, IsPreconnected (ball w r ∩ {x | 0 < σ * Chazelle.det u v x}) := fun σ =>
    ((convex_ball w r).inter (Chazelle.Jordan.convex_det_pos u v σ)).isPreconnected
  have hsub : ∀ σ : ℝ, ball w r ∩ {x | 0 < σ * Chazelle.det u v x} ⊆ P.boundaryᶜ := fun σ =>
    Chazelle.Jordan.side_subset_compl P hstrip σ
  have hL : offset u v t₀ δ ∈ Hp := ⟨hδ1, by
    show 0 < 1 * Chazelle.det u v _
    rw [Chazelle.Jordan.det_offset]; nlinarith⟩
  have hR : offset u v t₀ (-δ) ∈ Hm := ⟨hδ2, by
    show 0 < -1 * Chazelle.det u v _
    rw [Chazelle.Jordan.det_offset]; nlinarith⟩
  have hdw : Chazelle.det u v w = 0 := by
    rw [hw]; exact Chazelle.Geometry.det_eq_zero_of_mem_segment
      (Chazelle.Geometry.lerp_mem_segment _ _ ht₀.1.le ht₀.2.le)
  refine ⟨r, hr, fun ε hε0 hεr => ?_⟩
  have hdist : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ((w.1 + σ * ε, w.2) : Point) ∈ ball w r := by
    intro σ hσ
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
      show w.1 + σ * ε - w.1 = σ * ε by ring, abs_mul, abs_of_pos hε0]
    rcases hσ with rfl | rfl <;> norm_num <;> grind
  have hdet : ∀ σ : ℝ, Chazelle.det u v ((w.1 + σ * ε, w.2) : Point) =
      -(σ * ε) * (v.2 - u.2) := by
    grind [Chazelle.det]
  have hm := hdist (-1) (Or.inr rfl)
  have hp := hdist 1 (Or.inl rfl)
  rw [show w.1 + -1 * ε = w.1 - ε by ring] at hm
  rw [show w.1 + 1 * ε = w.1 + ε by ring] at hp
  have hdm : Chazelle.det u v ((w.1 - ε, w.2) : Point) = ε * (v.2 - u.2) := by
    have := hdet (-1); grind
  have hdp : Chazelle.det u v ((w.1 + ε, w.2) : Point) = -(ε * (v.2 - u.2)) := by
    have := hdet 1; grind
  have hLR : offset u v t₀ δ ∈ P.filled ↔ offset u v t₀ (-δ) ∉ P.filled := hδs
  rcases lt_or_gt_of_ne (sub_ne_zero.2 (Ne.symm hh)) with hneg | hpos
  · -- `v.2 < u.2`: the right neighbour is on the positive side
    have hpH : ((w.1 + ε, w.2) : Point) ∈ Hp := ⟨hp, by
      show 0 < 1 * _; rw [hdp]; nlinarith⟩
    have hmH : ((w.1 - ε, w.2) : Point) ∈ Hm := ⟨hm, by
      show 0 < -1 * _; rw [hdm]; nlinarith⟩
    have e1 := FactsInterior.filled_iff_of_preconnected hP (hpre 1) (hsub 1) hpH hL
    have e2 := FactsInterior.filled_iff_of_preconnected hP (hpre (-1)) (hsub (-1)) hmH hR
    grind
  · -- `u.2 < v.2`: the left neighbour is on the positive side
    have hmH : ((w.1 - ε, w.2) : Point) ∈ Hp := ⟨hm, by
      show 0 < 1 * _; rw [hdm]; nlinarith⟩
    have hpH : ((w.1 + ε, w.2) : Point) ∈ Hm := ⟨hp, by
      show 0 < -1 * _; rw [hdp]; nlinarith⟩
    have e1 := FactsInterior.filled_iff_of_preconnected hP (hpre 1) (hsub 1) hmH hL
    have e2 := FactsInterior.filled_iff_of_preconnected hP (hpre (-1)) (hsub (-1)) hpH hR
    grind

variable {Q : Polygon} {C : Chain}

/-- **A sub-chord through an interior point**: inside a horizontal segment whose ends are off the
interior of `Q`, every interior point lies on an interior chord of `Q` contained in the segment. -/
theorem sub_chord {y a b x : ℝ} (hab : a ≤ x ∧ x ≤ b)
    (ha : ((a, y) : Point) ∉ Q.filled \ Q.boundary) (hb : ((b, y) : Point) ∉ Q.filled \ Q.boundary)
    (hx : ((x, y) : Point) ∈ Q.filled \ Q.boundary) (hQ : Q.Simple) :
    ∃ a' b', a ≤ a' ∧ a' < x ∧ x < b' ∧ b' ≤ b ∧ IsHChordIn (Q.filled \ Q.boundary) y a' b' := by
  have hDo : IsOpen (Q.filled \ Q.boundary) := Chazelle.Jordan.isOpen_filled_sdiff_boundary hQ
  have hcont : Continuous (fun t : ℝ => ((t, y) : Point)) := by fun_prop
  have hclo : IsClosed {t : ℝ | ((t, y) : Point) ∉ Q.filled \ Q.boundary} :=
    hDo.isClosed_compl.preimage hcont
  -- the left end
  set A := Icc a x ∩ {t : ℝ | ((t, y) : Point) ∉ Q.filled \ Q.boundary} with hA
  have hAc : IsClosed A := isClosed_Icc.inter hclo
  have hAne : A.Nonempty := ⟨a, ⟨le_rfl, hab.1⟩, ha⟩
  have hAbdd : BddAbove A := ⟨x, fun t ht => ht.1.2⟩
  have ha'A := hAc.csSup_mem hAne hAbdd
  set a' := sSup A with ha'
  have ha'x : a' < x := lt_of_le_of_ne ha'A.1.2 (fun e => ha'A.2 (by grind))
  have hleft : ∀ t, a' < t → t ≤ x → ((t, y) : Point) ∈ Q.filled \ Q.boundary := by
    intro t ht1 ht2
    by_contra hn
    have : t ≤ a' := le_csSup hAbdd ⟨⟨le_trans ha'A.1.1 ht1.le, ht2⟩, hn⟩
    linarith
  -- the right end
  set B := Icc x b ∩ {t : ℝ | ((t, y) : Point) ∉ Q.filled \ Q.boundary} with hB
  have hBc : IsClosed B := isClosed_Icc.inter hclo
  have hBne : B.Nonempty := ⟨b, ⟨hab.2, le_rfl⟩, hb⟩
  have hBbdd : BddBelow B := ⟨x, fun t ht => ht.1.1⟩
  have hb'B := hBc.csInf_mem hBne hBbdd
  set b' := sInf B with hb'
  have hxb' : x < b' := lt_of_le_of_ne hb'B.1.1 (fun e => hb'B.2 (by grind))
  have hright : ∀ t, x ≤ t → t < b' → ((t, y) : Point) ∈ Q.filled \ Q.boundary := by
    intro t ht1 ht2
    by_contra hn
    have : b' ≤ t := csInf_le hBbdd ⟨⟨ht1, le_trans ht2.le hb'B.1.2⟩, hn⟩
    linarith
  refine ⟨a', b', ha'A.1.1, ha'x, hxb', hb'B.1.2,
    ⟨by linarith, ha'A.2, hb'B.2, fun t ht1 ht2 => ?_⟩⟩
  grind

/-- **One piece per chord.**  A horizontal chord of the domain of the top chain contains at most
one interior chord of `Q`, when the last edge of `Q` is not horizontal. -/
theorem one_piece (hQ : Q.Simple) (T : Top Q C) (hh : (Q.vtx C.m).2 ≠ (Q.vtx 0).2)
    {y a b : ℝ} (hc : IsHChordIn C.dom y a b)
    {d₁ d₂ : Set Point} (hd₁ : d₁ ∈ (interiorModel Q).Adm) (hd₂ : d₂ ∈ (interiorModel Q).Adm)
    (h₁ : d₁ ⊆ hseg y a b) (h₂ : d₂ ⊆ hseg y a b) : d₁ = d₂ := by
  obtain ⟨y₁, a₁, b₁, hc₁, rfl⟩ := hd₁
  obtain ⟨y₂, a₂, b₂, hc₂, rfl⟩ := hd₂
  have hmem : ∀ {y' a' b' : ℝ}, IsHChordIn (Q.filled \ Q.boundary) y' a' b' →
      hseg y' a' b' ⊆ hseg y a b → y' = y ∧ a ≤ a' ∧ b' ≤ b := by
    intro y' a' b' hc' hs
    have e1 := hs (show ((a', y') : Point) ∈ hseg y' a' b' from ⟨rfl, le_rfl, hc'.lt.le⟩)
    have e2 := hs (show ((b', y') : Point) ∈ hseg y' a' b' from ⟨rfl, hc'.lt.le, le_rfl⟩)
    exact ⟨e1.1, e1.2.1, e2.2.2⟩
  obtain ⟨hy₁, ha₁, hb₁⟩ := hmem hc₁ h₁
  obtain ⟨hy₂, ha₂, hb₂⟩ := hmem hc₂ h₂
  rw [hy₁] at hc₁ ⊢
  rw [hy₂] at hc₂ ⊢
  -- a boundary point of `Q` inside the chord lies on `e_{n-1}` at height `y`
  have hbd : ∀ e : ℝ, a < e → e < b → ((e, y) : Point) ∉ Q.filled \ Q.boundary →
      ((e, y) : Point) ∈ closure (Q.filled \ Q.boundary) →
      ∃ s ∈ Ioo (0 : ℝ) 1, ((e, y) : Point) = lerp (Q.vtx C.m) (Q.vtx 0) s := by
    intro e hae heb hnD hcl
    have hf : ((e, y) : Point) ∈ Q.filled :=
      closure_minimal (fun z hz => hz.1) (Chazelle.Jordan.isClosed_filled Q) hcl
    have hbd : ((e, y) : Point) ∈ Q.boundary := by
      grind
    exact T.boundary_dom hbd (hc.open_mem e hae heb)
  -- the parameter on `e_{n-1}` is determined by the height
  have hs_eq : ∀ e e' s s' : ℝ, ((e, y) : Point) = lerp (Q.vtx C.m) (Q.vtx 0) s →
      ((e', y) : Point) = lerp (Q.vtx C.m) (Q.vtx 0) s' → s = s' ∧ e = e' := by
    grind [Chazelle.Geometry.lerp_fst, Chazelle.Geometry.lerp_snd]
  -- closure points
  have hclL : ∀ {a' b' : ℝ}, IsHChordIn (Q.filled \ Q.boundary) y a' b' →
      ((b', y) : Point) ∈ closure (Q.filled \ Q.boundary) := by
    intro a' b' hc'
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    set m := min (ε / 2) ((b' - a') / 2)
    have hm0 : 0 < m := lt_min (by linarith) (by linarith [hc'.lt])
    have hm1 : m < ε := by grind
    have hm2 : m < b' - a' := by grind
    refine ⟨(b' - m, y), hc'.open_mem _ (by linarith) (by linarith), ?_⟩
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
      show b' - (b' - m) = m by ring, abs_of_pos hm0]
    grind
  have hclR : ∀ {a' b' : ℝ}, IsHChordIn (Q.filled \ Q.boundary) y a' b' →
      ((a', y) : Point) ∈ closure (Q.filled \ Q.boundary) := by
    intro a' b' hc'
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    set m := min (ε / 2) ((b' - a') / 2)
    have hm0 : 0 < m := lt_min (by linarith) (by linarith [hc'.lt])
    have hm1 : m < ε := by grind
    have hm2 : m < b' - a' := by grind
    refine ⟨(a' + m, y), hc'.open_mem _ (by linarith) (by linarith), ?_⟩
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
      show a' - (a' + m) = -m by ring, abs_neg, abs_of_pos hm0]
    grind
  -- two distinct pieces would be separated by a crossing with the interior on both sides
  have key : ∀ {a₁ b₁ a₂ b₂ : ℝ}, IsHChordIn (Q.filled \ Q.boundary) y a₁ b₁ →
      IsHChordIn (Q.filled \ Q.boundary) y a₂ b₂ → a ≤ a₁ → b₂ ≤ b → b₁ ≤ a₂ → False := by
    intro a₁ b₁ a₂ b₂ hc₁ hc₂ ha₁ hb₂ h12
    obtain ⟨s, hs, e⟩ := hbd b₁ (by linarith [hc₁.lt]) (by linarith [hc₂.lt]) hc₁.right_not
      (hclL hc₁)
    obtain ⟨s', hs', e'⟩ := hbd a₂ (by linarith [hc₁.lt]) (by linarith [hc₂.lt]) hc₂.left_not
      (hclR hc₂)
    obtain ⟨rfl, rfl⟩ := hs_eq _ _ _ _ e e'
    have hmn : C.m < Q.n := by have := T.hm; omega
    have hsucc : (C.m + 1) % Q.n = 0 := by rw [T.hm, Nat.mod_self]
    have hh' : (Q.vtx C.m).2 ≠ (Q.vtx ((C.m + 1) % Q.n)).2 := by grind
    obtain ⟨ε₀, hε₀, hcross⟩ := cross_sides hQ hmn hs hh'
    rw [hsucc, ← e] at hcross
    set ε := min (ε₀ / 2) (min ((b₁ - a₁) / 2) ((b₂ - b₁) / 2)) with hεd
    have hε0 : 0 < ε := lt_min (by linarith) (lt_min (by linarith [hc₁.lt]) (by linarith [hc₂.lt]))
    have hε1 : ε < ε₀ := by have := min_le_left (ε₀ / 2) (min ((b₁ - a₁) / 2) ((b₂ - b₁) / 2)); linarith
    have hε2 : ε < b₁ - a₁ := by
      have := min_le_right (ε₀ / 2) (min ((b₁ - a₁) / 2) ((b₂ - b₁) / 2))
      have := min_le_left ((b₁ - a₁) / 2) ((b₂ - b₁) / 2); linarith
    have hε3 : ε < b₂ - b₁ := by
      have := min_le_right (ε₀ / 2) (min ((b₁ - a₁) / 2) ((b₂ - b₁) / 2))
      have := min_le_right ((b₁ - a₁) / 2) ((b₂ - b₁) / 2); linarith
    have hl := hc₁.open_mem (b₁ - ε) (by linarith) (by linarith)
    have hr := hc₂.open_mem (b₁ + ε) (by linarith) (by linarith)
    exact ((hcross ε hε0 hε1).1 hl.1) hr.1
  rcases lt_trichotomy a₁ a₂ with h | h | h
  · have hb₁a₂ : b₁ ≤ a₂ := by
      by_contra hlt; push Not at hlt
      exact hc₂.left_not (hc₁.open_mem a₂ h hlt)
    grind
  · subst h
    rcases lt_trichotomy b₁ b₂ with h' | h' | h'
    · exact absurd (hc₂.open_mem b₁ hc₁.lt h') hc₁.right_not
    · rw [h']
    · exact absurd (hc₁.open_mem b₂ hc₂.lt h') hc₂.right_not
  · have hb₂a₁ : b₂ ≤ a₁ := by
      by_contra hlt; push Not at hlt
      exact hc₁.left_not (hc₂.open_mem a₁ h hlt)
    grind

/-- **The pieces** of a chain family: the interior chords of `Q` inside its chords. -/
def pieces (Q : Polygon) (F₀ : Set (Set Point)) : Set (Set Point) :=
  {d | d ∈ (interiorModel Q).Adm ∧ ∃ c ∈ F₀, d ⊆ c}

/-- **The pieces form a chord family of the interior model.** -/
theorem chordFamily_pieces (T : Top Q C) {F₀ : Set (Set Point)}
    (hF₀ : (chainModel C).ChordFamily C.P F₀) (hQ : Q.Simple)
    (hh : (Q.vtx C.m).2 ≠ (Q.vtx 0).2) :
    (interiorModel Q).ChordFamily Q (pieces Q F₀) ∧ (pieces Q F₀).ncard ≤ F₀.ncard := by
  classical
  -- the chosen chord of a piece
  have hch : ∀ d ∈ pieces Q F₀, ∃ c ∈ F₀, d ⊆ c := fun d hd => hd.2
  choose! f hf hfd using hch
  have hinj : Set.InjOn f (pieces Q F₀) := by
    intro d₁ h₁ d₂ h₂ e
    obtain ⟨y, a, b, hc, -, hcab⟩ := hF₀.2.1 (hf d₁ h₁)
    have s1 := hfd d₁ h₁
    have s2 := hfd d₂ h₂
    rw [← e] at s2
    rw [hcab] at s1 s2
    exact one_piece hQ T hh hc h₁.1 h₂.1 s1 s2
  have hfin : (pieces Q F₀).Finite :=
    Set.Finite.of_finite_image (hF₀.1.subset (by grind)) hinj
  refine ⟨⟨hfin, fun d hd => hd.1, fun d hd => ?_⟩, ?_⟩
  · obtain ⟨c, hc, hdc⟩ := hd.2
    obtain ⟨h, hh', a, b, rfl⟩ := hF₀.2.2 c hc
    obtain ⟨y', a', b', hc', rfl⟩ := hd.1
    have e := hdc (show ((a', y') : Point) ∈ hseg y' a' b' from ⟨rfl, le_rfl, hc'.lt.le⟩)
    refine ⟨h, by rw [← T.hP]; exact hh', a', b', ?_⟩
    rw [show y' = (C.P.vtx h).2 from e.1, T.hP]
  · exact Set.ncard_le_ncard_of_injOn f (fun d hd => hf d hd) hinj hF₀.1

end

end Trans

end Chazelle.Core
