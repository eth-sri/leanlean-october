module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvTie

/-!
# The sweep (WP-D), stage 3: the invariant after a key with an anchored chord

At a key `K` of the `C₁` part carrying an **anchored** chord `Z` (attached also at a position of the
open right stretch), the event loop sets its label set to the side labels of the anchored chords at
`K` (`EvSideLab`).  `evInv_anchor` shows that this re-establishes `EvInv`: every later non-cut
position reached through keys carrying only bracket chords is enclosed, or faces a region on a side
of an anchored chord at `K`.  The proof follows the region just after `K`, through a bracket that
opens at `K` (then the region beyond its closer is the middle region of the tie at `K`, on a side of
`Z`), using `evGL`, `keyStruct`, `side_comp_off`, `faced_both_off` and, for ties, the pieces of a
chord of `S₂` (`pieces_le_two`).

Hypothesis `NoTieV` (a tie at a copy of the shared vertex beyond the start) is proved separately.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideInArc)
open WalkEmbed

namespace Sweep

section Anchor

variable (J : Merge.Junction)

section
variable (S₂ : Set (Set Point))
include S₂
/-- **Side labels**: every region on a side of `Z` has a valid label set `Λ`. -/
def EvSideLab (Λ : Set (Set Point)) (Z : Set Point) : Prop :=
  ∀ G ∈ (chainModel J.whole).regions (F₂plus J S₂), ∀ ρ : ℝ, (ρ = 1 ∨ ρ = -1) →
    SideOf (chainModel J.whole) ρ Z G → EvVal J S₂ Λ G

/-- **No tie at a copy of the shared vertex beyond the start.** -/
def NoTieV : Prop :=
  ∀ e ∈ F₂plus J S₂, ∀ e' ∈ F₂plus J S₂, e ≠ e' → ∀ (p : ℕ) (t : ℝ),
    SideAttach (chainModel J.whole).W e p t → SideAttach (chainModel J.whole).W e' p t →
    sidePt (chainModel J.whole).W p t = J.shared → (Lst J : ℝ) < oW J (p + t) → False


end

variable {J}

section
variable (hP : J.P.Simple) {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite)
include hP S₂ hS₂ hS₂f
/-- Two positions with equal offsets are equal. -/
theorem pos_eq_of_oW {p p' : ℕ} {t t' : ℝ}
    (hp : p < (chainModel J.whole).W.n) (hp' : p' < (chainModel J.whole).W.n) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (ht0' : 0 ≤ t') (ht1' : t' < 1) (h : oW J (p + t) = oW J (p' + t')) :
    p = p' ∧ t = t' := by
  have hC := corr_right0 J hP hS₂ hS₂f
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < (chainModel J.whole).W.n := by
    exact_mod_cast hC.hg
  obtain ⟨a0, a1⟩ := Corr.key_mem hp ht0 ht1
  obtain ⟨b0, b1⟩ := Corr.key_mem hp' ht0' ht1'
  exact Chazelle.Chain.sideKey_inj ht0 ht1 ht0' ht1' (off_inj hg0 hgn a0 a1 b0 b1 h)

/-- **A cut-free stretch just after a position, of length below `ε`.** -/
theorem after_pos_eps {p : ℕ} {t : ℝ}
    (hp : p < (chainModel J.whole).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1) {G : Set Point}
    (hW : AfterFaces (chainModel J.whole) p t G) {ε : ℝ} (hε : 0 < ε) :
    ∃ s, 0 < s ∧ s < ε ∧ t + s < 1 ∧ (chainModel J.whole).Faces p (t + s) G ∧
      ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (p + (t + s)) ∧
      oW J (p + (t + s)) = oW J (p + t) + s ∧
      ∀ x, (chainModel J.whole).IsCut (F₂plus J S₂) x → 0 ≤ x → x < (chainModel J.whole).W.n →
        ¬ (oW J (p + t) < oW J x ∧ oW J x < oW J (p + (t + s))) := by
  obtain ⟨δ, hδ, hW'⟩ := hW
  obtain ⟨s, hs0, hs1, hf, hnc, hoff, hgap⟩ := after_pos_exists hP hS₂ hS₂f hp ht0 ht1
    (G := G) ⟨min δ ε, lt_min hδ hε, fun s h0 h1 h2 => hW' s h0 (lt_of_lt_of_le h1
      (min_le_left _ _)) h2⟩
  -- shrink to below `ε`: the positions of the stretch face the same region
  by_cases hsε : s < ε
  · ram_grind
  · push Not at hsε
    have hC := corr_right0 J hP hS₂ hS₂f
    set s' := min (min δ ε) s / 2 with hs'
    have hm : 0 < min (min δ ε) s := lt_min (lt_min hδ hε) hs0
    have h1 := min_le_left (min δ ε) s
    have h2 := min_le_right (min δ ε) s
    have h3 := min_le_left δ ε
    have h4 := min_le_right δ ε
    have hs'0 : 0 < s' := by linarith
    have hoff' : oW J (p + (t + s')) = oW J (p + t) + s' :=
      off_add_small hC.hg hp ht0 hs'0.le (by linarith)
    refine ⟨s', hs'0, by linarith, by linarith, hW' s' hs'0 (by linarith) (by linarith), ?_,
      hoff', ?_⟩
    · intro hcut
      obtain ⟨k0, k1⟩ := Corr.key_mem hp (show 0 ≤ t + s' by linarith) (show t + s' < 1 by linarith)
      grind
    ram_grind


end

section
variable (hP : J.P.Simple) {e : Set Point} (he : e ∈ Merge.augChords J.whole)
include hP he
/-- **The direction of a chord at a position is unique.** -/
theorem dirAt_unique
    {p : ℕ} {t d d' : ℝ} (_hA : SideAttach (chainModel J.whole).W e p t)
    (h : DirAt (chainModel J.whole).W e p t d) (h' : DirAt (chainModel J.whole).W e p t d') :
    d = d' := by
  have hM : WalkAx (chainModel J.whole) := FactsChain.walkAx J.whole hP
  obtain ⟨a, b, hab, heab, hy, -⟩ := hM.ends e he
  have ha : a ∈ e := by rw [heab]; exact Geometry.left_mem_segment _ _
  have hb : b ∈ e := by rw [heab]; exact Geometry.right_mem_segment _ _
  have hne : a.1 ≠ b.1 := fun hx => hab (Prod.ext hx hy)
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases h' with ⟨rfl, h'⟩ | ⟨rfl, h'⟩
  · rfl
  · exfalso; apply hne; linarith [h' a ha, h a ha, h' b hb, h b hb]
  · exfalso; apply hne; linarith [h' a ha, h a ha, h' b hb, h b hb]
  · rfl

/-- **A chord leaves its two attachments in opposite directions.** -/
theorem dirAt_other
    {pa pb : ℕ} {ta tb d : ℝ} (hA : SideAttach (chainModel J.whole).W e pa ta)
    (hB : SideAttach (chainModel J.whole).W e pb tb)
    (hAB : sidePt (chainModel J.whole).W pa ta ≠ sidePt (chainModel J.whole).W pb tb)
    (h : DirAt (chainModel J.whole).W e pa ta d) : DirAt (chainModel J.whole).W e pb tb (-d) := by
  have hM : WalkAx (chainModel J.whole) := FactsChain.walkAx J.whole hP
  have hy : (sidePt (chainModel J.whole).W pa ta).2 = (sidePt (chainModel J.whole).W pb tb).2 :=
    (attach_snd_eq hP he hB hA.2.2.2.1)
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact Or.inr ⟨by norm_num, dir_opposite hM he hA hB hAB h⟩
  · rcases hM.attach_dir he hB with h' | h'
    all_goals ram_grind


end

section
variable (hP : J.P.Simple) {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite)
include hP hS₂ hS₂f
/-- **The anchored chord is not strictly inside a bracket interval**: a chord `e ≠ Z` attached at
offsets `A < B` with `A < oK < B`, `Z` attached at `K` and at an offset below `A`, is impossible. -/
theorem anchor_not_inside {Z e : Set Point}
    (hZ : Z ∈ F₂plus J S₂) (he : e ∈ F₂plus J S₂) (hZe : Z ≠ e) {pK pz pa pb : ℕ}
    {tK tz ta tb : ℝ} (hZK : SideAttach (chainModel J.whole).W Z pK tK)
    (hZz : SideAttach (chainModel J.whole).W Z pz tz)
    (hA : SideAttach (chainModel J.whole).W e pa ta) (hB : SideAttach (chainModel J.whole).W e pb tb)
    (h1 : oW J (pa + ta) < oW J (pK + tK)) (h2 : oW J (pK + tK) < oW J (pb + tb))
    (hz : oW J (pz + tz) < oW J (pa + ta)) : False := by
  have hC := corr_right0 J hP hS₂ hS₂f
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < (chainModel J.whole).W.n := by
    exact_mod_cast hC.hg
  have hAB := pt_ne_of_off_ne hP hS₂ hS₂f he hA hB (by linarith : oW J (pa + ta) ≠ oW J (pb + tb))
  have := no_cross_off hC.hM hC.hF hC.hfin he hZ (Ne.symm hZe) hA hB hAB hZK hZz hg0 hgn
    (by grind [oW_eq]) (by simp_all [oW_eq] )
    (by simp_all [oW_eq] <;> omega_nf)
  grind [oW_eq]

/-- **A position just after a key with a closed block before it is not enclosed**: if the chords
attached at offsets in `[oK, oB]` other than `Z` have all their attachments there, `Z` is attached
at `K` and below `Lst`, and the position `y` (just after `B`, no cut between) precedes a
non-enclosed `x`, then `y` is not enclosed. -/
theorem noEncl_of_closed {Z : Set Point}
    (hZ : Z ∈ F₂plus J S₂) {pK pz : ℕ} {tK tz : ℝ}
    (hZK : SideAttach (chainModel J.whole).W Z pK tK)
    (hZz : SideAttach (chainModel J.whole).W Z pz tz) (hzL : oW J (pz + tz) < Lst J)
    (hLst : (Lst J : ℝ) ≤ oW J (pK + tK)) {oB : ℝ} (hKB : oW J (pK + tK) ≤ oB)
    (hcl : ∀ e ∈ F₂plus J S₂, e ≠ Z → ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s →
      oW J (pK + tK) ≤ oW J (q + s) → oW J (q + s) ≤ oB → ∀ (q' : ℕ) (s' : ℝ),
        SideAttach (chainModel J.whole).W e q' s' →
          oW J (pK + tK) ≤ oW J (q' + s') ∧ oW J (q' + s') ≤ oB)
    {oy ox : ℝ} (hBy : oB < oy) (hyx : oy < ox) (hgap : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (s : ℝ),
      SideAttach (chainModel J.whole).W e q s → ¬ (oB < oW J (q + s) ∧ oW J (q + s) < oy))
    (hEx : ¬ EvEncl J S₂ ox) : ¬ EvEncl J S₂ oy := by
  rintro ⟨e, he, qa, qb, sa, sb, hA, hB, hAB, hLa, hay, hby⟩
  -- the first attachment is at most `oB`
  have hA' : oW J (qa + sa) ≤ oB := by
    ram_grind
  rcases hby with hby | hby
  · -- a bracket: the other end beyond `x` would enclose `x`
    have hbx : oW J (qb + sb) ≤ ox := by
      by_contra h
      push Not at h
      exact hEx ⟨e, he, qa, qb, sa, sb, hA, hB, hAB, hLa, by linarith, Or.inl h⟩
    by_cases heZ : e = Z
    · subst heZ
      -- `Z` has an attachment below `Lst`: it is `qa` or `qb`
      have hC := corr_right0 J hP hS₂ hS₂f
      rcases key_of_two hC.hM (hC.hF he) hA hB hAB hZz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · linarith
      · linarith
    rcases lt_or_ge (oW J (qa + sa)) (oW J (pK + tK)) with h | h
    · exact anchor_not_inside hP hS₂ hS₂f hZ he (Ne.symm heZ) hZK hZz hA hB h (by linarith)
        (by linarith)
    ram_grind
  · -- a pocket: `x` is enclosed too
    exact hEx ⟨e, he, qa, qb, sa, sb, hA, hB, hAB, hLa, by linarith, Or.inr hby⟩

/-- **A chord nested in another**: a chord `e ≠ c` attached strictly between the two attachments
of `c` has all its attachments between them. -/
theorem closed_nested {c e : Set Point}
    (hc : c ∈ F₂plus J S₂) (he : e ∈ F₂plus J S₂) (hce : c ≠ e) {pa pb q q' : ℕ}
    {ta tb s s' : ℝ} (hA : SideAttach (chainModel J.whole).W c pa ta)
    (hB : SideAttach (chainModel J.whole).W c pb tb) (hab : oW J (pa + ta) < oW J (pb + tb))
    (hQ : SideAttach (chainModel J.whole).W e q s) (h1 : oW J (pa + ta) < oW J (q + s))
    (h2 : oW J (q + s) < oW J (pb + tb)) (hQ' : SideAttach (chainModel J.whole).W e q' s') :
    oW J (pa + ta) ≤ oW J (q' + s') ∧ oW J (q' + s') ≤ oW J (pb + tb) := by
  have hC := corr_right0 J hP hS₂ hS₂f
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < (chainModel J.whole).W.n := by
    exact_mod_cast hC.hg
  have hAB := pt_ne_of_off_ne hP hS₂ hS₂f hc hA hB hab.ne
  have := no_cross_off hC.hM hC.hF hC.hfin hc he hce hA hB hAB hQ hQ' hg0 hgn
    (by simp_all [oW_eq] ) (by simp_all [oW_eq] )
    (by simp_all [oW_eq] <;> omega_nf)
  simp_all [oW_eq] 


end

/-- The keys of the attachments of a chord. -/
theorem attach_key_mem {e : Set Point} {q : ℕ} {s : ℝ}
    (hA : SideAttach (chainModel J.whole).W e q s) :
    0 ≤ (q : ℝ) + s ∧ (q : ℝ) + s < (chainModel J.whole).W.n :=
  Corr.key_mem hA.1 hA.2.1 hA.2.2.1

end Anchor

end Sweep

end

end Chazelle.Core
