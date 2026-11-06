module

public import Chazelle.Golf

public import Chazelle.Core.SweepIface

/-!
# The sweep (WP-D), stage 3: the invariant of the event loop (label sets)

The event loop of stage 3 walks the keys of the `C₁` part of the walk of `C` (offsets `oW ≥ Lst`)
with a **label set** `Λ` (at most four regions of `S₂`).  Its invariant `EvInv J S₂ oK Λ` at the
last processed key (offset `oK`) speaks about every later non-cut position `x` reached through
cuts carrying only **bracket chords** (`EvBrk`: every attachment on the `C₁` part): the region
faced at `x` either has a valid label in `Λ` (or a gap label, `EvVal`), or `x` is **enclosed**
(`EvEncl`: strictly between the two attachments of a bracket chord, or after the `C₁` attachment
of a chord attached at offset `0`, a pocket), where no label is needed.

* `evInv_mono`: across keys carrying only bracket chords the invariant (and `Λ`) is kept;
* `evInv_pocket`: after a pocket key every position is enclosed;
* `labIn_of_evInv`: the invariant gives the label facts of the event log (`LabIn`).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt)
open WalkEmbed

namespace Sweep

section EvInv

variable (J : Merge.Junction)

/-- **A bracket chord**: every attachment lies on the `C₁` part. -/
def EvBrk (e : Set Point) : Prop :=
  ∀ (p : ℕ) (t : ℝ), SideAttach (chainModel J.whole).W e p t → (Lst J : ℝ) ≤ oW J (p + t)

/-- **The offset `o` is enclosed**: strictly between the two attachments of a chord of `F₂⁺` on
the `C₁` part, or after the `C₁` attachment of a chord attached at offset `0` (a pocket). -/
def EvEncl (S₂ : Set (Set Point)) (o : ℝ) : Prop :=
  ∃ e ∈ F₂plus J S₂, ∃ (pa pb : ℕ) (ta tb : ℝ), SideAttach (chainModel J.whole).W e pa ta ∧
    SideAttach (chainModel J.whole).W e pb tb ∧
    sidePt (chainModel J.whole).W pa ta ≠ sidePt (chainModel J.whole).W pb tb ∧
    (Lst J : ℝ) ≤ oW J (pa + ta) ∧ oW J (pa + ta) < o ∧ (o < oW J (pb + tb) ∨ oW J (pb + tb) = 0)

/-- **A label set is valid for a region**: some valid label (`Valid`) of the region is in the set
or is a gap label. -/
def EvVal (S₂ : Set (Set Point)) (Λ : Set (Set Point)) (G : Set Point) : Prop :=
  ∃ L, (L ∈ Λ ∨ GapLab J S₂ L) ∧ L ∈ (chainModel J.right).regions S₂ ∧ Valid J S₂ G L

/-- **The facts at a non-cut position**: it is enclosed, or the regions faced there have a valid
label set. -/
def EvPos (S₂ : Set (Set Point)) (Λ : Set (Set Point)) (p : ℕ) (t : ℝ) : Prop :=
  EvEncl J S₂ (oW J (p + t)) ∨
    ∀ G ∈ (chainModel J.whole).regions (F₂plus J S₂), (chainModel J.whole).Faces p t G →
      EvVal J S₂ Λ G

/-- **The invariant of the event loop** at a key with offset `oK` and label set `Λ`: every later
non-cut position reached through keys carrying only bracket chords has `EvPos`. -/
def EvInv (S₂ : Set (Set Point)) (oK : ℝ) (Λ : Set (Set Point)) : Prop :=
  ∀ (p : ℕ) (t : ℝ), p < (chainModel J.whole).W.n → t ∈ Ioo (0 : ℝ) 1 →
    ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (p + t) → oK < oW J (p + t) →
    (∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s →
      oK < oW J (q + s) → oW J (q + s) < oW J (p + t) → EvBrk J e) →
    EvPos J S₂ Λ p t

variable {J}

/-- **Keys carrying only bracket chords keep the invariant.** -/
theorem evInv_mono {S₂ : Set (Set Point)} {oK oK' : ℝ} {Λ : Set (Set Point)}
    (h : EvInv J S₂ oK Λ) (hle : oK ≤ oK')
    (hbr : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s →
      oK < oW J (q + s) → oW J (q + s) ≤ oK' → EvBrk J e) :
    EvInv J S₂ oK' Λ := by
  intro p t hp ht hnc ho hb
  refine h p t hp ht hnc (⟡) fun e he q s hA h1 h2 => ?_
  rcases le_or_gt (oW J (q + s)) oK' with h3 | h3
  · exact hbr e he q s hA h1 h3
  · exact hb e he q s hA h3 h2

/-- **After a pocket key** every position is enclosed. -/
theorem evInv_pocket {S₂ : Set (Set Point)} {e : Set Point} (he : e ∈ F₂plus J S₂)
    {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach (chainModel J.whole).W e pa ta)
    (hB : SideAttach (chainModel J.whole).W e pb tb)
    (hAB : sidePt (chainModel J.whole).W pa ta ≠ sidePt (chainModel J.whole).W pb tb)
    (hAo : (Lst J : ℝ) ≤ oW J (pa + ta)) (hBo : oW J (pb + tb) = 0) (Λ : Set (Set Point)) :
    EvInv J S₂ (oW J (pa + ta)) Λ :=
  fun _ _ _ _ _ ho _ => Or.inl ⟨e, he, pa, pb, ta, tb, hA, hB, hAB, hAo, ho, Or.inr hBo⟩

/-- `oW` is the offset from the base `gW`. -/
theorem oW_eq (x : ℝ) :
    oW J x = off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) x := rfl

theorem Lst_eq : (Lst J : ℝ) = ((rL1 J + rL2 J : ℕ) : ℝ) := rfl

/-- **An enclosed position faces an unlabelled region.** -/
theorem not_rlabel_of_encl (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {p : ℕ} {t : ℝ}
    (hp : p < (chainModel J.whole).W.n) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hnc : ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (p + t))
    (hE : EvEncl J S₂ (oW J (p + t))) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂)) (hf : (chainModel J.whole).Faces p t G)
    (V : Set Point) : ¬ RLabel J S₂ G V := by
  obtain ⟨e, he, pa, pb, ta, tb, hA, hB, hAB, hAo, ho, hBo⟩ := hE
  rcases hBo with hBo | hBo
  · exact no_label_of_bracket J hP hS₂ hS₂f hG he hA hB hAB hAo (hAo.trans (ho.trans hBo).le) hp ht hnc hf
      (Or.inl ⟨ho, hBo⟩) V
  · exact no_label_of_pocket J hP hS₂ hS₂f hG he hA hB hAB hAo hBo hp ht hnc hf ho V

/-- **A cut-free stretch just after a position** facing the region faced just after it. -/
theorem after_pos_exists (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {p : ℕ} {t : ℝ}
    (hp : p < (chainModel J.whole).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1) {G : Set Point}
    (hW : AfterFaces (chainModel J.whole) p t G) :
    ∃ s, 0 < s ∧ t + s < 1 ∧ (chainModel J.whole).Faces p (t + s) G ∧
      ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (p + (t + s)) ∧
      oW J (p + (t + s)) = oW J (p + t) + s ∧
      ∀ x, (chainModel J.whole).IsCut (F₂plus J S₂) x → 0 ≤ x → x < (chainModel J.whole).W.n →
        ¬ (oW J (p + t) < oW J x ∧ oW J x < oW J (p + (t + s))) := by
  have hC := corr_right0 J hP hS₂ hS₂f
  have hM := hC.hM
  obtain ⟨δ, hδ, hfac⟩ := hW
  obtain ⟨δ₁, hδ₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (eventually_not_cut_after hM hC.hF hC.hfin ((p : ℝ) + t))
  have hδ₁' : (0 : ℝ) < δ₁ := hδ₁
  set s := min (min δ δ₁) (1 - t) / 2 with hs
  have hm : 0 < min (min δ δ₁) (1 - t) := lt_min (lt_min hδ hδ₁') (by linarith)
  have h1 := min_le_left (min δ δ₁) (1 - t)
  have h2 := min_le_right (min δ δ₁) (1 - t)
  have h3 := min_le_left δ δ₁
  have h4 := min_le_right δ δ₁
  have hs0 : 0 < s := by linarith
  have hoff : oW J (p + (t + s)) = oW J (p + t) + s :=
    off_add_small hC.hg hp ht0 hs0.le (by linarith)
  refine ⟨s, hs0, by linarith, hfac s hs0 (by linarith) (by linarith), ?_, hoff, ?_⟩
  · have := hsub ⟨show 0 < s by linarith, show s < δ₁ by linarith⟩
    rw [Set.mem_ofPred_eq] at this
    rwa [← add_assoc]
  · rintro x hx hx0 hxn ⟨hlo, hhi⟩
    rw [hoff] at hhi
    have hu : 0 ≤ oW J x - oW J (p + t) := by linarith
    have hx' := eq_of_off_small hC.hg hp ht0 hu (by linarith) hx0 hxn
      (show oW J x = oW J (p + t) + (oW J x - oW J (p + t)) by ring)
    have := hsub ⟨show 0 < oW J x - oW J (p + t) by linarith,
      show oW J x - oW J (p + t) < δ₁ by linarith⟩
    rw [Set.mem_ofPred_eq] at this
    apply this
    rw [hx'] at hx
    exact hx

/-- **The label facts of the event log from the invariant.** -/
theorem labIn_of_evInv (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {Λ : Set (Set Point)} {p : ℕ}
    {t : ℝ} (hp : p < (chainModel J.whole).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (h : EvInv J S₂ (oW J (p + t)) Λ) : LabIn J S₂ p t Λ := by
  intro G hG hW V hV hR
  obtain ⟨s, hs0, hs1, hf, hnc, hoff, hgap⟩ := after_pos_exists hP hS₂ hS₂f hp ht0 ht1 hW
  have hpos := h p (t + s) hp ⟨⟡, hs1⟩ hnc (by rw [hoff]; linarith)
    (fun e he q s' hA h1 h2 => by
      obtain ⟨k0, k1⟩ := Corr.key_mem hA.1 hA.2.1 hA.2.2.1
      exact absurd ⟨h1, h2⟩ (hgap _ ⟨e, he, q, s', hA, rfl⟩ k0 k1))
  rcases hpos with hE | hval
  · exact absurd hR (not_rlabel_of_encl hP hS₂ hS₂f hp ⟨⟡, hs1⟩ hnc hE hG hf V)
  · obtain ⟨L, hL, -, hv⟩ := hval G hG hf
    rcases hv.1 V hV hR with rfl | hg
    · rcases hL with hL | hL
      · exact Or.inl hL
      · exact Or.inr hL
    · exact Or.inr hg

end EvInv

end Sweep

end

end Chazelle.Core
