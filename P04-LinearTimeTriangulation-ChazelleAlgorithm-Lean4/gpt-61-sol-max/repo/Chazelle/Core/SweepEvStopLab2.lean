module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvStopLab

/-!
# The sweep (WP-D), stage 2: the side labels of an anchored stop chord (part 2, ties)

At a tie of the open right stretch (a vertex position, not the base, not the split vertex) of a
chord `e` of `F₂⁺` lying in no chord of `S₂` and a chord `e' ⊆ c' ∈ S₂`:

* `slb_U2`: `c'` is the only chord of `S₂` attached at the counterpart position of the walk of
  `C₂` (a chord of `S₂` going the way of `e` would contain `e`);
* `slb_middle_fused`: the middle region of the tie has as label the region faced just after or
  just before the counterpart position (the two sides of `c'`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Sweep
open Chazelle.Chain (SideAttach sidePt)
open WalkEmbed

@[expose] public section

variable {J : Merge.Junction}

/-- A chord of `F₂⁺` going east (west) from a point `w` of `C₂`, and a chord of `S₂` going the same
way from `w`: the first lies in the second. -/
theorem slb_sub_same_way (_hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) {e c : Set Point} (he : e ∈ F₂plus J S₂)
    (hc : c ∈ S₂) {w : Point} (hwe : w ∈ e) (hwc : w ∈ c)
    (hdir : ((∀ z ∈ e, w.1 ≤ z.1) ∧ ∀ z ∈ c, w.1 ≤ z.1) ∨
      ((∀ z ∈ e, z.1 ≤ w.1) ∧ ∀ z ∈ c, z.1 ≤ w.1)) : e ⊆ c := by
  obtain ⟨y, a, b, hH, hyt, rfl, -, -⟩ := Merge.augChords_spec (hS₂ hc)
  obtain ⟨y₁, a₁, b₁, hH₁, -, rfl, -, -⟩ := Merge.augChords_spec (F₂plus_subset J hS₂ he)
  have hy1 : y₁ ≤ J.right.top.2 := by
    have := F₂plus_snd_le J hS₂ he hwe
    rw [hwe.1] at this; exact this
  obtain ⟨hwy, hwa, hwb⟩ := hwc
  obtain ⟨hwy₁, hwa₁, hwb₁⟩ := hwe
  have hyy : y₁ = y := hwy₁.symm.trans hwy
  subst hyy
  rcases hdir with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have ea : a = w.1 := le_antisymm hwa (h2 (a, y₁) ⟨rfl, le_rfl, hH.lt.le⟩)
    have ea₁ : a₁ = w.1 := le_antisymm hwa₁ (h1 (a₁, y₁) ⟨rfl, le_rfl, hH₁.lt.le⟩)
    have hbb : b₁ ≤ b := by
      by_contra hlt
      push Not at hlt
      apply hH.right_not
      exact dom_right J (hH₁.open_mem b (by linarith [hH.lt]) hlt) hy1
    rintro z ⟨hzy, hza, hzb⟩
    exact ⟨hzy, by linarith, by linarith⟩
  · have eb : b = w.1 := le_antisymm (h2 (b, y₁) ⟨rfl, hH.lt.le, le_rfl⟩) hwb
    have eb₁ : b₁ = w.1 := le_antisymm (h1 (b₁, y₁) ⟨rfl, hH₁.lt.le, le_rfl⟩) hwb₁
    have haa : a ≤ a₁ := by
      by_contra hlt
      push Not at hlt
      apply hH.left_not
      exact dom_right J (hH₁.open_mem a hlt (by linarith [hH.lt])) hy1
    rintro z ⟨hzy, hza, hzb⟩
    exact ⟨hzy, by linarith, by linarith⟩

/-- **One chord of `S₂` at the counterpart of a tie with a stop chord.** -/
theorem slb_U2 (hP : J.P.Simple) {Q : Polygon} {S₂ : Set (Set Point)}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂) {e e' c' : Set Point}
    (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂) (hne : e' ≠ e)
    (hnf : ∀ c ∈ S₂, ¬ e ⊆ c) (hc' : c' ∈ S₂) (he'c' : e' ⊆ c') {d : ℕ} (hd : d < Lst J)
    (hA : SideAttach (chainModel J.whole).W e ((gW J + d) % (chainModel J.whole).W.n) 0)
    (hA' : SideAttach (chainModel J.whole).W e' ((gW J + d) % (chainModel J.whole).W.n) 0)
    (hcA : SideAttach (chainModel J.right).W c' (cpA J d) 0) {c'' : Set Point} (hc'' : c'' ∈ S₂)
    (hA'' : SideAttach (chainModel J.right).W c'' (cpA J d) 0) : c'' = c' := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hM := hC.hM
  have hM₂ := hC.hM₂
  have hw : sidePt (chainModel J.whole).W ((gW J + d) % (chainModel J.whole).W.n) 0 =
      sidePt (chainModel J.right).W (cpA J d) 0 := hC.sidePt_eq hd 0
  set w := sidePt (chainModel J.whole).W ((gW J + d) % (chainModel J.whole).W.n) 0 with hwd
  have hwe : w ∈ e := hA.2.2.2.1
  
  
  have hwc'' : w ∈ c'' := by rw [hw]; exact hA''.2.2.2.1
  have dE := hM.attach_dir (hC.hF he) hA
  have dE' := hM.attach_dir (hC.hF he') hA'
  have dC' := hM₂.attach_dir (hS₂.2.1 hc') hcA
  have dC'' := hM₂.attach_dir (hS₂.2.1 hc'') hA''
  rw [← hw] at dC' dC''
  -- `e`, `e'` go opposite ways
  have hopp : ((∀ z ∈ e, w.1 ≤ z.1) ∧ ∀ z ∈ e', z.1 ≤ w.1) ∨
      ((∀ z ∈ e, z.1 ≤ w.1) ∧ ∀ z ∈ e', w.1 ≤ z.1) := by
    rcases dE with h1 | h1 <;> rcases dE' with h2 | h2
    · exact absurd (hM.attach_east_unique hC.hF he' he hA' hA h2 h1) hne
    · ram_grind
    · ram_grind
    · exact absurd (hM.attach_west_unique hC.hF he' he hA' hA h2 h1) hne
  -- `c'` goes the way of `e'`
  have hc'way : ((∀ z ∈ e', w.1 ≤ z.1) → ∀ z ∈ c', w.1 ≤ z.1) ∧
      ((∀ z ∈ e', z.1 ≤ w.1) → ∀ z ∈ c', z.1 ≤ w.1) := by
    constructor
    · intro h
      rcases dC' with h' | h'
      · exact h'
      · exact (dir_not_both hM (hC.hF he') hA' h (fun z hz => h' z (he'c' hz))).elim
    · intro h
      rcases dC' with h' | h'
      · exact (dir_not_both hM (hC.hF he') hA' (fun z hz => h' z (he'c' hz)) h).elim
      · exact h'
  
  rcases hopp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `e` east, `e'` and `c'` west
    have hc'w := hc'way.2 h2
    rcases dC'' with h3 | h3
    · exact absurd (slb_sub_same_way hP hS₂.2.1 he hc'' hwe hwc'' (Or.inl ⟨h1, h3⟩))
        (hnf c'' hc'')
    · exact hM₂.attach_west_unique hS₂.2.1 hc'' hc' hA'' hcA (by rw [← hw]; exact h3)
        (by rw [← hw]; exact hc'w)
  · have hc'e := hc'way.1 h2
    rcases dC'' with h3 | h3
    · exact hM₂.attach_east_unique hS₂.2.1 hc'' hc' hA'' hcA (by rw [← hw]; exact h3)
        (by rw [← hw]; exact hc'e)
    · exact absurd (slb_sub_same_way hP hS₂.2.1 he hc'' hwe hwc'' (Or.inr ⟨h1, h3⟩))
        (hnf c'' hc'')

theorem slb_cpB_eq {d : ℕ} (hd0 : d ≠ 0) (hdr : d ≠ rL1 J) : cpB J d = cpA J d := by
  grind [dq, cpA, cpB]

/-- **The middle region of a tie with a fused partner** (away from the base and the split
vertex): its label is faced at the counterpart position. -/
theorem slb_middle_fused (hP : J.P.Simple) {Q : Polygon} {S₂ : Set (Set Point)}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {e e' c' : Set Point}
    (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂) (hne : e' ≠ e)
    (hnf : ∀ c ∈ S₂, ¬ e ⊆ c) (hc' : c' ∈ S₂) (he'c' : e' ⊆ c') {d : ℕ} (hd : d < Lst J)
    (hd0 : d ≠ 0) (hdr : d ≠ rL1 J)
    (hA : SideAttach (chainModel J.whole).W e ((gW J + d) % (chainModel J.whole).W.n) 0)
    (hA' : SideAttach (chainModel J.whole).W e' ((gW J + d) % (chainModel J.whole).W.n) 0)
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hS' : SideOf (chainModel J.whole) ρ e' G) {Va Vb : Set Point}
    (hVa : Va ∈ (chainModel J.right).regions S₂) (hVb : Vb ∈ (chainModel J.right).regions S₂)
    (ha : AfterFaces (chainModel J.right) (cpA J d) 0 Va)
    (hb : BeforeFaces (chainModel J.right) (cpB J d) 0 Vb) : EvVal J S₂ {Va, Vb} G := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hGM₂ : GoodModel (chainModel J.right) := Or.inl ⟨J.right, hP, rfl⟩
  rw [slb_cpB_eq hd0 hdr] at hb
  have hcA : SideAttach (chainModel J.right).W c' (cpA J d) 0 :=
    attach_counterpart2 J hP hS₂.2.1 hS₂.1 hd le_rfl zero_lt_one (fun _ => ⟨hd0, hdr⟩) he'
      (hS₂.2.1 hc') he'c' hA'
  have huniq : ∀ c'' ∈ S₂, SideAttach (chainModel J.right).W c'' (cpA J d) 0 → c'' = c' :=
    fun c'' hc'' h => slb_U2 hP hS₂ he he' hne hnf hc' he'c' hd hA hA' hcA hc'' h
  have hsec : (0 : ℝ) = 0 → d ≠ 0 ∧ d ≠ rL1 J := fun _ => ⟨hd0, hdr⟩
  have lab := fun {V : Set Point} (hV : V ∈ (chainModel J.right).regions S₂)
      (hVs : SideOf (chainModel J.right) ρ c' V) =>
    sideLabel_fused J hP hS₂ hF he' hc' he'c' hd le_rfl zero_lt_one hsec hA' hρ hV hVs G hG hS'
  rcases hC.hM₂.attach_dir (hS₂.2.1 hc') hcA with h | h
  · have sa := after_side hGM₂ hS₂ hc' hcA huniq (Or.inl ⟨rfl, h⟩) hVa ha
    have sb := before_side hGM₂ hS₂ hc' hcA huniq (Or.inl ⟨rfl, h⟩) hVb hb
    rcases hρ with rfl | rfl
    · exact slb_evVal (Set.mem_insert_of_mem _ rfl) hVb (lab hVb sb)
    · exact slb_evVal (Set.mem_insert _ _) hVa (lab hVa sa)
  · have sa := after_side hGM₂ hS₂ hc' hcA huniq (Or.inr ⟨rfl, h⟩) hVa ha
    have sb := before_side hGM₂ hS₂ hc' hcA huniq (Or.inr ⟨rfl, h⟩) hVb hb
    rcases hρ with rfl | rfl
    · exact slb_evVal (Set.mem_insert _ _) hVa (lab hVa (by simpa using sa))
    · exact slb_evVal (Set.mem_insert_of_mem _ rfl) hVb (lab hVb sb)

end

end SweepEv

end Chazelle.Core
