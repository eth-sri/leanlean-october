module

public import Chazelle.Core.SweepEvKey

/-!
# The sweep (WP-D), stage 3: ties on the `C₁` part and the pieces of a chord of `S₂`

* `tie_dom`: two distinct chords of `F₂⁺` attached at one position off the open right stretch
  meet at a point of the domain of `C₂`, or at the shared vertex;
* `parent_unique`: a chord with two distinct points inside two chords of `S₂` determines them;
* `pieces_le_two`: three chords of `F₂⁺` inside one chord `c ∈ S₂`, attached at points of the
  domain of `C₂`, are not pairwise distinct (each is the piece seen from an end of `c`,
  `piece_of_parent`).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideInArc)
open WalkEmbed

namespace Sweep

section Tie

variable {J : Merge.Junction}

/-- Every point of an admissible chord of `C` attached at a position has the height of the
position's point. -/
theorem attach_snd_eq (hP : J.P.Simple) {f : Set Point} (hf : f ∈ Merge.augChords J.whole)
    {p : ℕ} {t : ℝ} (hA : SideAttach (chainModel J.whole).W f p t) {z : Point} (hz : z ∈ f) :
    z.2 = (sidePt (chainModel J.whole).W p t).2 := by
  have hM : WalkAx (chainModel J.whole) := FactsChain.walkAx J.whole hP
  obtain ⟨a, b, -, hfab, hy, -⟩ := hM.ends f hf
  have key : ∀ w ∈ f, w.2 = a.2 := by
    intro w hw
    rw [hfab] at hw
    obtain ⟨s, -, -, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hw
    simp only [Geometry.lerp_snd, hy, sub_self, mul_zero, add_zero]
  rw [key z hz, key _ hA.2.2.2.1]

/-- **The point of a tie off the open right stretch** is in the domain of `C₂` or is the shared
vertex. -/
theorem tie_dom (hP : J.P.Simple) {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    (hS₂f : S₂.Finite) {e e' : Set Point} (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂)
    (hne : e ≠ e') {p : ℕ} {t : ℝ} (hA : SideAttach (chainModel J.whole).W e p t)
    (hA' : SideAttach (chainModel J.whole).W e' p t)
    (hout : ¬ (0 < oW J (p + t) ∧ oW J (p + t) < Lst J)) :
    sidePt (chainModel J.whole).W p t ∈ J.right.dom ∨
      sidePt (chainModel J.whole).W p t = J.shared := by
  have hC := corr_right0 J hP hS₂ hS₂f
  have hM := hC.hM
  set x := sidePt (chainModel J.whole).W p t
  have hpt : ∀ {f : Set Point}, f ∈ F₂plus J S₂ → SideAttach (chainModel J.whole).W f p t →
      ∃ z ∈ f, z ∈ J.whole.dom ∧ z.2 = x.2 := by
    intro f hf hAf
    obtain ⟨z, hz, hzD⟩ := exists_mem_dom hM (hC.hF hf) hAf
    exact ⟨z, hz, hzD, attach_snd_eq hP (F₂plus_subset J hS₂ hf) hAf hz⟩
  -- `x` lies strictly inside the box
  have hbox : x ∈ Chain.box J.whole.radius := by
    rcases hM.tie_pair hC.hF he he' hne hA hA' with ⟨hE, hW⟩ | ⟨hW, hE⟩
    · obtain ⟨zE, hzE, hzED, hzE2⟩ := hpt he hA
      obtain ⟨zW, hzW, hzWD, -⟩ := hpt he' hA'
      have h1 := (J.whole.dom_subset_box hzED)
      have h2 := (J.whole.dom_subset_box hzWD)
      have e1 := hE zE hzE
      have e2 := hW zW hzW
      refine ⟨abs_lt.2 ⟨?_, ?_⟩, by rw [← hzE2]; exact h1.2⟩
      · linarith [(abs_lt.1 h2.1).1]
      · linarith [(abs_lt.1 h1.1).2]
    · obtain ⟨zE, hzE, hzED, hzE2⟩ := hpt he' hA'
      obtain ⟨zW, hzW, hzWD, -⟩ := hpt he hA
      have h1 := (J.whole.dom_subset_box hzED)
      have h2 := (J.whole.dom_subset_box hzWD)
      have e1 := hE zE hzE
      have e2 := hW zW hzW
      refine ⟨abs_lt.2 ⟨?_, ?_⟩, by rw [← hzE2]; exact h1.2⟩
      · linarith [(abs_lt.1 h2.1).1]
      · linarith [(abs_lt.1 h1.1).2]
  have hR : J.right.radius = J.whole.radius := FuseMath.radius_of_P J (C' := J.right) rfl
  have hy : x.2 ≤ J.right.top.2 := F₂plus_snd_le J hS₂ he hA.2.2.2.1
  by_cases hxd : x ∈ J.right.dom
  · exact Or.inl hxd
  · right
    rcases (Merge.not_mem_dom_iff J.right hy).1 hxd with h | h
    · exact absurd (hR ▸ hbox) h
    · by_contra hv
      exact hout (off_right_pt J hP hS₂ hS₂f hA.1 hA.2.1 hA.2.2.1 h hv)

/-- **A chord of `S₂` containing two distinct points of a chord is determined.** -/
theorem parent_unique {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {c c' : Set Point} (hc : c ∈ S₂) (hc' : c' ∈ S₂) {u w : Point} (huw : u ≠ w) (hu : u ∈ c)
    (hw : w ∈ c) (hu' : u ∈ c') (hw' : w ∈ c') : c = c' := by
  obtain ⟨y, a, b, hH, -, rfl, -, -⟩ := Merge.augChords_spec (hS₂ hc)
  obtain ⟨y', a', b', hH', -, rfl, -, -⟩ := Merge.augChords_spec (hS₂ hc')
  have hx : u.1 ≠ w.1 := fun h => huw (Prod.ext h (hu.1.trans hw.1.symm))
  have hconv : ∀ {y a b : ℝ}, u ∈ Visibility.hseg y a b → w ∈ Visibility.hseg y a b →
      (((u.1 + w.1) / 2, y) : Point) ∈ Visibility.hseg y a b ∧
        (((u.1 + w.1) / 2, y) : Point) ≠ (a, y) ∧ (((u.1 + w.1) / 2, y) : Point) ≠ (b, y) := by
    intro y a b hu hw
    obtain ⟨-, h1, h2⟩ := hu
    obtain ⟨-, h3, h4⟩ := hw
    refine ⟨⟨rfl, by simp only; linarith, by simp only; linarith⟩, fun h => ?_, fun h => ?_⟩
    · have := congrArg Prod.fst h
      simp only at this
      rcases lt_or_gt_of_ne hx with h5 | h5 <;> linarith
    · have := congrArg Prod.fst h
      simp only at this
      rcases lt_or_gt_of_ne hx with h5 | h5 <;> linarith
  have hyy : y = y' := hu.1.symm.trans hu'.1
  subst hyy
  obtain ⟨hm, hma, hmb⟩ := hconv hu hw
  obtain ⟨hm', -, -⟩ := hconv hu' hw'
  rcases Chain.hchordIn_inter hH hH' hm hm' with ⟨-, rfl, rfl⟩ | ⟨h1, -⟩
  · rfl
  · rcases h1 with h | h
    · exact absurd h hma
    · exact absurd h hmb

/-- **At most two pieces of a chord of `S₂`**: three chords of `F₂⁺` inside `c ∈ S₂`, attached at
points of the domain of `C₂`, are not pairwise distinct. -/
theorem pieces_le_two (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) {c : Set Point} (hc : c ∈ S₂) {e₁ e₂ e₃ : Set Point}
    (he₁ : e₁ ∈ F₂plus J S₂) (he₂ : e₂ ∈ F₂plus J S₂) (he₃ : e₃ ∈ F₂plus J S₂) (h₁ : e₁ ⊆ c)
    (h₂ : e₂ ⊆ c) (h₃ : e₃ ⊆ c) {p₁ p₂ p₃ : ℕ} {t₁ t₂ t₃ : ℝ}
    (hA₁ : SideAttach (chainModel J.whole).W e₁ p₁ t₁)
    (hA₂ : SideAttach (chainModel J.whole).W e₂ p₂ t₂)
    (hA₃ : SideAttach (chainModel J.whole).W e₃ p₃ t₃)
    (hD₁ : sidePt (chainModel J.whole).W p₁ t₁ ∈ J.right.dom)
    (hD₂ : sidePt (chainModel J.whole).W p₂ t₂ ∈ J.right.dom)
    (hD₃ : sidePt (chainModel J.whole).W p₃ t₃ ∈ J.right.dom) :
    e₁ = e₂ ∨ e₁ = e₃ ∨ e₂ = e₃ := by
  rcases piece_of_parent J hP hS₂ he₁ hc h₁ hA₁ hD₁ with ⟨-, k₁⟩ | ⟨-, k₁⟩ <;>
    rcases piece_of_parent J hP hS₂ he₂ hc h₂ hA₂ hD₂ with ⟨-, k₂⟩ | ⟨-, k₂⟩ <;>
    rcases piece_of_parent J hP hS₂ he₃ hc h₃ hA₃ hD₃ with ⟨-, k₃⟩ | ⟨-, k₃⟩
  all_goals first
    | exact Or.inl (k₁.trans k₂.symm)
    | exact Or.inr (Or.inl (k₁.trans k₃.symm))
    | exact Or.inr (Or.inr (k₂.trans k₃.symm))

end Tie

end Sweep

end

end Chazelle.Core
