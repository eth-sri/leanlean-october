module

public import Chazelle.Core.DownPhaseTransClip
public import Chazelle.Rwx

/-!
# WP-M (T, part 4): regions and degrees after the transition

For the top chain `C` of a simple polygon `Q` (last edge not horizontal) and a chord family `F₀`
of `chainModel C`, with pieces `S₀ = pieces Q F₀`:
* every point of a chord of `F₀` inside `Q` lies on a piece (`mem_piece`);
* every region `V` of `S₀` lies in a region `U` of `F₀` (`exists_chain_region`);
* **(T2)** the degree of `V` is at most the degree of `U` (`deg_le`): each exit of `V` is the
  piece of an exit of `U`, and different exits of `V` come from different chords (`one_piece`).
-/

namespace Chazelle.Core

namespace Trans

@[expose] public section

open Set
open Chazelle.Chain (IsHChordIn TouchesIn freeIn regionsIn)
open Chazelle.Visibility (hseg)

variable {Q : Polygon} {C : Chain}

/-- **Every interior point of a chain chord lies on a piece.** -/
theorem mem_piece (hQ : Q.Simple) (T : Top Q C) {F₀ : Set (Set Point)}
    (hF₀ : F₀ ⊆ (chainModel C).Adm) {c : Set Point} (hc : c ∈ F₀) {z : Point} (hzc : z ∈ c)
    (hzD : z ∈ (interiorModel Q).D) : ∃ d ∈ pieces Q F₀, z ∈ d := by
  obtain ⟨y, a, b, hch, -, rfl⟩ := hF₀ hc
  obtain ⟨hzy, hza, hzb⟩ := hzc
  have hdom := T.interior_sub_dom hQ
  have hz : ((z.1, y) : Point) ∈ Q.filled \ Q.boundary := by
    rwx [← hzy]
  obtain ⟨a', b', ha', ha'x, hxb', hb', hch'⟩ := sub_chord ⟨hza, hzb⟩
    (fun h => hch.left_not (hdom h)) (fun h => hch.right_not (hdom h)) hz hQ
  refine ⟨hseg y a' b', ⟨⟨y, a', b', hch', rfl⟩, hseg y a b, hc, fun p hp =>
    ⟨hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩, hzy, ha'x.le, hxb'.le⟩

/-- **Every region of the pieces lies in a region of the chain family.** -/
theorem exists_chain_region (hQ : Q.Simple) (T : Top Q C) {F₀ : Set (Set Point)}
    (hF₀ : F₀ ⊆ (chainModel C).Adm) {V : Set Point}
    (hV : V ∈ (interiorModel Q).regions (pieces Q F₀)) :
    ∃ U ∈ (chainModel C).regions F₀, V ⊆ U := by
  obtain ⟨v, hv⟩ := Chazelle.Chain.regionsIn_nonempty hV
  have hfree : V ⊆ freeIn (chainModel C).D F₀ := by
    intro z hz
    have hzV := Chazelle.Chain.regionsIn_subset hV hz
    refine ⟨T.interior_sub_dom hQ hzV.1, fun ⟨c, hc, hzc⟩ => ?_⟩
    obtain ⟨d, hd, hzd⟩ := mem_piece hQ T hF₀ hc hzc hzV.1
    exact hzV.2 ⟨d, hd, hzd⟩
  exact ⟨_, ⟨v, hfree hv, rfl⟩,
    (Chazelle.Chain.regionsIn_isPreconnected hV).subset_connectedComponentIn hv hfree⟩

/-- **(T2) The degree does not grow.** -/
theorem deg_le (hQ : Q.Simple) (T : Top Q C) (hh : (Q.vtx C.m).2 ≠ (Q.vtx 0).2)
    {F₀ : Set (Set Point)} (hF₀ : (chainModel C).ChordFamily C.P F₀) {U V : Set Point}
    (hVU : V ⊆ U) :
    (interiorModel Q).deg (pieces Q F₀) V ≤ (chainModel C).deg F₀ U := by
  classical
  unfold Model.deg
  have hch : ∀ d ∈ pieces Q F₀, ∃ c ∈ F₀, d ⊆ c := fun d hd => hd.2
  choose! f hf hfd using hch
  have hdom := T.interior_sub_dom hQ
  refine Set.ncard_le_ncard_of_injOn f ?_ ?_ (hF₀.1.subset fun c hc => hc.1)
  · rintro d ⟨hd, z, ⟨hzd, hzD⟩, hzcl⟩
    exact ⟨hf d hd, z, ⟨hfd d hd hzd, hdom hzD⟩, closure_mono hVU hzcl⟩
  · intro d₁ h₁ d₂ h₂ e
    obtain ⟨y, a, b, hc, -, hcab⟩ := hF₀.2.1 (hf d₁ h₁.1)
    have s1 := hfd d₁ h₁.1
    have s2 := hfd d₂ h₂.1
    rw [← e] at s2
    rw [hcab] at s1 s2
    exact one_piece hQ T hh hc h₁.1.1 h₂.1.1 s1 s2

/-- **(T2) The pieces of a conformal chain family are conformal.** -/
theorem degLe_pieces (hQ : Q.Simple) (T : Top Q C) (hh : (Q.vtx C.m).2 ≠ (Q.vtx 0).2)
    {F₀ : Set (Set Point)} (hF₀ : (chainModel C).ChordFamily C.P F₀) {D : ℕ}
    (hD : (chainModel C).DegLe F₀ D) : (interiorModel Q).DegLe (pieces Q F₀) D := by
  intro V hV
  obtain ⟨U, hU, hVU⟩ := exists_chain_region hQ T hF₀.2.1 hV
  exact (deg_le hQ T hh hF₀ hVU).trans (hD U hU)

end

end Trans

end Chazelle.Core
