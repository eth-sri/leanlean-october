module

public import Chazelle.Core.DownPhaseDegSide
public import Chazelle.RewriteTactics

/-!
# Degree bound on host curves, part 4: the degree bound

`HSegObs.deg_leH`: in the setting `HSegObs.GoodH R S t` (segment obstacles that may be horizontal
and share heights, at most `t` vertices per height), every region of a finite family of
horizontal chords of the domain containing the vertex chords is touched by at most `2 (t + 1)`
chords.  The proof is `SegObs.deg_le_four` with the side count `Trap.ncard_sideH` in place of the
two-chord side count: above the region lies either one crossing chord or at most `t + 1` chords of
the top side, and symmetrically below.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (IsHChordIn freeIn regionsIn TouchesIn box)
open Chazelle.Visibility (hseg)
open Chazelle.Geometry (point_ext)

namespace HSegObs

open SegObs SegObs.Trap

variable {R : ℝ} {S : Set (Point × Point)} {t : ℕ}

/-- **Degree `≤ 2 (t + 1)`**: every region of a finite family of horizontal chords of the domain
that contains the vertex chords is touched by at most `2 (t + 1)` of them. -/
theorem deg_leH (hS : GoodH R S t) {G : Set (Set Point)} (hG : ∀ c ∈ G, HCD (dom R S) c)
    (hGfin : G.Finite) (hfull : FullAt R S G) {U : Set Point}
    (hU : U ∈ regionsIn (dom R S) G) :
    {c | c ∈ G ∧ TouchesIn (dom R S) c U}.ncard ≤ 2 * (t + 1) := by
  classical
  set D := dom R S with hD
  obtain ⟨q, hqf, rfl⟩ := hU
  obtain ⟨sL, sR, y₁, y₂, h⟩ := exists_trapH hS hfull hqf.1 hqf.2
  set T := tr sL sR y₁ y₂ with hTdef
  set U := connectedComponentIn (freeIn D G) q with hUdef
  have hUT  := h.region_subsetH hS hfull hqf
  have hTD  := h.tr_subset_domH hS
  have hqT  := hUT (mem_connectedComponentIn hqf)
  have hfreeU : U ⊆ freeIn D G := connectedComponentIn_subset _ _
  have hcl : closure U ⊆ ctr sL sR y₁ y₂ :=
    (closure_mono hUT).trans (closure_tr_subset _ _ _ _)
  have hqy₁  := hqT.1
  have hqy₂  := hqT.2.1
  -- a domain point of the closed trapezoid at a middle height is inside
  have hmid : ∀ z ∈ D, z ∈ ctr sL sR y₁ y₂ → y₁ < z.2 → z.2 < y₂ → z ∈ T := by
    intro z hzD hzC hz1 hz2
    obtain ⟨h1, h2, h3, h4⟩ := hzC
    exact ⟨hz1, hz2, lt_of_le_of_ne h3 fun e => hzD.2 (h.memLH h1 h2 e.symm),
      lt_of_le_of_ne h4 fun e => hzD.2 (h.memRH h1 h2 e)⟩
  -- a chord meeting `T` contains its whole slice
  have hslice : ∀ c ∈ G, ∀ z ∈ c, z ∈ T → ∀ w ∈ T, w.2 = z.2 → w ∈ c := by
    intro c hc z hz hzT w hwT hwz
    obtain ⟨y, a, b, hh, rfl⟩ := hG c hc
    have hzy  := hz.1
    refine mem_of_joined hh hz (hTD hzT) (hwz.trans hzy) fun s h1 h2 => hTD ?_
    have hseg : Chazelle.segment z w ⊆ T :=
      Geometry.segment_subset_of_convex (convex_tr _ _ _ _) hzT hwT
    apply hseg
    rw [Visibility.segment_horizontal_eq_hseg hwz.symm]
    exact ⟨hzy.symm, h1, h2⟩
  -- `U` is on one side of a chord crossing `T`
  have hno : ∀ c ∈ G, ∀ z ∈ c, z ∈ T → ∀ p ∈ U, p.2 ≠ z.2 := fun c hc z hz hzT p hp he =>
    (hfreeU hp).2 ⟨c, hc, hslice c hc z hz hzT p (hUT hp) he⟩
  have hUc := (isPreconnected_connectedComponentIn : IsPreconnected U)
  have hbelow : ∀ c ∈ G, ∀ z ∈ c, z ∈ T → q.2 < z.2 → ∀ p ∈ U, p.2 < z.2 := by
    intro c hc z hz hzT hqz
    have := hUc.subset_left_of_subset_union (u := {p : Point | p.2 < z.2})
      (v := {p : Point | z.2 < p.2}) (isOpen_lt continuous_snd continuous_const)
      (isOpen_lt continuous_const continuous_snd)
      (Set.disjoint_left.2 fun p (h1 : _ < _) (h2 : _ < _) => lt_asymm h1 h2)
      (fun p hp => (lt_or_gt_of_ne (hno c hc z hz hzT p hp)).elim Or.inl Or.inr)
      ⟨q, mem_connectedComponentIn hqf, hqz⟩
    exact fun p hp => this hp
  have habove : ∀ c ∈ G, ∀ z ∈ c, z ∈ T → z.2 < q.2 → ∀ p ∈ U, z.2 < p.2 := by
    intro c hc z hz hzT hqz
    have := hUc.subset_left_of_subset_union (u := {p : Point | z.2 < p.2})
      (v := {p : Point | p.2 < z.2}) (isOpen_lt continuous_const continuous_snd)
      (isOpen_lt continuous_snd continuous_const)
      (Set.disjoint_left.2 fun p (h1 : _ < _) (h2 : _ < _) => lt_asymm h1 h2)
      (fun p hp => (lt_or_gt_of_ne (hno c hc z hz hzT p hp)).elim Or.inr Or.inl)
      ⟨q, mem_connectedComponentIn hqf, hqz⟩
    exact fun p hp => this hp
  have hclle : ∀ y : ℝ, (∀ p ∈ U, p.2 < y) → ∀ p ∈ closure U, p.2 ≤ y := fun y hy =>
    fun p hp => closure_minimal (fun x hx => (hy x hx).le)
      (isClosed_le continuous_snd continuous_const) hp
  have hclge : ∀ y : ℝ, (∀ p ∈ U, y < p.2) → ∀ p ∈ closure U, y ≤ p.2 := fun y hy =>
    fun p hp => closure_minimal (fun x hx => (hy x hx).le)
      (isClosed_le continuous_const continuous_snd) hp
  -- the two classes of exit chords
  set E₁ := {c | c ∈ G ∧ ∃ z ∈ c, z ∈ D ∧ z ∈ closure U ∧ (z.2 = y₂ ∨ (q.2 < z.2 ∧ z.2 < y₂))}
    with hE₁
  set E₂ := {c | c ∈ G ∧ ∃ z ∈ c, z ∈ D ∧ z ∈ closure U ∧ (z.2 = y₁ ∨ (y₁ < z.2 ∧ z.2 < q.2))}
    with hE₂
  have hsub : {c | c ∈ G ∧ TouchesIn D c U} ⊆ E₁ ∪ E₂ := by
    rintro c ⟨hc, z, ⟨hz, hzD⟩, hzU⟩
    obtain ⟨h1, h2, -, -⟩ := hcl hzU
    rcases h2.lt_or_eq with h2 | h2
    · rcases h1.lt_or_eq with h1 | h1
      · have hzT := hmid z hzD (hcl hzU) h1 h2
        rcases lt_or_gt_of_ne (hno c hc z hz hzT q (mem_connectedComponentIn hqf)) with h3 | h3
        · exact Or.inl ⟨hc, z, hz, hzD, hzU, Or.inr ⟨h3, h2⟩⟩
        · exact Or.inr ⟨hc, z, hz, hzD, hzU, Or.inr ⟨h1, h3⟩⟩
      · exact Or.inr ⟨hc, z, hz, hzD, hzU, Or.inl h1.symm⟩
    · exact Or.inl ⟨hc, z, hz, hzD, hzU, Or.inl h2⟩
  -- at most two chords above
  have hE₁ : E₁.ncard ≤ t + 1 := by
    by_cases hA : ∃ c₀ ∈ E₁, ∃ z₀ ∈ c₀, z₀ ∈ D ∧ z₀ ∈ closure U ∧ q.2 < z₀.2 ∧ z₀.2 < y₂
    · obtain ⟨c₀, hc₀, z₀, hz₀, hz₀D, hz₀U, hq0, h0⟩ := hA
      have hz₀T := hmid z₀ hz₀D (hcl hz₀U) (hqy₁.trans hq0) h0
      have hU0 := hbelow c₀ hc₀.1 z₀ hz₀ hz₀T hq0
      have hsub1 : E₁ ⊆ {c₀} := by
        rintro c ⟨hc, z, hz, hzD, hzU, hzc⟩
        have hz0 := hclle _ hU0 z hzU
        have hmz : q.2 < z.2 ∧ z.2 < y₂ := by
          rcases hzc with e | e
          · rwli [e] at hz0
          · exact e
        have hzT := hmid z hzD (hcl hzU) (hqy₁.trans hmz.1) hmz.2
        have hUz := hbelow c hc z hz hzT hmz.1
        have hz0' := hclle _ hUz z₀ hz₀U
        have heq  := le_antisymm hz0' hz0
        have hz₀c := hslice c hc z hz hzT z₀ hz₀T heq
        exact eq_of_common (hG c hc) (hG c₀ hc₀.1) hz₀c hz₀ hz₀D
      calc E₁.ncard ≤ ({c₀} : Set (Set Point)).ncard := ncard_le_ncard hsub1 (finite_singleton _)
        _ ≤ t + 1 := by rwo [ncard_singleton]
    · push Not at hA
      have htop : ∀ c ∈ E₁, ∃ z ∈ c, z ∈ D ∧ z ∈ closure U ∧ z.2 = y₂ := by
        rintro c hc
        obtain ⟨hcG, z, hz, hzD, hzU, hzc⟩ := hc
        rcases hzc with e | e
        · exact ⟨z, hz, hzD, hzU, e⟩
        · exact absurd e.2 (not_lt.2 (hA c ⟨hcG, z, hz, hzD, hzU, Or.inr e⟩ z hz hzD hzU e.1))
      refine h.ncard_sideH hS h.y₁_lt_y₂.le le_rfl (sideOK_top hS h) fun c hc => ?_
      obtain ⟨z, hz, hzD, hzU, hzy⟩ := htop c hc
      obtain ⟨-, -, h3, h4⟩ := hcl hzU
      rw [hzy] at h3 h4
      exact ⟨hG c hc.1, z, hz, hzD, hzy, h3, h4⟩
  -- at most two chords below
  have hE₂ : E₂.ncard ≤ t + 1 := by
    by_cases hA : ∃ c₀ ∈ E₂, ∃ z₀ ∈ c₀, z₀ ∈ D ∧ z₀ ∈ closure U ∧ y₁ < z₀.2 ∧ z₀.2 < q.2
    · obtain ⟨c₀, hc₀, z₀, hz₀, hz₀D, hz₀U, h0, hq0⟩ := hA
      have hz₀T := hmid z₀ hz₀D (hcl hz₀U) h0 (hq0.trans hqy₂)
      have hU0 := habove c₀ hc₀.1 z₀ hz₀ hz₀T hq0
      have hsub1 : E₂ ⊆ {c₀} := by
        rintro c ⟨hc, z, hz, hzD, hzU, hzc⟩
        have hz0 := hclge _ hU0 z hzU
        have hmz : y₁ < z.2 ∧ z.2 < q.2 := by
          rcases hzc with e | e
          · rwli [e] at hz0
          · exact e
        have hzT := hmid z hzD (hcl hzU) hmz.1 (hmz.2.trans hqy₂)
        have hUz := habove c hc z hz hzT hmz.2
        have hz0' := hclge _ hUz z₀ hz₀U
        have heq  := le_antisymm hz0 hz0'
        have hz₀c := hslice c hc z hz hzT z₀ hz₀T heq
        exact eq_of_common (hG c hc) (hG c₀ hc₀.1) hz₀c hz₀ hz₀D
      calc E₂.ncard ≤ ({c₀} : Set (Set Point)).ncard := ncard_le_ncard hsub1 (finite_singleton _)
        _ ≤ t + 1 := by rwo [ncard_singleton]
    · push Not at hA
      have hbot : ∀ c ∈ E₂, ∃ z ∈ c, z ∈ D ∧ z ∈ closure U ∧ z.2 = y₁ := by
        rintro c hc
        obtain ⟨hcG, z, hz, hzD, hzU, hzc⟩ := hc
        rcases hzc with e | e
        · exact ⟨z, hz, hzD, hzU, e⟩
        · exact absurd e.2 (not_lt.2 (hA c ⟨hcG, z, hz, hzD, hzU, Or.inr e⟩ z hz hzD hzU e.1))
      refine h.ncard_sideH hS le_rfl h.y₁_lt_y₂.le (sideOK_bot hS h) fun c hc => ?_
      obtain ⟨z, hz, hzD, hzU, hzy⟩ := hbot c hc
      obtain ⟨-, -, h3, h4⟩ := hcl hzU
      rw [hzy] at h3 h4
      exact ⟨hG c hc.1, z, hz, hzD, hzy, h3, h4⟩
  have hfin12 : (E₁ ∪ E₂).Finite :=
    (hGfin.subset fun c hc => hc.1).union (hGfin.subset fun c hc => hc.1)
  calc {c | c ∈ G ∧ TouchesIn D c U}.ncard ≤ (E₁ ∪ E₂).ncard := ncard_le_ncard hsub hfin12
    _ ≤ E₁.ncard + E₂.ncard := ncard_union_le _ _
    _ ≤ 2 * (t + 1) := by omega

end HSegObs

end

end Chazelle.Core
