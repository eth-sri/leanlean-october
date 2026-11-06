module

public import Chazelle.Core.DownPhaseDropWt

/-!
# WP-M (B3′, part 10): degrees after dropping a bottom block of chords

Finding M6: dropping the wall-to-wall chords of a chain normal form does not raise the degree
bound.  This file proves it in a slab form for any chord system in a box (`degLe_drop`).

The dropped chords lie at heights `≤ ys`, the kept chords at heights `≥ yp > ys`, and the open
slab `U = (-R, R) × (-R, yp)` lies in the domain.
* A region `W` of the kept chords missing `U` misses the dropped chords, so it is a region of all
  the chords with the same exits.
* A region `W` meeting `U` lies in `U ∪ X`, where `X` is the region of all the chords containing
  the thin slab `(-R, R) × (ys, yp)`.  Every kept exit of `W` is at height `≥ yp`, so it touches
  `X`.  Hence `deg W ≤ deg X`.
-/

namespace Chazelle.Core

namespace BoxT

@[expose] public section

open Set
open Chazelle.Chain (ChordSystem freeIn regionsIn TouchesIn)

/-- **Dropping a bottom block of chords keeps the degree bound.** -/
theorem degLe_drop {D : Set Point} {F F' : Set (Set Point)} (hsys : ChordSystem D F)
    (hfin : F.Finite) (hsub : F' ⊆ F) {R ys yp : ℝ} (hR : 0 < R) (hys : -R ≤ ys) (hlt : ys < yp)
    (hDbox : ∀ z ∈ D, |z.1| < R ∧ |z.2| < R)
    (hUD : ∀ z : Point, -R < z.1 → z.1 < R → -R < z.2 → z.2 < yp → z ∈ D)
    (hF' : ∀ c ∈ F', ∀ z ∈ c, yp ≤ z.2)
    (hW : ∀ c ∈ F, c ∉ F' → ∀ z ∈ c, z.2 ≤ ys)
    {d : ℕ} (hd : ∀ U ∈ regionsIn D F, {c | c ∈ F ∧ TouchesIn D c U}.ncard ≤ d) :
    ∀ W ∈ regionsIn D F', {c | c ∈ F' ∧ TouchesIn D c W}.ncard ≤ d := by
  set U : Set Point := Ioo (-R) R ×ˢ Ioo (-R) yp
  set Up : Set Point := Ioo (-R) R ×ˢ Ioo ys yp
  have hUo : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hUpc : IsPreconnected Up := isPreconnected_Ioo.prod isPreconnected_Ioo
  have hUpF : Up ⊆ freeIn D F := by
    intro z hz
    refine ⟨hUD z hz.1.1 hz.1.2 (by linarith [hz.2.1]) hz.2.2, ?_⟩
    rintro ⟨c, hc, hzc⟩
    by_cases hc' : c ∈ F'
    · linarith [hF' c hc' z hzc, hz.2.2]
    · linarith [hW c hc hc' z hzc, hz.2.1]
  set p0 : Point := (0, (ys + yp) / 2)
  have hp0 : p0 ∈ Up := ⟨⟨by simp [p0]; linarith, by simp [p0]; linarith⟩,
    ⟨by simp [p0]; linarith, by simp [p0]; linarith⟩⟩
  set X := connectedComponentIn (freeIn D F) p0
  have hXr : X ∈ regionsIn D F := ⟨p0, hUpF hp0, rfl⟩
  have hXo : IsOpen X := hsys.regionsIn_open subset_rfl hXr
  have hUpX : Up ⊆ X := hUpc.subset_connectedComponentIn hp0 hUpF
  -- points of the closure of `U` above `ys` are in the closure of `X`
  have hclU : ∀ z, z ∈ closure U → ys < z.2 → z ∈ closure X := by
    intro z hz hzy
    have hO : IsOpen {w : Point | ys < w.2} := isOpen_lt continuous_const continuous_snd
    have := hO.inter_closure ⟨hzy, hz⟩
    refine closure_mono ?_ this
    rintro w ⟨hw1, hw2⟩
    exact hUpX ⟨hw2.1, hw1, hw2.2.2⟩
  have hclU' : closure U ⊆ {w : Point | w.2 ≤ yp} :=
    closure_minimal (fun w hw => hw.2.2.le) (isClosed_le continuous_snd continuous_const)
  -- a free point in the closure of `X` is in `X`
  have hfreeX : ∀ w, w ∈ freeIn D F → w ∈ closure X → w ∈ X := by
    intro w hw hwc
    set Y := connectedComponentIn (freeIn D F) w
    have hYr : Y ∈ regionsIn D F := ⟨w, hw, rfl⟩
    have hYo : IsOpen Y := hsys.regionsIn_open subset_rfl hYr
    have hwY : w ∈ Y := mem_connectedComponentIn hw
    obtain ⟨v, hvY, hvX⟩ := mem_closure_iff.1 hwc Y hYo hwY
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hYr hXr with h | h
    · rwa [← h]
    · exact absurd (h.le_bot ⟨hvY, hvX⟩) (fun h => h)
  intro W hWr
  have hWF' : W ⊆ freeIn D F' := Chazelle.Chain.regionsIn_subset hWr
  have hfin' : {c | c ∈ F ∧ TouchesIn D c X}.Finite := hfin.subset fun c hc => hc.1
  by_cases hWU : (W ∩ U).Nonempty
  · -- `W ⊆ U ∪ X`
    have hsubW : W ⊆ U ∪ X := by
      refine (Chazelle.Chain.regionsIn_isPreconnected hWr).subset_of_closure_inter_subset
        (hUo.union hXo) (by obtain ⟨w, h1, h2⟩ := hWU; exact ⟨w, h1, Or.inl h2⟩) ?_
      rintro w ⟨hwc, hwW⟩
      have hwD : w ∈ D := (hWF' hwW).1
      obtain ⟨hb1, hb2⟩ := hDbox w hwD
      rw [abs_lt] at hb1 hb2
      by_cases hwF : w ∈ ⋃₀ F
      · obtain ⟨c, hc, hwc'⟩ := hwF
        have hc' : c ∉ F' := fun h => (hWF' hwW).2 ⟨c, h, hwc'⟩
        have := hW c hc hc' w hwc'
        exact Or.inl ⟨⟨hb1.1, hb1.2⟩, ⟨hb2.1, by linarith⟩⟩
      · have hwfree : w ∈ freeIn D F := ⟨hwD, hwF⟩
        rw [closure_union] at hwc
        rcases hwc with hwc | hwc
        · by_cases hwy : w.2 < yp
          · exact Or.inl ⟨⟨hb1.1, hb1.2⟩, ⟨hb2.1, hwy⟩⟩
          · have := hclU' hwc
            simp only [mem_ofPred_eq] at this
            exact Or.inr (hfreeX w hwfree (hclU w hwc (by linarith)))
        · exact Or.inr (hfreeX w hwfree hwc)
    refine le_trans (Set.ncard_le_ncard ?_ hfin') (hd X hXr)
    rintro c ⟨hc, z, ⟨hzc, hzD⟩, hzW⟩
    refine ⟨hsub hc, z, ⟨hzc, hzD⟩, ?_⟩
    have hzy := hF' c hc z hzc
    have hz := closure_mono hsubW hzW
    rw [closure_union] at hz
    rcases hz with hz | hz
    · exact hclU z hz (by linarith)
    · exact hz
  · -- `W` misses the dropped chords: it is a region of `F`
    have hWF : W ⊆ freeIn D F := by
      intro w hw
      refine ⟨(hWF' hw).1, ?_⟩
      rintro ⟨c, hc, hwc⟩
      have hc' : c ∉ F' := fun h => (hWF' hw).2 ⟨c, h, hwc⟩
      have hwy := hW c hc hc' w hwc
      obtain ⟨hb1, hb2⟩ := hDbox w (hWF' hw).1
      rw [abs_lt] at hb1 hb2
      exact hWU ⟨w, hw, ⟨hb1.1, hb1.2⟩, ⟨hb2.1, by linarith⟩⟩
    obtain ⟨w0, hw0⟩ := Chazelle.Chain.regionsIn_nonempty hWr
    have hWeq : W = connectedComponentIn (freeIn D F) w0 := by
      apply Subset.antisymm
      · exact (Chazelle.Chain.regionsIn_isPreconnected hWr).subset_connectedComponentIn hw0 hWF
      · rw [Chazelle.Chain.regionsIn_eq_component hWr hw0]
        exact connectedComponentIn_mono w0 (Chazelle.Chain.freeIn_anti D hsub)
    have hWr' : W ∈ regionsIn D F := ⟨w0, hWF hw0, hWeq⟩
    refine le_trans (Set.ncard_le_ncard ?_ (hfin.subset fun c hc => hc.1)) (hd W hWr')
    rintro c ⟨hc, ht⟩
    exact ⟨hsub hc, ht⟩

end

end BoxT

end Chazelle.Core
