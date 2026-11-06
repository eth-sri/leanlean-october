module

public import Chazelle.Golf

public import Chazelle.Core.FactsL23

/-!
# WP-B: the two sides of a chord and the region tree (review finding C5)

* `chordSides : ChordSidesSpec` — every chord `c` of a finite admissible family has two distinct
  side regions, the region just above and the region just below its open part (uniformly along
  the chord), and these are exactly the regions `c` touches.  This is the exact splitting of
  `Chazelle.Chain.ChordSystem` (`regionsIn_insert`, `halfDisk_all`, `touches_iff_of_split`).
* `regionTree : RegionTreeSpec` — finitely many regions, one more than chords, and the region
  graph (regions sharing a chord) is connected (`ChordSystem.regionsIn_finite_ncard`,
  `ChordSystem.dualGraph_reachable`).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (ChordSystem freeIn regionsIn TouchesIn halfDisk)

/-- **The two sides of a chord in a chord system.** -/
theorem chordSides_of_system {D : Set Point} {F : Set (Set Point)} (hF : ChordSystem D F)
    {c : Set Point} (hc : c ∈ F) :
    ∃ U V, U ∈ regionsIn D F ∧ V ∈ regionsIn D F ∧ U ≠ V ∧
      (∀ z ∈ c, z ∈ D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), (z.1, z.2 + δ) ∈ U ∧ (z.1, z.2 - δ) ∈ V) ∧
      (∀ W ∈ regionsIn D F, TouchesIn D c W ↔ W = U ∨ W = V) := by
  set S := F \ {c} with hSdef
  have hS : S ⊆ F := fun d hd => hd.1
  have hcS : c ∉ S := fun h => h.2 rfl
  have hins : insert c S = F := insert_sdiff_singleton.trans (insert_eq_of_mem hc)
  obtain ⟨R, hR, hcR, R₁, R₂, hne, hunion, hR₁, hR₂, heq⟩ := hF.regionsIn_insert hS hc hcS
  have htouch := hF.touches_iff_of_split hS hc hcS hR hcR hunion hR₁ hR₂ heq
  have hRo : IsOpen R := hF.regionsIn_open hS hR
  have hRS : R ⊆ freeIn D S := Chazelle.Chain.regionsIn_subset hR
  obtain ⟨z₀, hz₀c, hz₀D⟩ := (hF.chord_inter_nonempty_isPreconnected hc).1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hRo z₀ (hcR ⟨hz₀c, hz₀D⟩)
  obtain ⟨ε₀, hε₀, hsep⟩ := hF.chord_separates_in subset_rfl hc hz₀c hz₀D
  set ε := min r ε₀ / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; have := lt_min hr hε₀; linarith
  have hεr : ε < r := by rw [hε]; have := min_le_left r ε₀; linarith
  have hεε : ε < ε₀ := by rw [hε]; have := min_le_right r ε₀; linarith
  obtain ⟨hp, hm, hpm⟩ := hsep ε hε0 hεε
  set U := connectedComponentIn (freeIn D F) (z₀.1, z₀.2 + ε) with hU
  set V := connectedComponentIn (freeIn D F) (z₀.1, z₀.2 - ε) with hV
  have hUr : U ∈ regionsIn D F := ⟨_, hp, rfl⟩
  have hVr : V ∈ regionsIn D F := ⟨_, hm, rfl⟩
  have hUr' : U ∈ regionsIn D (insert c S) := by rw [hins]; exact hUr
  have hVr' : V ∈ regionsIn D (insert c S) := by rw [hins]; exact hVr
  -- the half-disks at `z₀`
  have hhalf : ∀ τ : ℝ, (τ = 1 ∨ τ = -1) → ∀ X ∈ regionsIn D (insert c S),
      ((z₀.1, z₀.2 + τ * ε) : Point) ∈ X → halfDisk z₀ r τ ⊆ X := by
    intro τ hτ X hX hxX
    refine Chazelle.Chain.subset_regionsIn_of_inter hX (Chazelle.Chain.isPreconnected_halfDisk _ _ _)
      (hF.halfDisk_subset_freeIn_insert hc hz₀c (hball.trans hRS)) ⟨_, ?_, hxX⟩
    exact Chazelle.Chain.vert_mem_halfDisk hτ hε0 hεr
  have hUhalf : halfDisk z₀ r 1 ⊆ U :=
    hhalf 1 (Or.inl rfl) U hUr' (by rw [one_mul]; exact mem_connectedComponentIn hp)
  have hVhalf : halfDisk z₀ r (-1) ⊆ V :=
    hhalf (-1) (Or.inr rfl) V hVr' (by
      rw [show z₀.2 + -1 * ε = z₀.2 - ε by ring]; exact mem_connectedComponentIn hm)
  -- the side regions along the whole chord
  have hall : ∀ τ : ℝ, (τ = 1 ∨ τ = -1) → ∀ X ∈ regionsIn D (insert c S),
      halfDisk z₀ r τ ⊆ X → ∀ z ∈ c, z ∈ D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), (z.1, z.2 + τ * δ) ∈ X := by
    intro τ hτ X hX hsub z hzc hzD
    have hall := hF.halfDisk_all hc hRo hcR hRS hX hτ ⟨z₀, ⟨hz₀c, hz₀D⟩, r, hr, hball, hsub⟩
    obtain ⟨r', hr', hball'⟩ := Metric.isOpen_iff.1 hRo z (hcR ⟨hzc, hzD⟩)
    filter_upwards [Ioo_mem_nhdsGT hr'] with δ hδ
    exact hall z ⟨hzc, hzD⟩ r' hr' hball' (Chazelle.Chain.vert_mem_halfDisk hτ hδ.1 hδ.2)
  have hUne : U ≠ V := hpm
  -- `U` and `V` touch `c`
  have hcU : TouchesIn D c U :=
    ⟨z₀, ⟨hz₀c, hz₀D⟩, closure_mono hUhalf (Chazelle.Chain.mem_closure_halfDisk (Or.inl rfl) hr)⟩
  have hcV : TouchesIn D c V :=
    ⟨z₀, ⟨hz₀c, hz₀D⟩, closure_mono hVhalf (Chazelle.Chain.mem_closure_halfDisk (Or.inr rfl) hr)⟩
  rw [hins] at htouch
  refine ⟨U, V, hUr, hVr, hUne, fun z hzc hzD => ?_, fun W hW => ?_⟩
  · filter_upwards [hall 1 (Or.inl rfl) U hUr' hUhalf z hzc hzD,
      hall (-1) (Or.inr rfl) V hVr' hVhalf z hzc hzD] with δ h1 h2
    rw [one_mul] at h1
    rw [show z.2 + -1 * δ = z.2 - δ by ring] at h2
    exact ⟨h1, h2⟩
  · have hU12 := (htouch U hUr).1 hcU
    have hV12 := (htouch V hVr).1 hcV
    rw [htouch W hW]
    rcases hU12 with h1 | h1 <;> rcases hV12 with h2 | h2
    · exact absurd (h1.trans h2.symm) hUne
    · rw [h1, h2]
    · rw [h1, h2]; exact Or.comm
    · exact absurd (h1.trans h2.symm) hUne

/-- **WP-B: the two sides of a chord** (`ChordSidesSpec`). -/
theorem chordSides : ChordSidesSpec := by
  intro M Q F hM hF c hc
  exact chordSides_of_system ((walkAx_of_goodModel hM).sys F hF.2.1 hF.1) hc

/-- **WP-B: the region tree** (`RegionTreeSpec`). -/
theorem regionTree : RegionTreeSpec := by
  intro M Q F hM hF
  have hW := walkAx_of_goodModel hM
  have hsys := hW.sys F hF.2.1 hF.1
  obtain ⟨hfin, hcard⟩ := hsys.regionsIn_finite_ncard hW.preconn hW.nonempty subset_rfl
  refine ⟨hfin, hcard, fun U hU V hV => ?_⟩
  have h := hsys.dualGraph_reachable hW.preconn hW.nonempty subset_rfl U hU V hV
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  refine Relation.ReflTransGen.mono (r := (Chazelle.Chain.dualGraphIn M.D F).Adj) ?_ _ _ h
  intro A B hAB
  obtain ⟨-, -, -, c, hc, h1, h2⟩ := hAB
  exact ⟨c, hc, h1, h2⟩

end

end Chazelle.Core
