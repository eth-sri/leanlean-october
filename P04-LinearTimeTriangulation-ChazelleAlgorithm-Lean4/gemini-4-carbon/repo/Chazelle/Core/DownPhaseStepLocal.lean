module

public import Chazelle.Core.DownPhaseLocal

/-!
# Down step, part 1: independence across regions

Chords are added to a family `S` inside several of its regions at once (`T ⊇ S`).  For a region
`R` of `S` and an intermediate family `S ⊆ G ⊆ T` such that every chord of `T` outside `G` meets
the domain only inside another region `R' ≠ R` of `S` (`OutOther`), a region `V ⊆ R` of `T`:

* is a region of `G` (`region_restrict`);
* is touched by the same chords in `T` and in `G` (`touch_restrict`, `exits_restrict`);
* has the same weight in `T` and in `G` (`weight_restrict`, by `Gran.weightLocal`, removing the
  chords of the other regions one at a time).

Design: `docs/design-downphase-nf.md` §4.2.
-/

namespace Chazelle.Core

namespace DownStep

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (ChordSystem freeIn regionsIn TouchesIn)

/-- Every chord of `T` outside `G` meets the domain only inside a region `R' ≠ R` of `S`. -/
def OutOther (D : Set Point) (S G T : Set (Set Point)) (R : Set Point) : Prop :=
  ∀ c ∈ T, c ∉ G → ∃ R' ∈ regionsIn D S, R' ≠ R ∧ c ∩ D ⊆ R'

variable {D : Set Point} {S G T : Set (Set Point)} {R V : Set Point}

theorem OutOther.mono {H : Set (Set Point)} (h : OutOther D S G T R) (hGH : G ⊆ H) :
    OutOther D S H T R := fun c hc hcH => h c hc fun hcG => hcH (hGH hcG)

/-- **A region inside `R` of the full family is a region of the intermediate family.** -/
theorem region_restrict (hSG : S ⊆ G) (hGT : G ⊆ T) (hR : R ∈ regionsIn D S)
    (hK : OutOther D S G T R) (hV : V ∈ regionsIn D T) (hVR : V ⊆ R) : V ∈ regionsIn D G := by
  obtain ⟨v, hv⟩ := Chazelle.Chain.regionsIn_nonempty hV
  have hVG : V ⊆ freeIn D G :=
    (Chazelle.Chain.regionsIn_subset hV).trans (Chazelle.Chain.freeIn_anti D hGT)
  set W := connectedComponentIn (freeIn D G) v with hW
  have hvW : v ∈ W := mem_connectedComponentIn (hVG hv)
  have hWS : W ⊆ freeIn D S :=
    (connectedComponentIn_subset _ _).trans (Chazelle.Chain.freeIn_anti D hSG)
  have hWR : W ⊆ R := Chazelle.Chain.subset_regionsIn_of_inter hR
    isPreconnected_connectedComponentIn hWS ⟨v, hvW, hVR hv⟩
  have hWT : W ⊆ freeIn D T := fun w hw => by
    have hwG : w ∈ freeIn D G := connectedComponentIn_subset _ _ hw
    refine ⟨hwG.1, ?_⟩
    rintro ⟨c, hc, hwc⟩
    by_cases hcG : c ∈ G
    · exact hwG.2 ⟨c, hcG, hwc⟩
    · obtain ⟨R', hR', hne, hsub⟩ := hK c hc hcG
      exact (Chazelle.Chain.regionsIn_disjoint_of_ne hR' hR hne).le_bot
        ⟨hsub ⟨hwc, hwG.1⟩, hWR hw⟩
  have hWV : W ⊆ V := by
    rw [Chazelle.Chain.regionsIn_eq_component hV hv]
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hvW hWT
  have hVW : V ⊆ W := (Chazelle.Chain.regionsIn_isPreconnected hV).subset_connectedComponentIn hv hVG
  exact ⟨v, hVG hv, Subset.antisymm hVW hWV⟩

/-- **The chords of the other regions do not touch `V`.** -/
theorem touch_restrict (hsys : ChordSystem D T) (hST : S ⊆ T) (hR : R ∈ regionsIn D S)
    (hK : OutOther D S G T R) (hVR : V ⊆ R) {c : Set Point} (hc : c ∈ T) (hcG : c ∉ G) :
    ¬ TouchesIn D c V := by
  rintro ⟨z, ⟨hzc, hzD⟩, hzV⟩
  obtain ⟨R', hR', hne, hsub⟩ := hK c hc hcG
  have hRo : IsOpen R' := hsys.regionsIn_open hST hR'
  obtain ⟨w, hwR', hwV⟩ := mem_closure_iff.1 hzV R' hRo (hsub ⟨hzc, hzD⟩)
  exact (Chazelle.Chain.regionsIn_disjoint_of_ne hR' hR hne).le_bot ⟨hwR', hVR hwV⟩

/-- **The exits of `V` in the full family are its exits in the intermediate family.** -/
theorem exits_restrict (hsys : ChordSystem D T) (hST : S ⊆ T) (hGT : G ⊆ T)
    (hR : R ∈ regionsIn D S) (hK : OutOther D S G T R) (hVR : V ⊆ R) :
    {c | c ∈ T ∧ TouchesIn D c V} = {c | c ∈ G ∧ TouchesIn D c V} := by
  ext c
  constructor
  · rintro ⟨hc, ht⟩
    by_contra hcG
    exact touch_restrict hsys hST hR hK hVR hc (fun h => hcG ⟨h, ht⟩) ht
  · rintro ⟨hc, ht⟩
    exact ⟨hGT hc, ht⟩

/-- **The weight of `V` in the full family is its weight in the intermediate family.** -/
theorem weight_restrict {M : Model} (hM : WalkAx M) (hT : T ⊆ M.Adm) (hfin : T.Finite)
    (hSG : S ⊆ G) (hGT : G ⊆ T) (hR : R ∈ M.regions S) (hK : OutOther M.D S G T R)
    (hV : V ∈ M.regions T) (hVR : V ⊆ R) : M.weight T V = M.weight G V := by
  have hloc := Gran.weightLocal hM hT hfin
  have hsys := hM.sys T hT hfin
  have hST : S ⊆ T := hSG.trans hGT
  have key : ∀ K : Set (Set Point), K.Finite → K ⊆ T \ G →
      M.weight (G ∪ K) V = M.weight G V := by
    intro K hKf
    refine Set.Finite.induction_on
      (motive := fun K _ => K ⊆ T \ G → M.weight (G ∪ K) V = M.weight G V) K hKf ?_ ?_
    · intro _; rw [union_empty]
    · intro c K hcK _ ih hsub
      have hcT : c ∈ T := (hsub (mem_insert c K)).1
      have hcG : c ∉ G := (hsub (mem_insert c K)).2
      have hKsub : K ⊆ T \ G := fun d hd => hsub (mem_insert_of_mem c hd)
      set H := G ∪ insert c K with hH
      have hHT : H ⊆ T := union_subset hGT (insert_subset hcT fun d hd => (hKsub hd).1)
      have hHd : H \ {c} = G ∪ K := by
        ext d
        simp only [hH, Set.mem_sdiff, mem_union, mem_insert_iff, mem_singleton_iff]
        constructor
        · rintro ⟨h1 | rfl | h1, h2⟩
          · exact Or.inl h1
          · exact absurd rfl h2
          · exact Or.inr h1
        · rintro (h1 | h1)
          · exact ⟨Or.inl h1, fun e => hcG (e ▸ h1)⟩
          · exact ⟨Or.inr (Or.inr h1), fun e => hcK (e ▸ h1)⟩
      have hVH : V ∈ M.regions H :=
        region_restrict (hSG.trans subset_union_left) hHT hR (hK.mono subset_union_left) hV hVR
      have hnt : ¬ TouchesIn M.D c V := touch_restrict hsys hST hR hK hVR hcT hcG
      have := hloc H hHT c (Or.inr (mem_insert c K)) V hVH hnt
      rw [hHd] at this
      rw [← this, ih hKsub]
  have hTG : T = G ∪ (T \ G) := (union_sdiff_cancel hGT).symm
  rw [hTG]
  exact key _ (hfin.subset sdiff_subset) subset_rfl

end

end DownStep

end Chazelle.Core
