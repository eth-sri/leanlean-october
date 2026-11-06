module
public import Mathlib

public import PottsDiscontinuity.TorusLoops.LoopTailRectangleFK
public import PottsDiscontinuity.TorusLoops.RectangleExplorationProductBound

/-!
# Union bound over disjoint horizontal crossings

The crossing count is covered by root-set events. Each fixed root set is
estimated by the exploration product bound, and the number of possible root
sets is at most exponential in the height of the rectangle.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open MeasureTheory
open PottsDiscontinuity.Torus
open PottsDiscontinuity.FK
open PottsDiscontinuity.Zhang

open scoped Classical

variable {N M : ℕ}

noncomputable section





/-- Left-boundary face vertices of the cut rectangle. -/
abbrev RectangleLeftRoot (N M : ℕ) :=
  {u : FaceVertex N M true // u.val.1.val = 0}

/-- The distinct-root crossing event indexed by a finite set of left roots. -/
def rectangleLeftRootSetEvent (hN : Even N) (hM : Even M)
    (S : Finset (RectangleLeftRoot N M))  :=
  rectangleDistinctRootCrossingEvent hN hM (S.toList.map Subtype.val)

private theorem rectangleCutGraph_eq_fullDiamondGraph_closedOnSeams
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false) :
    rectangleOpenGraph hN hM A = diamondOpenGraph hN hM true A := by
  grind [rectangleOpenGraph, diamondOpenGraph]

theorem rectangleFKCrossingEvent_exists_rootSet
    (hN : Even N) (hM : Even M)
    (k : ℕ) (C : Configuration (rectangleBaseGraph hN hM))
    (hC : C ∈ rectangleFKCrossingEvent hN hM k) :
    ∃ S : Finset (RectangleLeftRoot N M), S.card = k ∧
      C ∈ rectangleLeftRootSetEvent hN hM S := by
  
  let A := rectangleRCConfigOfConfiguration hN hM C
  let R := rectangleOpenGraph hN hM A
  
  have hK  := hC
  obtain ⟨T, hTK, hTcard⟩ := Finset.exists_subset_card_eq hK
  
  have hgraph : R = FK.openGraph (rectangleBaseGraph hN hM) C := by
    have hcutDiamond := rectangleCutGraph_eq_fullDiamondGraph_closedOnSeams
      hN hM A (rectangleRCConfigOfConfiguration_closedOnSeams hN hM C)
    have hconfig := rectangleConfigurationOfRC_rectangleRCConfigOfConfiguration
      hN hM C
    have hFKDiamond :=
      PottsDiscontinuity.TorusLoops.rectangleOpenGraph_eq_diamondOpenGraph_closedOnSeams
        hN hM A (rectangleRCConfigOfConfiguration_closedOnSeams hN hM C)
    aesop
  let witness : ∀ c , c ∈ T →
      ∃ x : RectangleLeftRoot N M, ∃ y : FaceVertex N M true,
        y.val.1.val + 1 = N ∧ R.connectedComponentMk x.val = c ∧ R.Reachable x.val y := by
    intro c hc
    
    rcases Finset.mem_filter.mp (hTK hc) with ⟨_, x, y, hx, hy, hxc, hreach⟩
    exact ⟨⟨x, hx⟩, y, hy, hxc, hreach⟩
  let chosen  :=
    fun c hc => Classical.choose (witness c hc)
  have chosen_data : ∀ c hc,
      ∃ y : FaceVertex N M true, y.val.1.val + 1 = N ∧
        R.connectedComponentMk (chosen c hc).val = c ∧
          R.Reachable (chosen c hc).val y := by
    grind
  let S  :=
    T.attach.image fun c => chosen c.val c.property
  have hchosen_inj : ∀ a ∈ T.attach, ∀ b ∈ T.attach,
      chosen a.val a.property = chosen b.val b.property → a = b := by
    grind
  
  refine ⟨S,  by
                dsimp [S]
                rw [Finset.card_image_iff.mpr hchosen_inj, Finset.card_attach, hTcard] , ?_⟩
  
  
  
  exact ⟨ by
            intro x hx
            rcases List.mem_map.mp hx with ⟨xr, hxr, rfl⟩
            have hxS : xr ∈ S := by simpa using hxr
            rcases Finset.mem_image.mp hxS with ⟨c, hc, hcx⟩
            have hd := chosen_data c.val c.property
            let y := Classical.choose hd
            have hdSpec := Classical.choose_spec hd
            have hy  := hdSpec.1
            have hreach := hdSpec.2.2
            refine ⟨y, hy, ?_⟩
            change (FK.openGraph (rectangleBaseGraph hN hM) C).Reachable
               ↑xr  y
            exact hgraph ▸  hcx ▸ hreach  ,  by
                       apply List.Nodup.map
                       · intro x y hxy
                         exact Subtype.ext hxy
                       · exact Finset.nodup_toList S ,  by
                               intro x hx y hy hxy hconn
                               rcases List.mem_map.mp hx with ⟨xr, hxr, rfl⟩
                               have hxS : xr ∈ S := by simpa using hxr
                               rcases Finset.mem_image.mp hxS with ⟨c, hc, hcx⟩
                               rcases List.mem_map.mp hy with ⟨yr, hyr, rfl⟩
                               have hyS : yr ∈ S := by simpa using hyr
                               rcases Finset.mem_image.mp hyS with ⟨d, hd, hdy⟩
                               
                               
                               
                               have hdd := (Classical.choose_spec (chosen_data d.val d.property)).2.1
                               have hconn' :
                                   (FK.openGraph (rectangleBaseGraph hN hM) C).Reachable
                                     (chosen c.val c.property).val (chosen d.val d.property).val := by
                                 
                                 rw [← hcx, ← hdy] at hconn
                                 exact hconn
                               have hreach  := hgraph.symm ▸ hconn'
                               
                               have hcd  := Subtype.ext (Trans.trans (Trans.trans (Eq.symm ((Classical.choose_spec (chosen_data c.val c.property)).2.1)) (SimpleGraph.ConnectedComponent.sound hreach)) hdd)
                               subst d
                               apply hxy
                               exact congrArg Subtype.val (hcx.symm.trans hdy) ⟩

/-- There are at most `M` choices for a left-boundary face root. -/
theorem rectangleLeftRoot_card_le (N M : ℕ) :
    Fintype.card (RectangleLeftRoot N M) ≤ M := by
  
  
  
  calc
    Fintype.card (RectangleLeftRoot N M) ≤ Fintype.card (Fin M) :=
      Fintype.card_le_of_injective (fun u => u.val.val.2) (by
                                        intro a b hab
                                        aesop)
    _ = M := Fintype.card_fin M

section

variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))


private theorem rectangleFKEventProbability_eq_measure
    
    (E : Set (Configuration (rectangleBaseGraph hN hM))) :
    rectangleFKEventProbability hN hM q E =
      (measure (rectangleBaseGraph hN hM) (rectangleFKParameters q)
        (BoundaryCondition.free ∅) E).toReal := by
  rw [measure_toReal_eq_indicator_sum]
  unfold rectangleFKEventProbability rectangleFKEventWeight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro C hC
  by_cases h : C ∈ E <;> simp [h, configurationProbability]

/-- The free-rectangle probability of at least `k` horizontal crossing
components is at most the number of left-root sets times the exploration
product bound. -/
theorem rectangleFKCrossingEvent_probability_le_rootUnion
     (k : ℕ) :
    rectangleFKEventProbability hN hM q (rectangleFKCrossingEvent hN hM k) ≤
      (2 : ℝ) ^ M *
        rectangleFreeOneArmProbability q (N / 2 - 1) ^ k := by
  
  let Left := RectangleLeftRoot N M
  let I := {S : Finset Left // S.card = k}
  let event : I → Set (Configuration (rectangleBaseGraph hN hM)) :=
    fun S => rectangleLeftRootSetEvent hN hM S.val
  let μ := measure (rectangleBaseGraph hN hM) (rectangleFKParameters q)
    (BoundaryCondition.free ∅)
  let ρ := rectangleFreeOneArmProbability q (N / 2 - 1)
  
  
  
  have hprobS (S : I) : rectangleBaseEventProbability hN hM q (event S) ≤ ρ ^ k := by
    let roots := S.val.toList.map Subtype.val
    
    
    have hlen : roots.length = k := by
      simp [roots, S.property]
    simpa [event, rectangleLeftRootSetEvent, roots, hlen, ρ] using  rectangleDistinctRootCrossingEvent_probability_le_pow
                                                                      hN hM q roots (by
                                                                                       grind) 
  
  have hsum :  ∑ S : I, μ.real (event S)  ≤
       Fintype.card I  * ρ ^ k := by
    calc
       ∑ S : I, μ.real (event S)  ≤ ∑ _S : I, ρ ^ k :=
        Finset.sum_le_sum fun S _ => by
          simpa [Measure.real, rectangleBaseEventProbability] using hprobS S
      _ =  Fintype.card I  * ρ ^ k := by simp
  
  
  rw [rectangleFKEventProbability_eq_measure hN hM q]
  simpa [μ, Measure.real] using (Trans.trans (measureReal_mono (by
                                                                  intro C hC
                                                                  obtain ⟨S, hSk, hCS⟩ :=
                                                                    rectangleFKCrossingEvent_exists_rootSet hN hM k C hC
                                                                  exact Set.mem_iUnion.mpr ⟨⟨S, hSk⟩, hCS⟩) (measure_ne_top μ (Set.iUnion event))) (measureReal_iUnion_fintype_le event)).trans (hsum.trans
    (mul_le_mul_of_nonneg_right (by
                                   exact_mod_cast  by
                                                     calc
                                                       Fintype.card I ≤ Fintype.card (Finset Left) :=
                                                         Fintype.card_le_of_injective Subtype.val Subtype.val_injective
                                                       _ = 2 ^ Fintype.card Left := Fintype.card_finset
                                                       _ ≤ 2 ^ M := Nat.pow_le_pow_right (by omega) (rectangleLeftRoot_card_le N M) ) (pow_nonneg (by
                                                      dsimp [ρ]
                                                      unfold rectangleFreeOneArmProbability
                                                      exact NNReal.coe_nonneg _) k)))

end

end

end PottsDiscontinuity.TorusLoops
