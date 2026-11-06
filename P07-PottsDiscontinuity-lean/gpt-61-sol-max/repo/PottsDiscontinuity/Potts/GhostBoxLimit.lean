module
public import Mathlib

public import PottsDiscontinuity.Potts.GhostBoxConditional

/-! The literal ghost edge law converges to the wired FK box limit. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section


section

variable (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
include hq hβ

/-- The explicit finite-energy comparison squeeze for every supported cylinder. -/
theorem ghostBox_allOpen_squeeze 
    (n : ℕ) (hn : 1 ≤ n) (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, ∃ f, FK.frozenEdgeEmbedding (box (n - 1)) f = e) :
    let θ := fkParameters q hq β hβ
    let u := (openBoxProbabilityMeasure θ (n + 1)).toMeasure.real (FK.LatticeConfiguration.allOpen F)
    let c := (openBoxProbabilityMeasure θ (n - 1)).toMeasure.real (FK.LatticeConfiguration.allOpen F)
    let g := (ghostBoxProbabilityMeasure q hq β hβ n).toMeasure.real (FK.LatticeConfiguration.allOpen F)
    u - (c - u) / (1 - FK.edgeParameter θ) ^ 4 ≤ g ∧ g ≤ u := by
  
  
  let S := openBoxCylinderEvent (n - 1) F
  have hmn : n - 1 < n := by omega
  
  have hrestrict := nestedBoxEvent_openBoxCylinderEvent (show n - 1 ≤ n + 1 by omega) F hF
  have hs := corner_corrected_box_squeeze (fkParameters q hq β hβ) hmn S (openBoxCylinderEvent_upper _ _)
  
  
  rw [hrestrict] at hs
  rw [ghostBoxProbabilityMeasure_allOpen_eq_conditional q hq β hβ n (by omega) F (by
                                                                                    intro e he
                                                                                    obtain ⟨f, hf⟩ := hF e he
                                                                                    exact ⟨FK.embeddedEdgeEmbedding _ _ (nestedBoxEmbedding (by omega))
                                                                                      (nestedBox_map_le _) f, (nestedEdgeEmbedding_compatible _ f).trans hf⟩)]
  simp only [Measure.real, openBoxProbabilityMeasure_allOpen]
  exact hs

/-- All increasing cylinder probabilities of the literal ghost law converge
 to those of any weak wired-box limit. -/
theorem ghostBox_allOpen_tendsto 
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto  (FK.wiredBoxProbabilityMeasure (fkParameters q hq β hβ) (0, 0)) 
      atTop (𝓝 μ)) (F : Finset squareLattice.edgeSet) :
    Tendsto (fun n => (ghostBoxProbabilityMeasure q hq β hβ n).toMeasure.real
      (FK.LatticeConfiguration.allOpen F)) atTop (𝓝 (μ.toMeasure.real (FK.LatticeConfiguration.allOpen F))) := by
  let θ := fkParameters q hq β hβ
  have hw : Tendsto (fun n => (openBoxProbabilityMeasure θ n).toMeasure.real
      (FK.LatticeConfiguration.allOpen F)) atTop (𝓝 (μ.toMeasure.real (FK.LatticeConfiguration.allOpen F))) := by
    
    
    simpa only [openBoxProbabilityMeasure_eq_wired, ProbabilityMeasure.measureReal_eq_coe_coeFn,
      Function.comp_def] using  NNReal.continuous_coe.continuousAt.tendsto.comp (FK.LatticeConfiguration.tendsto_allOpen_of_weak hμ F) 
  have hu := hw.comp (tendsto_add_atTop_nat 1)
  
  have hl := hu.sub (((hw.comp (tendsto_sub_atTop_nat 1)).sub hu).div_const ((1 - FK.edgeParameter θ) ^ 4))
  simp only [sub_self, zero_div, sub_zero] at hl
  have hevent : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧
      ∀ e ∈ F, ∃ f, FK.frozenEdgeEmbedding (box (n - 1)) f = e := by
    have hs : ∀ᶠ m : ℕ in atTop, ∀ e ∈ F, ∃ f, FK.frozenEdgeEmbedding (box m) f = e := (eventually_all_finset F).mpr fun e a =>
                                                                                         Eventually.mono (FK.eventually_edge_lift_box e) fun n hn =>
                                                                                           Exists.casesOn hn fun f hf => Exists.intro f (Subtype.ext hf)
    exact (eventually_ge_atTop 1).and ((tendsto_sub_atTop_nat 1).eventually hs)
  have hb := hevent.mono  fun n hn => ghostBox_allOpen_squeeze q hq β hβ n hn.1 F hn.2 
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu (hb.mono fun _ h => h.1)
    (hb.mono fun _ h => h.2)

end

end
end PottsDiscontinuity.Potts
