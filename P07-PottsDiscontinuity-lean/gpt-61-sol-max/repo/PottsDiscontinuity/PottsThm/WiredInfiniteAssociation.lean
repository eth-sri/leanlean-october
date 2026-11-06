module
public import Mathlib

public import PottsDiscontinuity.PottsThm.WiredAssociation
public import PottsDiscontinuity.Potts.WiredConnectionEvents
public import PottsDiscontinuity.Potts.MonotoneEventLimits
public import PottsDiscontinuity.RCInfinite.ClusterEvents

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.RCInfinite

noncomputable section

attribute [local instance] configurationMeasurableSpace

def wiredEscapeApprox (x : LatticeVertex) (n : ℕ)  :=
  wiredDataEvent n {(some x, none)}

private theorem rcInfiniteOpenGraph_mono {ω η : LatticeConfiguration} (hωη : ω ≤ η) :
    rcInfiniteOpenGraph ω ≤ rcInfiniteOpenGraph η := by
  intro x y hxy
  rw [rcInfiniteOpenGraph_adj] at hxy ⊢
  aesop

section

variable (x : LatticeVertex)


private theorem wiredEscapeApprox_upper  (n : ℕ) :
    IsUpperSet (wiredEscapeApprox x n) := fun ⦃ω η⦄ hωη hω z hz => localWiredSetoid_mono (rcInfiniteOpenGraph_mono hωη) n (hω z hz)

private theorem wiredEscapeApprox_iInter  :
     ⋂ n, wiredEscapeApprox x n  = infiniteAt x := by
  change  ⋂ n, wiredDataEvent n {(some x, none)}  = _
  rw [iInter_wiredDataEvent]
  
  simp [infiniteMergedDataEvent]
  rfl

private theorem wiredEscapeApprox_antitone  :
    Antitone (wiredEscapeApprox x) := fun m n hmn => wiredDataEvent_antitone _ hmn

private theorem wiredEscapeApprox_measurable  (n : ℕ) :
    MeasurableSet (wiredEscapeApprox x n) :=
  (wiredDataEvent_isClopen n _).2.measurableSet

end

/-- Whole-plane wired infinite-cluster events are positively associated in any
actual wired box limit. The finite wired connection events decrease to the
infinite-cluster events, so the clopen FKG inequality passes to their limit. -/
theorem wired_infinite_at_positive_association (θ : Parameters)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto  (wiredBoxProbabilityMeasure θ (0, 0))  atTop (𝓝 φ))
    (x y : LatticeVertex) :
    φ.toMeasure.real (infiniteAt x) * φ.toMeasure.real (infiniteAt y) ≤
      φ.toMeasure.real (infiniteAt x ∩ infiniteAt y) := by
  let A  := wiredEscapeApprox x
  let B  := wiredEscapeApprox y
  let C  := fun n => A n ∩ B n
  have hAanti : Antitone A := wiredEscapeApprox_antitone x
  have hBanti : Antitone B := wiredEscapeApprox_antitone y
  
  have hAmeas (n : ℕ)  := wiredEscapeApprox_measurable x n
  have hBmeas (n : ℕ)  := wiredEscapeApprox_measurable y n
  have hCmeas (n : ℕ)  := (hAmeas n).inter (hBmeas n)
   
   
   
  have hIA :  ⋂ n, A n  = infiniteAt x := wiredEscapeApprox_iInter x
  have hIB :  ⋂ n, B n  = infiniteAt y := wiredEscapeApprox_iInter y
  
  have hAseq' : Tendsto (fun n => φ.toMeasure.real (A n)) atTop
      (𝓝 (φ.toMeasure.real (infiniteAt x))) := by
    simpa only [hIA] using  decreasing_event_diagonal_tendsto (μs := fun _ : ℕ => φ) (μ := φ) (E := A)
                                hAanti hAmeas (fun _ => tendsto_const_nhds)  fun _ => le_rfl 
  
  
  have hprod := hAseq'.mul (by
                              simpa only [hIB] using  decreasing_event_diagonal_tendsto (μs := fun _ : ℕ => φ) (μ := φ) (E := B)
                                                          hBanti hBmeas (fun _ => tendsto_const_nhds)  fun _ => le_rfl )
  
  exact le_of_tendsto_of_tendsto' hprod (by
                                           simpa only [ by
                                                          calc
                                                             ⋂ n, C n  = (⋂ n, A n) ∩  ⋂ n, B n  := by
                                                              ext ω
                                                              simp only [C, Set.mem_iInter, Set.mem_inter_iff]
                                                              all_goals grind
                                                            _ = infiniteAt x ∩ infiniteAt y := by rw [hIA, hIB] ] using (decreasing_event_diagonal_tendsto (μs := fun _ : ℕ => φ) (μ := φ) (E := C)
                                                                       (by
                                                                          exact Antitone.inter hAanti hBanti) hCmeas (fun _ => tendsto_const_nhds)  fun _ => le_rfl))  fun n => wired_clopen_positive_association θ φ hφ (A n) (B n)
                                                                                     (wiredDataEvent_isClopen n _) (wiredDataEvent_isClopen n _)
                                                                                     (wiredEscapeApprox_upper x n) (wiredEscapeApprox_upper y n) 

end
end PottsDiscontinuity.PottsThm
