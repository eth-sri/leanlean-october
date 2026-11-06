module

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

def wiredEscapeApprox (x : LatticeVertex) (n : ℕ) : Set LatticeConfiguration :=
  wiredDataEvent n {(some x, none)}

private theorem rcInfiniteOpenGraph_mono {ω η : LatticeConfiguration} (hωη : ω ≤ η) :
    rcInfiniteOpenGraph ω ≤ rcInfiniteOpenGraph η := by
  intro x y hxy
  rw [rcInfiniteOpenGraph_adj] at hxy ⊢
  obtain ⟨hedge, hopen⟩ := hxy
  exact ⟨hedge, eq_top_mono (hωη ⟨s(x, y), hedge⟩) hopen⟩

private theorem wiredEscapeApprox_upper (x : LatticeVertex) (n : ℕ) :
    IsUpperSet (wiredEscapeApprox x n) :=
  fun _ _ hωη hω z hz => localWiredSetoid_mono (rcInfiniteOpenGraph_mono hωη) n (hω z hz)

private theorem wiredEscapeApprox_iInter (x : LatticeVertex) :
    (⋂ n, wiredEscapeApprox x n) = infiniteAt x := by
  change (⋂ n, wiredDataEvent n {(some x, none)}) = _
  rw [iInter_wiredDataEvent]
  ext ω
  simp [infiniteMergedDataEvent, infiniteMergedSetoid_some_none, RCInfinite.infiniteAt, cluster]
  rfl

private theorem wiredEscapeApprox_antitone (x : LatticeVertex) :
    Antitone (wiredEscapeApprox x) := wiredDataEvent_antitone _

private theorem wiredEscapeApprox_measurable (x : LatticeVertex) (n : ℕ) :
    MeasurableSet (wiredEscapeApprox x n) :=
  (wiredDataEvent_isClopen n _).2.measurableSet

theorem wired_infinite_at_positive_association (θ : Parameters)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n) atTop (𝓝 φ))
    (x y : LatticeVertex) :
    φ.toMeasure.real (infiniteAt x) * φ.toMeasure.real (infiniteAt y) ≤
      φ.toMeasure.real (infiniteAt x ∩ infiniteAt y) := by
  let A : ℕ → Set LatticeConfiguration := wiredEscapeApprox x
  let B : ℕ → Set LatticeConfiguration := wiredEscapeApprox y
  let C : ℕ → Set LatticeConfiguration := fun n => A n ∩ B n
  have hAseq : Tendsto (fun n => φ.toMeasure.real (A n)) atTop (𝓝 (φ.toMeasure.real (infiniteAt x))) := by
    rw [← wiredEscapeApprox_iInter x]
    exact decreasing_event_diagonal_tendsto (μs := fun _ : ℕ => φ) (μ := φ) (E := A)
      (wiredEscapeApprox_antitone x) (wiredEscapeApprox_measurable x)
      (fun _ => tendsto_const_nhds) (fun _ => le_rfl)
  have hBseq : Tendsto (fun n => φ.toMeasure.real (B n)) atTop (𝓝 (φ.toMeasure.real (infiniteAt y))) := by
    rw [← wiredEscapeApprox_iInter y]
    exact decreasing_event_diagonal_tendsto (μs := fun _ : ℕ => φ) (μ := φ) (E := B)
      (wiredEscapeApprox_antitone y) (wiredEscapeApprox_measurable y)
      (fun _ => tendsto_const_nhds) (fun _ => le_rfl)
  have hCseq : Tendsto (fun n => φ.toMeasure.real (C n)) atTop
      (𝓝 (φ.toMeasure.real (infiniteAt x ∩ infiniteAt y))) := by
    rw [← wiredEscapeApprox_iInter x, ← wiredEscapeApprox_iInter y, ← Set.iInter_inter_distrib]
    exact decreasing_event_diagonal_tendsto (μs := fun _ : ℕ => φ) (μ := φ) (E := C)
      (fun _ _ hmn _ hω => ⟨wiredEscapeApprox_antitone x hmn hω.1, wiredEscapeApprox_antitone y hmn hω.2⟩)
      (fun n => (wiredEscapeApprox_measurable x n).inter (wiredEscapeApprox_measurable y n))
      (fun _ => tendsto_const_nhds) (fun _ => le_rfl)
  exact le_of_tendsto_of_tendsto' (hAseq.mul hBseq) hCseq fun n =>
    wired_clopen_positive_association θ φ hφ (A n) (B n)
      (wiredDataEvent_isClopen n _) (wiredDataEvent_isClopen n _)
      (wiredEscapeApprox_upper x n) (wiredEscapeApprox_upper y n)

end
end PottsDiscontinuity.PottsThm
