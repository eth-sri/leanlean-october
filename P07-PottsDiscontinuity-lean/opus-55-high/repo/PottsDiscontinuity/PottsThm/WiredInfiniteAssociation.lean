module

public import PottsDiscontinuity.PottsThm.WiredAssociation
public import PottsDiscontinuity.Potts.WiredConnectionEvents
public import PottsDiscontinuity.Potts.MonotoneEventLimits
public import PottsDiscontinuity.RCInfinite.ClusterEvents

public section

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

theorem rcInfiniteOpenGraph_mono {ω η : LatticeConfiguration} (hωη : ω ≤ η) :
    rcInfiniteOpenGraph ω ≤ rcInfiniteOpenGraph η := by
  intro x y hxy
  rw [rcInfiniteOpenGraph_adj] at hxy ⊢
  tauto

section
variable (x : LatticeVertex)
theorem wiredEscapeApprox_upper (n : ℕ) :
    IsUpperSet (wiredEscapeApprox x n) := by
  intro ω η hωη hω z hz
  exact localWiredSetoid_mono (rcInfiniteOpenGraph_mono hωη) n (hω z hz)

theorem wiredEscapeApprox_iInter  :
    (⋂ n, wiredEscapeApprox x n) = infiniteAt x := by
  change (⋂ n, wiredDataEvent n {(some x, none)}) = _
  rw [iInter_wiredDataEvent]
  simp [infiniteMergedDataEvent, infiniteMergedSetoid_some_none, RCInfinite.infiniteAt, cluster]
  rfl

theorem wiredEscapeApprox_antitone  :
    Antitone (wiredEscapeApprox x) := by
  intro m n hmn
  exact wiredDataEvent_antitone _ hmn

theorem wiredEscapeApprox_measurable (n : ℕ) :
    MeasurableSet (wiredEscapeApprox x n) :=
  (wiredDataEvent_isClopen n _).2.measurableSet
end

/-- Whole-plane wired infinite-cluster events are positively associated in any
actual wired box limit. The finite wired connection events decrease to the
infinite-cluster events, so the clopen FKG inequality passes to their limit. -/
theorem wired_infinite_at_positive_association (θ : Parameters)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n) atTop (𝓝 φ))
    (x y : LatticeVertex) :
    φ.toMeasure.real (infiniteAt x) * φ.toMeasure.real (infiniteAt y) ≤
      φ.toMeasure.real (infiniteAt x ∩ infiniteAt y) := by
  let A := wiredEscapeApprox x
  let B := wiredEscapeApprox y
  let C := fun n => A n ∩ B n
  have hAanti := wiredEscapeApprox_antitone x
  have hBanti := wiredEscapeApprox_antitone y
  have hCanti : Antitone C := by
    intro m n hmn ω hω
    exact ⟨hAanti hmn hω.1, hBanti hmn hω.2⟩
  have hAmeas (n : ℕ) := wiredEscapeApprox_measurable x n
  have hBmeas (n : ℕ) := wiredEscapeApprox_measurable y n
  have hAseq :=
    decreasing_event_diagonal_tendsto (μs := fun _ : ℕ => φ) (μ := φ) (E := A)
      hAanti hAmeas (fun _ => tendsto_const_nhds) (fun _ => le_rfl)
  have hBseq :=
    decreasing_event_diagonal_tendsto (μs := fun _ : ℕ => φ) (μ := φ) (E := B)
      hBanti hBmeas (fun _ => tendsto_const_nhds) (fun _ => le_rfl)
  have hCseq :=
    decreasing_event_diagonal_tendsto (μs := fun _ : ℕ => φ) (μ := φ) (E := C)
      hCanti (by aesop) (fun _ => tendsto_const_nhds) (fun _ => le_rfl)
  have hIA : (⋂ n, A n) = infiniteAt x := by
    grind [wiredEscapeApprox_iInter]
  have hIB : (⋂ n, B n) = infiniteAt y := by
    grind [wiredEscapeApprox_iInter]
  have hIC : (⋂ n, C n) = infiniteAt x ∩ infiniteAt y := by
    calc
      (⋂ n, C n) = (⋂ n, A n) ∩ (⋂ n, B n) := by
        ext ω
        simp
        grind
      _ = infiniteAt x ∩ infiniteAt y := by simp_all
  have hAseq' : Tendsto (fun n => φ.toMeasure.real (A n)) atTop
      (𝓝 (φ.toMeasure.real (infiniteAt x))) := by
    simp_all
  have hBseq' : Tendsto (fun n => φ.toMeasure.real (B n)) atTop
      (𝓝 (φ.toMeasure.real (infiniteAt y))) := by
    simp_all
  have hCseq' : Tendsto (fun n => φ.toMeasure.real (C n)) atTop
      (𝓝 (φ.toMeasure.real (infiniteAt x ∩ infiniteAt y))) := by
    simp_all
  have hfinite (n : ℕ) : φ.toMeasure.real (A n) * φ.toMeasure.real (B n) ≤
      φ.toMeasure.real (C n) :=
    wired_clopen_positive_association θ φ hφ (A n) (B n)
      (wiredDataEvent_isClopen n _) (wiredDataEvent_isClopen n _)
      (wiredEscapeApprox_upper x n) (wiredEscapeApprox_upper y n)
  exact le_of_tendsto_of_tendsto' (hAseq'.mul hBseq') hCseq' hfinite

end
end PottsDiscontinuity.PottsThm
