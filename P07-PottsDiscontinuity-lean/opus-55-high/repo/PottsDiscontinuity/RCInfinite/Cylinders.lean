module

public import PottsDiscontinuity.RCInfinite.BoxExhaustion

@[expose] public section

open MeasureTheory Filter Topology Set

namespace PottsDiscontinuity.RCInfinite
open FK

abbrev Edge := squareLattice.edgeSet

/-- An event reads only the coordinates in `E`. The set `E` need not be finite. -/
def DependsOn (E : Set Edge) (A : Set LatticeConfiguration) : Prop :=
  ∀ ω η, (∀ e ∈ E, ω e = η e) → (ω ∈ A ↔ η ∈ A)

/-- A finite-coordinate event on the original lattice edges. -/
def IsCylinder (A : Set LatticeConfiguration) : Prop :=
  ∃ F : Finset Edge, DependsOn (F : Set Edge) A


theorem DependsOn.compl {E : Set Edge} {A : Set LatticeConfiguration}
    (h : DependsOn E A) : DependsOn E Aᶜ := by
  intro ω η hω
  exact not_congr (h ω η hω)

theorem DependsOn.inter {E F : Set Edge} {A B : Set LatticeConfiguration}
    (hA : DependsOn E A) (hB : DependsOn F B) : DependsOn (E ∪ F) (A ∩ B) := by
  intro ω η hω
  exact and_congr (hA ω η (fun e he => hω e (Or.inl he)))
    (hB ω η (fun e he => hω e (Or.inr he)))

theorem IsCylinder.compl {A : Set LatticeConfiguration} (h : IsCylinder A) :
    IsCylinder Aᶜ := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, hF.compl⟩

theorem IsCylinder.inter {A B : Set LatticeConfiguration}
    (hA : IsCylinder A) (hB : IsCylinder B) : IsCylinder (A ∩ B) := by
  obtain ⟨E, hE⟩ := hA
  obtain ⟨F, hF⟩ := hB
  exact ⟨E ∪ F, by simpa using hE.inter hF⟩

theorem isCylinder_coordinate (e : Edge) (b : Bool) :
    IsCylinder {ω : LatticeConfiguration | ω e = b} := by
  refine ⟨{e}, ?_⟩
  intro ω η hω
  simp_all

theorem isCylinder_allOpen (F : Finset Edge) :
    IsCylinder (LatticeConfiguration.allOpen F) := by
  refine ⟨F, ?_⟩
  intro ω η hω
  change (∀ e ∈ F, ω e = true) ↔ (∀ e ∈ F, η e = true)
  grind

section
variable {A : Set LatticeConfiguration} (hA : IsCylinder A)
include hA
theorem IsCylinder.isClopen  :
    IsClopen A := by
  obtain ⟨F, hF⟩ := hA
  let restrict : LatticeConfiguration → (F → Bool) := fun ω e => ω e
  let extend : (F → Bool) → LatticeConfiguration :=
    fun ξ e => if he : e ∈ F then ξ ⟨e, he⟩ else false
  have heq : A = restrict ⁻¹' (extend ⁻¹' A) := by
    ext ω
    exact hF ω (extend (restrict ω)) (by
      grind)
  rw [heq]
  exact (isClopen_discrete (extend ⁻¹' A)).preimage (by fun_prop)

theorem IsCylinder.measurableSet  :
    MeasurableSet A := hA.isClopen.isOpen.measurableSet
end

/-- The two actual finite-box laws, with their respective exterior extensions. -/
noncomputable def boxMeasure (θ : Parameters) (i : Fin 2) (c : LatticeVertex) (r : ℕ) :
    ProbabilityMeasure LatticeConfiguration :=
  if i = 0 then boxProbabilityMeasure θ c r else wiredBoxProbabilityMeasure θ c r

section
variable (θ : Parameters) (c : LatticeVertex) (r : ℕ)
@[simp] theorem boxMeasure_free  :
    boxMeasure θ 0 c r = boxProbabilityMeasure θ c r := by rfl

@[simp] theorem boxMeasure_wired  :
    boxMeasure θ 1 c r = wiredBoxProbabilityMeasure θ c r := by rfl
end

section
variable (θ : Parameters) (i : Fin 2) (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
include μ hμ
theorem boxMeasure_tendsto  :
    Tendsto (fun n => boxMeasure θ i (0, 0) n) atTop
      (𝓝 (⟨μ, hμ.1⟩ : ProbabilityMeasure LatticeConfiguration)) := by
  fin_cases i
  · simpa using free_box_exhaustion θ μ hμ (fun _ => (0, 0)) (fun n => n)
      origin_latticeBox_nested origin_latticeBox_exhaustive
  · simpa using wired_box_exhaustion θ μ hμ (fun _ => (0, 0)) (fun n => n)
      origin_latticeBox_nested origin_latticeBox_exhaustive

theorem tendsto_cylinder_probability {A : Set LatticeConfiguration} (hA : IsCylinder A) :
    Tendsto (fun n => (boxMeasure θ i (0, 0) n : Measure LatticeConfiguration).real A)
      atTop (𝓝 (μ.real A)) := by
  have h := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
    (boxMeasure_tendsto θ i μ hμ) hA.isClopen
  simpa [ProbabilityMeasure.coeFn_def, Measure.real, ENNReal.toReal, Function.comp_def] using
    (NNReal.continuous_coe.tendsto _).comp h
end

end PottsDiscontinuity.RCInfinite
