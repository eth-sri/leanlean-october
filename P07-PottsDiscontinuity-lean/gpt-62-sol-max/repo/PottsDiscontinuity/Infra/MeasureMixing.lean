module

public import Mathlib

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Function ENNReal

namespace PottsDiscontinuity

private theorem hasSum_measureReal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {A : ℕ → Set Ω}
    (hD : Pairwise (Disjoint on A)) (hA : ∀ n, MeasurableSet (A n)) :
    HasSum (fun n => μ.real (A n)) (μ.real (⋃ n, A n)) := by
  rw [Measure.real_def, measure_iUnion hD hA, ENNReal.tsum_toReal_eq (fun n => measure_ne_top μ (A n))]
  exact ENNReal.hasSum_toReal (by rw [← measure_iUnion hD hA]; finiteness)

/-- For a family dominated by one finite measure, convergence of the total mass and
convergence on a generating π-system imply setwise convergence. -/
theorem tendsto_measureReal_of_generateFrom {Ω ι : Type*} [MeasurableSpace Ω]
    {l : Filter ι} {C : Set (Set Ω)} (hgen : ‹MeasurableSpace Ω› = MeasurableSpace.generateFrom C)
    (hpi : IsPiSystem C) (μ : Measure Ω) [IsFiniteMeasure μ]
    {ν : ι → Measure Ω} {ν₀ : Measure Ω} (hν : ∀ i, ν i ≤ μ) (h₀ : ν₀ ≤ μ)
    (hu : Tendsto (fun i => (ν i).real univ) l (𝓝 (ν₀.real univ)))
    (hC : ∀ A ∈ C, Tendsto (fun i => (ν i).real A) l (𝓝 (ν₀.real A)))
    {A : Set Ω} (hA : MeasurableSet A) : Tendsto (fun i => (ν i).real A) l (𝓝 (ν₀.real A)) := by
  have : IsFiniteMeasure ν₀ := isFiniteMeasure_of_le μ h₀
  have (i : ι) : IsFiniteMeasure (ν i) := isFiniteMeasure_of_le μ (hν i)
  induction A, hA using MeasurableSpace.induction_on_inter hgen hpi with
  | empty => simpa using (tendsto_const_nhds (x := (0 : ℝ)))
  | basic A hA => simp_all
  | compl A hA ih => simpa [measureReal_compl hA] using hu.sub ih
  | iUnion A hd hm ih =>
    have hsum (ρ : Measure Ω) [IsFiniteMeasure ρ] : ρ.real (⋃ n, A n) = ∑' n, ρ.real (A n) :=
      (hasSum_measureReal ρ hd hm).tsum_eq.symm
    simp_rw [hsum]
    exact tendsto_tsum_of_dominated_convergence (hasSum_measureReal μ hd hm).summable ih
      (Eventually.of_forall fun i n => by
        rw [Real.norm_of_nonneg measureReal_nonneg]
        exact ENNReal.toReal_mono (measure_ne_top μ _) (hν i _))

/-- The mixing limit of a pair of events along an arbitrary filter of shifts. -/
def MixingLimit {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : ι → Ω → Ω) (l : Filter ι) (A B : Set Ω) : Prop :=
  Tendsto (fun i => μ.real (A ∩ (T i) ⁻¹' B)) l (𝓝 (μ.real A * μ.real B))

/-- It suffices to prove mixing for two events from a generating π-system. -/
theorem mixing_of_generators {Ω ι : Type*} [MeasurableSpace Ω]
    {l : Filter ι} {C : Set (Set Ω)} (hgen : ‹MeasurableSpace Ω› = MeasurableSpace.generateFrom C)
    (hpi : IsPiSystem C) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : ι → Ω → Ω} (hT : ∀ i, MeasurePreserving (T i) μ μ)
    (hC : ∀ A ∈ C, ∀ B ∈ C, MixingLimit μ T l A B)
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) : MixingLimit μ T l A B := by
  have hm {D : Set Ω} (hD : D ∈ C) : MeasurableSet D := hgen ▸
    MeasurableSpace.measurableSet_generateFrom hD
  have hμ (D : Set Ω) : μ D • μ ≤ μ := by
    rw [Measure.le_iff]
    intro S hS
    rw [Measure.smul_apply, smul_eq_mul]
    exact mul_le_of_le_one_left' prob_le_one
  have hs (C D : Set Ω) : (μ C • μ).real D = μ.real C * μ.real D := by
    simp [Measure.real_def]
  have hfirst {A B : Set Ω} (hA : MeasurableSet A) (hb : B ∈ C) : MixingLimit μ T l A B := by
    let ν := fun i => μ.restrict ((T i) ⁻¹' B)
    have hval (i : ι) {D : Set Ω} (hD : MeasurableSet D) :
        (ν i).real D = μ.real (D ∩ (T i) ⁻¹' B) := by
      simp [ν, Measure.real_def, Measure.restrict_apply hD]
    have hu (i : ι) : (ν i).real univ = μ.real B := by
      rw [hval i MeasurableSet.univ, univ_inter, Measure.real_def, ← Measure.map_apply
        (hT i).measurable (hm hb), (hT i).map_eq, Measure.real_def]
    have h₀ : Tendsto (fun i => (ν i).real univ) l (𝓝 ((μ B • μ).real univ)) := by
      simpa [hu, Measure.real_def] using (tendsto_const_nhds (x := μ.real B))
    have hlim := tendsto_measureReal_of_generateFrom hgen hpi μ
      (ν := ν) (fun i => Measure.restrict_le_self) (hμ B) h₀ (fun D hD => by
        simp_rw [hval _ (hm hD), hs, mul_comm (μ.real B)]
        exact hC D hD B hb) hA
    unfold MixingLimit
    simpa [hval _ hA, hs, mul_comm (μ.real B)] using hlim
  let ν := fun i => (μ.restrict A).map (T i)
  have hval (i : ι) {D : Set Ω} (hD : MeasurableSet D) :
      (ν i).real D = μ.real (A ∩ (T i) ⁻¹' D) := by
    simp [ν, Measure.real_def, Measure.map_apply (hT i).measurable hD,
      Measure.restrict_apply ((hT i).measurable hD), inter_comm]
  have hle i : ν i ≤ μ := by
    rw [← (hT i).map_eq]
    exact Measure.map_mono Measure.restrict_le_self (hT i).measurable
  have hu : Tendsto (fun i => (ν i).real univ) l (𝓝 ((μ A • μ).real univ)) := by
    simpa [hval _ MeasurableSet.univ, Measure.real_def] using
          (tendsto_const_nhds (x := μ.real A))
  have hlim := tendsto_measureReal_of_generateFrom hgen hpi μ hle (hμ A) hu (fun D hD => by
    simpa [MixingLimit, hval _ (hm hD), hs] using
          (hfirst hA hD : Tendsto _ _ _)) hB
  simpa [MixingLimit, hval _ hB, hs] using hlim

/-- A measurable invariant event in a mixing probability system has probability zero or one. -/
theorem zero_or_compl_zero_of_mixing {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {T : ι → Ω → Ω} {l : Filter ι} [l.NeBot]
    {A : Set Ω} (hA : MeasurableSet A) (h : MixingLimit μ T l A A)
    (hinv : ∀ i, (T i) ⁻¹' A = A) : μ A = 0 ∨ μ Aᶜ = 0 := by
  unfold MixingLimit at h
  simp only [hinv, inter_self] at h
  have he := tendsto_nhds_unique tendsto_const_nhds h
  have hz : μ.real A * (μ.real A - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with hz | hz
  · exact Or.inl ((ENNReal.toReal_eq_zero_iff (μ A)).mp hz |>.resolve_right (measure_ne_top _ _))
  · have h₁ : μ A = 1 := (ENNReal.toReal_eq_one_iff (μ A)).mp (sub_eq_zero.mp hz)
    simp [measure_compl hA (measure_ne_top _ _), h₁]

end PottsDiscontinuity
