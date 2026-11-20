module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

namespace PottsDiscontinuity

open MeasureTheory MeasurableSpace Set Filter Topology

variable {X ι : Type*} [m : MeasurableSpace X] {l : Filter ι} {G : Set (Set X)}

section
variable {μ : Measure X}

/-- A common finite upper bound upgrades convergence on a generating π-system
(and on the whole space) to setwise convergence, by dominated convergence. -/
private theorem setwise_of_domination [IsFiniteMeasure μ]
    {ν : ι → Measure X} [∀ i, IsFiniteMeasure (ν i)] (hdom : ∀ i, ν i ≤ μ)
    (hgen : m = generateFrom G) (hpi : IsPiSystem G) {c : ℝ}
    (hu : Tendsto (fun i => (ν i).real univ) l (𝓝 (c * μ.real univ)))
    (hg : ∀ A ∈ G, Tendsto (fun i => (ν i).real A) l (𝓝 (c * μ.real A))) :
    ∀ A, MeasurableSet A → Tendsto (fun i => (ν i).real A) l (𝓝 (c * μ.real A)) := by
  refine induction_on_inter (C := fun A _ => Tendsto (fun i => (ν i).real A) l (𝓝 (c * μ.real A)))
    hgen hpi (by simpa using tendsto_const_nhds) hg ?_ ?_
  · intro A hA ih
    simpa only [measureReal_compl hA, mul_sub] using hu.sub ih
  · intro f hd hm ih
    have sum (ρ : Measure X) [IsFiniteMeasure ρ] :
        ∑' k, ρ.real (f k) = ρ.real (⋃ k, f k) := by
      rw [Measure.real_def, measure_iUnion hd hm, ENNReal.tsum_toReal_eq (fun k => measure_ne_top _ _)]
      rfl
    have ht := tendsto_tsum_of_dominated_convergence (summable_measure_toReal (μ := μ) hm hd) ih
      (.of_forall fun i k => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact ENNReal.toReal_mono (measure_ne_top _ _) ((hdom i) (f k)))
    simpa only [tsum_mul_left, sum] using ht

/-- Mixing is detected on pairs of generators. The two sections of the joint
law are restrictions and pushforwards of restrictions of the marginal. -/
theorem mixing_of_piSystem [IsProbabilityMeasure μ] {T : ι → X → X}
    (hT : ∀ i, MeasurePreserving (T i) μ μ) (hgen : m = generateFrom G) (hpi : IsPiSystem G)
    (hmix : ∀ A ∈ G, ∀ B ∈ G,
      Tendsto (fun i => μ.real (A ∩ T i ⁻¹' B)) l (𝓝 (μ.real A * μ.real B)))
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun i => μ.real (A ∩ T i ⁻¹' B)) l (𝓝 (μ.real A * μ.real B)) := by
  have left (B) (h : B ∈ G) :
      Tendsto (fun i => (μ.restrict (T i ⁻¹' B)).real A) l (𝓝 (μ.real B * μ.real A)) := by
    refine setwise_of_domination (μ := μ)
      (fun _ => Measure.restrict_le_self) hgen hpi (c := μ.real B) ?_ ?_ A hA
    · simpa [Measure.real_def, (hT _).measure_preimage (hgen ▸ measurableSet_generateFrom h).nullMeasurableSet] using
        (tendsto_const_nhds)
    · intro U hU
      simpa [Measure.real_def, Measure.restrict_apply (hgen ▸ measurableSet_generateFrom hU), mul_comm] using hmix U hU B h
  let ν := fun i => (μ.restrict A).map (T i)
  have eqν i S (hS : MeasurableSet S) : (ν i).real S = μ.real (A ∩ T i ⁻¹' S) := by
    simp [ν, Measure.real_def, Measure.map_apply (hT i).measurable hS,
      Measure.restrict_apply ((hT i).measurable hS), inter_comm]
  rw [show (fun i => μ.real (A ∩ T i ⁻¹' B)) = (fun i => (ν i).real B) from
    by grind]
  refine setwise_of_domination ?_ hgen hpi ?_ ?_ B hB
  · intro i
    rw [← (hT i).map_eq]
    exact Measure.map_mono Measure.restrict_le_self (hT i).measurable
  · simpa [eqν] using tendsto_const_nhds
  · intro S hS
    simpa only [eqν _ _ (hgen ▸ measurableSet_generateFrom hS), Measure.real_def, Measure.restrict_apply hA, mul_comm] using left S hS

end

/-- A family of measure-preserving maps with asymptotically independent events. -/
structure MixingFamily (T : ι → X → X) (μ : Measure X) (l : Filter ι) : Prop where
  preserving : ∀ i, MeasurePreserving (T i) μ μ
  mixing : ∀ ⦃A B⦄, MeasurableSet A → MeasurableSet B →
    Tendsto (fun i => μ.real (A ∩ T i ⁻¹' B)) l (𝓝 (μ.real A * μ.real B))

namespace MixingFamily
variable {Y : Type*} [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    {T : ι → X → X} {S : ι → Y → Y}

theorem prod [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hT : MixingFamily T μ l) (hS : MixingFamily S ν l) :
    MixingFamily (fun i => Prod.map (T i) (S i)) (μ.prod ν) l := by
  have hp i := (hT.preserving i).prod (hS.preserving i)
  refine ⟨hp, fun {_ _} => mixing_of_piSystem hp generateFrom_prod.symm isPiSystem_prod ?_⟩
  rintro _ ⟨A, hA, B, hB, rfl⟩ _ ⟨C, hC, D, hD, rfl⟩
  simpa [preimage_prod_map_prod, prod_inter_prod, mul_mul_mul_comm] using
    (hT.mixing hA hC).mul (hS.mixing hB hD)

theorem map (hT : MixingFamily T μ l) {F : X → Y} (hF : Measurable F)
    (hS : ∀ i, Measurable (S i)) (hcomm : ∀ i, Function.Semiconj F (T i) (S i)) :
    MixingFamily S (μ.map F) l := by
  refine ⟨fun i => ⟨hS i, ?_⟩, fun {A B} hA hB => ?_⟩
  · rw [Measure.map_map (hS i) hF, ← (hcomm i).comp_eq, ← Measure.map_map hF
      (hT.preserving i).measurable, (hT.preserving i).map_eq]
  · simpa only [Measure.real_def, Measure.map_apply hF (hA.inter ((hS _ ) hB)),
      Measure.map_apply hF hA, Measure.map_apply hF hB, preimage_inter, ← preimage_comp,
      ← (hcomm _).comp_eq] using hT.mixing (hF hA) (hF hB)

end MixingFamily

/-- An event asymptotically independent of itself has mass zero or one. -/
theorem zero_one_of_self_mixing {μ : Measure X} [IsProbabilityMeasure μ] {A : Set X}
    [l.NeBot] {f : ι → Set X} (heq : ∀ i, f i = A)
    (ht : Tendsto (fun i => μ.real (A ∩ f i)) l (𝓝 (μ.real A * μ.real A))) :
    μ A = 0 ∨ μ A = 1 := by
  simp only [heq, inter_self] at ht
  have h := tendsto_nhds_unique tendsto_const_nhds ht
  rcases eq_zero_or_one_of_sq_eq_self (show μ.real A ^ 2 = μ.real A by grind) with h | h
  · exact Or.inl (((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right (measure_ne_top _ _))
  · exact Or.inr ((ENNReal.toReal_eq_one_iff _).mp h)

end PottsDiscontinuity
