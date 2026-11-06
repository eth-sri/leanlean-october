module

public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.UniformOn

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Set Topology
open scoped symmDiff
open scoped ENNReal

noncomputable section

def DependsOnIndices {I C : Type*} (F : Finset I) (A : Set (I → C)) : Prop :=
  ∀ u v, (∀ i ∈ F, u i = v i) → (u ∈ A ↔ v ∈ A)

theorem DependsOnIndices.union {I C : Type*} [DecidableEq I] {F G : Finset I}
    {A B : Set (I → C)} (hA : DependsOnIndices F A) (hB : DependsOnIndices G B) :
    DependsOnIndices (F ∪ G) (A ∪ B) := fun u v huv =>
  or_congr (hA u v fun i hi => huv i (Finset.mem_union_left G hi))
    (hB u v fun i hi => huv i (Finset.mem_union_right F hi))

theorem dependsOnIndices_sdiff {I C : Type*} [DecidableEq I] {F G : Finset I}
    {A B : Set (I → C)} (hA : DependsOnIndices F A) (hB : DependsOnIndices G B) :
    DependsOnIndices (F ∪ G) (A \ B) := fun u v huv =>
  and_congr (hA u v fun i hi => huv i (Finset.mem_union_left G hi))
    (not_congr (hB u v fun i hi => huv i (Finset.mem_union_right F hi)))

def finiteIndexEvents {I C : Type*} : Set (Set (I → C)) :=
  {A | ∃ F : Finset I, DependsOnIndices F A}

theorem finiteIndexEvents_isSetRing {I C : Type*} [DecidableEq I] :
    IsSetRing (finiteIndexEvents (I := I) (C := C)) where
  empty_mem := ⟨∅, fun _ _ _ => Iff.rfl⟩
  union_mem := by rintro A B ⟨F, hF⟩ ⟨G, hG⟩; exact ⟨F ∪ G, hF.union hG⟩
  sdiff_mem := by rintro A B ⟨F, hF⟩ ⟨G, hG⟩; exact ⟨F ∪ G, dependsOnIndices_sdiff hF hG⟩

def finiteCoordinateRestrict {I C : Type*} (F : Finset I) (u : I → C) :
    (↥F → C) := fun i => u i.1

def finiteCoordinateExtend {I C : Type*} [DecidableEq I]
    (F : Finset I) (c₀ : C) (u : ↥F → C) : I → C :=
  fun i => if h : i ∈ F then u ⟨i, h⟩ else c₀

private theorem measurableSet_of_finite_type {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Finite X] (A : Set X) : MeasurableSet A := by
  classical
  rw [show A = ⋃ x : A, ({x.1} : Set X) by ext; simp]
  exact MeasurableSet.iUnion fun x => MeasurableSet.singleton x.1

private theorem finiteIndexEvent_preimage {I C : Type*} [DecidableEq I]
    (F : Finset I) (c₀ : C) {A : Set (I → C)} (hF : DependsOnIndices F A) :
    A = finiteCoordinateRestrict F ⁻¹' (finiteCoordinateExtend F c₀ ⁻¹' A) := by
  ext u
  exact hF u _ fun i hi => by simp [finiteCoordinateExtend, finiteCoordinateRestrict, hi]

private theorem finiteIndexEvent_measurable {I C : Type*} [Countable I] [Finite C]
    [MeasurableSpace C] [MeasurableSingletonClass C] [DecidableEq I]
    (c₀ : C) {A : Set (I → C)} (hA : A ∈ finiteIndexEvents (I := I) (C := C)) :
    MeasurableSet A := by
  obtain ⟨F, hF⟩ := hA
  rw [finiteIndexEvent_preimage F c₀ hF]
  exact (measurable_pi_iff.mpr fun i => measurable_pi_apply i.1) (measurableSet_of_finite_type _)

private theorem finiteCoordinateCylinder_generateFrom {I C : Type*} [Countable I]
    [Finite C] [MeasurableSpace C] [MeasurableSingletonClass C] [DecidableEq I]
    (c₀ : C) :
    (inferInstance : MeasurableSpace (I → C)) =
      MeasurableSpace.generateFrom (finiteIndexEvents (I := I) (C := C)) := by
  classical
  refine le_antisymm (iSup_le fun i => MeasurableSpace.comap_le_iff_le_map.2 fun T _ => ?_)
    (MeasurableSpace.generateFrom_le fun A => finiteIndexEvent_measurable c₀)
  change MeasurableSet[MeasurableSpace.generateFrom
    (finiteIndexEvents (I := I) (C := C))] ((fun u : I → C => u i) ⁻¹' T)
  rw [show (fun u : I → C => u i) ⁻¹' T = ⋃ c : T, {u | u i = c.1} by ext; simp]
  exact MeasurableSet.iUnion fun c => MeasurableSpace.measurableSet_generateFrom
    ⟨{i}, fun u v huv => by change u i = c.1 ↔ v i = c.1; rw [huv i (by simp)]⟩

private theorem finiteIndexEvent_approx {I C : Type*} [Countable I] [Finite C]
    [MeasurableSpace C] [MeasurableSingletonClass C] [DecidableEq I]
    (μ : Measure (I → C)) [IsFiniteMeasure μ] (c₀ : C)
    {A : Set (I → C)} (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ B, B ∈ finiteIndexEvents (I := I) (C := C) ∧ μ (B ∆ A) < ε :=
  exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (finiteIndexEvents_isSetRing (I := I) (C := C))
    ⟨{univ}, Set.countable_singleton _, by rintro _ rfl; exact ⟨∅, fun _ _ _ => Iff.rfl⟩, by simp⟩
    (finiteCoordinateCylinder_generateFrom (I := I) (C := C) c₀) hA hε

theorem abs_measureReal_sub_le_symmDiff {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |μ.real A - μ.real B| ≤ μ.real (A ∆ B) := by
  have h := (MeasuredSets.lipschitzWith_measureReal (μ := μ)).dist_le_mul
    (⟨A, hA⟩ : MeasuredSets μ) (⟨B, hB⟩ : MeasuredSets μ)
  change |μ.real A - μ.real B| ≤ (1 : ℝ) * μ.real (A ∆ B) at h
  simpa only [one_mul] using h

def iidFieldMeasure {I C : Type*} [MeasurableSpace C]
    (ν : Measure C) : Measure (I → C) := Measure.infinitePi (fun _ => ν)

def iidFieldShift {I C : Type*} (e : I ≃ I) (u : I → C) : I → C :=
  fun i => u (e.symm i)

theorem iidFieldShift_measurePreserving {I C : Type*} [MeasurableSpace C]
    (ν : Measure C) [IsProbabilityMeasure ν] (e : I ≃ I) :
    MeasurePreserving (iidFieldShift e) (iidFieldMeasure ν) (iidFieldMeasure ν) := by
  refine ⟨measurable_pi_iff.mpr fun i => measurable_pi_apply (e.symm i), ?_⟩
  rw [show iidFieldShift e = ⇑(MeasurableEquiv.piCongrLeft (fun _ : I => C) e) by
    funext u i; simp [iidFieldShift, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]]
  exact Measure.infinitePi_map_piCongrLeft (μ := fun _ : I => ν) e

theorem iidField_independent_supported_events {I C : Type*} [DecidableEq I]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C]
    (ν : Measure C) [IsProbabilityMeasure ν] (c₀ : C) (F G : Finset I)
    (hFG : Disjoint F G) (A B : Set (I → C))
    (hA : DependsOnIndices F A) (hB : DependsOnIndices G B) :
    iidFieldMeasure ν (A ∩ B) = iidFieldMeasure ν A * iidFieldMeasure ν B := by
  classical
  have hEval : ProbabilityTheory.iIndepFun (fun i (u : I → C) => u i) (iidFieldMeasure ν) :=
    ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : I => ν) (X := fun _ (c : C) => c) (by fun_prop)
  have hProj := hEval.indepFun_finset F G hFG (fun i => measurable_pi_apply i)
  rw [finiteIndexEvent_preimage F c₀ hA, finiteIndexEvent_preimage G c₀ hB]
  exact hProj.measure_inter_preimage_eq_mul _ _
    (measurableSet_of_finite_type _) (measurableSet_of_finite_type _)

theorem DependsOnIndices.preimage_iidFieldShift {I C : Type*} {F : Finset I}
    {A : Set (I → C)} (hA : DependsOnIndices F A) (e : I ≃ I) :
    DependsOnIndices (F.map e.symm.toEmbedding) (iidFieldShift e ⁻¹' A) :=
  fun _ _ huv => hA _ _ fun i hi => huv (e.symm i) (Finset.mem_map.mpr ⟨i, hi, rfl⟩)

theorem iidField_mixing_of_finite_separation {I C : Type*} [Countable I] [DecidableEq I]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C]
    (ν : Measure C) [IsProbabilityMeasure ν] (c₀ : C)
    (e : (ℤ × ℤ) → I ≃ I)
    (hsep : ∀ F G : Finset I, ∀ᶠ a : ℤ × ℤ in cofinite,
      Disjoint F (G.map (e a).symm.toEmbedding))
    {A B : Set (I → C)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun a : ℤ × ℤ =>
      (iidFieldMeasure ν).real (A ∩ iidFieldShift (e a) ⁻¹' B)) cofinite
      (𝓝 ((iidFieldMeasure ν).real A * (iidFieldMeasure ν).real B)) := by
  let μ : Measure (I → C) := iidFieldMeasure ν
  have : IsProbabilityMeasure μ :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun _ => ν)))
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hδ : 0 < ε / 8 := by positivity
  obtain ⟨A', hA'fin, hA'err⟩ := finiteIndexEvent_approx μ c₀ hA (ENNReal.ofReal_pos.mpr hδ)
  obtain ⟨B', hB'fin, hB'err⟩ := finiteIndexEvent_approx μ c₀ hB (ENNReal.ofReal_pos.mpr hδ)
  have hA'meas : MeasurableSet A' := finiteIndexEvent_measurable c₀ hA'fin
  have hB'meas : MeasurableSet B' := finiteIndexEvent_measurable c₀ hB'fin
  have hA'errR : μ.real (A ∆ A') < ε / 8 := by
    rw [symmDiff_comm, Measure.real_def, ← ENNReal.toReal_ofReal hδ.le]
    exact (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hA'err
  have hB'errR : μ.real (B' ∆ B) < ε / 8 := by
    rw [Measure.real_def, ← ENNReal.toReal_ofReal hδ.le]
    exact (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hB'err
  obtain ⟨F, hF⟩ := hA'fin
  obtain ⟨G, hG⟩ := hB'fin
  filter_upwards [hsep F G] with a ha
  let Ta : (I → C) → (I → C) := iidFieldShift (e a)
  have hT : MeasurePreserving Ta μ μ := iidFieldShift_measurePreserving ν (e a)
  have hind := congrArg ENNReal.toReal (iidField_independent_supported_events ν c₀ F
    (G.map (e a).symm.toEmbedding) ha A' (Ta ⁻¹' B') hF (hG.preimage_iidFieldShift (e a)))
  have hmassB' : (iidFieldMeasure ν (Ta ⁻¹' B')).toReal = (iidFieldMeasure ν B').toReal := by
    rw [← Measure.map_apply hT.measurable hB'meas, hT.map_eq]
  have htarget : μ.real (A' ∩ Ta ⁻¹' B') = μ.real A' * μ.real B' := by
    simpa [μ, Measure.real_def, ENNReal.toReal_mul, hmassB'] using hind
  have hBerrShift : μ.real ((Ta ⁻¹' B) ∆ (Ta ⁻¹' B')) = μ.real (B' ∆ B) := by
    rw [← Set.preimage_symmDiff, Measure.real_def,
      ← Measure.map_apply hT.measurable (hB.symmDiff hB'meas), hT.map_eq, symmDiff_comm]
    rfl
  have hJointErr : |μ.real (A ∩ Ta ⁻¹' B) - μ.real A' * μ.real B'| ≤
      μ.real (A ∆ A') + μ.real (B' ∆ B) := by
    rw [← htarget, ← hBerrShift]
    exact (abs_measureReal_sub_le_symmDiff μ (hA.inter (hT.measurable hB))
      (hA'meas.inter (hT.measurable hB'meas))).trans <|
      (measureReal_mono fun u hu => by
        simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union] at hu ⊢; tauto).trans
      (measureReal_union_le _ _)
  have hAerr : |μ.real A - μ.real A'| ≤ μ.real (A ∆ A') := by
    simpa only [abs_sub_comm, symmDiff_comm] using abs_measureReal_sub_le_symmDiff μ hA'meas hA
  have hBerr : |μ.real B - μ.real B'| ≤ μ.real (B' ∆ B) := by
    simpa [abs_sub_comm] using abs_measureReal_sub_le_symmDiff μ hB'meas hB
  have hProdErr : |μ.real A * μ.real B - μ.real A' * μ.real B'| ≤
      μ.real (A ∆ A') + μ.real (B' ∆ B) := by
    calc |μ.real A * μ.real B - μ.real A' * μ.real B'|
      _ = |(μ.real A - μ.real A') * μ.real B + μ.real A' * (μ.real B - μ.real B')| := by
        congr 1; ring
      _ ≤ |(μ.real A - μ.real A') * μ.real B| + |μ.real A' * (μ.real B - μ.real B')| :=
        abs_add_le _ _
      _ = |μ.real A - μ.real A'| * μ.real B + μ.real A' * |μ.real B - μ.real B'| := by
        rw [abs_mul, abs_of_nonneg measureReal_nonneg, abs_mul, abs_of_nonneg measureReal_nonneg]
      _ ≤ |μ.real A - μ.real A'| * 1 + 1 * |μ.real B - μ.real B'| :=
        add_le_add (mul_le_mul_of_nonneg_left measureReal_le_one (abs_nonneg _))
          (mul_le_mul_of_nonneg_right measureReal_le_one (abs_nonneg _))
      _ ≤ μ.real (A ∆ A') + μ.real (B' ∆ B) := by linarith
  rw [Real.dist_eq]
  linarith [abs_sub_le (μ.real (A ∩ Ta ⁻¹' B)) (μ.real A' * μ.real B') (μ.real A * μ.real B),
    abs_sub_comm (μ.real A' * μ.real B') (μ.real A * μ.real B)]

end
end PottsDiscontinuity.PottsThm
