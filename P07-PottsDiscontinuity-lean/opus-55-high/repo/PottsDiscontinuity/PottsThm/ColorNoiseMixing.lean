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

section
variable {I C : Type*}
/-- An event of a product field which reads only the coordinates in `F`. -/
def DependsOnIndices (F : Finset I) (A : Set (I → C)) : Prop :=
  ∀ u v, (∀ i ∈ F, u i = v i) → (u ∈ A ↔ v ∈ A)

end

section
variable {I C : Type*} [DecidableEq I] {F G : Finset I} {A B : Set (I → C)} (hA : DependsOnIndices F A) (hB : DependsOnIndices G B)
include hA hB
theorem DependsOnIndices.union  :
    DependsOnIndices (F ∪ G) (A ∪ B) := by
  intro u v huv
  apply or_congr
  · exact hA u v (fun i hi => huv i (Finset.mem_union.mpr (.inl hi)))
  · exact hB u v (fun i hi => huv i (Finset.mem_union.mpr (.inr hi)) )

theorem dependsOnIndices_sdiff  :
    DependsOnIndices (F ∪ G) (A \ B) := by
  intro u v huv
  exact and_congr (hA u v (fun i hi => huv i (Finset.mem_union.mpr (.inl hi))))
    (not_congr (hB u v (fun i hi => huv i (Finset.mem_union.mpr (.inr hi)))))
end

section
variable {I C : Type*}
include C
def finiteIndexEvents  : Set (Set (I → C)) :=
  {A | ∃ F : Finset I, DependsOnIndices F A}

theorem finiteIndexEvents_isSetRing [DecidableEq I] :
    IsSetRing (finiteIndexEvents (I := I) (C := C)) where
  empty_mem := ⟨∅, by tauto⟩
  union_mem := by
    rintro A B ⟨F, hF⟩ ⟨G, hG⟩
    exact ⟨F ∪ G, hF.union hG⟩
  sdiff_mem := by
    rintro A B ⟨F, hF⟩ ⟨G, hG⟩
    exact ⟨F ∪ G, dependsOnIndices_sdiff hF hG⟩

def finiteCoordinateRestrict (F : Finset I) (u : I → C) :
    (↥F → C) := fun i => u i.1

def finiteCoordinateExtend [DecidableEq I]
    (F : Finset I) (c₀ : C) (u : ↥F → C) : I → C :=
  fun i => if h : i ∈ F then u ⟨i, h⟩ else c₀

theorem finiteCoordinateRestrict_measurable [MeasurableSpace C] (F : Finset I) :
    Measurable (finiteCoordinateRestrict F : (I → C) → (↥F → C)) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply i.1
end

theorem measurableSet_of_finite_type {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Finite X] (A : Set X) : MeasurableSet A := by
  have hA : A = ⋃ x : A, ({x.1} : Set X) := by simp
  rw [hA]
  exact MeasurableSet.iUnion fun x => MeasurableSet.singleton x.1

section
variable {I C : Type*} [Countable I] [Finite C] [MeasurableSpace C] [MeasurableSingletonClass C] [DecidableEq I]
theorem finiteIndexEvent_measurable (c₀ : C) {A : Set (I → C)} (hA : A ∈ finiteIndexEvents (I := I) (C := C)) :
    MeasurableSet A := by
  obtain ⟨F, hF⟩ := hA
  let r : (I → C) → (↥F → C) := finiteCoordinateRestrict F
  let e := finiteCoordinateExtend F c₀
  have heq : A = r ⁻¹' (e ⁻¹' A) := by
    ext u
    apply hF u (e (r u)) ?_
    grind [finiteCoordinateExtend, finiteCoordinateRestrict]
  rw [heq]
  exact finiteCoordinateRestrict_measurable F (measurableSet_of_finite_type _)

theorem finiteCoordinateCylinder_generateFrom (c₀ : C) :
    (inferInstance : MeasurableSpace (I → C)) =
      MeasurableSpace.generateFrom (finiteIndexEvents (I := I) (C := C)) := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · refine iSup_le fun i => ?_
    refine MeasurableSpace.comap_le_iff_le_map.2 ?_
    intro T hT
    apply MeasurableSpace.measurableSet_generateFrom
    refine ⟨{i}, ?_⟩
    intro u v huv
    simp_all
  · intro A hA
    exact finiteIndexEvent_measurable c₀ hA

theorem finiteIndexEvent_approx (μ : Measure (I → C)) [IsFiniteMeasure μ] (c₀ : C)
    {A : Set (I → C)} (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ B, B ∈ finiteIndexEvents (I := I) (C := C) ∧ μ (B ∆ A) < ε := by
  have hcover : ∃ D : Set (Set (I → C)), D.Countable ∧
      D ⊆ finiteIndexEvents ∧ μ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{univ}, Set.countable_singleton _, ?_, by simp⟩
    intro B hB
    subst B
    exact ⟨∅, by tauto⟩
  exact exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (finiteIndexEvents_isSetRing) hcover
    (finiteCoordinateCylinder_generateFrom c₀) hA hε
end

theorem abs_measureReal_sub_le_symmDiff {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |μ.real A - μ.real B| ≤ μ.real (A ∆ B) := by
  have h := (MeasuredSets.lipschitzWith_measureReal (μ := μ)).dist_le_mul
    (⟨A, hA⟩ : MeasuredSets μ) (⟨B, hB⟩ : MeasuredSets μ)
  aesop

section
variable {I C : Type*}
def iidFieldMeasure [MeasurableSpace C]
    (ν : Measure C) : Measure (I → C) := Measure.infinitePi (fun _ => ν)

def iidFieldShift (e : I ≃ I) (u : I → C) : I → C :=
  fun i => u (e.symm i)

theorem iidFieldShift_measurePreserving [MeasurableSpace C]
    (ν : Measure C) [IsProbabilityMeasure ν] (e : I ≃ I) :
    MeasurePreserving (iidFieldShift e) (iidFieldMeasure ν) (iidFieldMeasure ν) := by
  constructor
  · exact measurable_pi_iff.mpr fun i => measurable_pi_apply (e.symm i)
  · have hfun : iidFieldShift e =
        ⇑(MeasurableEquiv.piCongrLeft (fun _ : I => C) e) := by
      funext u i
      simp [iidFieldShift, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
    rw [hfun]
    exact Measure.infinitePi_map_piCongrLeft (μ := fun _ : I => ν) e

theorem iidField_independent_supported_events [DecidableEq I]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C]
    (ν : Measure C) [IsProbabilityMeasure ν] (c₀ : C) (F G : Finset I)
    (hFG : Disjoint F G) (A B : Set (I → C))
    (hA : DependsOnIndices F A) (hB : DependsOnIndices G B) :
    iidFieldMeasure ν (A ∩ B) = iidFieldMeasure ν A * iidFieldMeasure ν B := by
  let μ : Measure (I → C) := iidFieldMeasure ν
  let projF : (I → C) → (↥F → C) := finiteCoordinateRestrict F
  let projG : (I → C) → (↥G → C) := finiteCoordinateRestrict G
  let extF := finiteCoordinateExtend F c₀
  let extG := finiteCoordinateExtend G c₀
  have hAeq : A = projF ⁻¹' (extF ⁻¹' A) := by
    ext u
    apply hA u (extF (projF u))
    grind [finiteCoordinateExtend, finiteCoordinateRestrict]
  have hBeq : B = projG ⁻¹' (extG ⁻¹' B) := by
    ext u
    apply hB u (extG (projG u))
    grind [finiteCoordinateExtend, finiteCoordinateRestrict]
  have hEval : ProbabilityTheory.iIndepFun (fun i (u : I → C) => u i) μ :=
    ProbabilityTheory.iIndepFun_infinitePi
      (X := fun _ (c : C) => c) (by fun_prop)
  have hProj := hEval.indepFun_finset F G hFG (fun i => measurable_pi_apply i)
  rw [hAeq, hBeq]
  exact hProj.measure_inter_preimage_eq_mul (extF ⁻¹' A) (extG ⁻¹' B)
    (measurableSet_of_finite_type _) (measurableSet_of_finite_type _)

theorem DependsOnIndices.preimage_iidFieldShift {F : Finset I}
    {A : Set (I → C)} (hA : DependsOnIndices F A) (e : I ≃ I) :
    DependsOnIndices (F.map e.symm.toEmbedding) (iidFieldShift e ⁻¹' A) := by
  intro u v huv
  apply hA
  aesop

theorem iidField_mixing_of_finite_separation [Countable I] [DecidableEq I]
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
  have hμprob : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (Measure.infinitePi (fun _ => ν))
    infer_instance
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / 8
  have hδ : 0 < δ := by positivity
  obtain ⟨A', hA'fin, hA'err⟩ := finiteIndexEvent_approx μ c₀ hA
    (ENNReal.ofReal_pos.mpr hδ)
  obtain ⟨B', hB'fin, hB'err⟩ := finiteIndexEvent_approx μ c₀ hB
    (ENNReal.ofReal_pos.mpr hδ)
  have hA'meas := finiteIndexEvent_measurable c₀ hA'fin
  have hB'meas := finiteIndexEvent_measurable c₀ hB'fin
  have hA'errR : μ.real (A' ∆ A) < δ := by
    simpa [δ, Measure.real_def, ENNReal.toReal_ofReal hδ.le] using ((ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hA'err)
  have hB'errR : μ.real (B' ∆ B) < δ := by
    simpa [δ, Measure.real_def, ENNReal.toReal_ofReal hδ.le] using ((ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hB'err)
  obtain ⟨F, hF⟩ := hA'fin
  obtain ⟨G, hG⟩ := hB'fin
  filter_upwards [(hsep F G)] with a ha
  let Ta : (I → C) → (I → C) := iidFieldShift (e a)
  have hT : MeasurePreserving Ta μ μ := by
    grind [iidFieldMeasure, iidFieldShift_measurePreserving]
  have hind := iidField_independent_supported_events ν c₀ F
    (G.map (e a).symm.toEmbedding) ha A' (Ta ⁻¹' B') hF (hG.preimage_iidFieldShift (e a))
  have hBerrShift : μ.real ((Ta ⁻¹' B) ∆ (Ta ⁻¹' B')) = μ.real (B' ∆ B) := by
    calc
      _ = μ.real (Ta ⁻¹' (B ∆ B')) := by rfl
      _ = μ.real (B ∆ B') := by
        simp only [Measure.real_def]
        rw [← Measure.map_apply hT.measurable (hB.symmDiff hB'meas), hT.map_eq]
      _ = μ.real (B' ∆ B) := by grind
  have hJointSet : (A ∩ (Ta ⁻¹' B)) ∆ (A' ∩ (Ta ⁻¹' B')) ⊆
      (A ∆ A') ∪ ((Ta ⁻¹' B) ∆ (Ta ⁻¹' B')) := by
    grind
  have hJointErr : |μ.real (A ∩ Ta ⁻¹' B) - μ.real (A' ∩ Ta ⁻¹' B')| ≤
      μ.real (A ∆ A') + μ.real (B' ∆ B) := by
    have hleft := hA.inter (hT.measurable hB)
    have hright := hA'meas.inter (hT.measurable hB'meas)
    calc
      _ ≤ μ.real ((A ∩ (Ta ⁻¹' B)) ∆ (A' ∩ (Ta ⁻¹' B'))) := (abs_measureReal_sub_le_symmDiff μ hleft hright)
      _ ≤ μ.real ((A ∆ A') ∪ ((Ta ⁻¹' B) ∆ (Ta ⁻¹' B'))) := measureReal_mono hJointSet
      _ ≤ μ.real (A ∆ A') + μ.real ((Ta ⁻¹' B) ∆ (Ta ⁻¹' B')) := measureReal_union_le _ _
      _ = _ := by linarith
  have hProbProdErr : |μ.real A * μ.real B - μ.real A' * μ.real B'| ≤
      μ.real (A ∆ A') + μ.real (B' ∆ B) := by
    have hAerr₀ := abs_measureReal_sub_le_symmDiff μ hA'meas hA
    have hBerr₀ := abs_measureReal_sub_le_symmDiff μ hB'meas hB
    have hAerr : |μ.real A - μ.real A'| ≤ μ.real (A ∆ A') := by
      grind
    have hBerr : |μ.real B - μ.real B'| ≤ μ.real (B' ∆ B) := by
      grind
    calc
      _ = |(μ.real A - μ.real A') * μ.real B + μ.real A' * (μ.real B - μ.real B')| := by
        ring
      _ ≤ |(μ.real A - μ.real A') * μ.real B| +
          |μ.real A' * (μ.real B - μ.real B')| := abs_add_le _ _
      _ = |μ.real A - μ.real A'| * μ.real B +
          μ.real A' * |μ.real B - μ.real B'| := by
        rw [abs_mul, abs_of_nonneg measureReal_nonneg, abs_mul, abs_of_nonneg measureReal_nonneg]
      _ ≤ _ := by
        have h1 : |μ.real A - μ.real A'| * μ.real B ≤ μ.real (A ∆ A') := by
          calc
            _ ≤ |μ.real A - μ.real A'| * 1 :=
              mul_le_mul_of_nonneg_left measureReal_le_one (abs_nonneg (μ.real A - μ.real A'))
            _ = |μ.real A - μ.real A'| := by ring
            _ ≤ _ := hAerr
        have h2 : μ.real A' * |μ.real B - μ.real B'| ≤ μ.real (B' ∆ B) := by
          calc
            _ ≤ 1 * |μ.real B - μ.real B'| :=
              mul_le_mul_of_nonneg_right measureReal_le_one (abs_nonneg (μ.real B - μ.real B'))
            _ = |μ.real B - μ.real B'| := by ring
            _ ≤ _ := hBerr
        linarith
  have htarget : μ.real (A' ∩ (Ta ⁻¹' B')) = μ.real A' * μ.real B' := by
    have hreal := congrArg ENNReal.toReal hind
    rw [ENNReal.toReal_mul] at hreal
    have hreal' : μ.real (A' ∩ (Ta ⁻¹' B')) =
        μ.real A' * μ.real (Ta ⁻¹' B') := by
      tauto
    have hmass : μ.real (Ta ⁻¹' B') = μ.real B' := by
      simp only [Measure.real_def]
      rw [← Measure.map_apply hT.measurable hB'meas, hT.map_eq]
    simp_all
  have hbound : |μ.real (A ∩ Ta ⁻¹' B) - μ.real A * μ.real B| < ε := by
    grind
  omega
end

end
end PottsDiscontinuity.PottsThm
