module
public import Mathlib

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

/-- An event of a product field which reads only the coordinates in `F`. -/
def DependsOnIndices {I C : Type*} (F : Finset I) (A : Set (I → C)) : Prop :=
  ∀ u v, (∀ i ∈ F, u i = v i) → (u ∈ A ↔ v ∈ A)

section

variable {I C : Type*}






theorem DependsOnIndices.union  [DecidableEq I] {F G : Finset I}
    {A B : Set (I → C)} (hA : DependsOnIndices F A) (hB : DependsOnIndices G B) :
    DependsOnIndices (F ∪ G) (A ∪ B) := by
  grind +locals

theorem dependsOnIndices_sdiff  [DecidableEq I] {F G : Finset I}
    {A B : Set (I → C)} (hA : DependsOnIndices F A) (hB : DependsOnIndices G B) :
    DependsOnIndices (F ∪ G) (A \ B) := by
  grind +locals

end

def finiteIndexEvents {I C : Type*} : Set (Set (I → C)) :=
  {A | ∃ F : Finset I, DependsOnIndices F A}

theorem finiteIndexEvents_isSetRing {I C : Type*} [DecidableEq I] :
    IsSetRing (finiteIndexEvents (I := I) (C := C)) where
  empty_mem := ⟨∅, by intro u v _; simp⟩
  union_mem := by
    rintro A B ⟨F, hF⟩ ⟨G, hG⟩
    exact ⟨F ∪ G, hF.union hG⟩
  sdiff_mem := by
    rintro A B ⟨F, hF⟩ ⟨G, hG⟩
    exact ⟨F ∪ G, dependsOnIndices_sdiff hF hG⟩

def finiteCoordinateRestrict {I C : Type*} (F : Finset I) (u : I → C) :
     ↥F → C  := fun i => u i.1

def finiteCoordinateExtend {I C : Type*} [DecidableEq I]
    (F : Finset I) (c₀ : C) (u : ↥F → C) : I → C :=
  fun i => if h : i ∈ F then u ⟨i, h⟩ else c₀

private theorem finiteCoordinateRestrict_measurable {I C : Type*}
    [MeasurableSpace C] (F : Finset I) :
    Measurable (finiteCoordinateRestrict F : (I → C) →  ↥F → C ) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply i.1

private theorem measurableSet_of_finite_type {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Finite X] (A : Set X) : MeasurableSet A := MeasurableSet.of_discrete

section

variable {I C : Type*}


private theorem finiteIndexEvent_measurable  [Countable I] [Finite C]
    [MeasurableSpace C] [MeasurableSingletonClass C] [DecidableEq I]
    (c₀ : C) {A : Set (I → C)} (hA : A ∈ finiteIndexEvents (I := I) (C := C)) :
    MeasurableSet A := by
  obtain ⟨F, hF⟩ := hA
  
  let e  := finiteCoordinateExtend F c₀
  have heq : A =  finiteCoordinateRestrict F  ⁻¹'  e ⁻¹' A  := by
    grind +locals
  rw [heq]
  
  exact finiteCoordinateRestrict_measurable F (measurableSet_of_finite_type _)

private theorem finiteCoordinateCylinder_generateFrom  [Countable I]
    [Finite C] [MeasurableSpace C] [MeasurableSingletonClass C] [DecidableEq I]
    (c₀ : C) :
    (inferInstance : MeasurableSpace (I → C)) =
      MeasurableSpace.generateFrom (finiteIndexEvents (I := I) (C := C)) := by
  
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · refine iSup_le fun i => ?_
    refine MeasurableSpace.comap_le_iff_le_map.2 ?_
    intro T hT
    have heq : (fun u : I → C => u i) ⁻¹' T = ⋃ c : T, {u | u i = c.1} := by
      ext u
      simp
    show MeasurableSet[MeasurableSpace.generateFrom
      (finiteIndexEvents (I := I) (C := C))] ((fun u  => u i) ⁻¹' T)
    rw [heq]
    refine MeasurableSet.iUnion fun c => ?_
    apply MeasurableSpace.measurableSet_generateFrom
    refine ⟨{i}, ?_⟩
    intro u v huv
    change u i = c.1 ↔ v i = c.1
    rw [huv i (by simp)]
  · exact fun t a => finiteIndexEvent_measurable c₀ a

private theorem finiteIndexEvent_approx  [Countable I] [Finite C]
    [MeasurableSpace C] [MeasurableSingletonClass C] [DecidableEq I]
    (μ : Measure (I → C)) [IsFiniteMeasure μ] (c₀ : C)
    {A : Set (I → C)} (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ B, B ∈ finiteIndexEvents (I := I) (C := C) ∧ μ (B ∆ A) < ε := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
                                                                (finiteIndexEvents_isSetRing (I := I) (C := C)) (by
                                                                                                                   refine ⟨{univ}, Set.countable_singleton _, ?_, by simp⟩
                                                                                                                   intro B hB
                                                                                                                   subst B
                                                                                                                   exact ⟨∅, by intro u v _; simp⟩)
                                                                (finiteCoordinateCylinder_generateFrom (I := I) (C := C) c₀) hA hε

end

theorem abs_measureReal_sub_le_symmDiff {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |μ.real A - μ.real B| ≤ μ.real (A ∆ B) := by
  have h := (MeasuredSets.lipschitzWith_measureReal (μ := μ)).dist_le_mul
     ⟨A, hA⟩   ⟨B, hB⟩ 
  aesop

def iidFieldMeasure {I C : Type*} [MeasurableSpace C]
    (ν : Measure C) : Measure (I → C) := Measure.infinitePi  fun _ => ν 

def iidFieldShift {I C : Type*} (e : I ≃ I) (u : I → C) : I → C :=
  fun i => u (e.symm i)

section

variable {I C : Type*}
include I C

theorem iidFieldShift_measurePreserving  [MeasurableSpace C]
    (ν : Measure C) [IsProbabilityMeasure ν] (e : I ≃ I) :
    MeasurePreserving (iidFieldShift e) (iidFieldMeasure ν) (iidFieldMeasure ν) := by
  constructor
  · exact measurable_pi_iff.mpr fun i => measurable_pi_apply (e.symm i)
  · have hfun : iidFieldShift e =
        ⇑(MeasurableEquiv.piCongrLeft (fun _  => C) e) := by
      funext u i
      simp [iidFieldShift, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
    rw [hfun]
    exact Measure.infinitePi_map_piCongrLeft (μ := fun _  => ν) e

theorem iidField_independent_supported_events  [DecidableEq I]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C]
    (ν : Measure C) [IsProbabilityMeasure ν] (c₀ : C) (F G : Finset I)
    (hFG : Disjoint F G) (A B : Set (I → C))
    (hA : DependsOnIndices F A) (hB : DependsOnIndices G B) :
    iidFieldMeasure ν (A ∩ B) = iidFieldMeasure ν A * iidFieldMeasure ν B := by
  
  
  
  
  let extF  := finiteCoordinateExtend F c₀
  let extG  := finiteCoordinateExtend G c₀
  have hAeq : A =  finiteCoordinateRestrict F  ⁻¹'  extF ⁻¹' A  := by
    grind +locals
  have hBeq : B =  finiteCoordinateRestrict G  ⁻¹'  extG ⁻¹' B  := by
    grind +locals
  have hEval : ProbabilityTheory.iIndepFun (fun i (u : I → C) => u i) (iidFieldMeasure ν) := ProbabilityTheory.iIndepFun_infinitePi fun i => measurable_id'
  have hProj := hEval.indepFun_finset F G hFG  measurable_pi_apply 
  rw [hAeq, hBeq]
  exact hProj.measure_inter_preimage_eq_mul (extF ⁻¹' A) (extG ⁻¹' B)
    (measurableSet_of_finite_type _) (measurableSet_of_finite_type _)

theorem DependsOnIndices.preimage_iidFieldShift  {F : Finset I}
    {A : Set (I → C)} (hA : DependsOnIndices F A) (e : I ≃ I) :
    DependsOnIndices (F.map e.symm.toEmbedding) (iidFieldShift e ⁻¹' A) := by
  intro u v huv
  
  apply hA
  aesop

theorem iidField_mixing_of_finite_separation  [Countable I] [DecidableEq I]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C]
    (ν : Measure C) [IsProbabilityMeasure ν] (c₀ : C)
    (e :  ℤ × ℤ  → I ≃ I)
    (hsep : ∀ F G : Finset I, ∀ᶠ a : ℤ × ℤ in cofinite,
      Disjoint F (G.map (e a).symm.toEmbedding))
    {A B : Set (I → C)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun a : ℤ × ℤ =>
      (iidFieldMeasure ν).real (A ∩ iidFieldShift (e a) ⁻¹' B)) cofinite
      (𝓝 ((iidFieldMeasure ν).real A * (iidFieldMeasure ν).real B)) := by
  let μ : Measure (I → C) := iidFieldMeasure ν
  have hμprob : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (Measure.infinitePi  fun _ => ν )
    infer_instance
  
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ  := ε / 8
  have hδ : 0 < δ := by  positivity
  obtain ⟨A', hA'fin, hA'err⟩ := finiteIndexEvent_approx μ c₀ hA
    (ENNReal.ofReal_pos.mpr hδ)
  obtain ⟨B', hB'fin, hB'err⟩ := finiteIndexEvent_approx μ c₀ hB
    (ENNReal.ofReal_pos.mpr hδ)
  have hA'meas  := finiteIndexEvent_measurable c₀ hA'fin
  have hB'meas  := finiteIndexEvent_measurable c₀ hB'fin
  have hA'errR : μ.real (A' ∆ A) < δ := by
    
    simpa [Measure.real_def, ENNReal.toReal_ofReal hδ.le] using  (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hA'err 
  have hB'errR : μ.real (B' ∆ B) < δ := by
    
    simpa [Measure.real_def, ENNReal.toReal_ofReal hδ.le] using  (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hB'err 
  obtain ⟨F, hF⟩ := hA'fin
  obtain ⟨G, hG⟩ := hB'fin
  
  filter_upwards [ hsep F G ] with a ha
  let Ta : (I → C) →  I → C  := iidFieldShift (e a)
  have hT : MeasurePreserving Ta μ μ := by
    grind [iidFieldShift_measurePreserving]
  
  
  have hBerrShift : μ.real ((Ta ⁻¹' B) ∆ (Ta ⁻¹' B')) = μ.real (B' ∆ B) := by
    
    calc
      _ = μ.real (Ta ⁻¹'  B ∆ B' ) := by rw [ Eq.symm (preimage_symmDiff B B') ]
      _ = μ.real (B ∆ B') := by
        simp only [Measure.real_def]
        rw [← Measure.map_apply hT.measurable (hB.symmDiff hB'meas), hT.map_eq]
      _ = μ.real (B' ∆ B) := by rw [symmDiff_comm]
  
  have hJointErr : |μ.real (A ∩ Ta ⁻¹' B) - μ.real (A' ∩ Ta ⁻¹' B')| ≤
      μ.real (A ∆ A') + μ.real (B' ∆ B) := by
    
    
    
    calc
      _ ≤ μ.real ((A ∩  Ta ⁻¹' B ) ∆ (A' ∩  Ta ⁻¹' B' )) := (abs_measureReal_sub_le_symmDiff μ (hA.inter (hT.measurable hB)) (hA'meas.inter (hT.measurable hB'meas)))
      _ ≤ μ.real ( A ∆ A'  ∪  (Ta ⁻¹' B) ∆ (Ta ⁻¹' B') ) := measureReal_mono (by
                                                                                grind)
      _ ≤ μ.real (A ∆ A') + μ.real ((Ta ⁻¹' B) ∆ (Ta ⁻¹' B')) := measureReal_union_le _ _
      _ = _ := by rw [hBerrShift]
  have hProbProdErr : |μ.real A * μ.real B - μ.real A' * μ.real B'| ≤
      μ.real (A ∆ A') + μ.real (B' ∆ B) := by
    have hAerr₀ := abs_measureReal_sub_le_symmDiff μ hA'meas hA
    
    
    
    
    
    
    
    
    calc
      _ = |(μ.real A - μ.real A') * μ.real B + μ.real A' * (μ.real B - μ.real B')| := by
        
        ring
      _ ≤ |(μ.real A - μ.real A') * μ.real B| +
          |μ.real A' * (μ.real B - μ.real B')| := abs_add_le _ _
      _ = |μ.real A - μ.real A'| * μ.real B +
          μ.real A' * |μ.real B - μ.real B'| := by
        rw [abs_mul, abs_of_nonneg  measureReal_nonneg , abs_mul, abs_of_nonneg  measureReal_nonneg ]
      _ ≤ _ := by
        have h1 : |μ.real A - μ.real A'| * μ.real B ≤ μ.real (A ∆ A') := by
          calc
            _ ≤ |μ.real A - μ.real A'| * 1 :=
              mul_le_mul_of_nonneg_left  measureReal_le_one  (abs_nonneg (μ.real A - μ.real A'))
            _ = |μ.real A - μ.real A'| := by ring
            _ ≤ _ :=  by
                        grind 
        have h2 : μ.real A' * |μ.real B - μ.real B'| ≤ μ.real (B' ∆ B) := by
          calc
            _ ≤ 1 * |μ.real B - μ.real B'| :=
              mul_le_mul_of_nonneg_right  measureReal_le_one  (abs_nonneg (μ.real B - μ.real B'))
            _ = |μ.real B - μ.real B'| := by ring
            _ ≤ _ :=  by
                        simpa [abs_sub_comm] using  abs_measureReal_sub_le_symmDiff μ hB'meas hB  
        linarith
  have htarget : μ.real (A' ∩  Ta ⁻¹' B' ) = μ.real A' * μ.real B' := by
    have hreal := congrArg ENNReal.toReal (iidField_independent_supported_events ν c₀ F
                                             (G.map (e a).symm.toEmbedding) ha A' (Ta ⁻¹' B') hF (hG.preimage_iidFieldShift (e a)))
    
    have hreal' : μ.real (A' ∩  Ta ⁻¹' B' ) =
        μ.real A' * μ.real (Ta ⁻¹' B') := by
      simpa [Measure.real_def] using hreal
    have hmass : μ.real (Ta ⁻¹' B') = μ.real B' := by
      simp only [Measure.real_def]
      rw [← Measure.map_apply hT.measurable hB'meas, hT.map_eq]
    rw [hmass] at hreal'
    exact hreal'
  
  
  simpa [μ, Ta, Real.dist_eq] using  by
                                       grind 

end

end
end PottsDiscontinuity.PottsThm
