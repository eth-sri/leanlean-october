module
public import Mathlib

public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import PottsDiscontinuity.PottsThm.ColorNoiseMixing

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Topology Set MeasurableSpace
open scoped symmDiff

noncomputable section

def measurableRectangles {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] :
    Set (Set (X × Y)) :=
  {R | ∃ A B, MeasurableSet A ∧ MeasurableSet B ∧ R = A ×ˢ B}

section

variable {X Y : Type*}


theorem measurableRectangles_isSetSemiring  [MeasurableSpace X]
    [MeasurableSpace Y] : IsSetSemiring (measurableRectangles (X := X) (Y := Y)) := by
  
  constructor
  · refine ⟨∅, univ, MeasurableSet.empty, MeasurableSet.univ, ?_⟩
    simp
  · rintro R ⟨A, B, hA, hB, rfl⟩ S ⟨C, D, hC, hD, rfl⟩
    refine ⟨A ∩ C, B ∩ D, hA.inter hC, hB.inter hD, ?_⟩
    aesop
  · rintro R ⟨A, B, hA, hB, rfl⟩ S ⟨C, D, hC, hD, rfl⟩
    let R₁  := (A \ C) ×ˢ B
    let R₂  := (A ∩ C) ×ˢ (B \ D)
    let K : Finset (Set (X × Y)) := insert R₁ {R₂}
    
    
    have memK_iff (T : Set (X × Y)) : T ∈ K ↔ T = R₁ ∨ T = R₂ := by
      grind
    
    
    
    exact ⟨K,  by
                 intro T hT
                 have hT'  := (memK_iff T).mp hT
                 rcases hT' with hT' | hT'
                 · subst T
                   exact ⟨A \ C, B, hA.inter hC.compl, hB, rfl⟩
                 · subst T
                   exact ⟨A ∩ C, B \ D, hA.inter hC, hB.inter hD.compl, rfl⟩ ,  by
                     intro T hT U hU hne
                     grind ,  by
                            ext z
                            simp only [Set.mem_sdiff, Set.mem_prod]
                            constructor
                            · simp_all <;> grind
                            · grind ⟩

theorem measurableRectangles_generateFrom  [MeasurableSpace X]
    [MeasurableSpace Y] :
    MeasurableSpace.generateFrom (measurableRectangles (X := X) (Y := Y)) =
      (inferInstance : MeasurableSpace (X × Y)) := by
  have hrect : measurableRectangles (X := X) (Y := Y) =
      image2 (· ×ˢ ·) {A : Set X | MeasurableSet A}
        {B : Set Y | MeasurableSet B} := by
    grind +locals
  rw [hrect]
  exact generateFrom_prod

theorem measurableRectangleRing_generateFrom  [MeasurableSpace X]
    [MeasurableSpace Y] :
    MeasurableSpace.generateFrom
        (supClosure (measurableRectangles (X := X) (Y := Y))) =
      (inferInstance : MeasurableSpace (X × Y)) := by
  rw [← measurableRectangles_generateFrom (X := X) (Y := Y)]
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    intro R hR
    exact measurableSet_generateFrom_of_mem_supClosure hR
  · apply MeasurableSpace.generateFrom_le
    intro R hR
    exact measurableSet_generateFrom (subset_supClosure hR)

end

def productShift {Γ X Y : Type*} (T : Γ → X → X) (S : Γ → Y → Y)
    (a : Γ) : X × Y → X × Y := fun z => (T a z.1, S a z.2)

private theorem prodMeasure_real_rectangle {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {A : Set X} {B : Set Y} :
    (μ.prod ν).real (A ×ˢ B) = μ.real A * ν.real B := by
      simp_all

/-- The product of two translation mixing systems has no nontrivial invariant
events. The proof uses rectangles as a generating set ring, so it does not
require either factor to have a finite dimensional state space. -/
theorem mixingProduct_invariant_event {Γ X Y : Type*} [Infinite Γ]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : Γ → X → X) (S : Γ → Y → Y)
    (hTpres : ∀ a, MeasurePreserving (T a) μ μ)
    (hSpres : ∀ a, MeasurePreserving (S a) ν ν)
    (hTmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun a => μ.real (A ∩  T a  ⁻¹' B)) cofinite (𝓝 (μ.real A * μ.real B)))
    (hSmix : ∀ A B : Set Y, MeasurableSet A → MeasurableSet B →
      Tendsto (fun a => ν.real (A ∩  S a  ⁻¹' B)) cofinite (𝓝 (ν.real A * ν.real B)))
    {E : Set (X × Y)} (hE : MeasurableSet E)
    (hEinv : ∀ a,  productShift T S a  ⁻¹' E = E) :
    (μ.prod ν) E = 0 ∨ (μ.prod ν) Eᶜ = 0 := by
  
  let ρ  := μ.prod ν
  have : IsProbabilityMeasure ρ :=  inferInstance
  have hprodPres (a : Γ) : MeasurePreserving (productShift T S a) ρ ρ := by
                                                                           solve_by_elim [_root_.MeasureTheory.MeasurePreserving.prod]
  let R  := supClosure
    (measurableRectangles (X := X) (Y := Y))
  
  have hRcover : ∃ D : Set (Set (X × Y)), D.Countable ∧ D ⊆ R ∧ ρ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{univ}, Set.countable_singleton _, ?_, by simp ⟩
    intro U hU
    subst U
    apply subset_supClosure
    exact ⟨univ, univ, MeasurableSet.univ, MeasurableSet.univ, by simp⟩
  have hfiniteApproxIndep (E' : Set (X × Y)) (P : Finpartition E')
      (hPrect : (P.parts : Set (Set (X × Y))) ⊆ measurableRectangles (X := X) (Y := Y))
      (A : Set X) (B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      |ρ.real (E ∩  A ×ˢ B ) - ρ.real E' * ρ.real (A ×ˢ B)| ≤ ρ.real (E' ∆ E) := by
    let Q  := productShift T S
    have hshiftMeas (a : Γ) : Measurable (Q a) := by
                                                    solve_by_elim [_root_.Measurable.prodMk, _root_.Measurable.comp, _root_.MeasureTheory.MeasurePreserving.measurable, _root_.measurable_fst, _root_.measurable_snd]
    have htargetMeas  := hA.prod hB
    have hEparts : E' = ⋃ U ∈ P.parts, U :=
      P.sup_parts.symm.trans (Finset.sup_set_eq_biUnion _ _)
    have hRmeas (U : Set (X × Y)) (hU : U ∈ P.parts) : MeasurableSet U := by
      obtain ⟨C, D, hC, hD, rfl⟩ := hPrect hU
      exact hC.prod hD
    have hE'meas  := Eq.mpr  (congrArg MeasurableSet hEparts)  (Finset.measurableSet_biUnion P.parts hRmeas)
    
    have hpieceTerm (U : Set (X × Y)) (hU : U ∈ P.parts) :
        Tendsto (fun a => ρ.real (U ∩  Q a  ⁻¹'  A ×ˢ B )) cofinite
          (𝓝 (ρ.real U * ρ.real (A ×ˢ B))) := by
      obtain ⟨C, D, hC, hD, hUeq⟩ := hPrect hU
      have hset (a : Γ) : U ∩  Q a  ⁻¹'  A ×ˢ B  =
          (C ∩  T a  ⁻¹' A) ×ˢ (D ∩  S a  ⁻¹' B) := by
        grind +locals
      
      
      have hlimit :  μ.real C * μ.real A  * (ν.real D * ν.real B) =
          ρ.real U * ρ.real (A ×ˢ B) := by
        grind [prodMeasure_real_rectangle]
      convert  (hTmix C A hC hA).mul (hSmix D B hD hB)  using 1
      · aesop
      · exact congrArg 𝓝 hlimit.symm
    have hjointSum (a : Γ) : ρ.real (E' ∩  Q a  ⁻¹'  A ×ˢ B ) =
        ∑ U ∈ P.parts, ρ.real (U ∩  Q a  ⁻¹'  A ×ˢ B ) := by
      conv_lhs => simp only [hEparts, Set.iUnion_inter]
      exact measureReal_biUnion_finset
        (fun U hU V hV hne =>
          (P.disjoint hU hV hne).mono inter_subset_left inter_subset_left)
        (fun U hU => (hRmeas U hU).inter (hshiftMeas a htargetMeas))
         fun U _ => measure_ne_top ρ _ 
    
    have hjointLimit : Tendsto (fun a  =>
        ρ.real (E' ∩  Q a  ⁻¹'  A ×ˢ B )) cofinite
        (𝓝 (ρ.real E' * ρ.real (A ×ˢ B))) := by
      have hsumLimit' :=  tendsto_finsetSum P.parts hpieceTerm 
      rw [← Finset.sum_mul, ←  Trans.trans (congrArg ρ.real hEparts)
                                                                                          (measureReal_biUnion_finset (Finpartition.disjoint P) hRmeas fun b a => measure_ne_top ρ (id b)) ] at hsumLimit'
      all_goals grind
    have hconst (a : Γ) : ρ.real (E ∩  Q a  ⁻¹'  A ×ˢ B ) =
        ρ.real (E ∩  A ×ˢ B ) := by
      have hpre :  Q a  ⁻¹' (E ∩  A ×ˢ B ) = E ∩  Q a  ⁻¹'  A ×ˢ B  := by
        rw [Set.preimage_inter, hEinv a]
      
      rw [← hpre]
      exact  by
               simp only [Measure.real_def]
               rw [← Measure.map_apply (hprodPres a).measurable (hE.inter htargetMeas),
                 (hprodPres a).map_eq] 
    have hchangeLe (a : Γ) : |ρ.real (E ∩  Q a  ⁻¹'  A ×ˢ B ) -
        ρ.real (E' ∩  Q a  ⁻¹'  A ×ˢ B )| ≤ ρ.real (E' ∆ E) := by
      have hsubset : (E ∩  Q a  ⁻¹'  A ×ˢ B ) ∆
          (E' ∩  Q a  ⁻¹'  A ×ˢ B ) ⊆ E ∆ E' := by
        grind
      have hle := abs_measureReal_sub_le_symmDiff ρ
        (hE.inter (hshiftMeas a htargetMeas)) (hE'meas.inter (hshiftMeas a htargetMeas))
      calc
        _ ≤ ρ.real ((E ∩  Q a  ⁻¹'  A ×ˢ B ) ∆ (E' ∩  Q a  ⁻¹'  A ×ˢ B )) := hle
        _ ≤ ρ.real (E ∆ E') := measureReal_mono hsubset
        _ = ρ.real (E' ∆ E) := by rw [symmDiff_comm]
    by_contra hnot
    
    let η  := (|ρ.real (E ∩  A ×ˢ B ) - ρ.real E' * ρ.real (A ×ˢ B)| -
      ρ.real (E' ∆ E)) / 2
    have hη : 0 < η := by dsimp [η]; linarith
    obtain ⟨a, ha⟩ := (Metric.tendsto_nhds.mp hjointLimit _ hη).exists
    rw [Real.dist_eq] at ha
    have hchangeRect : |ρ.real (E ∩  A ×ˢ B ) -
        ρ.real (E' ∩  Q a  ⁻¹'  A ×ˢ B )| ≤ ρ.real (E' ∆ E) := by
      rw [← hconst a]
      exact hchangeLe a
    
    dsimp [η] at ha
    nlinarith [hchangeRect, ha,  lt_of_not_ge hnot ,  abs_sub_le (ρ.real (E ∩  A ×ˢ B ))
                                         (ρ.real (E' ∩  Q a  ⁻¹'  A ×ˢ B )) (ρ.real E' * ρ.real (A ×ˢ B)) ]
  have hrectIndependent (A : Set X) (B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      ρ.real (E ∩  A ×ˢ B ) = ρ.real E * ρ.real (A ×ˢ B) := by
    by_contra hne
    have hdpos  :=
      abs_pos.mpr (sub_ne_zero.mpr hne)
    let η  := |ρ.real (E ∩  A ×ˢ B ) - ρ.real E * ρ.real (A ×ˢ B)| / 2
    have hη : 0 < η := by dsimp [η]; linarith
    obtain ⟨E', hE'R, hE'err⟩ :=
      exists_measure_symmDiff_lt_of_generateFrom_isSetRing  (measurableRectangles_isSetSemiring (X := X) (Y := Y)).isSetRing_supClosure  hRcover
        (measurableRectangleRing_generateFrom (X := X) (Y := Y)).symm hE
        (ENNReal.ofReal_pos.mpr hη)
    have hE'errR : ρ.real (E' ∆ E) < η := by
      
      simpa [Measure.real_def, ENNReal.toReal_ofReal hη.le] using  (ENNReal.toReal_lt_toReal (measure_ne_top ρ _) ENNReal.ofReal_ne_top).mpr hE'err 
    obtain ⟨P, hPrect⟩ :=
      (measurableRectangles_isSetSemiring (X := X) (Y := Y)).mem_supClosure_iff.mp hE'R
    
    have hE'meas : MeasurableSet E' := by
      
      rw [ P.sup_parts.symm.trans (Finset.sup_set_eq_biUnion _ _) ]
      exact P.parts.measurableSet_biUnion  fun U hU => by
        obtain ⟨C, D, hC, hD, rfl⟩ := hPrect hU
        exact hC.prod hD 
    have hmass  :=
      abs_measureReal_sub_le_symmDiff ρ hE'meas hE
    have hrectNonneg : 0 ≤ ρ.real (A ×ˢ B) := measureReal_nonneg
    have hrectLeOne : ρ.real (A ×ˢ B) ≤ 1 := measureReal_le_one
    
    have hdev₁  :=
      lt_of_le_of_lt (hfiniteApproxIndep E' P hPrect A B hA hB) hE'errR
    have hdev₂ :
        |ρ.real E' * ρ.real (A ×ˢ B) - ρ.real E * ρ.real (A ×ˢ B)| < η :=
      lt_of_le_of_lt (by
                        calc
                          _ = |ρ.real E' - ρ.real E| * |ρ.real (A ×ˢ B)| := by
                            rw [← sub_mul, abs_mul]
                          _ ≤ ρ.real (E' ∆ E) * 1 := by
                            rw [abs_of_nonneg hrectNonneg]
                            exact mul_le_mul hmass hrectLeOne hrectNonneg  measureReal_nonneg 
                          _ = ρ.real (E' ∆ E) := mul_one _) hE'errR
    
    dsimp [η] at hdev₁ hdev₂
    nlinarith [hdpos,  abs_sub_le (ρ.real (E ∩  A ×ˢ B ))
                         (ρ.real E' * ρ.real (A ×ˢ B)) (ρ.real E * ρ.real (A ×ˢ B)) ]
  have hmeasure : ρ.restrict E =  ρ E  • ρ := by
    apply Measure.ext_prod
    intro A B hA hB
    rw [Measure.restrict_apply (hA.prod hB)]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top ρ _)
      (ENNReal.mul_ne_top (measure_ne_top ρ _) (measure_ne_top ρ _))).mp
    simpa [← Measure.real_def, Set.inter_comm] using
      hrectIndependent A B hA hB
  have hself := congrArg (fun m  => m.real E) hmeasure
  have hmul : ρ.real E = ρ.real E * ρ.real E := by
    simpa [Measure.real_def] using hself
  have hp : ρ.real E = 0 ∨ ρ.real E = 1 := by
    grind
  rcases hp with hp | hp
  · left
    exact (measureReal_eq_zero_iff).mp hp
  · right
    apply (measureReal_eq_zero_iff).mp
    have := measureReal_add_measureReal_compl (μ := ρ) hE
    simp only [probReal_univ] at this
    linarith

end
end PottsDiscontinuity.PottsThm
