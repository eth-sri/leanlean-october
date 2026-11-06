module

public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import PottsDiscontinuity.PottsThm.ColorNoiseMixing
public import Mathlib.Probability.Independence.ZeroOne

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open ProbabilityTheory MeasureTheory Filter Topology Set MeasurableSpace
open scoped symmDiff

noncomputable section

section
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
include Y
def measurableRectangles  :
    Set (Set (X × Y)) :=
  {R | ∃ A B, MeasurableSet A ∧ MeasurableSet B ∧ R = A ×ˢ B}

theorem measurableRectangles_isSetSemiring  : IsSetSemiring (measurableRectangles (X := X) (Y := Y)) := by
  constructor
  · refine ⟨∅, univ, MeasurableSet.empty, MeasurableSet.univ, ?_⟩
    simp
  · rintro R ⟨A, B, hA, hB, rfl⟩ S ⟨C, D, hC, hD, rfl⟩
    refine ⟨A ∩ C, B ∩ D, hA.inter hC, hB.inter hD, ?_⟩
    grind
  · rintro R ⟨A, B, hA, hB, rfl⟩ S ⟨C, D, hC, hD, rfl⟩
    let R₁ := (A \ C) ×ˢ B
    let R₂ := (A ∩ C) ×ˢ (B \ D)
    let K : Finset (Set (X × Y)) := insert R₁ {R₂}
    have memK_iff (T : Set (X × Y)) : T ∈ K ↔ T = R₁ ∨ T = R₂ := by
      grind
    have hK : (K : Set (Set (X × Y))) ⊆
        measurableRectangles := by
      intro T hT
      have hT' : T = R₁ ∨ T = R₂ := by simp_all
      rcases hT' with hT' | hT'
      · subst T
        exact ⟨A \ C, B, hA.inter hC.compl, hB, rfl⟩
      · subst T
        exact ⟨A ∩ C, B \ D, hA.inter hC, hB.inter hD.compl, rfl⟩
    have hdisj : PairwiseDisjoint (K : Set (Set (X × Y))) id := by
      intro T hT U hU hne
      grind
    have hdecomp : A ×ˢ B \ C ×ˢ D = ⋃₀ (K : Set (Set (X × Y))) := by
      ext z
      simp only [Set.mem_sdiff, Set.mem_prod, Set.mem_sUnion, K, R₁, R₂]
      constructor
      · by_cases hzC : z.1 ∈ C
        · simp_all
        simp_all
      grind
    grind

theorem measurableRectangles_generateFrom  :
    MeasurableSpace.generateFrom (measurableRectangles (X := X) (Y := Y)) =
      (inferInstance : MeasurableSpace (X × Y)) := by
  have hrect : measurableRectangles =
      image2 (· ×ˢ ·) {A : Set X | MeasurableSet A}
        {B : Set Y | MeasurableSet B} := by
    simp only [measurableRectangles]
    grind
  rw [hrect]
  exact generateFrom_prod

end

def productShift {Γ X Y : Type*} (T : Γ → X → X) (S : Γ → Y → Y)
    (a : Γ) : X × Y → X × Y := fun z => (T a z.1, S a z.2)

theorem prodMeasure_real_rectangle {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {A : Set X} {B : Set Y} :
    (μ.prod ν).real (A ×ˢ B) = μ.real A * ν.real B := by
  simp

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
      Tendsto (fun a => μ.real (A ∩ (T a) ⁻¹' B)) cofinite (𝓝 (μ.real A * μ.real B)))
    (hSmix : ∀ A B : Set Y, MeasurableSet A → MeasurableSet B →
      Tendsto (fun a => ν.real (A ∩ (S a) ⁻¹' B)) cofinite (𝓝 (ν.real A * ν.real B)))
    {E : Set (X × Y)} (hE : MeasurableSet E)
    (hEinv : ∀ a, (productShift T S a) ⁻¹' E = E) :
    (μ.prod ν) E = 0 ∨ (μ.prod ν) Eᶜ = 0 := by
  set ρ := μ.prod ν
  have hS := measurableRectangles_isSetSemiring (X := X) (Y := Y)
  have hQ (a : Γ) : MeasurePreserving (productShift T S a) ρ ρ := (hTpres a).prod (hSpres a)
  have hmix : ∀ F ∈ supClosure (measurableRectangles), ∀ A B, MeasurableSet A →
      MeasurableSet B → Tendsto (fun a => ρ.real (F ∩ productShift T S a ⁻¹' A ×ˢ B)) cofinite
        (𝓝 (ρ.real F * ρ.real (A ×ˢ B))) := by
    intro F hF A B hA hB
    obtain ⟨P, hP⟩ := hS.mem_supClosure_iff.mp hF
    have hm : ∀ U ∈ P.parts, MeasurableSet U := fun U hU => by
      obtain ⟨C, D, hC, hD, rfl⟩ := hP hU
      exact hC.prod hD
    have hF : ⋃ U ∈ P.parts, U = F := by simpa using P.sup_parts
    have key := tendsto_finsetSum (f := fun U a => ρ.real (U ∩ productShift T S a ⁻¹' A ×ˢ B))
      (a := fun U => ρ.real U * ρ.real (A ×ˢ B))
      P.parts fun U hU => by
        obtain ⟨C, D, hC, hD, rfl⟩ := hP hU
        have hset (a : Γ) : C ×ˢ D ∩ productShift T S a ⁻¹' A ×ˢ B =
            (C ∩ T a ⁻¹' A) ×ˢ (D ∩ S a ⁻¹' B) := by grind [productShift]
        simp only [hset, ρ, prodMeasure_real_rectangle]
        convert (hTmix C A hC hA).mul (hSmix D B hD hB) using 2
        ring
    rw [← Finset.sum_mul, ← measureReal_biUnion_finset (f := fun U => U) P.disjoint hm, hF] at key
    refine key.congr fun a => ?_
    conv_rhs => rw [← hF, iUnion₂_inter]
    exact Eq.symm (measureReal_biUnion_finset (P.disjoint.mono fun _ => inter_subset_left)
      fun U hU => (hm U hU).inter ((hQ a).measurable (hA.prod hB)))
  have hind : ∀ A B, MeasurableSet A → MeasurableSet B →
      ρ.real (E ∩ A ×ˢ B) = ρ.real E * ρ.real (A ×ˢ B) := by
    intro A B hA hB
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨F, hF, hFE⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring (μ := ρ) hS
      ⟨{univ}, countable_singleton _, by simpa using ⟨univ, univ, .univ, .univ, by simp⟩, by simp⟩
      measurableRectangles_generateFrom.symm hE (ENNReal.ofReal_pos.mpr (half_pos hε))
    have hFm : MeasurableSet F := by
      have := measurableSet_generateFrom_of_mem_supClosure hF
      rwa [measurableRectangles_generateFrom] at this
    have hG := hA.prod hB
    have h1 : dist (ρ.real (E ∩ A ×ˢ B)) (ρ.real F * ρ.real (A ×ˢ B)) ≤ ρ.real (E ∆ F) :=
      le_of_tendsto' (tendsto_const_nhds.dist (hmix F hF A B hA hB)) fun a => by
      rw [Real.dist_eq, ← (hQ a).measureReal_preimage (hE.inter hG).nullMeasurableSet, preimage_inter,
        hEinv]
      exact (abs_measureReal_sub_le_symmDiff ρ (hE.inter ((hQ a).measurable hG))
        (hFm.inter ((hQ a).measurable hG))).trans (measureReal_mono (by
          rw [← inter_symmDiff_distrib_right]; exact inter_subset_left))
    have h2 := abs_measureReal_sub_le_symmDiff ρ hFm hE
    have h3 : ρ.real (F ∆ E) < ε / 2 := ENNReal.toReal_lt_of_lt_ofReal hFE
    have h4 : ρ.real (A ×ˢ B) ≤ 1 := measureReal_le_one
    have h5 : 0 ≤ ρ.real (A ×ˢ B) := measureReal_nonneg
    rw [symmDiff_comm] at h1
    rw [Real.dist_eq, abs_le] at *
    constructor <;> nlinarith
  have hI : IndepSet E E ρ := (IndepSet_iff_Indep _ _ _).mpr <| indep_of_indep_of_le_right
    (IndepSets.indep (generateFrom_singleton_le hE) le_rfl (.singleton E) isPiSystem_prod rfl
      generateFrom_prod.symm <| (IndepSets_iff _ _ _).mpr <| by
        rintro _ _ rfl ⟨A, hA, B, hB, rfl⟩
        rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness), ENNReal.toReal_mul]
        exact hind A B hA hB) (generateFrom_singleton_le hE)
  exact (measure_eq_zero_or_one_of_indepSet_self hI).imp_right (prob_compl_eq_zero_iff hE).mpr

end
end PottsDiscontinuity.PottsThm
