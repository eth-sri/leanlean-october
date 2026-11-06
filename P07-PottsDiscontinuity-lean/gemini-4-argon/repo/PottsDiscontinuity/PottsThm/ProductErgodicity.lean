module

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

theorem measurableRectangles_isSetSemiring {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] : IsSetSemiring (measurableRectangles (X := X) (Y := Y)) where
  empty_mem := ⟨∅, univ, MeasurableSet.empty, MeasurableSet.univ, by simp⟩
  inter_mem := by
    rintro _ ⟨A, B, hA, hB, rfl⟩ _ ⟨C, D, hC, hD, rfl⟩
    exact ⟨A ∩ C, B ∩ D, hA.inter hC, hB.inter hD, Set.prod_inter_prod⟩
  sdiff_eq_sUnion' := by
    classical
    rintro _ ⟨A, B, hA, hB, rfl⟩ _ ⟨C, D, hC, hD, rfl⟩
    let R₁ : Set (X × Y) := (A \ C) ×ˢ B
    let R₂ : Set (X × Y) := (A ∩ C) ×ˢ (B \ D)
    refine ⟨{R₁, R₂}, ?_, ?_, ?_⟩
    · intro T hT
      rcases Finset.mem_insert.mp hT with rfl | hT
      · exact ⟨A \ C, B, hA.diff hC, hB, rfl⟩
      · rw [Finset.mem_singleton.mp hT]
        exact ⟨A ∩ C, B \ D, hA.inter hC, hB.diff hD, rfl⟩
    · intro T hT U hU hne
      rcases Finset.mem_insert.mp hT with rfl | hT <;>
        rcases Finset.mem_insert.mp hU with rfl | hU
      · exact (hne rfl).elim
      · rw [Finset.mem_singleton.mp hU]
        exact Set.disjoint_left.mpr fun z hz₁ hz₂ => hz₁.1.2 hz₂.1.2
      · rw [Finset.mem_singleton.mp hT]
        exact Set.disjoint_left.mpr fun z hz₁ hz₂ => hz₂.1.2 hz₁.1.2
      · rw [Finset.mem_singleton.mp hT, Finset.mem_singleton.mp hU] at hne
        exact (hne rfl).elim
    · ext z
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.sUnion_insert,
        Set.sUnion_singleton, Set.mem_sdiff, Set.mem_prod, Set.mem_union,
        Set.mem_inter_iff, R₁, R₂]
      by_cases hzC : z.1 ∈ C <;> tauto

theorem measurableRectangles_generateFrom {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] :
    MeasurableSpace.generateFrom (measurableRectangles (X := X) (Y := Y)) =
      (inferInstance : MeasurableSpace (X × Y)) := by
  rw [show measurableRectangles (X := X) (Y := Y) =
      image2 (· ×ˢ ·) {A : Set X | MeasurableSet A} {B : Set Y | MeasurableSet B} by
    ext R; simp only [measurableRectangles, Set.mem_ofPred_eq, Set.mem_image2]; aesop]
  exact generateFrom_prod

theorem measurableRectangleRing_generateFrom {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] :
    MeasurableSpace.generateFrom
        (supClosure (measurableRectangles (X := X) (Y := Y))) =
      (inferInstance : MeasurableSpace (X × Y)) := by
  rw [← measurableRectangles_generateFrom (X := X) (Y := Y)]
  exact le_antisymm
    (generateFrom_le fun _ => measurableSet_generateFrom_of_mem_supClosure)
    (generateFrom_le fun _ hR => measurableSet_generateFrom (subset_supClosure hR))

def productShift {Γ X Y : Type*} (T : Γ → X → X) (S : Γ → Y → Y)
    (a : Γ) : X × Y → X × Y := fun z => (T a z.1, S a z.2)

private theorem prodMeasure_real_rectangle {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {A : Set X} {B : Set Y} :
    (μ.prod ν).real (A ×ˢ B) = μ.real A * ν.real B := by
  simp only [Measure.real_def, Measure.prod_prod, ENNReal.toReal_mul]

private theorem finpartition_rect_measure_inter {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (ρ : Measure (X × Y)) [IsFiniteMeasure ρ]
    {E' : Set (X × Y)} (P : Finpartition E')
    (hPrect : (P.parts : Set (Set (X × Y))) ⊆ measurableRectangles (X := X) (Y := Y)) :
    MeasurableSet E' ∧ ∀ S, MeasurableSet S →
      ρ.real (E' ∩ S) = ∑ U ∈ P.parts, ρ.real (U ∩ S) := by
  have hEparts : E' = ⋃ U ∈ P.parts, U :=
    P.sup_parts.symm.trans ((Finset.sup_id_set_eq_sUnion P.parts).trans (by ext; simp))
  have hRmeas (U : Set (X × Y)) (hU : U ∈ P.parts) : MeasurableSet U := by
    obtain ⟨C, D, hC, hD, rfl⟩ := hPrect hU; exact hC.prod hD
  refine ⟨hEparts.symm ▸ P.parts.measurableSet_biUnion hRmeas, fun S hS => ?_⟩
  have h1 : E' ∩ S = ⋃ U ∈ P.parts, (U ∩ S) :=
    (congrArg (· ∩ S) hEparts).trans (by ext; simp; aesop)
  exact (congrArg ρ.real h1).trans (measureReal_biUnion_finset
    (fun U hU V hV hne => (P.disjoint hU hV hne).mono inter_subset_left inter_subset_left)
    (fun U hU => (hRmeas U hU).inter hS))

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
  classical
  let ρ : Measure (X × Y) := μ.prod ν
  have : IsProbabilityMeasure ρ := inferInstanceAs (IsProbabilityMeasure (μ.prod ν))
  have hprodPres (a : Γ) : MeasurePreserving (productShift T S a) ρ ρ :=
    (hTpres a).prod (hSpres a)
  let R : Set (Set (X × Y)) := supClosure (measurableRectangles (X := X) (Y := Y))
  have hRring : IsSetRing R :=
    (measurableRectangles_isSetSemiring (X := X) (Y := Y)).isSetRing_supClosure
  have hRcover : ∃ D : Set (Set (X × Y)), D.Countable ∧ D ⊆ R ∧ ρ (⋃₀ D)ᶜ = 0 :=
    ⟨{univ}, Set.countable_singleton _, fun _ hU => by
      rw [Set.mem_singleton_iff.mp hU]
      exact subset_supClosure ⟨univ, univ, MeasurableSet.univ, MeasurableSet.univ, by simp⟩,
      by simp [ρ]⟩
  have happrox (η : ℝ) (hη : 0 < η) :
      ∃ (E' : Set (X × Y)) (P : Finpartition E'),
        (P.parts : Set (Set (X × Y))) ⊆ measurableRectangles (X := X) (Y := Y) ∧
        ρ.real (E' ∆ E) < η := by
    obtain ⟨E', hE'R, hE'err⟩ :=
      exists_measure_symmDiff_lt_of_generateFrom_isSetRing hRring hRcover
        (measurableRectangleRing_generateFrom (X := X) (Y := Y)).symm hE
        (ENNReal.ofReal_pos.mpr hη)
    obtain ⟨P, hPrect⟩ :=
      (measurableRectangles_isSetSemiring (X := X) (Y := Y)).mem_supClosure_iff.mp hE'R
    refine ⟨E', P, hPrect, ?_⟩
    simpa [ρ, Measure.real_def, ENNReal.toReal_ofReal hη.le] using
      (ENNReal.toReal_lt_toReal (measure_ne_top ρ _) ENNReal.ofReal_ne_top).mpr hE'err
  have hfiniteApproxIndep (E' : Set (X × Y)) (P : Finpartition E')
      (hPrect : (P.parts : Set (Set (X × Y))) ⊆ measurableRectangles (X := X) (Y := Y))
      (A : Set X) (B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      |ρ.real (E ∩ (A ×ˢ B)) - ρ.real E' * ρ.real (A ×ˢ B)| ≤ ρ.real (E' ∆ E) := by
    let Q : Γ → X × Y → X × Y := productShift T S
    have htargetMeas : MeasurableSet (A ×ˢ B) := hA.prod hB
    obtain ⟨hE'meas, hE'inter⟩ := finpartition_rect_measure_inter ρ P hPrect
    have hE'measure : ρ.real E' = ∑ U ∈ P.parts, ρ.real U := by
      simpa using hE'inter univ MeasurableSet.univ
    have hpieceTerm (U : Set (X × Y)) (hU : U ∈ P.parts) :
        Tendsto (fun a => ρ.real (U ∩ (Q a) ⁻¹' (A ×ˢ B))) cofinite
          (𝓝 (ρ.real U * ρ.real (A ×ˢ B))) := by
      obtain ⟨C, D, hC, hD, rfl⟩ := hPrect hU
      have hset (a : Γ) : (C ×ˢ D) ∩ (Q a) ⁻¹' (A ×ˢ B) =
          (C ∩ (T a) ⁻¹' A) ×ˢ (D ∩ (S a) ⁻¹' B) := by
        ext z; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Q, productShift]; tauto
      convert (hTmix C A hC hA).mul (hSmix D B hD hB) using 1
      · funext a; rw [hset, prodMeasure_real_rectangle]
      · rw [prodMeasure_real_rectangle, prodMeasure_real_rectangle]; ring_nf
    have hjointLimit : Tendsto (fun a : Γ =>
        ρ.real (E' ∩ (Q a) ⁻¹' (A ×ˢ B))) cofinite
        (𝓝 (ρ.real E' * ρ.real (A ×ˢ B))) := by
      have hsumLimit := tendsto_finsetSum P.parts hpieceTerm
      rw [← Finset.sum_mul, ← hE'measure] at hsumLimit
      exact hsumLimit.congr' (Eventually.of_forall fun a =>
        (hE'inter _ ((hprodPres a).measurable htargetMeas)).symm)
    have hchangeRect (a : Γ) : |ρ.real (E ∩ (A ×ˢ B)) -
        ρ.real (E' ∩ (Q a) ⁻¹' (A ×ˢ B))| ≤ ρ.real (E' ∆ E) := by
      have hpre : (Q a) ⁻¹' (E ∩ (A ×ˢ B)) = E ∩ (Q a) ⁻¹' (A ×ˢ B) := by
        rw [Set.preimage_inter, hEinv a]
      have hconst : ρ.real (E ∩ (Q a) ⁻¹' (A ×ˢ B)) = ρ.real (E ∩ (A ×ˢ B)) := by
        rw [← hpre]; simp only [Measure.real_def]
        rw [← Measure.map_apply (hprodPres a).measurable (hE.inter htargetMeas),
          (hprodPres a).map_eq]
      rw [← hconst, symmDiff_comm]
      exact (abs_measureReal_sub_le_symmDiff ρ
        (hE.inter ((hprodPres a).measurable htargetMeas))
        (hE'meas.inter ((hprodPres a).measurable htargetMeas))).trans
        (measureReal_mono fun z hz => by
          simp only [Set.mem_symmDiff, Set.mem_inter_iff] at hz ⊢; tauto)
    by_contra hnot
    have hη : 0 < (|ρ.real (E ∩ (A ×ˢ B)) - ρ.real E' * ρ.real (A ×ˢ B)| -
        ρ.real (E' ∆ E)) / 2 := by linarith
    obtain ⟨a, ha⟩ := (Metric.tendsto_nhds.mp hjointLimit _ hη).exists
    rw [Real.dist_eq] at ha
    have htri := abs_sub_le (ρ.real (E ∩ (A ×ˢ B)))
      (ρ.real (E' ∩ (Q a) ⁻¹' (A ×ˢ B))) (ρ.real E' * ρ.real (A ×ˢ B))
    linarith [hchangeRect a]
  have hrectIndependent (A : Set X) (B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      ρ.real (E ∩ (A ×ˢ B)) = ρ.real E * ρ.real (A ×ˢ B) := by
    by_contra hne
    have hdpos : 0 < |ρ.real (E ∩ (A ×ˢ B)) - ρ.real E * ρ.real (A ×ˢ B)| :=
      abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨E', P, hPrect, hE'errR⟩ := happrox (|ρ.real (E ∩ (A ×ˢ B)) - ρ.real E * ρ.real (A ×ˢ B)| / 2)
      (by linarith)
    have hbound := hfiniteApproxIndep E' P hPrect A B hA hB
    have hE'meas := (finpartition_rect_measure_inter ρ P hPrect).1
    have hmass : |ρ.real E' - ρ.real E| ≤ ρ.real (E' ∆ E) :=
      abs_measureReal_sub_le_symmDiff ρ hE'meas hE
    have hprodDiff : |ρ.real E' * ρ.real (A ×ˢ B) - ρ.real E * ρ.real (A ×ˢ B)| ≤
        ρ.real (E' ∆ E) := by
      rw [← sub_mul, abs_mul, abs_of_nonneg measureReal_nonneg]
      exact (mul_le_mul hmass measureReal_le_one measureReal_nonneg measureReal_nonneg).trans_eq
        (mul_one _)
    have htri := abs_sub_le (ρ.real (E ∩ (A ×ˢ B)))
      (ρ.real E' * ρ.real (A ×ˢ B)) (ρ.real E * ρ.real (A ×ˢ B))
    linarith
  let p : ℝ := ρ.real E
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := measureReal_le_one
  by_cases hp : p = 0
  · exact Or.inl ((ENNReal.toReal_eq_zero_iff (ρ E)).mp hp |>.resolve_right (measure_ne_top ρ E))
  · by_cases hp' : p = 1
    · right
      have hcompl : ρ.real Eᶜ = 0 := by
        have hadd := measureReal_add_measureReal_compl (μ := ρ) hE
        have huniv : ρ.real univ = 1 := by simp
        dsimp [p] at hp'
        linarith
      exact (ENNReal.toReal_eq_zero_iff (ρ Eᶜ)).mp hcompl |>.resolve_right (measure_ne_top ρ Eᶜ)
    · let gap : ℝ := p * (1 - p)
      have hgap : 0 < gap := mul_pos (lt_of_le_of_ne hp0 (Ne.symm hp)) (by linarith [lt_of_le_of_ne hp1 hp'])
      obtain ⟨E₀, P₀, hP₀rect, hE₀errR⟩ := happrox (gap / 4) (by positivity)
      obtain ⟨hE₀measSet, hE₀inter⟩ := finpartition_rect_measure_inter ρ P₀ hP₀rect
      have hE₀sum : ρ.real E₀ = ∑ U ∈ P₀.parts, ρ.real U := by
        simpa using hE₀inter univ MeasurableSet.univ
      have hindsum : ρ.real (E ∩ E₀) = p * ρ.real E₀ := by
        rw [inter_comm, hE₀inter E hE, hE₀sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun U hU => ?_
        obtain ⟨A, B, hA, hB, rfl⟩ := hP₀rect hU
        rw [inter_comm]; exact hrectIndependent A B hA hB
      have hfirst : |p - ρ.real (E ∩ E₀)| ≤ ρ.real (E₀ ∆ E) := by
        rw [abs_sub_comm]
        exact (abs_measureReal_sub_le_symmDiff ρ (hE.inter hE₀measSet) hE).trans
          (measureReal_mono fun z hz => by
            simp only [Set.mem_symmDiff, Set.mem_inter_iff] at hz ⊢; tauto)
      have hsecond : |p * ρ.real E₀ - p * p| ≤ ρ.real (E₀ ∆ E) := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hp0]
        exact (mul_le_mul hp1 (abs_measureReal_sub_le_symmDiff ρ hE₀measSet hE)
          (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      have htri := abs_sub_le p (ρ.real (E ∩ E₀)) (p * p)
      have hgapAbs : |p - p * p| = gap := by
        rw [show p - p * p = gap by dsimp [gap]; ring, abs_of_pos hgap]
      rw [hgapAbs, hindsum] at htri
      rw [hindsum] at hfirst
      linarith

end
end PottsDiscontinuity.PottsThm
