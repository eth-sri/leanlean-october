module

public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import PottsDiscontinuity.PottsThm.ColorNoiseMixing

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Topology Set MeasurableSpace
open scoped symmDiff

noncomputable section

private def measurableRectangles {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] :
    Set (Set (X × Y)) :=
  {R | ∃ A B, MeasurableSet A ∧ MeasurableSet B ∧ R = A ×ˢ B}

private theorem measurableRectangles_isSetSemiring {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] : IsSetSemiring (measurableRectangles (X := X) (Y := Y)) := by
  classical
  refine ⟨⟨∅, univ, .empty, .univ, by simp⟩, ?_, ?_⟩
  · rintro _ ⟨A, B, hA, hB, rfl⟩ _ ⟨C, D, hC, hD, rfl⟩
    exact ⟨A ∩ C, B ∩ D, hA.inter hC, hB.inter hD, by ext; simp [Set.mem_prod]; tauto⟩
  · rintro _ ⟨A, B, hA, hB, rfl⟩ _ ⟨C, D, hC, hD, rfl⟩
    let R₁ : Set (X × Y) := (A \ C) ×ˢ B
    let R₂ : Set (X × Y) := (A ∩ C) ×ˢ (B \ D)
    refine ⟨{R₁, R₂}, fun T hT => ?_, fun T hT U hU hne => ?_, ?_⟩
    · rcases Finset.mem_insert.mp hT with rfl | hT2
      · exact ⟨A \ C, B, hA.diff hC, hB, rfl⟩
      · rw [Finset.mem_singleton.mp hT2]; exact ⟨A ∩ C, B \ D, hA.inter hC, hB.diff hD, rfl⟩
    · have h12 : Disjoint R₁ R₂ := Set.disjoint_left.mpr fun _ h1 h2 => h1.1.2 h2.1.2
      rcases Finset.mem_insert.mp hT with rfl | hT2 <;> rcases Finset.mem_insert.mp hU with rfl | hU2
      · exact (hne rfl).elim
      · rw [Finset.mem_singleton.mp hU2]; exact h12
      · rw [Finset.mem_singleton.mp hT2]; exact h12.symm
      · rw [Finset.mem_singleton.mp hT2, Finset.mem_singleton.mp hU2] at hne; exact (hne rfl).elim
    · ext ⟨x, y⟩; simp only [Finset.coe_insert, Finset.coe_singleton, Set.sUnion_insert, Set.sUnion_singleton,
        Set.mem_sdiff, Set.mem_prod, Set.mem_union, Set.mem_inter_iff, R₁, R₂]
      by_cases hx : x ∈ C <;> tauto

def productShift {Γ X Y : Type*} (T : Γ → X → X) (S : Γ → Y → Y)
    (a : Γ) : X × Y → X × Y := fun z => (T a z.1, S a z.2)

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
  classical
  let ρ : Measure (X × Y) := μ.prod ν
  have : IsProbabilityMeasure ρ := inferInstanceAs (IsProbabilityMeasure (μ.prod ν))
  have hprodPres (a : Γ) : MeasurePreserving (productShift T S a) ρ ρ := (hTpres a).prod (hSpres a)
  let R := supClosure (measurableRectangles (X := X) (Y := Y))
  have hRring : IsSetRing R := measurableRectangles_isSetSemiring.isSetRing_supClosure
  have hRgen : MeasurableSpace.generateFrom R = (inferInstance : MeasurableSpace (X × Y)) := by
    have hrect : measurableRectangles (X := X) (Y := Y) = image2 (· ×ˢ ·) {A | MeasurableSet A} {B | MeasurableSet B} := by
      ext; simp only [measurableRectangles, Set.mem_ofPred_eq, Set.mem_image2]; aesop
    rw [← generateFrom_prod, ← hrect]
    exact le_antisymm (generateFrom_le fun _ h => measurableSet_generateFrom_of_mem_supClosure h)
      (generateFrom_le fun _ h => measurableSet_generateFrom (subset_supClosure h))
  have hRcover : ∃ D : Set (Set (X × Y)), D.Countable ∧ D ⊆ R ∧ ρ (⋃₀ D)ᶜ = 0 :=
    ⟨{univ}, countable_singleton _, singleton_subset_iff.mpr (subset_supClosure ⟨univ, univ, .univ, .univ, by simp⟩), by simp [ρ]⟩
  have hpart_props {E' : Set (X × Y)} (P : Finpartition E')
      (hP : (P.parts : Set (Set (X × Y))) ⊆ measurableRectangles (X := X) (Y := Y)) :
      MeasurableSet E' ∧ ∀ {S : Set (X × Y)}, MeasurableSet S → ρ.real (E' ∩ S) = ∑ U ∈ P.parts, ρ.real (U ∩ S) := by
    have heq : E' = ⋃ U ∈ P.parts, U := by
      simpa [Finset.sup_id_set_eq_sUnion] using P.sup_parts.symm
    have hm (U) (hU : U ∈ P.parts) : MeasurableSet U := by obtain ⟨C, D, hC, hD, rfl⟩ := hP hU; exact hC.prod hD
    refine ⟨heq ▸ P.parts.measurableSet_biUnion hm, fun {S} hS => ?_⟩
    have hi : E' ∩ S = ⋃ U ∈ P.parts, U ∩ S := by
      ext z; simp only [Set.mem_inter_iff, Set.mem_iUnion]
      exact ⟨fun ⟨hz, hS⟩ => by obtain ⟨U, hU, hzU⟩ := Set.mem_iUnion₂.mp (heq ▸ hz); exact ⟨U, hU, hzU, hS⟩,
        fun ⟨U, hU, hzU, hS⟩ => ⟨heq.symm ▸ Set.mem_iUnion₂.mpr ⟨U, hU, hzU⟩, hS⟩⟩
    rw [hi]
    exact measureReal_biUnion_finset (fun U hU V hV hne => (P.disjoint hU hV hne).mono inter_subset_left inter_subset_left)
      fun U hU => (hm U hU).inter hS
  have hrectIndep (A : Set X) (B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      ρ.real (E ∩ (A ×ˢ B)) = ρ.real E * ρ.real (A ×ˢ B) := by
    by_contra hne
    let η := |ρ.real (E ∩ (A ×ˢ B)) - ρ.real E * ρ.real (A ×ˢ B)| / 2
    have hη : 0 < η := half_pos (abs_pos.mpr (sub_ne_zero.mpr hne))
    obtain ⟨E', hE'R, hE'err⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing hRring hRcover hRgen.symm hE (ENNReal.ofReal_pos.mpr hη)
    have hE'lt : ρ.real (E' ∆ E) < η := by
      simpa [Measure.real_def, ENNReal.toReal_ofReal hη.le] using (ENNReal.toReal_lt_toReal (measure_ne_top ρ _) ENNReal.ofReal_ne_top).mpr hE'err
    obtain ⟨P, hPrect⟩ := measurableRectangles_isSetSemiring.mem_supClosure_iff.mp hE'R
    obtain ⟨hE'm, hPsum⟩ := hpart_props P hPrect
    let Q := productShift T S
    have hAB : MeasurableSet (A ×ˢ B) := hA.prod hB
    have hpiece (U) (hU : U ∈ P.parts) : Tendsto (fun a => ρ.real (U ∩ Q a ⁻¹' (A ×ˢ B))) cofinite (𝓝 (ρ.real U * ρ.real (A ×ˢ B))) := by
      obtain ⟨C, D, hC, hD, rfl⟩ := hPrect hU
      have h1 (a : Γ) : ρ.real ((C ×ˢ D) ∩ Q a ⁻¹' (A ×ˢ B)) = μ.real (C ∩ T a ⁻¹' A) * ν.real (D ∩ S a ⁻¹' B) := by
        rw [show (C ×ˢ D) ∩ Q a ⁻¹' (A ×ˢ B) = (C ∩ T a ⁻¹' A) ×ˢ (D ∩ S a ⁻¹' B) by
          ext; simp [Set.mem_prod, Q, productShift]; tauto]
        simp [ρ, Measure.real_def, Measure.prod_prod, ENNReal.toReal_mul]
      have h2 : (μ.real C * μ.real A) * (ν.real D * ν.real B) = ρ.real (C ×ˢ D) * ρ.real (A ×ˢ B) := by
        simp only [ρ, Measure.real_def, Measure.prod_prod, ENNReal.toReal_mul]; ring
      simpa [h1, h2] using (hTmix C A hC hA).mul (hSmix D B hD hB)
    have hjLim : Tendsto (fun a => ρ.real (E' ∩ Q a ⁻¹' (A ×ˢ B))) cofinite (𝓝 (ρ.real E' * ρ.real (A ×ˢ B))) := by
      have hs := tendsto_finsetSum P.parts hpiece
      have hEm : ρ.real E' = ∑ U ∈ P.parts, ρ.real U := by simpa using hPsum .univ
      rw [← Finset.sum_mul, ← hEm] at hs
      exact hs.congr fun a => (hPsum ((hprodPres a).measurable hAB)).symm
    have hfinBdd : |ρ.real (E ∩ (A ×ˢ B)) - ρ.real E' * ρ.real (A ×ˢ B)| ≤ ρ.real (E' ∆ E) := by
      by_contra hnot
      let δ := (|ρ.real (E ∩ (A ×ˢ B)) - ρ.real E' * ρ.real (A ×ˢ B)| - ρ.real (E' ∆ E)) / 2
      obtain ⟨a, ha⟩ := (Metric.tendsto_nhds.mp hjLim δ (by dsimp [δ]; linarith)).exists
      rw [Real.dist_eq] at ha
      have hconst : ρ.real (E ∩ Q a ⁻¹' (A ×ˢ B)) = ρ.real (E ∩ (A ×ˢ B)) := by
        have hpre : Q a ⁻¹' (E ∩ (A ×ˢ B)) = E ∩ Q a ⁻¹' (A ×ˢ B) := by rw [Set.preimage_inter, hEinv a]
        rw [← hpre]; simp only [Measure.real_def]
        rw [← Measure.map_apply (hprodPres a).measurable (hE.inter hAB), (hprodPres a).map_eq]
      have hchg : |ρ.real (E ∩ Q a ⁻¹' (A ×ˢ B)) - ρ.real (E' ∩ Q a ⁻¹' (A ×ˢ B))| ≤ ρ.real (E' ∆ E) :=
        (abs_measureReal_sub_le_symmDiff ρ (hE.inter ((hprodPres a).measurable hAB))
          (hE'm.inter ((hprodPres a).measurable hAB))).trans
          ((measureReal_mono fun z hz => by simp only [Set.mem_symmDiff, Set.mem_inter_iff] at hz ⊢; tauto).trans_eq
            (congrArg ρ.real (symmDiff_comm _ _)))
      rw [hconst] at hchg
      have htri := abs_sub_le (ρ.real (E ∩ (A ×ˢ B))) (ρ.real (E' ∩ Q a ⁻¹' (A ×ˢ B))) (ρ.real E' * ρ.real (A ×ˢ B))
      dsimp [δ] at ha; linarith
    have hprodDiff : |ρ.real E' * ρ.real (A ×ˢ B) - ρ.real E * ρ.real (A ×ˢ B)| ≤ ρ.real (E' ∆ E) := by
      rw [← sub_mul, abs_mul, abs_of_nonneg measureReal_nonneg]
      exact (mul_le_mul (abs_measureReal_sub_le_symmDiff ρ hE'm hE) measureReal_le_one measureReal_nonneg measureReal_nonneg).trans_eq (mul_one _)
    have htri := abs_sub_le (ρ.real (E ∩ (A ×ˢ B))) (ρ.real E' * ρ.real (A ×ˢ B)) (ρ.real E * ρ.real (A ×ˢ B))
    dsimp [η] at hE'lt; linarith
  let p := ρ.real E
  by_cases hp0 : p = 0
  · exact .inl ((ENNReal.toReal_eq_zero_iff _).mp hp0 |>.resolve_right (measure_ne_top ρ E))
  by_cases hp1 : p = 1
  · right
    have hc : ρ.real Eᶜ = 0 := by
      have := measureReal_add_measureReal_compl (μ := ρ) hE; simp [p, hp1] at this; linarith
    exact (ENNReal.toReal_eq_zero_iff _).mp hc |>.resolve_right (measure_ne_top ρ Eᶜ)
  exfalso
  have hp_pos : 0 < p := lt_of_le_of_ne measureReal_nonneg (Ne.symm hp0)
  have hp_lt1 : p < 1 := lt_of_le_of_ne measureReal_le_one hp1
  let gap := p * (1 - p)
  have hgap : 0 < gap := mul_pos hp_pos (by linarith)
  let δ₀ := gap / 4; have hδ₀ : 0 < δ₀ := by positivity
  obtain ⟨E₀, hE₀R, hE₀err⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing hRring hRcover hRgen.symm hE (ENNReal.ofReal_pos.mpr hδ₀)
  have hE₀lt : ρ.real (E₀ ∆ E) < δ₀ := by
    simpa [Measure.real_def, ENNReal.toReal_ofReal hδ₀.le] using (ENNReal.toReal_lt_toReal (measure_ne_top ρ _) ENNReal.ofReal_ne_top).mpr hE₀err
  obtain ⟨P₀, hP₀rect⟩ := measurableRectangles_isSetSemiring.mem_supClosure_iff.mp hE₀R
  obtain ⟨hE₀m, hP₀sum⟩ := hpart_props P₀ hP₀rect
  have hindsum : ρ.real (E ∩ E₀) = p * ρ.real E₀ := by
    rw [Set.inter_comm, hP₀sum hE, show ρ.real E₀ = ∑ U ∈ P₀.parts, ρ.real U by simpa using hP₀sum .univ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun U hU => ?_
    obtain ⟨A, B, hA, hB, rfl⟩ := hP₀rect hU
    rw [Set.inter_comm]; exact hrectIndep A B hA hB
  have h1 : |p - ρ.real (E ∩ E₀)| ≤ ρ.real (E₀ ∆ E) := by
    rw [abs_sub_comm]
    exact (abs_measureReal_sub_le_symmDiff ρ (hE.inter hE₀m) hE).trans
      (measureReal_mono fun z hz => by simp only [Set.mem_symmDiff, Set.mem_inter_iff] at hz ⊢; tauto)
  have h2 : |p * ρ.real E₀ - p * p| ≤ ρ.real (E₀ ∆ E) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hp_pos.le]
    exact (mul_le_mul hp_lt1.le (abs_measureReal_sub_le_symmDiff ρ hE₀m hE) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have htri := abs_sub_le p (ρ.real (E ∩ E₀)) (p * p)
  rw [hindsum, show |p - p * p| = gap from (abs_of_nonneg (by nlinarith)).trans (by dsimp [gap]; ring)] at htri
  rw [hindsum] at h1
  dsimp [δ₀] at hE₀lt; linarith

end
end PottsDiscontinuity.PottsThm
