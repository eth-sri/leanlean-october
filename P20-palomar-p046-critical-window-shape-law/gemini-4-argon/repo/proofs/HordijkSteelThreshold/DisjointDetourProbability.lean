module

public import proofs.HordijkSteelThreshold.ColumnEventProduct

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory

variable {I R Ω : Type*} [Fintype R] [MeasurableSpace Ω] (μ : Measure Ω)
  [IsProbabilityMeasure μ] (field : R → Ω → Prop)

def detourFailed (B : Finset R) (ω : Ω) : Prop :=
  ¬ ∀ r ∈ B, field r ω

theorem measure_disjoint_detours_failed_le (hind : iIndepFun field μ)
    (hmeas : ∀ r, Measurable (field r)) (a : ENNReal) (ha : a ≤ 1)
    (hmarg : ∀ r, μ {ω | field r ω} = a) (support : I → Finset R) (T : Finset I)
    (hdis : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (support i) (support j))
    (hsize : ∀ i ∈ T, (support i).card ≤ 2) :
    μ {ω | ∀ i ∈ T, detourFailed field (support i) ω} ≤ (1 - a ^ 2) ^ T.card := by
  have hsingle (B : Finset R) : μ {ω | detourFailed field B ω} = 1 - a ^ B.card := by
    have he : {ω | ∀ r ∈ B, field r ω} = ⋂ r ∈ B, (field r) ⁻¹' {True} := by ext; simp
    have hm : MeasurableSet {ω | ∀ r ∈ B, field r ω} :=
      he ▸ MeasurableSet.biInter (Finset.countable_toSet B) fun r _ => (MeasurableSet.singleton True).preimage (hmeas r)
    change μ ({ω | ∀ r ∈ B, field r ω}ᶜ) = _
    rw [measure_compl hm (measure_ne_top _ _), measure_univ, he,
      hind.measure_inter_preimage_eq_mul B (fun _ _ => .singleton True)]
    simp only [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true, hmarg, Finset.prod_const]
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    have hBD : Disjoint (support i) (T.biUnion support) :=
      Finset.disjoint_left.mpr fun r hri hrD => by
        obtain ⟨j, hj, hrj⟩ := Finset.mem_biUnion.mp hrD
        exact Finset.disjoint_left.mp
          (hdis i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (by rintro rfl; exact hi hj)) hri hrj
    have hind' : IndepFun (detourFailed field (support i))
        (fun ω => ∀ j ∈ T, detourFailed field (support j) ω) μ :=
      (hind.indepFun_finset (support i) (T.biUnion support) hBD hmeas).comp
        (measurable_of_finite fun v : support i → Prop => ¬ ∀ r (hr : r ∈ support i), v ⟨r, hr⟩)
        (measurable_of_finite fun v : T.biUnion support → Prop => ∀ j (hj : j ∈ T),
          ¬ ∀ r (hr : r ∈ support j), v ⟨r, Finset.mem_biUnion.mpr ⟨j, hj, hr⟩⟩)
    have hp := hind'.measure_inter_preimage_eq_mul {True} {True} (.singleton True) (.singleton True)
    rw [show {ω | ∀ j ∈ insert i T, detourFailed field (support j) ω} =
      {ω | detourFailed field (support i) ω} ∩ {ω | ∀ j ∈ T, detourFailed field (support j) ω} by ext; simp]
    simp only [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true, hsingle] at hp
    rw [hp, Finset.card_insert_of_notMem hi, pow_succ']
    exact mul_le_mul'
      (tsub_le_tsub_left (pow_le_pow_of_le_one zero_le ha (hsize i (Finset.mem_insert_self _ _))) 1)
      (ih (fun j hj k hk => hdis j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
        fun j hj => hsize j (Finset.mem_insert_of_mem hj))

end HordijkSteelThreshold
