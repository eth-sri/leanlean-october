
import proofs.RAFCriticalWindowQuantitative.RecordContraction


namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold MeasureTheory unitInterval Classical RAF.Concrete

def recordCap (ell : ℕ) : ℕ → ℕ :=
  Nat.rec 2 (fun _ cap => 2*cap+ell)

theorem recordCap_ge_two (ell j : ℕ) : 2 ≤ recordCap ell j := by
  induction j <;> simp_all [recordCap]; omega



variable (f : PrefixIndex)

theorem escapedMissing_antitone (v : List Bool) : Antitone (fun B => escapedMissing f B v) := by
  intro B N hBN ω hω
  grind [escapedMissing, finiteReversibleGenerated_mono_cap]

variable (a : I)


theorem finite_seed_truncation (L r : ℕ) :
    infiniteSplitPi a {ω | ∃ w, recordCap L r < w.length ∧
      InfiniteReversibleGenerated 2 (indexedField f ω) w} ≤
    infiniteSplitPi a {ω | ∀ v ∈ actualBinaryWords L,
      InfiniteReversibleGenerated 2 (indexedField f ω) v} +
    (actualBinaryWords L).card * (1-(toNNReal a : ENNReal)^(L+1))^r := by
  apply (measure_le_inter_add_sdiff (infiniteSplitPi a) _
    {ω | ∀ v ∈ actualBinaryWords L,
      FiniteReversibleGenerated (recordCap L r) 2 (indexedField f ω) v}).trans
  apply add_le_add
  · exact measure_mono fun ω hω v hv => finiteReversibleGenerated_to_infinite (hω.2 v hv)
  · let seed := actualBinaryWords L
    
    calc
      _ ≤ infiniteSplitPi a (⋃ v ∈ seed, escapedMissing f (recordCap L r) v) := measure_mono (by
                                                                                               intro ω hω
                                                                                               simp_all [escapedMissing, seed])
      _ ≤ ∑ v ∈ seed, infiniteSplitPi a (escapedMissing f (recordCap L r) v) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _v ∈ seed, (1-(toNNReal a : ENNReal)^(L+1))^r := by
        apply Finset.sum_le_sum
        intro v hv
        obtain ⟨hv, hvL⟩ : 0 < v.length ∧ v.length ≤ L := by
          simpa [seed, mem_actualBinaryWords, List.length_pos_iff] using hv
        exact (((measure_mono (escapedMissing_antitone f v (((by induction r <;> simp [recordCap] at *; omega))))).trans
            (show infiniteSplitPi a (escapedMissing f (recordCap v.length r) v) ≤ (1-(toNNReal a : ENNReal)^(v.length+1))^r from by
          induction r with
          | zero => simpa using prob_le_one
          | succ r ih =>
            rw [pow_succ]
            refine le_trans ?_ (mul_le_mul' ih le_rfl)
            let B  := recordCap v.length r
            let hB : 2 ≤ recordCap v.length r := recordCap_ge_two _ _
            let z0 := 2*B+v.length
            let E := escapedMissing f z0 v
            let μ := infiniteSplitPi a
            let c : ENNReal := 1-toNNReal a^(v.length+1)
            let C  := {ω | ¬ FiniteReversibleGenerated B 2 (indexedField f ω) v}
            let D  := fun i => C ∩ indexedRecordAtom f B i
            change μ E ≤ _
            have hC : SplitPrefixDetermined (splitPrefixCoordinates B) C := by
              intro ω η he
              apply not_congr
              apply finiteReversibleGenerated_congr_prefix (M := B) le_rfl
              intro z hz
              exact he (f.index z) (f.preserves hz)
            have hmeasC := measurableSet_of_splitPrefixDetermined _ C hC
            have hmeas (i : RecordPrefixIndex)  :=
              hmeasC.inter (measurableSet_of_splitPrefixDetermined _ _ (indexedRecordAtom_determined f B i))
            
            have hpiece (i : RecordPrefixIndex) :
                μ (E ∩ D i) ≤
                  μ (D i) * c := by
              by_cases hn : (D i).Nonempty
              · obtain ⟨ω,hω⟩ := hn
            
                obtain ⟨w,hw,hg⟩ := hω.2.1.2.1
                have hBw : B < w.length := by simpa only [hw] using hω.2.1.1
                have hMB : i.fst ≤ 2 * recordCap v.length r := by
                  obtain ⟨v,hv,hvB,hvg⟩ := escape_has_bounded_record hB
                    ⟨w,by omega,finiteReversibleGenerated_to_infinite hg⟩
                  by_contra hn
                  exact hω.2.1.2.2 v.length hv (by omega) ⟨v,rfl,hvg⟩
                have hrecord (η : SplitField) (hη : η ∈ recordPrefixAtom B i) :
                    FiniteReversibleGenerated w.length 2 (currySplitField η) w := by
                  rw [hw]
                  apply (finiteReversibleGenerated_congr_prefix (M := i.1) le_rfl ?_).mp hg
                  intro z hz
                  exact (hω.2.2 ⟨z,hz⟩).trans (hη.2 ⟨z,hz⟩).symm

                apply (measure_mono (show _ ⊆
                  D i ∩ _
                  from fun η hη => ⟨hη.2,hη.1.2⟩)).trans
                have hdet : SplitPrefixDetermined (splitPrefixCoordinates w.length) (D i) := by
                  rw [hw]
                  intro η ξ he
                  apply and_congr
                  · apply hC
                    intro z hz
                    have hz' := (mem_splitPrefixCoordinates B z).mp hz
                    exact he z ((mem_splitPrefixCoordinates i.1 z).mpr ⟨by omega,by omega⟩)
                  · exact indexedRecordAtom_determined f B i η ξ he
                let n := w.length + v.length
                let U : Finset (List Bool × ℕ) := insert (w++v,w.length)
                  ((Finset.range v.length).image fun j => (w++v.take (j+1),w.length+j))
                let T := U.image f.index
                have hsize : T.card ≤ v.length+1 := calc
                  _ ≤ U.card := Finset.card_image_le
                  _ ≤ _+1 := Finset.card_insert_le _ _
                  _ ≤ v.length+1 := by
                    gcongr
                    exact Finset.card_image_le.trans (by simp)
                have hband (z) (hz : z ∈ U) : w.length < z.1.length ∧ z.1.length ≤ n := by
                  simp only [U, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hz
                  rcases hz with rfl | ⟨j,hj,rfl⟩ <;> simp <;> omega
                have hdis : Disjoint (splitPrefixCoordinates w.length) T := by
                  apply Finset.disjoint_left.mpr
                  intro z hz ht
                  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ht
                  have hl := (mem_splitPrefixCoordinates w.length _).mp hz
                  rw [f.product] at hl
                  exact (not_le_of_gt (hband r hr).1) hl.1
                have hs : (D i) ∩ {ω | ¬ FiniteReversibleGenerated z0 2 (indexedField f ω) v} ⊆
                    (D i) ∩ {ω | ¬ ∀ z ∈ T, ω z} := by
                  intro ω hω
                  refine ⟨hω.1, fun hopen => hω.2 ?_⟩
                  apply finiteReversibleGenerated_mono_cap (show n ≤ z0 by omega)
                  have hop (z) (hz : z ∈ U) : indexedField f ω z.1 z.2 :=
                    hopen _ (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
                  have hi : ∀ j, j ≤ v.length →
                      FiniteReversibleGenerated n 2 (indexedField f ω) (w++v.take j) := by
                    intro j
                    induction j with
                    | zero =>
                      intro _
                      simpa [indexedField] using finiteReversibleGenerated_mono_cap (show w.length ≤ n by omega)
                        (hrecord (ω ∘ f.index) hω.1.2)
                    | succ j ih =>
                      intro hj
                      have hjv : j < v.length := by omega
                      rw [← List.take_concat_get' v j hjv, ← List.append_assoc]
                      refine .ligate (ih (by omega)) (.food (by simp) (by simp) (by simp; omega)) ?_ ?_
                      · simpa [List.append_assoc, List.length_take, min_eq_left hjv.le,
                          List.take_concat_get' v j hjv] using hop (w++v.take (j+1),w.length+j)
                          (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr hjv,rfl⟩))
                      · simp
                        omega
                  have hp := hi v.length le_rfl
                  simp only [List.take_length] at hp
                  exact .right (List.length_pos_iff.mp (by omega)) (List.length_pos_iff.mp hv) hp
                    (hop _ (Finset.mem_insert_self _ _))

                apply (measure_mono hs).trans
                rw [split_prefix_failure_measure a _ T hdis (D i) hdet]
                exact mul_le_mul_right (tsub_le_tsub_left (by
                  apply pow_le_pow_of_le_one zero_le
                  · exact_mod_cast a.property.2
                  · exact hsize) 1) _
        
              · 
                simp [Set.not_nonempty_iff_eq_empty.mp hn]
            
            
            calc
              _ ≤ μ (⋃ i : RecordPrefixIndex, E ∩ D i) := measure_mono (by
                                                                                                                         intro ω hω
                                                                                                                         obtain ⟨w,hw,hg⟩ := hω.1
                                                                                                                         have hex : ∃ M, B < M ∧ indexedField f ω ∈ reversibleRecordEvent 2 M := by
                                                                                                                           obtain ⟨v,hv,_,hvg⟩ := escape_has_bounded_record hB ⟨w,by omega,hg⟩
                                                                                                                           exact ⟨v.length,hv,v,rfl,hvg⟩
                                                                                                                         refine Set.mem_iUnion.mpr ⟨⟨Nat.find hex,fun z => ω (f.index z.val)⟩,hω,?_,?_,fun _ => rfl⟩
                                                                                                                         · intro hgen
                                                                                                                           exact hω.2 (finiteReversibleGenerated_mono_cap (by omega) hgen)
                                                                                                                         · refine ⟨(Nat.find_spec hex).1,(Nat.find_spec hex).2,?_⟩
                                                                                                                           measurability)
              _ ≤ ∑' i : RecordPrefixIndex, μ (E ∩ D i) := measure_iUnion_le _
              _ ≤ ∑' i : RecordPrefixIndex, μ (D i) *
                  c := ENNReal.tsum_le_tsum hpiece
              _ = μ (⋃ i : RecordPrefixIndex, D i) *
                  c := by
                rw [ENNReal.tsum_mul_right,measure_iUnion (by
                                                            intro i j hij
                                                            exact (indexedRecordAtoms_disjoint f B hij).mono Set.inter_subset_right Set.inter_subset_right) hmeas]
              _ ≤ _ := mul_le_mul_left (measure_mono (by
                                                       intro ω hω
                                                       obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hω
                                                       obtain ⟨w,hw,hg⟩ := hi.2.1.2.1
                                                       exact ⟨⟨w,by have hb := hi.2.1.1; omega,finiteReversibleGenerated_to_infinite hg⟩,hi.1⟩)) _)).trans
              (pow_le_pow_left' (tsub_le_tsub_left (by
                                                     apply pow_le_pow_of_le_one zero_le
                                                     · exact_mod_cast a.property.2
                                                     · omega) 1) r))
      _ = _ := by simp [seed]

end RAFCriticalWindowQuantitative
