import proofs.HordijkSteelThreshold.RecordTargetTrial
import proofs.RAFCriticalWindowQuantitative.FiniteRepair


namespace RAFCriticalWindowQuantitative

open HordijkSteelThreshold

variable {L B : ℕ} (hLB : L ≤ B) {field : InfiniteSplitEnvironment}

include hLB in
theorem escape_has_bounded_record
    (h : ∃ w, B < w.length ∧ InfiniteReversibleGenerated L field w) :
    ∃ v, B < v.length ∧ v.length ≤ 2*B ∧
      FiniteReversibleGenerated v.length L field v := by
  by_contra! hn
  have finite {w} (h : InfiniteReversibleGenerated L field w) :
      FiniteReversibleGenerated B L field w := by
    induction h with
    | @ligate u v _ _ ho ihu ihv =>
      have huB := finiteReversibleGenerated_length_le ihu
      have hvB := finiteReversibleGenerated_length_le ihv
      by_cases hl : (u++v).length ≤ B
      · exact .ligate ihu ihv ho hl
      · have hb : B ≤ (u++v).length := by omega
        exact False.elim (hn (u++v) (by omega) (by simp; omega)
          (.ligate (finiteReversibleGenerated_mono_cap hb ihu)
            (finiteReversibleGenerated_mono_cap hb ihv) ho le_rfl))
    | _ => grind [FiniteReversibleGenerated]
  obtain ⟨w, hw, hg⟩ := h
  have := finiteReversibleGenerated_length_le (finite hg)
  omega

open Classical

variable (f : PrefixIndex) (B : ℕ)

def escapedMissing  (v : List Bool)  :=
  {ω | (∃ w, B < w.length ∧ InfiniteReversibleGenerated 2 (indexedField f ω) w) ∧
    ¬ FiniteReversibleGenerated B 2 (indexedField f ω) v}



def indexedRecordAtom  (i : RecordPrefixIndex)  :=
  {ω | ω ∘ f.index ∈ recordPrefixAtom B i}

theorem indexedRecordAtom_determined  (i : RecordPrefixIndex) :
    SplitPrefixDetermined (splitPrefixCoordinates i.1) (indexedRecordAtom f B i) := by
  intro ω η he
  exact recordPrefixAtom_determined B i _ _ fun z hz => he _ (f.preserves hz)

theorem indexedRecordAtoms_disjoint  {i j : RecordPrefixIndex} (hij : i ≠ j) :
    Disjoint (indexedRecordAtom f B i) (indexedRecordAtom f B j) :=
  (recordPrefixAtoms_disjoint B hij).preimage _

end RAFCriticalWindowQuantitative
