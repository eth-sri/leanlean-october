module

public import proofs.RAFCriticalWindowQuantitative.BoundedRecords
public import proofs.RAFCriticalWindowQuantitative.FiniteRepair

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAF.Polymer RAF.Concrete MeasureTheory unitInterval
open scoped ENNReal

variable {g : List Bool × ℕ → List Bool × ℕ}

def escapedMissing (g : List Bool × ℕ → List Bool × ℕ) (B : ℕ) (v : List Bool) : Set SplitField :=
  {ω | (∃ w, B < w.length ∧ InfiniteReversibleGenerated 2 (fieldOf g ω) w) ∧
    ¬ FiniteReversibleGenerated B 2 (fieldOf g ω) v}

theorem finite_missing_determined (hg : PrefixIndex g) (B : ℕ) (v : List Bool) :
    SplitPrefixDetermined (splitPrefixCoordinates B)
      {ω | ¬ FiniteReversibleGenerated B 2 (fieldOf g ω) v} := by
  intro ω η he
  have ht (x y)
      (hxy : ∀ z ∈ splitPrefixCoordinates B, x z = y z)
      (h : FiniteReversibleGenerated B 2 (fieldOf g x) v) :
      FiniteReversibleGenerated B 2 (fieldOf g y) v :=
    finiteReversibleGenerated_transfer_prefix (M := B) le_rfl
      (fun w hw k hk => hxy _ $ (hg _ _).2 $ (mem_splitPrefixCoordinates _ _).mpr ⟨hw,hk⟩) h
  grind

theorem escape_mem_record_atoms {B : ℕ} (hB : 2 ≤ B) {ω : SplitField}
    (h : ∃ w, B < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w) :
    ω ∈ ⋃ i : RecordPrefixIndex, recordPrefixAtom B i := by
  have hex : ∃ M, B < M ∧ currySplitField ω ∈ reversibleRecordEvent 2 M := by
    obtain ⟨w,hw,_,hg⟩ := escape_has_bounded_record hB h
    tauto
  exact Set.mem_iUnion.mpr ⟨⟨_,fun z => ω z.val⟩,⟨(Nat.find_spec hex).1,(Nat.find_spec hex).2,
    fun k hk hkM => (Nat.find_min hex hkM ⟨hk, ·⟩)⟩,fun _ => rfl⟩

theorem first_record_cap {B M : ℕ} (hB : 2 ≤ B) {ω : SplitField}
    (h : currySplitField ω ∈ firstRecordEvent 2 B M) : M ≤ 2*B := by
  obtain ⟨_,⟨w,hw,hg⟩,h⟩ := h
  obtain ⟨v,hv,hvB,hvg⟩ := escape_has_bounded_record hB ⟨w,by omega,finiteReversibleGenerated_to_infinite hg⟩
  exact not_lt.1 fun hn => h v.length hv (by omega) ⟨v,rfl,hvg⟩

/-- The deterministic-cap contraction; no conditioning on future escape. -/
theorem escaped_missing_contraction (hg : PrefixIndex g) (a : I) (v : List Bool) (hv : 0 < v.length)
    (B : ℕ) (hB : 2 ≤ B) :
    infiniteSplitPi a (escapedMissing g (2*B+v.length) v) ≤
      infiniteSplitPi a (escapedMissing g B v) * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
  let C : Set SplitField := {ω | ¬ FiniteReversibleGenerated B 2 (fieldOf g ω) v}
  let D : RecordPrefixIndex → Set SplitField := fun i => C ∩ (· ∘ g) ⁻¹' recordPrefixAtom B i
  have hC := finite_missing_determined hg B v
  have hA i : SplitPrefixDetermined (splitPrefixCoordinates i.1)
      ((· ∘ g) ⁻¹' recordPrefixAtom B i) := fun ω η he =>
    recordPrefixAtom_determined B i _ _ fun z hz => he _ $ (hg _ _).2 hz
  have hmeas i : MeasurableSet (D i) :=
    (measurableSet_of_splitPrefixDetermined _ C hC).inter
      (measurableSet_of_splitPrefixDetermined _ _ $ hA i)
  have hdis : Pairwise (fun i j => Disjoint (D i) $ D j) := fun i j hij =>
    ((recordPrefixAtoms_disjoint B hij).preimage _).mono Set.inter_subset_right Set.inter_subset_right
  have hpiece i :
      infiniteSplitPi a (escapedMissing g (2*B+v.length) v ∩ D i) ≤
        infiniteSplitPi a (D i) * (1-(toNNReal a)^(v.length+1)) := by
    rcases (D i).eq_empty_or_nonempty with he | ⟨ω, hω⟩
    · simp_all
    obtain ⟨w,hw,hBw,hrecord⟩ := recordPrefixAtom_word B i ⟨_,hω.2⟩
    have hMB := first_record_cap hB hω.2.1
    obtain ⟨S, hsize, hband, hgen⟩ := append_trial_support (N := w.length+v.length) w v (by omega) le_rfl
    obtain ⟨q, -, hq, hp⟩ := source_append_split (N := w.length+v.length) w v (by omega) hv le_rfl
    have hlen : molLength (reactionProduct q) = w.length + v.length := by
      rw [← moleculeWord_length, hp, List.length_append]
    let T := (insert q S).image $ fun r => g $ literalSplitCoordinate r
    have hdis : Disjoint (splitPrefixCoordinates w.length) T := by
      refine Finset.disjoint_left.mpr fun z hz ht => ?_
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ht
      have hl := (mem_splitPrefixCoordinates _ _).mp $ (hg _ _).mp hz
      change (moleculeWord $ reactionProduct r).length ≤ w.length ∧ _ at hl
      rw [moleculeWord_length] at hl
      rcases Finset.mem_insert.1 hr with rfl | hr
      · omega
      have hb := (hband r hr).1
      omega
    refine (measure_mono (t := D i ∩ {ω | ¬ ∀ z ∈ T, ω z}) ?_).trans ?_
    · refine fun η hη => ⟨hη.2,fun hopen =>
        hη.1.2 $ finiteReversibleGenerated_mono_cap (show w.length+v.length ≤ _ by omega) ?_⟩
      obtain ⟨x,hx,he⟩ := finiteReversible_to_literalClosure
        (finiteReversibleGenerated_mono_cap (show w.length ≤ w.length+v.length by omega) $ hrecord _ hη.2.2)
      have hU : insert q S ⊆ restrictedSplitReactions _ (fieldOf g η) := fun r hr => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,hopen _ $ Finset.mem_image.mpr ⟨r,hr,rfl⟩⟩
      obtain ⟨y,hy,hey⟩ := hgen _ ((Finset.subset_insert _ _).trans hU) x hx he
      simpa only [hq] using literalClosure_to_finiteReversible _ _ (temporaryReactionClosure_cleavage _ q
        (hU $ Finset.mem_insert_self _ _) $ moleculeWord_injective (hp.trans hey.symm) ▸ hy).2
    rw [split_prefix_failure_measure a _ T hdis (D i) $ by
      rw [hw]
      exact fun η ξ he => and_congr (hC _ _ fun z hz => he z $ by simp at hz ⊢; omega) $ hA i η ξ he]
    exact mul_le_mul_right (tsub_le_tsub_left (pow_le_pow_of_le_one zero_le
      (by exact_mod_cast a.property.2) $ Finset.card_image_le.trans $ (Finset.card_insert_le _ _).trans $ by omega) 1) _
  calc
    _ ≤ ∑' i, infiniteSplitPi a (escapedMissing g (2*B+v.length) v ∩ D i) :=
      (measure_mono fun ω hω => by
        obtain ⟨w,hw,hg⟩ := hω.1
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp $ escape_mem_record_atoms (ω := ω ∘ g) hB ⟨w,by omega,hg⟩
        exact Set.mem_iUnion.mpr ⟨i,hω,fun h => hω.2 $ finiteReversibleGenerated_mono_cap (by omega) h,hi⟩).trans
        (measure_iUnion_le _)
    _ ≤ ∑' i, infiniteSplitPi a (D i) * _ := ENNReal.tsum_le_tsum hpiece
    _ = infiniteSplitPi a (⋃ i, D i) * _ := by rw [ENNReal.tsum_mul_right, measure_iUnion hdis hmeas]
    _ ≤ _ := mul_le_mul_left (measure_mono fun ω hω => by
      obtain ⟨i,hC,⟨hb,⟨w,hw,hg⟩,_⟩,_⟩ := Set.mem_iUnion.mp hω
      exact ⟨⟨w,by omega,finiteReversibleGenerated_to_infinite hg⟩,hC⟩) _

end RAFCriticalWindowQuantitative
