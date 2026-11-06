module

public import proofs.RAFCriticalWindowQuantitative.RecordContraction

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAF.Polymer RAF.Concrete MeasureTheory unitInterval
open scoped ENNReal

def recordCap (ell : ℕ) : ℕ → ℕ :=
  Nat.rec 2 (fun _ cap => 2*cap+ell)

theorem recordCap_ge_two (ell j : ℕ) : 2 ≤ recordCap ell j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [recordCap] at *; omega

theorem recordCap_mono_length {ell L : ℕ} (h : ell ≤ L) (j : ℕ) :
    recordCap ell j ≤ recordCap L j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [recordCap] at *; omega

def idxField (idx : List Bool × ℕ → List Bool × ℕ) (ω : SplitField) : InfiniteSplitEnvironment :=
  fun w k => ω (idx (w, k))

def idxEscapedMissing (idx : List Bool × ℕ → List Bool × ℕ) (B : ℕ) (v : List Bool) : Set SplitField :=
  {ω | (∃ w, B < w.length ∧ InfiniteReversibleGenerated 2 (idxField idx ω) w) ∧
    ¬ FiniteReversibleGenerated B 2 (idxField idx ω) v}

theorem idx_escaped_missing_contraction (idx : List Bool × ℕ → List Bool × ℕ)
    (hprod : ∀ z, (idx z).1 = z.1)
    (hpref : ∀ {B z}, z ∈ splitPrefixCoordinates B → idx z ∈ splitPrefixCoordinates B)
    (a : I) (v : List Bool) (hv : 0 < v.length) (B : ℕ) (hB : 2 ≤ B) :
    infiniteSplitPi a (idxEscapedMissing idx (2*B+v.length) v) ≤
      infiniteSplitPi a (idxEscapedMissing idx B v) * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
  let C : Set SplitField := {ω | ¬ FiniteReversibleGenerated B 2 (idxField idx ω) v}
  let A (i : RecordPrefixIndex) : Set SplitField := {ω | (fun z => ω (idx z)) ∈ recordPrefixAtom B i}
  let D (i : RecordPrefixIndex) : Set SplitField := C ∩ A i
  have hC : SplitPrefixDetermined (splitPrefixCoordinates B) C := by
    intro ω η he
    have ht (x y : SplitField) (hxy : ∀ z ∈ splitPrefixCoordinates B, x z = y z) :
        FiniteReversibleGenerated B 2 (idxField idx x) v → FiniteReversibleGenerated B 2 (idxField idx y) v :=
      finiteReversibleGenerated_transfer_prefix le_rfl fun w hw k hk =>
        hxy (idx (w, k)) (hpref ((mem_splitPrefixCoordinates _ _).mpr ⟨hw, hk⟩))
    exact not_congr ⟨ht ω η he, ht η ω fun z hz => (he z hz).symm⟩
  have hA (i : RecordPrefixIndex) : SplitPrefixDetermined (splitPrefixCoordinates i.1) (A i) :=
    fun ω η he => recordPrefixAtom_determined B i _ _ fun z hz => he (idx z) (hpref hz)
  have hmeas (i : RecordPrefixIndex) : MeasurableSet (D i) :=
    (measurableSet_of_splitPrefixDetermined _ C hC).inter (measurableSet_of_splitPrefixDetermined _ _ (hA i))
  have hdis : Pairwise (fun i j => Disjoint (D i) (D j)) := fun i j hij =>
    Set.disjoint_left.mpr fun _ hi hj => Set.disjoint_left.mp (recordPrefixAtoms_disjoint B hij) hi.2 hj.2
  have hpiece (i : RecordPrefixIndex) :
      infiniteSplitPi a (idxEscapedMissing idx (2*B+v.length) v ∩ D i) ≤
        infiniteSplitPi a (D i) * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
    by_cases hn : (D i).Nonempty
    · obtain ⟨ω, hω⟩ := hn
      have hBM : B < i.1 := hω.2.1.1
      have hMB : i.1 ≤ 2*B := by
        obtain ⟨w, hw, hg⟩ := hω.2.1.2.1
        obtain ⟨u, hu, huB, hug⟩ := escape_has_bounded_record hB ⟨w, by omega, finiteReversibleGenerated_to_infinite hg⟩
        by_contra hlt; exact hω.2.1.2.2 u.length hu (by omega) ⟨u, rfl, hug⟩
      obtain ⟨w, hw, _, hrecord⟩ := recordPrefixAtom_word B i ⟨fun z => ω (idx z), hω.2⟩
      have hd : SplitPrefixDetermined (splitPrefixCoordinates w.length) (D i) := by
        rw [hw]; exact fun η ξ he => and_congr (hC _ _ fun z hz => by
          have := (mem_splitPrefixCoordinates B z).mp hz
          exact he z ((mem_splitPrefixCoordinates i.1 z).mpr ⟨by omega, by omega⟩)) (hA i η ξ he)
      let N := w.length + v.length
      obtain ⟨S, hsize, hband, hgen⟩ := target_trial_support (N := N) w v (by omega) hv le_rfl
      let T := S.image (fun r => idx (literalSplitCoordinate r))
      have hdisT : Disjoint (splitPrefixCoordinates w.length) T := by
        refine Finset.disjoint_left.mpr fun z hz ht => ?_
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
        have hl := (mem_splitPrefixCoordinates w.length _).mp hz
        have hb := (hband r hr).1
        rw [hprod] at hl; change (moleculeWord (reactionProduct r)).length ≤ w.length ∧ _ at hl
        rw [moleculeWord_length] at hl; omega
      have hs : idxEscapedMissing idx (2*B+v.length) v ∩ D i ⊆ D i ∩ {η | ¬ ∀ z ∈ T, η z} := by
        intro η ⟨hη1, hη2⟩
        refine ⟨hη2, fun hopen => hη1.2 (finiteReversibleGenerated_mono_cap (by omega : N ≤ 2*B+v.length) ?_)⟩
        obtain ⟨x, hx, he⟩ := finiteReversible_to_literalClosure
          (finiteReversibleGenerated_mono_cap (by omega : w.length ≤ N) (hrecord (fun z => η (idx z)) hη2.2))
        obtain ⟨y, hy, hev⟩ := hgen (restrictedSplitReactions N (idxField idx η))
          (fun r hr => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hopen _ (Finset.mem_image.mpr ⟨r, hr, rfl⟩)⟩) x hx he
        simpa only [hev] using literalClosure_to_finiteReversible (idxField idx η) y hy
      refine (measure_mono hs).trans ?_
      rw [split_prefix_failure_measure a _ T hdisT (D i) hd]
      exact mul_le_mul_right (tsub_le_tsub_left (pow_le_pow_of_le_one zero_le
        (by exact_mod_cast a.property.2) (Finset.card_image_le.trans hsize)) 1) _
    · simp [Set.not_nonempty_iff_eq_empty.mp hn]
  have hcover : idxEscapedMissing idx (2*B+v.length) v ⊆
      ⋃ i : RecordPrefixIndex, idxEscapedMissing idx (2*B+v.length) v ∩ D i := by
    intro ω hω
    obtain ⟨w, hw, hg⟩ := hω.1
    have hex : ∃ M, B < M ∧ idxField idx ω ∈ reversibleRecordEvent 2 M := by
      obtain ⟨u, hu, _, hug⟩ := escape_has_bounded_record hB ⟨w, by omega, hg⟩
      exact ⟨u.length, hu, u, rfl, hug⟩
    exact Set.mem_iUnion.mpr ⟨⟨Nat.find hex, fun z => ω (idx z.val)⟩, hω,
      fun hgen => hω.2 (finiteReversibleGenerated_mono_cap (by omega) hgen),
      ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, fun k hBk hk hr => Nat.find_min hex hk ⟨hBk, hr⟩⟩,
      fun _ => rfl⟩
  calc
    _ ≤ ∑' i, infiniteSplitPi a (idxEscapedMissing idx (2*B+v.length) v ∩ D i) :=
      (measure_mono hcover).trans (measure_iUnion_le _)
    _ ≤ ∑' i, infiniteSplitPi a (D i) * (1-(toNNReal a : ENNReal)^(v.length+1)) := ENNReal.tsum_le_tsum hpiece
    _ = infiniteSplitPi a (⋃ i, D i) * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
      rw [ENNReal.tsum_mul_right, measure_iUnion hdis hmeas]
    _ ≤ _ := mul_le_mul_left (measure_mono fun ω hω => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hω
      obtain ⟨w, hw, hg⟩ := hi.2.1.2.1
      exact ⟨⟨w, by have := hi.2.1.1; omega, finiteReversibleGenerated_to_infinite hg⟩, hi.1⟩) _

theorem finite_seed_failure_idx (idx : List Bool × ℕ → List Bool × ℕ)
    (hprod : ∀ z, (idx z).1 = z.1)
    (hpref : ∀ {B z}, z ∈ splitPrefixCoordinates B → idx z ∈ splitPrefixCoordinates B)
    (a : I) (seed : Finset (List Bool)) (L : ℕ)
    (hseed : ∀ v ∈ seed, 0 < v.length ∧ v.length ≤ L) (r : ℕ) :
    infiniteSplitPi a {ω |
      (∃ w, recordCap L r < w.length ∧ InfiniteReversibleGenerated 2 (idxField idx ω) w) ∧
      ¬ ∀ v ∈ seed, FiniteReversibleGenerated (recordCap L r) 2 (idxField idx ω) v} ≤
      (seed.card : ENNReal) * (1-(toNNReal a : ENNReal)^(L+1))^r := by
  have hrep (v : List Bool) (hv : 0 < v.length) (r : ℕ) :
      infiniteSplitPi a (idxEscapedMissing idx (recordCap v.length r) v) ≤
        (1-(toNNReal a : ENNReal)^(v.length+1))^r := by
    induction r with
    | zero => simpa using (prob_le_one : infiniteSplitPi a (idxEscapedMissing idx (recordCap v.length 0) v) ≤ 1)
    | succ r ih =>
      exact ((idx_escaped_missing_contraction idx hprod hpref a v hv _ (recordCap_ge_two _ _)).trans
        (mul_le_mul' ih le_rfl)).trans_eq (pow_succ _ _).symm
  refine ((measure_mono (t := ⋃ v ∈ seed, idxEscapedMissing idx (recordCap L r) v) fun ω hω => ?_).trans
    (measure_biUnion_finset_le _ _)).trans
    ((Finset.sum_le_sum (g := fun _ => (1-(toNNReal a : ENNReal)^(L+1))^r) fun v hv => ?_).trans_eq (by simp))
  · push Not at hω; obtain ⟨v, hv, hm⟩ := hω.2
    exact Set.mem_iUnion₂.mpr ⟨v, hv, hω.1, hm⟩
  · refine ((measure_mono (s := idxEscapedMissing idx (recordCap L r) v) (t := idxEscapedMissing idx (recordCap v.length r) v)
      fun ω ⟨⟨w, hw, hg⟩, h2⟩ => ⟨⟨w, (recordCap_mono_length (hseed v hv).2 r).trans_lt hw, hg⟩,
        fun hv' => h2 (finiteReversibleGenerated_mono_cap (recordCap_mono_length (hseed v hv).2 r) hv')⟩).trans
      (hrep v (hseed v hv).1 r)).trans (pow_le_pow_left' (tsub_le_tsub_left
        (pow_le_pow_of_le_one zero_le (by exact_mod_cast a.property.2) (by have := (hseed v hv).2; omega)) 1) r)

end RAFCriticalWindowQuantitative
