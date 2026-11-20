module
public import proofs.HordijkSteelThreshold.InfiniteStaticLaw

/-! Disjoint repairs beyond a completed record and their iterated failure bound. -/

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAF.Polymer RAF.Concrete MeasureTheory unitInterval

/-- Both models read marks from the same product space. The coordinate encoding
respects completed prefixes and preserves the product length of a repair. -/
structure ChannelMap where
  index : Coord → Coord
  product : ∀ z, (index z).1 = z.1
  half : ∀ w i, 2*i ≤ w.length → index (w,i) = (w,i)

namespace ChannelMap
variable (f : ChannelMap)

abbrev field (ω : SplitField) := currySplitField (ω ∘ f.index)
abbrev generated (B : ℕ) (v : List Bool) : Set SplitField :=
  {ω | FiniteReversibleGenerated B 2 (f.field ω) v}
abbrev escape (B : ℕ) : Set SplitField :=
  {ω | ∃ w, B < w.length ∧ InfiniteReversibleGenerated 2 (f.field ω) w}

variable {N B : ℕ} {w v : List Bool}

/-- Following a word by its successive one-letter extensions uses at most one
fresh mark per appended letter. -/
private lemma path (hN : (w++v).length ≤ N) : ∃ T : Finset Coord, T.card ≤ v.length ∧
    Disjoint (past w.length) (T : Set Coord) ∧ ∀ ω ∈ f.generated N w,
    (∀ z ∈ T, ω z) → ω ∈ f.generated N (w++v) := by
  induction v using List.reverseRecOn with
  | nil => simp_all
  | append_singleton v b ih =>
    rw [←List.append_assoc] at hN ⊢
    obtain ⟨T,hc,hd,hg⟩ := ih (by grind)
    let z := f.index ((w++v)++[b],(w++v).length)
    refine ⟨insert z T,(Finset.card_insert_le ..).trans (by simpa),
      by simpa [Set.disjoint_insert_right,past,z,f.product] using hd,?_⟩
    intro ω hw ho
    rw [Finset.forall_mem_insert] at ho
    exact .ligate (hg ω hw ho.2) (.food (by simp) (by grind)) ⟨ho.1,hN⟩

lemma failure (a : I) (hw : w ≠ []) (hv : v ≠ []) (hN : (w++v).length ≤ N)
    {E : Set SplitField} (hE : MeasurableSet[observed (past w.length)] E) (hrec : E ⊆ f.generated w.length w) :
    infiniteSplitPi a (E ∩ (f.generated N v)ᶜ) ≤ infiniteSplitPi a E * missRate a (v.length+1) := by
  obtain ⟨T,hc,hd,hg⟩ := f.path hN
  let z := f.index (w++v,w.length)
  have dis : Disjoint (past w.length) ((insert z T : Finset Coord) : Set _) := by
    simpa [Set.disjoint_insert_right,z,past,f.product,hv] using hd
  have law := fresh_law a dis hE {b | ∀ j, b j}ᶜ
  simp only [fail_open,Fintype.card_coe] at law
  apply (measure_mono ?_).trans (law.le.trans (mul_le_mul_right (miss_mono a ((Finset.card_insert_le ..).trans (by omega))) _))
  rintro ω ⟨he,hm⟩; refine ⟨he,fun ho => hm ?_⟩
  exact InfiniteReversibleGenerated.right hw hv (hg _ (finiteReversibleGenerated_mono_cap (by grind) (hrec he))
    fun y hy => ho ⟨y,Finset.mem_insert_of_mem hy⟩) ⟨ho ⟨z,by simp⟩,hN⟩

abbrev missing (B : ℕ) (v : List Bool) := f.escape B ∩ (f.generated B v)ᶜ

private lemma generated_meas {N M : ℕ} (h : N ≤ M) (w : List Bool) : MeasurableSet[observed (past M)] (f.generated N w) := by
  let E := {η : Reaction N → Prop | ∃ x ∈ temporaryReactionClosure 2 (Finset.univ.filter η), moleculeWord x = w}
  have m := observed_read (S := past M) (fun r : Reaction N => f.index (literalSplitCoordinate r))
    (fun r => by simpa [past,literalSplitCoordinate,f.product] using (moleculeWord_cap (reactionProduct r)).trans h)
  convert! m (Set.toFinite E).measurableSet using 1; ext; exact finiteReversible_iff_literalClosure _ _

/-- Contract on disjoint, completed record atoms, not conditional on future escape. -/
theorem contraction (a : I) (hv : v ≠ []) (hB : 2 ≤ B) (hN : 2*B+v.length ≤ N) :
    infiniteSplitPi a (f.missing N v) ≤ infiniteSplitPi a (f.missing B v) * missRate a (v.length+1) := by
  obtain ⟨e,sorted⟩ := enumerate_by (fun x : RecordWord B => (moleculeWord x.val).length)
  let w i := moleculeWord (e i).val
  have len i : B < (w i).length := by simpa [w,moleculeWord_length] using (e i).property
  let hit i := f.generated (w i).length (w i) ∩ (f.generated B v)ᶜ
  have part : (⋃ i, disjointed hit i) = f.missing B v := by
    simp only [iUnion_disjointed,hit,←Set.iUnion_inter,missing]; congr 1; ext ω
    rw [Set.mem_iUnion]; change (∃ i, ω ∈ f.generated _ (w i)) ↔ Escapes 2 B _
    rw [escape_iff_record hB]; exact (e.surjective.exists (p := fun x => ω ∈ f.generated (moleculeWord x.val).length (moleculeWord x.val))).symm
  have det i : MeasurableSet[observed (past (w i).length)] (disjointed hit i) := by
    have m j (h : j ≤ i) := (f.generated_meas (sorted h) (w j)).inter (f.generated_meas (len i).le v).compl
    rw [disjointed_eq_inter_compl]
    exact (m i le_rfl).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun h => (m j h.le).compl)
  let μ := infiniteSplitPi a
  calc
    _ ≤ μ (⋃ i, disjointed hit i ∩ (f.generated N v)ᶜ) := by
      rw [←Set.iUnion_inter,part]; apply measure_mono; rintro ω ⟨⟨u,hl,hg⟩,hn⟩
      exact ⟨⟨⟨u,by omega,hg⟩,fun hv => hn (finiteReversibleGenerated_mono_cap (by omega) hv)⟩,hn⟩
    _ ≤ _ := (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun i => f.failure a (moleculeWord_nonempty _) hv
      (by have := moleculeWord_cap (e i).val; grind) (det i) ((disjointed_subset hit i).trans Set.inter_subset_left))
    _ = _ := by rw [ENNReal.tsum_mul_right,←measure_iUnion (disjoint_disjointed hit) (fun i => observed_le _ _ (det i)),part]

end ChannelMap

def recordCap (ell : ℕ) : ℕ → ℕ :=
  Nat.rec 2 (fun _ cap => 2*cap+ell)

theorem recordCap_ge_two (ell j : ℕ) : 2 ≤ recordCap ell j := by
  induction j with
  | zero => rfl
  | succ j ih => grind [recordCap]

namespace ChannelMap
variable (f : ChannelMap) (a : I)

theorem target_failure {L : ℕ} (x : Molecule L) (r : ℕ) :
    let v := moleculeWord x;
    infiniteSplitPi a (f.missing (recordCap L r) v) ≤ (missRate a (L+1))^r := by
  induction r with
  | zero => rw [pow_zero]; exact prob_le_one
  | succ r ih =>
    rw [pow_succ]
    apply (f.contraction a (moleculeWord_nonempty x) (recordCap_ge_two L r) (Nat.add_le_add_left (moleculeWord_cap x) _)).trans
    exact mul_le_mul' ih (miss_mono a (Nat.add_le_add_right (moleculeWord_cap x) 1))

abbrev seed (L K : ℕ) : Set SplitField := {ω | ∀ x : Molecule L, ω ∈ f.generated K (moleculeWord x)}

theorem seed_failure (L r : ℕ) :
    let K := recordCap L r
    infiniteSplitPi a (f.escape K ∩ (f.seed L K)ᶜ) ≤
      2^(L+1)*(missRate a (L+1))^r := by
  let K := recordCap L r
  apply (finite_cover _ (fun x : Molecule L => f.missing K (moleculeWord x)) ?_
    (fun x => f.target_failure a x r)).trans
  · gcongr; exact_mod_cast card_molecules_le L
  · rintro ω ⟨he,hn⟩; obtain ⟨x,hx⟩ := Classical.not_forall.mp hn; exact ⟨x,he,hx⟩

end ChannelMap
end RAFCriticalWindowQuantitative
