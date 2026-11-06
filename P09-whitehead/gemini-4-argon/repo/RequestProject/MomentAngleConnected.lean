module

public import RequestProject.TruncatedCube

@[expose] public section

namespace FiniteChains

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

def IsTri (L : ASC V) (σ : Finset V) : Prop := σ ∈ L.faces ∧ σ.card = 3

def TriAdj (L : ASC V) (σ σ' : Finset V) : Prop :=
  IsTri L σ ∧ IsTri L σ' ∧ (σ ∩ σ').card = 2

def negSet (f : Cube V) : Finset V := univ.filter fun v => f v = CubeCoord.neg

omit [DecidableEq V] [LinearOrder V] in
@[simp] theorem mem_negSet {f : Cube V} {v : V} : v ∈ negSet f ↔ f v = CubeCoord.neg := by
  simp [negSet]

def Move (L : ASC V) (f g : Cube V) : Prop :=
  ∃ c c' : V, c ≠ c' ∧ f c = CubeCoord.free ∧ f c' ≠ CubeCoord.free ∧
    g c ≠ CubeCoord.free ∧ g c' = CubeCoord.free ∧
    (∀ v, v ≠ c → v ≠ c' → f v = g v) ∧ freeSet f ∈ L.faces ∧ freeSet g ∈ L.faces

omit [DecidableEq V] [LinearOrder V] in
theorem Move.symm {L : ASC V} {f g : Cube V} (h : Move L f g) : Move L g f :=
  let ⟨c, c', hcc, hfc, hfc', hgc, hgc', hagree, hfL, hgL⟩ := h
  ⟨c', c, hcc.symm, hgc', hgc, hfc', hfc, fun v hv hv' => (hagree v hv' hv).symm, hgL, hfL⟩

omit [LinearOrder V] in
theorem Move.shares_square {L : ASC V} {f g : Cube V} (h : Move L f g) :
    ∃ s : Cube V, (∃ j, s j ≠ CubeCoord.free ∧ f = Function.update s j CubeCoord.free) ∧
      (∃ j, s j ≠ CubeCoord.free ∧ g = Function.update s j CubeCoord.free) := by
  obtain ⟨c, c', hcc, hfc, hfc', hgc, hgc', hagree, -, -⟩ := h
  refine ⟨fun v => if v = c then g c else if v = c' then f c' else f v,
    ⟨c, by simpa using hgc, funext fun v => ?_⟩,
    ⟨c', by simp [hcc.symm, hfc'], funext fun v => ?_⟩⟩
  · by_cases hv : v = c
    · subst hv; simp [hfc]
    · by_cases hv' : v = c'
      · subst hv'; simp [hv]
      · simp [hv, hv']
  · by_cases hv : v = c'
    · subst hv; simp [hgc']
    · by_cases hvc : v = c
      · subst hvc; simp [hv]
      · simp [hv, hvc, hagree v hvc hv]

def moveTo (f : Cube V) (c c' : V) : Cube V := fun v =>
  if v = c then CubeCoord.pos else if v = c' then CubeCoord.free else f v

omit [LinearOrder V] in
theorem exists_move_path {L : ASC V} {σ σ' : Finset V}
    (hpath : Relation.ReflTransGen (TriAdj L) σ σ') :
    ∀ f : Cube V, freeSet f = σ → ∃ g : Cube V, freeSet g = σ' ∧ negSet g ⊆ negSet f ∧
      Relation.ReflTransGen (Move L) f g := by
  induction hpath with
  | refl => exact fun f hf => ⟨f, hf, Subset.refl _, .refl⟩
  | @tail τ τ' _ hstep ih =>
      intro f hf
      obtain ⟨g, hgfree, hgneg, hgpath⟩ := ih f hf
      obtain ⟨⟨hτL, hcard⟩, ⟨hτ'L, hcard'⟩, hint⟩ := hstep
      have hdiff : (τ \ τ').card = 1 := by have := card_sdiff_add_card_inter τ τ'; omega
      have hdiff' : (τ' \ τ).card = 1 := by
        have := card_sdiff_add_card_inter τ' τ; rw [inter_comm] at this; omega
      obtain ⟨c, hc⟩ := card_eq_one.1 hdiff
      obtain ⟨c', hc'⟩ := card_eq_one.1 hdiff'
      have hcmem : c ∈ τ ∧ c ∉ τ' := mem_sdiff.1 (by rw [hc]; simp)
      have hc'mem : c' ∈ τ' ∧ c' ∉ τ := mem_sdiff.1 (by rw [hc']; simp)
      have hcc : c ≠ c' := fun h => hcmem.2 (h ▸ hc'mem.1)
      have hτ' : τ' = insert c' (τ.erase c) := by
        refine eq_of_subset_of_card_le (fun z hz => ?_) ?_
        · simp only [mem_insert, mem_erase]
          by_cases hzc' : z = c'
          · exact .inl hzc'
          · refine .inr ⟨fun h => hcmem.2 (h ▸ hz), ?_⟩
            by_contra hzτ
            have : z ∈ τ' \ τ := mem_sdiff.2 ⟨hz, hzτ⟩
            rw [hc', mem_singleton] at this
            exact hzc' this
        · have := card_insert_le c' (τ.erase c)
          have := card_erase_of_mem hcmem.1; omega
      have hgc : g c = CubeCoord.free := by simpa using (hgfree ▸ hcmem.1 : c ∈ freeSet g)
      have hgc' : g c' ≠ CubeCoord.free := fun hcon => hc'mem.2 (hgfree ▸ by simpa using hcon)
      have hfreeNew : freeSet (moveTo g c c') = τ' := by
        rw [hτ', ← hgfree]; ext v
        by_cases hv : v = c
        · subst hv; simp [moveTo, hcc]
        · by_cases hv' : v = c'
          · subst hv'; simp [moveTo, hv]
          · simp [moveTo, hv, hv']
      have hnegSub : negSet (moveTo g c c') ⊆ negSet g := fun v hv => by
        simp only [mem_negSet, moveTo] at hv ⊢
        split_ifs at hv with hvc hvc'
        exact hv
      refine ⟨moveTo g c c', hfreeNew, hnegSub.trans hgneg,
        hgpath.tail ⟨c, c', hcc, hgc, hgc', by simp [moveTo], by simp [moveTo, hcc.symm],
          fun v hv hv' => by simp [moveTo, hv, hv'], hgfree ▸ hτL, hfreeNew ▸ hτ'L⟩⟩

omit [LinearOrder V] in
theorem reflTransGen_move_posCube {L : ASC V} (hdual : ∀ σ σ', IsTri L σ → IsTri L σ' →
      Relation.ReflTransGen (TriAdj L) σ σ')
    (hcover : ∀ v : V, ∃ σ, IsTri L σ ∧ v ∈ σ) {σ₀ : Finset V} (hσ₀ : IsTri L σ₀) :
    ∀ (n : ℕ) (f : Cube V), IsTri L (freeSet f) → (negSet f).card ≤ n →
      Relation.ReflTransGen (Move L) f (posCube σ₀)
  | 0, f, hf, hn => by
      obtain ⟨g, hgfree, hgneg, hgpath⟩ := exists_move_path (hdual _ _ hf hσ₀) f rfl
      have hgempty : negSet g = ∅ := subset_empty.1 (card_eq_zero.1 (Nat.le_zero.1 hn) ▸ hgneg)
      have hgeq : g = posCube σ₀ := by
        rw [← hgfree]; funext v
        by_cases hv : g v = CubeCoord.free
        · simp [posCube, hv]
        · have hvn : g v ≠ CubeCoord.neg := fun hn => by
            have : v ∈ negSet g := by simpa using hn
            simp [hgempty] at this
          have hvp : g v = CubeCoord.pos := by cases hgv : g v <;> first | rfl | contradiction
          have : v ∉ freeSet g := by simpa using hv
          simp [posCube, this, hvp]
      rwa [hgeq] at hgpath
  | n + 1, f, hf, hn => by
      rcases (negSet f).eq_empty_or_nonempty with hempty | ⟨v, hv⟩
      · exact reflTransGen_move_posCube hdual hcover hσ₀ 0 f hf (by simp [hempty])
      · obtain ⟨τ, hτ, hvτ⟩ := hcover v
        obtain ⟨g, hgfree, hgneg, hgpath⟩ := exists_move_path (hdual _ _ hf hτ) f rfl
        have hvg : v ∉ negSet g := fun hcon => by
          have hvfree : g v = CubeCoord.free := by simpa using (hgfree ▸ hvτ : v ∈ freeSet g)
          simp [negSet, hvfree] at hcon
        have hstrict : (negSet g).card < (negSet f).card :=
          card_lt_card ⟨hgneg, fun hcon => hvg (hcon hv)⟩
        exact hgpath.trans (reflTransGen_move_posCube hdual hcover hσ₀ n g (hgfree ▸ hτ) (by omega))

omit [LinearOrder V] in
theorem reflTransGen_move {L : ASC V} (hdual : ∀ σ σ', IsTri L σ → IsTri L σ' →
      Relation.ReflTransGen (TriAdj L) σ σ')
    (hcover : ∀ v : V, ∃ σ, IsTri L σ ∧ v ∈ σ) {f g : Cube V}
    (hf : IsTri L (freeSet f)) (hg : IsTri L (freeSet g)) :
    Relation.ReflTransGen (Move L) f g :=
  (reflTransGen_move_posCube hdual hcover hf (negSet f).card f hf le_rfl).trans
    (Relation.ReflTransGen.mono (fun _ _ (step : Move L _ _) => step.symm) _ _
      (Relation.ReflTransGen.swap _ _
        (reflTransGen_move_posCube hdual hcover hf (negSet g).card g hg le_rfl)))
