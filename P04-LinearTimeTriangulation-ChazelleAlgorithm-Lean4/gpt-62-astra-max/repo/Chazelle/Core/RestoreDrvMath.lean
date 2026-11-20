module

public import Chazelle.Core.RestoreDrvReg

/-!
# WP-E, part 9: the restoration driver — the mathematics of one round

After the region loop of a round, the list at `LB` is `oldL N ++ newL.map Prod.snd`, where
`newL` pairs the high regions of the current normal form `N` with sound chords (`FoundOK`).

* `round_list_ok`: the list is a valid input of `BuildNF` (`ChordTriplesOK`);
* `round_lset`: its chords are `N.F ∪ E` with `E` the new chords;
* `round_data`: `E` is round data (`RoundData`: one well-splitting chord per high region);
* `round_all`: every region with more than `D` exit chords received a chord.
-/

namespace Chazelle.Core

namespace Restore

open Chazelle.Chain (regionsIn TouchesIn)
open Chazelle.Merge (exitsIn)

@[expose] public section

variable {M : Model} {Q : Polygon} {N : NF} {reg : ℕ → Set Point}

theorem recOf_toSet (x : CRec) : (recOf (x.h, x.lp, x.rp)).toSet M Q = x.toSet M Q := rfl

/-- The new chords of a round. -/
def newSet (M : Model) (Q : Polygon) (newL : List (ℕ × (ℕ × ℕ × ℕ))) : Set (Set Point) :=
  {c | ∃ p ∈ newL, c = (recOf p.2).toSet M Q}

theorem mem_highList {D r r' : ℕ} : r' ∈ highList N D r ↔ r' < r ∧ D < degOf N r' := by
  unfold highList; simp

theorem highList_nodup (D r : ℕ) : (highList N D r).Nodup := List.nodup_range.filter _

theorem chords_map_nodup (hN : IsNF M Q N) : (N.chords.map fun x => x.toSet M Q).Nodup := by
  rw [List.nodup_iff_injective_get]
  rintro ⟨i, hi⟩ ⟨j, hj⟩ h
  simp only [List.get_eq_getElem, List.getElem_map] at h
  simp only [List.length_map] at hi hj
  have e : ∀ k (hk : k < N.chords.length), N.chords[k] = N.chord k := fun k hk => by
    unfold NF.chord; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
      Option.getD_some]
  rw [e i hi, e j hj] at h
  exact Fin.ext (hN.2.1 i j hi hj h)

theorem chord_toSet_mem {i : ℕ} (hi : i < N.nChords) : (N.chord i).toSet M Q ∈ N.F M Q :=
  ⟨N.chord i, OutNF.chord_mem hi, rfl⟩

/-- The new chord of a region lies in that region. -/
theorem found_sub {r : ℕ} {t : ℕ × ℕ × ℕ} (h : FoundOK M Q N reg r t) :
    (recOf t).toSet M Q ∩ M.D ⊆ reg r := h.2.2.2.2.1

/-- **Distinct high regions get distinct chords** (and a chord determines its region). -/
theorem found_region (hM : WalkAx M) (_hN : IsNF M Q N) (hregs : NFRegs M Q N reg) {r r' : ℕ}
    (hr : r < N.nRegions) (hr' : r' < N.nRegions) {t t' : ℕ × ℕ × ℕ}
    (h : FoundOK M Q N reg r t) (h' : FoundOK M Q N reg r' t')
    (he : (recOf t).toSet M Q = (recOf t').toSet M Q) : r = r' := by
  obtain ⟨z, hz⟩ := inter_nonempty_of_adm hM h.2.2.1
  have hz1 := found_sub h hz
  have hz2 := found_sub h' (he ▸ hz)
  obtain ⟨hRC, -, -, -⟩ := hregs
  have e1 := hRC.1 r hr
  have e2 := hRC.1 r' hr'
  have : reg r = reg r' := by
    rw [Chazelle.Chain.regionsIn_eq_component e1 hz1, Chazelle.Chain.regionsIn_eq_component e2 hz2]
  exact hRC.2.1 r r' hr hr' this

theorem fst_inj {l : List (ℕ × (ℕ × ℕ × ℕ))} (hl : (l.map Prod.fst).Nodup) {p p' : ℕ × (ℕ × ℕ × ℕ)}
    (hp : p ∈ l) (hp' : p' ∈ l) (h : p.1 = p'.1) : p = p' := by
  induction l with
  | nil => simp at hp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hl
    rcases List.mem_cons.1 hp with h1 | h1 <;> rcases List.mem_cons.1 hp' with h2 | h2
    · rw [h1, h2]
    · exact absurd ⟨p', h2, by rw [← h, h1]⟩ hl.1
    · exact absurd ⟨p, h1, by rw [h, h2]⟩ hl.1
    · exact ih hl.2 h1 h2

/-- The data of the end of a region loop. -/
structure NewOK (M : Model) (Q : Polygon) (N : NF) (reg : ℕ → Set Point) (D : ℕ)
    (newL : List (ℕ × (ℕ × ℕ × ℕ))) : Prop where
  fst : newL.map Prod.fst = highList N D N.nRegions
  good : ∀ p ∈ newL, FoundOK M Q N reg p.1 p.2

theorem NewOK.lt {D : ℕ} {newL : List (ℕ × (ℕ × ℕ × ℕ))} (h : NewOK M Q N reg D newL)
    {p : ℕ × (ℕ × ℕ × ℕ)} (hp : p ∈ newL) : p.1 < N.nRegions := by
  have : p.1 ∈ newL.map Prod.fst := List.mem_map_of_mem hp
  rw [h.fst, mem_highList] at this
  exact this.1

theorem NewOK.nodup_fst {D : ℕ} {newL : List (ℕ × (ℕ × ℕ × ℕ))} (h : NewOK M Q N reg D newL) :
    (newL.map Prod.fst).Nodup := by rw [h.fst]; exact highList_nodup _ _

/-- **The list of a round is a valid input of the normal-form construction.** -/
theorem round_list_ok (hM : WalkAx M) (hN : IsNF M Q N) (hregs : NFRegs M Q N reg) {D : ℕ}
    {newL : List (ℕ × (ℕ × ℕ × ℕ))} (h : NewOK M Q N reg D newL) :
    ChordTriplesOK M Q (oldL N ++ newL.map Prod.snd) := by
  have hmem : ∀ x ∈ oldL N ++ newL.map Prod.snd,
      (recOf x).toSet M Q ∈ M.Adm ∧ x.1 < Q.n ∧ (recOf x).Attached M Q := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hy
      have e : N.chords[i] = N.chord i := by
        unfold NF.chord; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
          Option.getD_some]
      rw [e]
      obtain ⟨-, -, -, -, -, -, hh, -⟩ := hN.2.2.2
      exact ⟨hN.1.2.1 (chord_toSet_mem hi), hh i hi, hN.2.2.1 i hi⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      obtain ⟨h1, h2, h3, -⟩ := h.good p hp
      exact ⟨h3, h2, h1⟩
  refine ⟨⟨(List.finite_toSet ((oldL N ++ newL.map Prod.snd).map
      fun x => (recOf x).toSet M Q)).subset ?_, fun c ⟨x, hx, hc⟩ => hc ▸ (hmem x hx).1,
    fun c ⟨x, hx, hc⟩ => ⟨x.1, (hmem x hx).2.1, _, _, hc⟩⟩, ?_, fun x hx => (hmem x hx).2.2,
    fun x hx => (hmem x hx).2.1⟩
  · rintro c ⟨x, hx, rfl⟩
    exact List.mem_map_of_mem (f := fun x => (recOf x).toSet M Q) hx
  · rw [List.map_append]
    refine List.nodup_append.2 ⟨?_, ?_, ?_⟩
    · have : (oldL N).map (fun x => (recOf x).toSet M Q) = N.chords.map fun x => x.toSet M Q := by
        simp [oldL, recOf_toSet]
      rw [this]; exact chords_map_nodup hN
    · rw [List.map_map]
      refine List.Nodup.map_on ?_ (List.Nodup.of_map _ h.nodup_fst)
      intro p hp p' hp' he
      exact fst_inj h.nodup_fst hp hp' (found_region hM hN hregs (h.lt hp) (h.lt hp')
        (h.good p hp) (h.good p' hp') he)
    · intro a ha b hb hab
      subst hab
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      obtain ⟨t, ht, hpe⟩ := List.mem_map.1 hb
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
      have hold : (recOf x).toSet M Q ∈ N.F M Q := by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact ⟨y, hy, rfl⟩
      exact (h.good p hp).2.2.2.1 (hpe ▸ hold)

/-- **The chords of the list of a round.** -/
theorem round_lset {newL : List (ℕ × (ℕ × ℕ × ℕ))} :
    Gran.lset M Q (oldL N ++ newL.map Prod.snd) = N.F M Q ∪ newSet M Q newL := by
  ext c
  simp only [Gran.lset, newSet, oldL, List.mem_append, List.mem_map, Set.mem_union,
    Set.mem_ofPred_eq, NF.F]
  constructor
  · rintro ⟨x, hx | ⟨p, hp, rfl⟩, rfl⟩
    · left
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hy, rfl⟩
    · right; exact ⟨p, hp, rfl⟩
  · rintro (⟨y, hy, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact ⟨_, Or.inl ⟨y, hy, rfl⟩, rfl⟩
    · exact ⟨_, Or.inr ⟨p, hp, rfl⟩, rfl⟩

/-- **The new chords of a round are round data.** -/
theorem round_data (hM : WalkAx M) (_hN : IsNF M Q N) (hregs : NFRegs M Q N reg) {D : ℕ}
    {newL : List (ℕ × (ℕ × ℕ × ℕ))} (h : NewOK M Q N reg D newL) :
    RoundData M (N.F M Q) (newSet M Q newL) := by
  obtain ⟨hRC, -, -, -⟩ := hregs
  refine ⟨fun c ⟨p, hp, hc⟩ => hc ▸ (h.good p hp).2.2.1, (List.finite_toSet (newL.map fun p =>
    (recOf p.2).toSet M Q)).subset fun c ⟨p, hp, hc⟩ => by
      rw [hc]; exact List.mem_map_of_mem (f := fun p => (recOf p.2).toSet M Q) hp,
    fun c ⟨p, hp, hc⟩ => ⟨reg p.1, hRC.1 _ (h.lt hp), hc ▸ (h.good p hp).2.2.2⟩, ?_⟩
  rintro e ⟨p, hp, rfl⟩ e' ⟨p', hp', rfl⟩ R hR hw hw'
  obtain ⟨z, hz⟩ := inter_nonempty_of_adm hM (h.good p hp).2.2.1
  obtain ⟨z', hz'⟩ := inter_nonempty_of_adm hM (h.good p' hp').2.2.1
  have hreg : ∀ q ∈ newL, ∀ y ∈ (recOf q.2).toSet M Q ∩ M.D,
      SplitsWell M (N.F M Q) R ((recOf q.2).toSet M Q) → reg q.1 = R := by
    intro q hq y hy hwq
    have e1 := hRC.1 _ (h.lt hq)
    rw [Chazelle.Chain.regionsIn_eq_component e1 (found_sub (h.good q hq) hy),
      Chazelle.Chain.regionsIn_eq_component hR (hwq.2.1 hy)]
  have h1 := hreg p hp z hz hw
  have h2 := hreg p' hp' z' hz' hw'
  have := hRC.2.1 _ _ (h.lt hp) (h.lt hp') (h1.trans h2.symm)
  rw [fst_inj h.nodup_fst hp hp' this]

/-- **Every high region received a chord.** -/
theorem round_all (hN : IsNF M Q N) (hregs : NFRegs M Q N reg) {D : ℕ}
    {newL : List (ℕ × (ℕ × ℕ × ℕ))} (h : NewOK M Q N reg D newL) :
    ∀ R ∈ regionsIn M.D (N.F M Q), D < (exitsIn M.D (N.F M Q) R).ncard →
      ∃ e ∈ newSet M Q newL, SplitsWell M (N.F M Q) R e := by
  obtain ⟨hRC, -, -, hRO⟩ := hregs
  intro R hR hD
  obtain ⟨r, hr, rfl⟩ := hRC.2.2 R hR
  have hdeg : (exitsIn M.D (N.F M Q) (reg r)).ncard = degOf N r :=
    Gran.deg_region hN hRC hRO hr
  have : r ∈ newL.map Prod.fst := by
    rw [h.fst, mem_highList]; exact ⟨hr, by rw [← hdeg]; exact hD⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 this
  exact ⟨_, ⟨p, hp, rfl⟩, (h.good p hp).2.2.2⟩

end

end Restore

end Chazelle.Core
