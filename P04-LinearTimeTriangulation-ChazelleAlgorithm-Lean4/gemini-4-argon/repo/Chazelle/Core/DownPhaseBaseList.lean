module

public import Chazelle.Core.DownPhaseBaseFull
public import Chazelle.Core.NFBuildCmp

/-!
# Down phase, A1 (math, part 2): the kept chord list and the renumbered event list

`keepL li n L = L.filter (keepX li n)`; chord `i` of `L`, if kept, becomes chord `rank i` of
`keepL` (`rank i` = number of kept chords before `i`); event code `c` (chord `c / 2`, side `c % 2`)
becomes `newCode c = 2 · rank (c / 2) + c % 2`, and `dropE` keeps the codes of kept chords, in
order, renumbered.  Then:

* `wposOf_newCode`: the renumbered code names the same walk position, so `codeLe` and the tie bit
  are unchanged (`codeLe_newCode`);
* `dropE_pairwise`, `dropE_perm`: the new event list is a `codeLe`-sorted permutation of
  `range (2 |keepL|)`;
* `chordTriplesOK_keepL`: the kept triples are valid;
* `family_keepL`: in the interior model, the kept family is the family intersected with `Full`
  (`mem_full_iff`).

Design: `docs/design-downphase-nf.md` §3.2.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open BuildNF (codeLe wposOf tieBit)

namespace DownBase

/-! ## Filtered lists, generically -/

section generic

variable {α : Type} (f : α → Bool)

/-- The number of kept entries before position `i`. -/
def rankF (L : List α) (i : ℕ) : ℕ := ((L.take i).filter f).length

theorem getD_filter_rank {L : List α} {i : ℕ} (d : α) (hi : i < L.length)
    (hf : f (L.getD i d) = true) : (L.filter f).getD (rankF f L i) d = L.getD i d := by
  induction L generalizing i with
  | nil => simp at hi
  | cons x L ih =>
    cases i with
    | zero =>
      simp only [List.getD_cons_zero] at hf ⊢
      simp [rankF, hf]
    | succ k =>
      simp only [List.getD_cons_succ] at hf ⊢
      have ih' := ih (by simp at hi; omega) hf
      unfold rankF at ih' ⊢
      simp only [List.take_succ_cons, List.filter_cons]
      split_ifs <;> (try simp only [List.length_cons, List.getD_cons_succ]) <;> exact ih'

theorem rankF_add (L : List α) (i m : ℕ) :
    rankF f L (i + m) = rankF f L i + (((L.drop i).take m).filter f).length := by
  unfold rankF
  rw [List.take_add, List.filter_append, List.length_append]

theorem rankF_lt_of {L : List α} {i j : ℕ} (d : α) (hij : i < j) (hi : i < L.length)
    (hf : f (L.getD i d) = true) : rankF f L i < rankF f L j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = i + (m + 1) := ⟨j - i - 1, by omega⟩
  rw [rankF_add]
  have hd : L.drop i = L[i] :: L.drop (i + 1) := List.drop_eq_getElem_cons hi
  have hLi : L.getD i d = L[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  rw [hLi] at hf
  rw [hd, List.take_succ_cons, List.filter_cons, ite_eq_left hf, List.length_cons]
  omega

theorem rankF_lt_length {L : List α} {i : ℕ} (d : α) (hi : i < L.length)
    (hf : f (L.getD i d) = true) : rankF f L i < (L.filter f).length := by
  have := rankF_lt_of f d (show i < i + 1 by omega) hi hf
  have h2 : rankF f L (i + 1) ≤ (L.filter f).length := by
    unfold rankF
    exact ((List.take_sublist _ _).filter f).length_le
  omega

theorem rankF_length (L : List α) : rankF f L L.length = (L.filter f).length := by
  unfold rankF; rw [List.take_length]

theorem rankF_succ {L : List α} {i : ℕ} (d : α) (hi : i < L.length) :
    rankF f L (i + 1) = rankF f L i + if f (L.getD i d) then 1 else 0 := by
  rw [rankF_add]
  have hd : L.drop i = L[i] :: L.drop (i + 1) := List.drop_eq_getElem_cons hi
  have hLi : L.getD i d = L[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  rw [hLi, hd, List.take_succ_cons, List.take_zero, List.filter_cons]
  split_ifs <;> simp

/-- The kept codes below `2 i`: twice the kept chords below `i`. -/
theorem count_codes {L : List α} (d : α) {i : ℕ} (hi : i ≤ L.length) :
    ((List.range (2 * i)).filter fun c => f (L.getD (c / 2) d)).length = 2 * rankF f L i := by
  induction i with
  | zero => simp [rankF]
  | succ k ih =>
    rw [rankF_succ f d (by omega), show 2 * (k + 1) = 2 * k + 1 + 1 by ring, List.range_succ,
      List.range_succ, List.filter_append, List.filter_append, List.length_append,
      List.length_append, show 2 * k + 1 = 2 * k + 1 from rfl, ih (by omega)]
    have e1 : (2 * k) / 2 = k := by omega
    have e2 : (2 * k + 1) / 2 = k := by omega
    simp only [List.filter_cons, List.filter_nil, e1, e2]
    split_ifs <;> simp; omega

end generic

/-! ## The kept list and the renumbering -/

variable (li : Bool) (n : ℕ)

/-- **The kept chord triples.** -/
def keepL (L : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) := L.filter (keepX li n)

/-- The event code `c` belongs to a kept chord. -/
def keptC (L : List (ℕ × ℕ × ℕ)) (c : ℕ) : Bool := keepX li n (L.getD (c / 2) (0, 0, 0))

/-- The renumbered event code. -/
def newCode (L : List (ℕ × ℕ × ℕ)) (c : ℕ) : ℕ := 2 * rankF (keepX li n) L (c / 2) + c % 2

/-- **The renumbered event list.** -/
def dropE (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) : List ℕ :=
  (E.filter (keptC li n L)).map (newCode li n L)

variable {li n}

theorem getD_keepL {L : List (ℕ × ℕ × ℕ)} {i : ℕ} (hi : i < L.length)
    (hk : keepX li n (L.getD i (0, 0, 0)) = true) :
    (keepL li n L).getD (rankF (keepX li n) L i) (0, 0, 0) = L.getD i (0, 0, 0) :=
  getD_filter_rank _ _ hi hk

theorem wposOf_newCode {L : List (ℕ × ℕ × ℕ)} {c : ℕ} (hc : c < 2 * L.length)
    (hk : keptC li n L c = true) : wposOf (keepL li n L) (newCode li n L c) = wposOf L c := by
  have h1 : newCode li n L c % 2 = c % 2 := by unfold newCode; omega
  have h2 : newCode li n L c / 2 = rankF (keepX li n) L (c / 2) := by unfold newCode; omega
  unfold wposOf
  rw [h1, h2]
  simp only [BuildRegions.crec]
  rw [getD_keepL (by omega) hk]

theorem tieBit_newCode (M : Model) {L : List (ℕ × ℕ × ℕ)} {c : ℕ} (hc : c < 2 * L.length)
    (hk : keptC li n L c = true) : tieBit M (keepL li n L) (newCode li n L c) = tieBit M L c := by
  have h1 : newCode li n L c % 2 = c % 2 := by unfold newCode; omega
  unfold tieBit
  rw [wposOf_newCode hc hk, h1]

theorem codeLe_newCode (M : Model) (Q : Polygon) {L : List (ℕ × ℕ × ℕ)} {c c' : ℕ}
    (hc : c < 2 * L.length) (hk : keptC li n L c = true) (hc' : c' < 2 * L.length)
    (hk' : keptC li n L c' = true) :
    codeLe M Q (keepL li n L) (newCode li n L c) (newCode li n L c') ↔ codeLe M Q L c c' := by
  unfold codeLe
  rw [wposOf_newCode hc hk, wposOf_newCode hc' hk', tieBit_newCode M hc hk,
    tieBit_newCode M hc' hk']

theorem newCode_lt {L : List (ℕ × ℕ × ℕ)} {c : ℕ} (hc : c < 2 * L.length)
    (hk : keptC li n L c = true) : newCode li n L c < 2 * (keepL li n L).length := by
  have := rankF_lt_length (keepX li n) (0, 0, 0) (show c / 2 < L.length by omega) hk
  unfold newCode keepL
  omega

theorem newCode_inj {L : List (ℕ × ℕ × ℕ)} {c c' : ℕ} (hc : c < 2 * L.length)
    (hk : keptC li n L c = true) (hc' : c' < 2 * L.length) (hk' : keptC li n L c' = true)
    (h : newCode li n L c = newCode li n L c') : c = c' := by
  unfold newCode at h
  rcases lt_trichotomy (c / 2) (c' / 2) with h1 | h1 | h1
  · have := rankF_lt_of (keepX li n) (0, 0, 0) h1 (by omega) hk
    omega
  · rw [h1] at h; omega
  · have := rankF_lt_of (keepX li n) (0, 0, 0) h1 (by omega) hk'
    omega

variable {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

theorem mem_lt (hperm : E.Perm (List.range (2 * L.length))) {c : ℕ} (hc : c ∈ E) :
    c < 2 * L.length := List.mem_range.1 (hperm.mem_iff.1 hc)

/-- **The renumbered event list is sorted.** -/
theorem dropE_pairwise (M : Model) (Q : Polygon) (hperm : E.Perm (List.range (2 * L.length)))
    (hsort : E.Pairwise (codeLe M Q L)) :
    (dropE li n L E).Pairwise (codeLe M Q (keepL li n L)) := by
  unfold dropE
  rw [List.pairwise_map]
  refine (hsort.filter _).imp_of_mem fun {a b} ha hb hab => ?_
  rw [List.mem_filter] at ha hb
  exact (codeLe_newCode M Q (mem_lt hperm ha.1) ha.2 (mem_lt hperm hb.1) hb.2).2 hab

/-- **The renumbered event list is a permutation of the new codes.** -/
theorem dropE_perm (hperm : E.Perm (List.range (2 * L.length))) :
    (dropE li n L E).Perm (List.range (2 * (keepL li n L).length)) := by
  have hnd : E.Nodup := hperm.nodup_iff.2 List.nodup_range
  have hnd' : (dropE li n L E).Nodup := by
    unfold dropE
    refine (hnd.filter _).map_on fun a ha b hb hab => ?_
    rw [List.mem_filter] at ha hb
    exact newCode_inj (mem_lt hperm ha.1) ha.2 (mem_lt hperm hb.1) hb.2 hab
  have hsub : dropE li n L E ⊆ List.range (2 * (keepL li n L).length) := by
    intro x hx
    unfold dropE at hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_filter] at hc
    exact List.mem_range.2 (newCode_lt (mem_lt hperm hc.1) hc.2)
  have hlen : (dropE li n L E).length = 2 * (keepL li n L).length := by
    unfold dropE
    rw [List.length_map, (hperm.filter _).length_eq]
    have := count_codes (keepX li n) (L := L) (0, 0, 0) (le_refl L.length)
    rw [rankF_length] at this
    exact this
  exact (hnd'.subperm hsub).perm_of_length_le (by rw [hlen, List.length_range])

/-- **The kept triples are valid.** -/
theorem chordTriplesOK_keepL {M : Model} {Q : Polygon} (h : ChordTriplesOK M Q L) :
    ChordTriplesOK M Q (keepL li n L) := by
  obtain ⟨hF, hnd, hat, hlt⟩ := h
  have hsub : {c | ∃ x ∈ keepL li n L, c = (recOf x).toSet M Q} ⊆
      {c | ∃ x ∈ L, c = (recOf x).toSet M Q} := by
    rintro c ⟨x, hx, rfl⟩
    exact ⟨x, (List.mem_filter.1 hx).1, rfl⟩
  refine ⟨⟨hF.1.subset hsub, hsub.trans hF.2.1, fun c hc => hF.2.2 c (hsub hc)⟩,
    hnd.sublist (List.filter_sublist.map _), fun x hx => hat x (List.mem_filter.1 hx).1,
    fun x hx => hlt x (List.mem_filter.1 hx).1⟩

/-- **The kept family is the family intersected with the vertex chords** (interior model). -/
theorem family_keepL {Q : Polygon} (hQ : Q.Simple) (hDH : DistinctHeights Q)
    (hli : li = true ↔ Mountain.LeftInside Q) (h : ChordTriplesOK (interiorModel Q) Q L) :
    {c | ∃ x ∈ keepL li Q.n L, c = (recOf x).toSet (interiorModel Q) Q} =
      {c | ∃ x ∈ L, c = (recOf x).toSet (interiorModel Q) Q} ∩ (interiorModel Q).Full := by
  obtain ⟨hF, -, hat, hlt⟩ := h
  have hiff : ∀ x ∈ L, ((recOf x).toSet (interiorModel Q) Q ∈ (interiorModel Q).Full ↔
      keepX li Q.n x = true) := fun x hx =>
    mem_full_iff hQ hDH hli (hat x hx) (hF.2.1 ⟨x, hx, rfl⟩) (hlt x hx)
  ext c
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxL, hk⟩ := List.mem_filter.1 hx
    exact ⟨⟨x, hxL, rfl⟩, (hiff x hxL).2 hk⟩
  · rintro ⟨⟨x, hx, rfl⟩, hfull⟩
    exact ⟨x, List.mem_filter.2 ⟨hx, (hiff x hx).1 hfull⟩, rfl⟩

end DownBase

end

end Chazelle.Core
