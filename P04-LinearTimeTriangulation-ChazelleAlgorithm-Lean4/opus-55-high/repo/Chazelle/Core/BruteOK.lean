module

public import Chazelle.Core.BruteList

/-!
# WP-K: the brute-force chord list is valid and is the full map

* `bruteList C`: the chord triples of the emitted (tour position, direction) entries, in the
  order of the tour, east before west;
* `bruteList_ok`: `ChordTriplesOK (chainModel C) C.P (bruteList C)`;
* `bruteList_set`: the chords of the list are exactly the full map `C.chords`.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sideCcw sideCross sideDot sideLeft sideLeftOf sidePt SideAttach)
open Chazelle.Visibility (rayPt OpenEdgePt xAt hseg)

namespace Brute

variable {C : Chain}

/-- The direction of code `d` (`0` east, else west). -/
def sig (d : ℕ) : ℝ := if d = 0 then 1 else -1

theorem sig_cases (d : ℕ) : sig d = 1 ∨ sig d = -1 := by
  unfold sig; split_ifs <;> simp

/-- The direction of code `d` is emitted at tour position `i`. -/
def Emit (C : Chain) (i d : ℕ) : Prop := emitR (prevPt C i) (vPt C i) (nextPt C i) (sig d)

/-- The chord triple of the entry `(i, d)`. -/
noncomputable def trip (C : Chain) (i d : ℕ) : ℕ × ℕ × ℕ :=
  if d = 0 then (C.edgeIdx (C.sideIdx C.sideBeta i), i + 6, farEdge C (C.sideIdx C.sideBeta i) 1)
  else (C.edgeIdx (C.sideIdx C.sideBeta i), farEdge C (C.sideIdx C.sideBeta i) (-1), i + 6)

/-- The entries `(i, d)`, `i ≤ 2m`, in the order of the tour, east before west. -/
def entries (m : ℕ) : List (ℕ × ℕ) := (List.range (2 * m + 1)).flatMap fun i => [(i, 0), (i, 1)]

open Classical in
/-- **The brute-force chord list.** -/
noncomputable def bruteList (C : Chain) : List (ℕ × ℕ × ℕ) :=
  ((entries C.m).filter fun e => decide (Emit C e.1 e.2)).map fun e => trip C e.1 e.2

theorem mem_entries {m : ℕ} {e : ℕ × ℕ} : e ∈ entries m ↔ e.1 ≤ 2 * m ∧ e.2 ≤ 1 := by
  unfold entries
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨i, hi, rfl | rfl⟩ <;> simp <;> omega
  · rintro ⟨h1, h2⟩
    refine ⟨e.1, by omega, ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h2 with h | h
    · left; ext <;> simp [h]
    · right; ext <;> simp [h]

theorem entries_nodup (m : ℕ) : (entries m).Nodup := by
  unfold entries
  rw [List.nodup_flatMap]
  refine ⟨fun i _ => by simp, List.nodup_range.pairwise_of_forall_ne fun a _ b _ hab => ?_⟩
  refine List.disjoint_left.2 fun x hx hx' => hab ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hx'
  rcases hx with rfl | rfl <;> rcases hx' with h | h <;> simp only [Prod.mk.injEq] at h <;> omega

/-- The vertex chord attached at the walk vertex of an emitted entry (parameter `0`). -/
theorem vert_attach0 (hP : C.P.Simple) (hDH : DistinctHeights C.P) {i : ℕ} (hi : i ≤ 2 * C.m)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (he : emitR (prevPt C i) (vPt C i) (nextPt C i) σ) :
    SideAttach (chainModel C).W (C.chordSet (C.sideIdx C.sideBeta i) σ) (i + 6) 0 := by
  have hpt : sidePt (chainModel C).W (i + 6) 0 = C.vertex (C.sideIdx C.sideBeta i) := by
    rw [Chain.sidePt_zero]; exact walk_vtx_tour hi
  have hl := (corner_iff hDH hi hσ).2 he
  exact (FuseMath.sideAttach_chordSet hP (by rw [walk_n]; omega) (C.sideIdx_le _ _) hpt hσ hl).2

/-- **An emitted entry describes the vertex chord**, attached at both ends. -/
theorem entry_ok (hP : C.P.Simple) (hDH : DistinctHeights C.P) {i d : ℕ} (hi : i ≤ 2 * C.m)
    (he : Emit C i d) :
    (recOf (trip C i d)).toSet (chainModel C) C.P = C.chordSet (C.sideIdx C.sideBeta i) (sig d) ∧
      (recOf (trip C i d)).Attached (chainModel C) C.P ∧ (trip C i d).1 < C.P.n ∧
      C.DirFree (C.sideIdx C.sideBeta i) (sig d) := by
  set k := C.sideIdx C.sideBeta i with hkd
  have hk : k ≤ C.m := C.sideIdx_le _ _
  obtain ⟨hf, hvpos, hvA⟩ := vert_attach hP hDH hi (sig_cases d) he
  obtain ⟨-, hfpos, hfA⟩ := far_attach hDH hk (sig_cases d) hf
  have hvk : vPt C i = C.vertex k := rfl
  have hpos := C.chordParam_pos hk (sig_cases d) hf
  have hh : (C.P.vtx (C.edgeIdx k)).2 = (C.vertex k).2 := rfl
  have hn : (trip C i d).1 < C.P.n := by unfold trip; split_ifs <;> exact C.edgeIdx_lt _
  by_cases hd : d = 0
  · subst hd
    have hs : sig 0 = 1 := rfl
    rw [hs] at hf hfpos hfA hvA hpos ⊢
    have ht : trip C i 0 = (C.edgeIdx k, i + 6, farEdge C k 1) := rfl
    have hset : (recOf (trip C i 0)).toSet (chainModel C) C.P = C.chordSet k 1 := by
      rw [ht]
      unfold CRec.toSet recOf CRec.lpos CRec.rpos
      simp only
      rw [hvpos, hfpos, hvk, hh, C.chordSet_eq_hseg, min_eq_left, max_eq_right] <;>
        simp only [Chain.chordEnd_fst] <;> linarith
    refine ⟨hset, ?_, hn, hf⟩
    unfold CRec.Attached
    rw [hset, ht]
    exact ⟨hvA, hfA⟩
  · have hs : sig d = -1 := by unfold sig; rw [ite_eq_right hd]
    rw [hs] at hf hfpos hfA hvA hpos ⊢
    have ht : trip C i d = (C.edgeIdx k, farEdge C k (-1), i + 6) := by
      unfold trip; rw [ite_eq_right hd]
    have hset : (recOf (trip C i d)).toSet (chainModel C) C.P = C.chordSet k (-1) := by
      rw [ht]
      unfold CRec.toSet recOf CRec.lpos CRec.rpos
      simp only
      rw [hvpos, hfpos, hvk, hh, C.chordSet_eq_hseg, min_eq_right, max_eq_left] <;>
        simp only [Chain.chordEnd_fst] <;> linarith
    refine ⟨hset, ?_, hn, hf⟩
    unfold CRec.Attached
    rw [hset, ht]
    exact ⟨hfA, hvA⟩

theorem mem_bruteList {x : ℕ × ℕ × ℕ} :
    x ∈ bruteList C ↔ ∃ i d, i ≤ 2 * C.m ∧ d ≤ 1 ∧ Emit C i d ∧ x = trip C i d := by
  classical
  unfold bruteList
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, mem_entries]
  constructor
  · rintro ⟨e, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
    exact ⟨e.1, e.2, h1, h2, h3, rfl⟩
  · rintro ⟨i, d, h1, h2, h3, rfl⟩
    exact ⟨(i, d), ⟨⟨h1, h2⟩, h3⟩, rfl⟩

/-- Points of a vertex chord are at the height of the vertex. -/
theorem chordSet_snd {k : ℕ} {σ : ℝ} {p : Point} (hp : p ∈ C.chordSet k σ) :
    p.2 = (C.vertex k).2 := by
  obtain ⟨t, -, -, rfl⟩ := hp
  simp [Chain.chordEnd_snd]

/-- **Distinct emitted entries give distinct chords.** -/
theorem chord_inj (hP : C.P.Simple) (hDH : DistinctHeights C.P) {i d i' d' : ℕ}
    (hi : i ≤ 2 * C.m) (hd : d ≤ 1) (hi' : i' ≤ 2 * C.m) (hd' : d' ≤ 1) (he : Emit C i d)
    (he' : Emit C i' d')
    (heq : C.chordSet (C.sideIdx C.sideBeta i) (sig d) =
      C.chordSet (C.sideIdx C.sideBeta i') (sig d')) : i = i' ∧ d = d' := by
  set k := C.sideIdx C.sideBeta i
  set k' := C.sideIdx C.sideBeta i'
  have hk : k ≤ C.m := C.sideIdx_le _ _
  have hk' : k' ≤ C.m := C.sideIdx_le _ _
  have hkk : k = k' := by
    have hv : C.vertex k ∈ C.chordSet k (sig d) := Geometry.left_mem_segment _ _
    rw [heq] at hv
    have := chordSet_snd hv
    by_contra hne
    exact ChainObs.vertex_snd_ne hDH hk hk' hne this
  have hA := vert_attach0 hP hDH hi (sig_cases d) he
  have hA' := vert_attach0 hP hDH hi' (sig_cases d') he'
  rw [heq] at hA
  have hc : C.chordSet k' (sig d') ∈ (chainModel C).Adm := by
    obtain ⟨hf', -⟩ := (entry_ok hP hDH hi' he').2.2
    exact Merge.chords_subset_augChords C ⟨k', sig d', hk', sig_cases d', (entry_ok hP hDH hi' he').2.2.2, rfl⟩
  have hpt : sidePt (chainModel C).W (i + 6) 0 = sidePt (chainModel C).W (i' + 6) 0 := by
    rw [Chain.sidePt_zero, Chain.sidePt_zero, walk_vtx_tour hi, walk_vtx_tour hi']
    show C.vertex k = C.vertex k'
    rw [hkk]
  have hii := ((walkAx_chainModel hP).attach_unique hc hA hA' hpt).1
  have hii' : i = i' := by omega
  refine ⟨hii', ?_⟩
  subst hii'
  by_contra hne
  have hf := (entry_ok hP hDH hi he).2.2.2
  have hf' := (entry_ok hP hDH hi he').2.2.2
  have hsd : sig d ≠ sig d' := by
    unfold sig; split_ifs <;> first | omega | norm_num
  -- the east chord has a point east of the vertex, the west chord none
  have key : ∀ σ σ' : ℝ, (σ = 1 ∨ σ = -1) → (σ' = 1 ∨ σ' = -1) → σ ≠ σ' → C.DirFree k σ →
      C.DirFree k σ' → C.chordSet k σ ≠ C.chordSet k σ' := by
    intro σ σ' hσ hσ' hne' hfσ hfσ' hEq
    have hpos := C.chordParam_pos hk hσ hfσ
    have hpos' := C.chordParam_pos hk hσ' hfσ'
    have hend : C.chordEnd k σ ∈ C.chordSet k σ := Geometry.right_mem_segment _ _
    rw [hEq] at hend
    obtain ⟨t, ht0, ht1, hpt⟩ := hend
    have h1 := congrArg Prod.fst hpt
    simp only [Chain.chordEnd_fst] at h1
    rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl
    · exact hne' rfl
    · nlinarith
    · nlinarith
    · exact hne' rfl
  exact key _ _ (sig_cases d) (sig_cases d') hsd hf hf' heq

/-- Every chord of the list is a vertex chord. -/
theorem bruteList_sub (hP : C.P.Simple) (hDH : DistinctHeights C.P) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ bruteList C) : (recOf x).toSet (chainModel C) C.P ∈ C.chords := by
  obtain ⟨i, d, hi, -, he, rfl⟩ := mem_bruteList.1 hx
  obtain ⟨hset, -, -, hf⟩ := entry_ok hP hDH hi he
  rw [hset]
  exact ⟨_, _, C.sideIdx_le _ _, sig_cases d, hf, rfl⟩

/-- **The chord list is valid** (`ChordTriplesOK`). -/
theorem bruteList_ok (hP : C.P.Simple) (hDH : DistinctHeights C.P) :
    ChordTriplesOK (chainModel C) C.P (bruteList C) := by
  classical
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · refine ((bruteList C).finite_toSet.image fun x => (recOf x).toSet (chainModel C) C.P).subset ?_
    rintro c ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro c ⟨x, hx, rfl⟩
    exact Merge.chords_subset_augChords C (bruteList_sub hP hDH hx)
  · rintro c ⟨x, hx, rfl⟩
    obtain ⟨i, d, hi, -, he, rfl⟩ := mem_bruteList.1 hx
    exact ⟨_, (entry_ok hP hDH hi he).2.2.1, _, _, rfl⟩
  · unfold bruteList
    rw [List.map_map]
    refine List.Nodup.map_on ?_ ((entries_nodup C.m).filter _)
    rintro ⟨i, d⟩ he ⟨i', d'⟩ he' heq
    simp only [List.mem_filter, decide_eq_true_eq, mem_entries] at he he'
    simp only [Function.comp] at heq
    rw [(entry_ok hP hDH he.1.1 he.2).1, (entry_ok hP hDH he'.1.1 he'.2).1] at heq
    obtain ⟨h1, h2⟩ := chord_inj hP hDH he.1.1 he.1.2 he'.1.1 he'.1.2 he.2 he'.2 heq
    rw [h1, h2]
  · intro x hx
    obtain ⟨i, d, hi, -, he, rfl⟩ := mem_bruteList.1 hx
    exact (entry_ok hP hDH hi he).2.1
  · intro x hx
    obtain ⟨i, d, hi, -, he, rfl⟩ := mem_bruteList.1 hx
    exact (entry_ok hP hDH hi he).2.2.1

/-- **The chords of the list are exactly the full map.** -/
theorem bruteList_set (hP : C.P.Simple) (hDH : DistinctHeights C.P) :
    {c | ∃ x ∈ bruteList C, c = (recOf x).toSet (chainModel C) C.P} = C.chords := by
  ext c
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact bruteList_sub hP hDH hx
  · intro hc
    obtain ⟨k, σ, hk, hσ, hf, rfl⟩ := hc
    have hcA : C.chordSet k σ ∈ (chainModel C).Adm :=
      Merge.chords_subset_augChords C ⟨k, σ, hk, hσ, hf, rfl⟩
    obtain ⟨a, b, -, hcab, -, hopen, hWa, hWb⟩ := (walkAx_chainModel hP).ends _ hcA
    -- the vertex is an endpoint
    have hvD : C.vertex k ∉ C.dom := fun h => C.not_mem_set_of_mem_dom h (C.vertex_mem_set hk)
    have hvab : C.vertex k = a ∨ C.vertex k = b := by
      have hv : C.vertex k ∈ C.chordSet k σ := Geometry.left_mem_segment _ _
      rw [hcab] at hv
      obtain ⟨s, hs0, hs1, hs⟩ := Geometry.mem_segment_iff_lerp.1 hv
      rcases hs0.lt_or_eq with hs0 | hs0
      · rcases hs1.lt_or_eq with hs1 | hs1
        · exact absurd (hs ▸ hopen s ⟨hs0, hs1⟩) hvD
        · right; rw [hs, hs1, Geometry.lerp_one]
      · left; rw [hs, ← hs0, Geometry.lerp_zero]
    have hWv : WalkEnd (chainModel C).W (C.chordSet k σ) (C.vertex k) := by
      rcases hvab with h | h <;> rw [h] <;> assumption
    obtain ⟨p, t, hA, hpt⟩ := hWv.1
    obtain ⟨hp, ht0, ht1, -, r, hr, hloc⟩ := hA
    obtain ⟨rfl, i, hi, rfl, hik⟩ := pos_of_vertex hP hp ht0 ht1 hk hpt
    -- the direction is in the left sector
    have hpos := C.chordParam_pos hk hσ hf
    set ε := min (r / 2) (C.chordParam k σ) with hε
    have hε0 : 0 < ε := lt_min (by linarith) hpos
    have hmem : rayPt (C.vertex k) σ ε ∈ C.chordSet k σ := by
      rw [C.chordSet_eq_image hk hσ hf]
      exact ⟨ε, ⟨hε0.le, min_le_right _ _⟩, rfl⟩
    have hne : rayPt (C.vertex k) σ ε ≠ C.vertex k := by
      intro e
      have := congrArg Prod.fst e
      simp only [Visibility.rayPt_fst] at this
      rcases hσ with rfl | rfl <;> linarith
    have hdist : dist (rayPt (C.vertex k) σ ε) (C.vertex k) < r := by
      rw [FuseMath.dist_rayPt _ hσ hε0.le]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hl := hloc _ hmem (by rw [hpt]; exact hne) (by rw [hpt]; exact hdist)
    rw [← hpt, FuseMath.sideLeft_rayPt hε0, hpt] at hl
    have hvi : C.vertex k = vPt C i := by unfold vPt; rw [hik]
    rw [hvi] at hl
    have hemit := (corner_iff hDH hi hσ).1 hl
    -- the entry
    obtain ⟨d, hd, hsd⟩ : ∃ d, d ≤ 1 ∧ sig d = σ := by
      rcases hσ with rfl | rfl
      · exact ⟨0, by omega, rfl⟩
      · exact ⟨1, le_rfl, rfl⟩
    have he : Emit C i d := by unfold Emit; rw [hsd]; exact hemit
    refine ⟨trip C i d, mem_bruteList.2 ⟨i, d, hi, hd, he, rfl⟩, ?_⟩
    rw [(entry_ok hP hDH hi he).1, hsd, hik]

end Brute

end

end Chazelle.Core
