module

public import Chazelle.Core.DownPhaseDrvSplice
public import Chazelle.Core.RestoreSearchArc

/-!
# Down-phase restoration rounds (D8), part 1: the arcs of `buildNF` and the buckets of new events

The restoration rounds of a down-phase level (design `docs/design-downphase-driver.md` §4.3)
splice the events of the new chords into the sorted event list `E` with the splice of the level
driver (`DrvR.splice_meets`), which sorts the new codes by **buckets**: a bucket number per new
event code, such that a smaller bucket means an earlier event (`codeLe`), with a bounded number of
codes per bucket.  The bucket of a new chord end `x` is read off the arc of `N = buildNF M Q L E`
on which `x` lies (`A` arcs, the last one wrapping around the start of the walk):

* `0`: `key x` at most the end of the last arc (the first event key);
* `j + 1` (`j + 1 < A`): `x` on the closed arc `j`;
* `A`: `key x` at least the start of the last arc (the last event key).

`BktKey` is this condition.  Main results:

* `kE_mono`: the event keys are nondecreasing along `E`;
* `arc_s`, `arc_e`, `key_s_lt_e`, `key_e_last`, `key_s_last`: the arcs of `buildNF` are the gaps of
  `E` (S-M1, `DownDrv.buildNF_arc`) in key order, the last one wrapping;
* `bktKey_le`: a smaller bucket has a smaller key, through an event key of `E`;
* `three_attach`: three admissible chords attached at one walk position are not distinct;
* **`codeLe_of_bkt`**: for the codes of the new chords `L₂` appended to `L`, a smaller bucket
  means `codeLe` (equal keys are impossible: the old event in between would be a third chord
  attached at the same position).
-/

namespace Chazelle.Core

namespace DrvD

@[expose] public section

open BuildNF (codeLe wposOf tieBit buildNF gapStarts arcRec arcList evs evOf)
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Geometry (point_ext)

variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-! ## Event keys -/

/-- The key of the event at index `i` of the event list. -/
noncomputable def kE (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (i : ℕ) : ℝ :=
  M.key Q (wposOf L (E.getD i 0))

theorem kap_evs {m : ℕ} (hm : m < E.length) :
    BuildSort.kap (evs M Q L E) m = kE M Q L E m := by
  have hm' : m < (evs M Q L E).length := by simp [evs, hm]
  rw [BuildSort.kap_eq hm']
  simp only [evs, List.getElem_map]
  unfold kE evOf wposOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]
  split_ifs <;> rfl

/-- **The event keys are nondecreasing** along a `codeLe`-sorted list. -/
theorem kE_mono (hsort : E.Pairwise (codeLe M Q L)) {i i' : ℕ} (hii : i ≤ i')
    (hi' : i' < E.length) : kE M Q L E i ≤ kE M Q L E i' := by
  rcases Nat.eq_or_lt_of_le hii with rfl | hlt
  · exact le_rfl
  · have h := List.pairwise_iff_getElem.1 hsort i i' (by omega) hi' hlt
    unfold kE
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    rcases h with h | ⟨h, -⟩
    · exact h.le
    · exact h.le

/-! ## The gap starts -/

/-- The start index (in `E`) of gap `j`. -/
noncomputable def gs (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (j : ℕ) : ℕ :=
  (gapStarts M Q L E).getD j 0

theorem mem_gapStarts {m : ℕ} : m ∈ gapStarts M Q L E ↔ m < E.length ∧
    (m + 1 = E.length ∨ BuildSort.kap (evs M Q L E) m < BuildSort.kap (evs M Q L E) (m + 1)) := by
  unfold gapStarts
  simp

theorem gapStarts_pairwise : (gapStarts M Q L E).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

theorem gs_eq {j : ℕ} (hj : j < (gapStarts M Q L E).length) :
    gs M Q L E j = (gapStarts M Q L E)[j] := by
  unfold gs; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

theorem gs_mem {j : ℕ} (hj : j < (gapStarts M Q L E).length) :
    gs M Q L E j ∈ gapStarts M Q L E := by
  rw [gs_eq hj]; exact List.getElem_mem hj

theorem gs_lt_len {j : ℕ} (hj : j < (gapStarts M Q L E).length) : gs M Q L E j < E.length :=
  (mem_gapStarts.1 (gs_mem hj)).1

theorem gs_lt_gs {j j' : ℕ} (hjj : j < j') (hj' : j' < (gapStarts M Q L E).length) :
    gs M Q L E j < gs M Q L E j' := by
  rw [gs_eq (by omega), gs_eq hj']
  exact List.pairwise_iff_getElem.1 gapStarts_pairwise j j' (by omega) hj' hjj

/-- **The last gap starts at the last event.** -/
theorem gs_last (hE : 0 < E.length) :
    0 < (gapStarts M Q L E).length ∧
      gs M Q L E ((gapStarts M Q L E).length - 1) = E.length - 1 := by
  have hmem : E.length - 1 ∈ gapStarts M Q L E := mem_gapStarts.2 ⟨by omega, Or.inl (by omega)⟩
  obtain ⟨j₀, hj₀, hj₀e⟩ := List.mem_iff_getElem.1 hmem
  have hA : 0 < (gapStarts M Q L E).length := by omega
  refine ⟨hA, ?_⟩
  have h0 : gs M Q L E j₀ = E.length - 1 := by rw [gs_eq hj₀]; exact hj₀e
  by_contra hne
  have hlt : j₀ < (gapStarts M Q L E).length - 1 := by
    rcases Nat.lt_or_ge j₀ ((gapStarts M Q L E).length - 1) with h | h
    · exact h
    · exact absurd (by rw [show (gapStarts M Q L E).length - 1 = j₀ by omega]; exact h0) hne
  have h1 := gs_lt_gs (M := M) (Q := Q) (L := L) (E := E) hlt (by omega)
  have h2 := gs_lt_len (M := M) (Q := Q) (L := L) (E := E)
    (j := (gapStarts M Q L E).length - 1) (by omega)
  omega

/-- **A gap other than the last one** ends at the next event, with a larger key. -/
theorem gs_succ (hE : 0 < E.length) {j : ℕ} (hj : j + 1 < (gapStarts M Q L E).length) :
    gs M Q L E j + 1 < E.length ∧ kE M Q L E (gs M Q L E j) < kE M Q L E (gs M Q L E j + 1) := by
  obtain ⟨-, hlast⟩ := gs_last (M := M) (Q := Q) (L := L) hE
  have h1 := gs_lt_gs (M := M) (Q := Q) (L := L) (E := E)
    (j := j) (j' := (gapStarts M Q L E).length - 1) (by omega) (by omega)
  rw [hlast] at h1
  refine ⟨by omega, ?_⟩
  rcases (mem_gapStarts.1 (gs_mem (M := M) (Q := Q) (L := L) (E := E) (by omega : j <
    (gapStarts M Q L E).length))).2 with h | h
  · omega
  · rwa [kap_evs (by omega), kap_evs (by omega)] at h

/-! ## The arcs of `buildNF` -/

theorem arcs_length (hK : 0 < L.length) :
    (buildNF M Q L E).arcs.length = (gapStarts M Q L E).length := by
  rw [DownDrv.buildNF_arcs hK, List.length_map]

theorem arc_s (hK : 0 < L.length) {j : ℕ} (hj : j < (gapStarts M Q L E).length) :
    ((buildNF M Q L E).arc j).s = wposOf L (E.getD (gs M Q L E j) 0) := by
  have h := DownDrv.buildNF_arc (M := M) (Q := Q) (L := L) (E := E) hK hj
  unfold NF.arc
  rw [h]
  rfl

theorem arc_e (hK : 0 < L.length) {j : ℕ} (hj : j < (gapStarts M Q L E).length) :
    ((buildNF M Q L E).arc j).e = wposOf L (E.getD ((gs M Q L E j + 1) % E.length) 0) := by
  have h := DownDrv.buildNF_arc (M := M) (Q := Q) (L := L) (E := E) hK hj
  unfold NF.arc
  rw [h]
  rfl

theorem key_s (hK : 0 < L.length) {j : ℕ} (hj : j < (gapStarts M Q L E).length) :
    M.key Q ((buildNF M Q L E).arc j).s = kE M Q L E (gs M Q L E j) := by
  rw [arc_s hK hj]; rfl

/-- The end of an arc other than the last one is the next event. -/
theorem key_e (hK : 0 < L.length) (hE : 0 < E.length) {j : ℕ}
    (hj : j + 1 < (gapStarts M Q L E).length) :
    M.key Q ((buildNF M Q L E).arc j).e = kE M Q L E (gs M Q L E j + 1) := by
  rw [arc_e hK (by omega), Nat.mod_eq_of_lt (gs_succ hE hj).1]; rfl

/-- **An arc other than the last one does not wrap.** -/
theorem key_s_lt_e (hK : 0 < L.length) (hE : 0 < E.length) {j : ℕ}
    (hj : j + 1 < (gapStarts M Q L E).length) :
    M.key Q ((buildNF M Q L E).arc j).s < M.key Q ((buildNF M Q L E).arc j).e := by
  rw [key_s hK (by omega), key_e hK hE hj]; exact (gs_succ hE hj).2

/-- The last arc ends at the first event. -/
theorem key_e_last (hK : 0 < L.length) (hE : 0 < E.length) :
    M.key Q ((buildNF M Q L E).arc ((gapStarts M Q L E).length - 1)).e = kE M Q L E 0 := by
  obtain ⟨hA, hlast⟩ := gs_last (M := M) (Q := Q) (L := L) hE
  rw [arc_e hK (by omega), hlast, Nat.sub_add_cancel hE, Nat.mod_self]; rfl

/-- The last arc starts at the last event. -/
theorem key_s_last (hK : 0 < L.length) (hE : 0 < E.length) :
    M.key Q ((buildNF M Q L E).arc ((gapStarts M Q L E).length - 1)).s =
      kE M Q L E (E.length - 1) := by
  obtain ⟨hA, hlast⟩ := gs_last (M := M) (Q := Q) (L := L) hE
  rw [key_s hK (by omega), hlast]

/-! ## Buckets -/

/-- **The bucket condition** of a key `x` for the bucket `b` of the normal form `N` (`A` arcs):
`b = 0`: `x` at most the end of the last arc; `1 ≤ b < A`: `x` on the closed arc `b - 1`;
`b = A`: `x` at least the start of the last arc. -/
def BktKey (M : Model) (Q : Polygon) (N : NF) (x : ℝ) (b : ℕ) : Prop :=
  (b = 0 ∧ x ≤ M.key Q (N.arc (N.arcs.length - 1)).e) ∨
  (1 ≤ b ∧ b < N.arcs.length ∧ M.key Q (N.arc (b - 1)).s ≤ x ∧
    x ≤ M.key Q (N.arc (b - 1)).e) ∨
  (b = N.arcs.length ∧ M.key Q (N.arc (N.arcs.length - 1)).s ≤ x)

theorem BktKey.le {N : NF} {x : ℝ} {b : ℕ} (h : BktKey M Q N x b) : b ≤ N.arcs.length := by
  rcases h with ⟨rfl, -⟩ | ⟨-, h, -⟩ | ⟨rfl, -⟩ <;> omega

/-- **A smaller bucket has a smaller key**, through an event key of `E`. -/
theorem bktKey_le (hK : 0 < L.length) (hE : 0 < E.length) (hsort : E.Pairwise (codeLe M Q L))
    {x y : ℝ} {b b' : ℕ} (hx : BktKey M Q (buildNF M Q L E) x b)
    (hy : BktKey M Q (buildNF M Q L E) y b') (hbb : b < b') :
    ∃ i, i < E.length ∧ x ≤ kE M Q L E i ∧ kE M Q L E i ≤ y := by
  have hA := arcs_length (M := M) (Q := Q) (E := E) hK
  obtain ⟨hA0, hlast⟩ := gs_last (M := M) (Q := Q) (L := L) hE
  -- the lower bound of `y`'s bucket
  have hlow : ∀ i, (b' < (gapStarts M Q L E).length → i ≤ gs M Q L E (b' - 1)) →
      i ≤ E.length - 1 → 1 ≤ b' → kE M Q L E i ≤ y := by
    intro i hi hi' hb1
    rcases hy with ⟨rfl, -⟩ | ⟨-, hb2, hs, -⟩ | ⟨hbA, hs⟩
    · omega
    · rw [hA] at hb2
      rw [key_s hK (by omega)] at hs
      exact le_trans (kE_mono hsort (hi hb2) (gs_lt_len (by omega))) hs
    · rw [hA, key_s_last hK hE] at hs
      exact le_trans (kE_mono hsort hi' (by omega)) hs
  rcases hx with ⟨rfl, hx⟩ | ⟨hb1, hb2, -, hx⟩ | ⟨hbA, -⟩
  · rw [hA, key_e_last hK hE] at hx
    exact ⟨0, hE, hx, hlow 0 (fun _ => Nat.zero_le _) (Nat.zero_le _) (by omega)⟩
  · rw [hA] at hb2
    have hj : b - 1 + 1 < (gapStarts M Q L E).length := by omega
    rw [show b - 1 = b - 1 from rfl, key_e hK hE hj] at hx
    have hsucc := gs_succ (M := M) (Q := Q) (L := L) hE hj
    refine ⟨gs M Q L E (b - 1) + 1, hsucc.1, hx, hlow _ (fun hb' => ?_) (by omega) (by omega)⟩
    have := gs_lt_gs (M := M) (Q := Q) (L := L) (E := E) (j := b - 1) (j' := b' - 1)
      (by omega) (by omega)
    omega
  · exfalso
    have := hy.le
    rw [hbA] at hbb
    omega

/-! ## Three chords at one position -/

/-- **Three admissible chords attached at one walk position are not distinct**: each leaves the
position horizontally, to the east or to the west, and two leaving in the same direction are equal
(`Restore.ray_eq`). -/
theorem three_attach (hM : WalkAx M) {c₁ c₂ c₃ : Set Point} (h₁ : c₁ ∈ M.Adm) (h₂ : c₂ ∈ M.Adm)
    (h₃ : c₃ ∈ M.Adm) {p : ℕ} {t : ℝ} (a₁ : SideAttach M.W c₁ p t) (a₂ : SideAttach M.W c₂ p t)
    (a₃ : SideAttach M.W c₃ p t) : c₁ = c₂ ∨ c₁ = c₃ ∨ c₂ = c₃ := by
  obtain ⟨o₁, ho₁, ho₁2, hc₁, ho₁D, ho₁o⟩ := Restore.attach_ray hM h₁ a₁
  obtain ⟨o₂, ho₂, ho₂2, hc₂, ho₂D, ho₂o⟩ := Restore.attach_ray hM h₂ a₂
  obtain ⟨o₃, ho₃, ho₃2, hc₃, ho₃D, ho₃o⟩ := Restore.attach_ray hM h₃ a₃
  set w := sidePt M.W p t
  have hd : ∀ o : Point, o ≠ w → o.2 = w.2 → o.1 - w.1 ≠ 0 := fun o ho ho2 h0 =>
    ho (point_ext (by linarith) ho2)
  have d₁ := hd o₁ ho₁ ho₁2
  have d₂ := hd o₂ ho₂ ho₂2
  have d₃ := hd o₃ ho₃ ho₃2
  rcases lt_or_gt_of_ne (mul_ne_zero d₁ d₂) with h12 | h12
  · rcases lt_or_gt_of_ne (mul_ne_zero d₁ d₃) with h13 | h13
    · right; right
      have h23 : 0 < (o₂.1 - w.1) * (o₃.1 - w.1) := by
        have := mul_pos_of_neg_of_neg h12 h13
        have e : (o₁.1 - w.1) * (o₂.1 - w.1) * ((o₁.1 - w.1) * (o₃.1 - w.1)) =
          (o₁.1 - w.1) ^ 2 * ((o₂.1 - w.1) * (o₃.1 - w.1)) := by ring
        rw [e] at this
        exact pos_of_mul_pos_right this (sq_nonneg _)
      rw [hc₂, hc₃, Restore.ray_eq ho₂2 ho₃2 h23 ho₂D ho₃D ho₂o ho₃o]
    · right; left
      rw [hc₁, hc₃, Restore.ray_eq ho₁2 ho₃2 h13 ho₁D ho₃D ho₁o ho₃o]
  · left
    rw [hc₁, hc₂, Restore.ray_eq ho₁2 ho₂2 h12 ho₁D ho₂D ho₁o ho₂o]

/-- **Equal keys of event positions are equal positions** (edge and parameter). -/
theorem pos_eq_of_key (hok : ChordTriplesOK M Q L) {a a' : ℕ} (ha : a < 2 * L.length)
    (ha' : a' < 2 * L.length) (h : M.key Q (wposOf L a) = M.key Q (wposOf L a')) :
    (wposOf L a).edge = (wposOf L a').edge ∧ M.param Q (wposOf L a) = M.param Q (wposOf L a') := by
  obtain ⟨-, t0, t1, -⟩ := BuildNF.attach_wposOf hok ha
  obtain ⟨-, t0', t1', -⟩ := BuildNF.attach_wposOf hok ha'
  unfold Model.key at h
  have h1 : ((wposOf L a).edge : ℝ) < (wposOf L a').edge + 1 := by linarith
  have h2 : ((wposOf L a').edge : ℝ) < (wposOf L a).edge + 1 := by linarith
  have h1' : (wposOf L a).edge < (wposOf L a').edge + 1 := by exact_mod_cast h1
  have h2' : (wposOf L a').edge < (wposOf L a).edge + 1 := by exact_mod_cast h2
  have he : (wposOf L a).edge = (wposOf L a').edge := by omega
  refine ⟨he, ?_⟩
  rw [he] at h; linarith

/-- The chords of a valid list are admissible. -/
theorem chordSet_adm (hok : ChordTriplesOK M Q L) {k : ℕ} (hk : k < L.length) :
    BuildOrder.chordSet M Q L k ∈ M.Adm :=
  hok.1.2.1 ⟨L.getD k (0, 0, 0), BuildOrder.getD_mem hk, rfl⟩

/-- **A smaller bucket means an earlier event** for the codes of new chords `L₂` appended to `L`:
the keys are ordered through an event key of `E`; equal keys would put three distinct chords (or
both ends of one chord) at one walk position. -/
theorem codeLe_of_bkt (hM : WalkAx M) {L₂ : List (ℕ × ℕ × ℕ)} (hok : ChordTriplesOK M Q (L ++ L₂))
    (hK : 0 < L.length) (hperm : E.Perm (List.range (2 * L.length)))
    (hsort : E.Pairwise (codeLe M Q L)) {a a' b b' : ℕ} (ha : 2 * L.length ≤ a)
    (ha2 : a < 2 * (L ++ L₂).length) (ha' : 2 * L.length ≤ a') (ha2' : a' < 2 * (L ++ L₂).length)
    (hx : BktKey M Q (buildNF M Q L E) (M.key Q (wposOf (L ++ L₂) a)) b)
    (hy : BktKey M Q (buildNF M Q L E) (M.key Q (wposOf (L ++ L₂) a')) b') (hbb : b < b') :
    codeLe M Q (L ++ L₂) a a' := by
  have hElen : E.length = 2 * L.length := by rw [hperm.length_eq, List.length_range]
  obtain ⟨i, hi, hxi, hiy⟩ := bktKey_le hK (by omega) hsort hx hy hbb
  rcases lt_or_eq_of_le (hxi.trans hiy) with hlt | heq
  · exact Or.inl hlt
  by_cases haa : a = a'
  · subst haa; exact Or.inr ⟨rfl, le_rfl⟩
  exfalso
  have hlen : (L ++ L₂).length = L.length + L₂.length := List.length_append
  -- the old event
  have hc₀ : E.getD i 0 < 2 * L.length := by
    have hmem : E.getD i 0 ∈ E := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.getElem_mem hi
    simpa using hperm.mem_iff.1 hmem
  have hc₀' : E.getD i 0 < 2 * (L ++ L₂).length := by rw [hlen]; omega
  have hkc : M.key Q (wposOf (L ++ L₂) (E.getD i 0)) = kE M Q L E i := by
    rw [DownDrv.wposOf_append hc₀]; rfl
  have hxa : M.key Q (wposOf (L ++ L₂) a) = M.key Q (wposOf (L ++ L₂) (E.getD i 0)) := by
    rw [hkc]; linarith
  have hya : M.key Q (wposOf (L ++ L₂) a') = M.key Q (wposOf (L ++ L₂) (E.getD i 0)) := by
    rw [hkc]; linarith
  obtain ⟨e1, p1⟩ := pos_eq_of_key hok ha2 hc₀' hxa
  obtain ⟨e2, p2⟩ := pos_eq_of_key hok ha2' hc₀' hya
  by_cases hii : a / 2 = a' / 2
  · -- the two ends of one chord are distinct points
    have hpos : M.pos Q (wposOf (L ++ L₂) a) = M.pos Q (wposOf (L ++ L₂) a') := by
      unfold Model.pos; rw [e1, p1, e2, p2]
    have hlt := BuildNF.pos_lt' (M := M) (Q := Q) (L := L ++ L₂) hM hok (i := a / 2) (by omega)
    rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
    · have h1' : a' % 2 = 1 := by omega
      rw [BuildNF.wposOf_even h0, BuildNF.wposOf_odd h1', ← hii] at hpos
      rw [hpos] at hlt; exact lt_irrefl _ hlt
    · have h0' : a' % 2 = 0 := by omega
      rw [BuildNF.wposOf_odd h1, BuildNF.wposOf_even h0', ← hii] at hpos
      rw [hpos] at hlt; exact lt_irrefl _ hlt
  · have A₀ := BuildNF.attach_wposOf hok hc₀'
    have A₁ := BuildNF.attach_wposOf hok ha2
    have A₂ := BuildNF.attach_wposOf hok ha2'
    rw [e1, p1] at A₁
    rw [e2, p2] at A₂
    rcases three_attach hM (chordSet_adm hok (by omega)) (chordSet_adm hok (by omega))
        (chordSet_adm hok (by omega)) A₀ A₁ A₂ with h | h | h
    · have := BuildOrder.chordSet_inj hok (by omega) (by omega) h; omega
    · have := BuildOrder.chordSet_inj hok (by omega) (by omega) h; omega
    · exact hii (BuildOrder.chordSet_inj hok (by omega) (by omega) h)

end

end DrvD

end Chazelle.Core
