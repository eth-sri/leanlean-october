module

public import Chazelle.MacT
public import Chazelle.Core.GranInitL5
public import Chazelle.Core.FuseMathCut
public import Chazelle.Core.NFDecompBfs
public import Chazelle.Core.ShootCutDyDn
public import Chazelle.Core.OracleBook
public import Chazelle.Core.SpecNF
public import Chazelle.Core.FactsAttach
public import Chazelle.Core.GranRamBody
public import Chazelle.Core.DownPhaseRegionBox

namespace Chazelle.Core
namespace BuildSort
@[expose] public section
open List

/-- The key of the `m`-th event. -/
noncomputable def kap (S : List Ev) (m : ℕ) : ℝ := (S.getD m ztt).2.1
theorem kap_eq {S : List Ev} {m : ℕ} (hm : m < S.length) : kap S m = (S[m]).2.1 := by
  zumtd

/-- Every event is at some index. -/
theorem index_of_mem {S : List Ev} {e : Ev} (he : e ∈ S) : ∃ k < S.length, kap S k = e.2.1 := by
  obtain ⟨k, hk, rfl⟩ := mem_iff_getElem.1 he
  exact ⟨k, hk, kap_eq hk⟩

/-- The key at an index is an event key. -/
theorem kap_mem {S : List Ev} {m : ℕ} (hm : m < S.length) : ∃ e ∈ S, e.2.1 = kap S m :=
  ⟨S[m], getElem_mem hm, (kap_eq hm).symm⟩
variable {n : ℝ}
/-- **Keys are sorted along the list.** -/
theorem kap_mono {S : List Ev} (hs : S.Pairwise ztdym) {i j : ℕ} (hij : i ≤ j)
    (hj : j < S.length) : kap S i ≤ kap S j := by
  rcases hij.lt_or_eq with h | rfl
  · rw [kap_eq (h.trans hj), kap_eq hj]
    exact key_le_of_evLe (pairwise_iff_getElem.1 hs i j _ hj h)
  simp

/-- The events up to index `m` have keys at most `kap S m`, those after at least `kap S (m+1)`. -/
theorem key_le_or_ge {S : List Ev} (hs : S.Pairwise ztdym) {m : ℕ}
    (hm : m + 1 < S.length) {e : Ev} (he : e ∈ S) : e.2.1 ≤ kap S m ∨ kap S ztbl ≤ e.2.1 := by
  obtain ⟨k, hk, hke⟩ := index_of_mem he
  rw [← hke]
  rcases Nat.lt_or_ge m k with h | h
  · exact Or.inr (kap_mono hs h hk)
  · exact Or.inl (kap_mono hs h by_omega)

/-- **The number of events below a key inside a gap.** -/
theorem cntBelow_gap {S : List Ev} (hs : S.Pairwise ztdym) {m : ℕ}
    (hm : m + 1 < S.length) {y : ℝ} (h1 : kap S m < y) (h2 : y < kap S ztbl) :
    cntBelow S y = m + 1 := by
  zujqi
  rw [← take_append_drop ztbl S, countP_append]
  have ht : (S.take ztbl).countP ztdnx = m + 1 := by
    rw [countP_eq_length.2, length_take, min_eq_left by_omega]
    zuge
    obtain ⟨j, hj, rfl⟩ := mem_take_iff_getElem.1 ha
    have := kap_mono hs (show j ≤ m by omega) by_omega
    rw [kap_eq (by omega : j < S.length)] at this
    grind
  have hd : (S.drop ztbl).countP ztdnx = 0 := by
    zummc
    zuge
    obtain ⟨j, hj, rfl⟩ := mem_drop_iff_getElem.1 ha
    have hj' : m + 1 + j < S.length := by_omega
    have := kap_mono hs (show m + 1 ≤ m + 1 + j by omega) hj'
    rw [kap_eq hj'] at this
    grind
  omega

/-- No event below the first key. -/
theorem cntBelow_first {S : List Ev} (hs : S.Pairwise ztdym)
    {y : ℝ} (hy : y < kap S 0) : cntBelow S y = 0 := by
  zujqi
  zummc
  zuge
  zufyq
  have := kap_mono hs ztvai hk
  grind

/-- Every event below a key above the last key. -/
theorem cntBelow_last {S : List Ev} (hs : S.Pairwise ztdym) (hS : 0 < S.length)
    {y : ℝ} (hy : kap S ztdgf < y) : cntBelow S y = S.length := by
  zujqi
  rw [countP_eq_length]
  zuge
  zufyq
  have := kap_mono hs ztmob by_omega
  grind
end
end BuildSort
namespace BuildRegions
@[expose] public section
open Set List
open Chazelle.Chain (SideAttach sideInArc sidePt sideKey_inj TouchesIn)
open BuildSort (Ev EvLe cycDist cntBelow kap)
open BuildOrder (events evPair chordSet mem_events event_data getD_mem chordSet_inj chordSet_mem)
variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {S : List Ev}
namespace Ctx
variable (h : Ctx M Q L S)
include h

/-- **The cut keys are the event keys.** -/
theorem isCut_iff {k : ℝ} : M.IsCut zthh k ↔ ∃ e ∈ S, e.2.1 = k := by
  constructor
  · rintro ⟨c, hc, p, t, hA, rfl⟩
    zufyp
    have hL := h.attL hj
    have hR := h.attR hj
    obtain ⟨e, -, -, -, -, -, hoth⟩ := h.walk.attach_other_end ztxxg hL
    have hRe := hoth _ _ hR (Ne.symm (h.pts_ne hj))
    by_cases hpt : sidePt M.W p t = sidePt M.W (crec L j).lp (M.param Q (crec L j).lpos)
    · obtain ⟨rfl, rfl⟩ := h.walk.attach_unique ztxxg hA hL hpt
      exact ⟨_, h.eL_mem hj, rfl⟩
    · have hpt' : sidePt M.W p t = sidePt M.W (crec L j).rp (M.param Q (crec L j).rpos) := by
        grind
      obtain ⟨rfl, rfl⟩ := h.walk.attach_unique ztxxg hA hR hpt'
      exact ⟨_, h.eR_mem hj, rfl⟩
  · zuecl
    zukr
    exact h.key_ne_of_not_cut hc e he rfl

/-- The keys of the events are in `[0, n)`. -/
theorem key_bounds_mem {e : Ev} (he : e ∈ S) : 0 ≤ e.2.1 ∧ e.2.1 < M.W.n := by
  obtain ⟨hi, hc⟩ := h.mem_cases he
  rcases hc with hc | hc <;> zvnmd
  · exact h.kl_bounds hi
  · exact h.kr_bounds hi
variable {m : ℕ}
theorem kap_bounds (hm : m < S.length) : 0 ≤ kap S m ∧ kap S m < M.W.n := by
  obtain ⟨e, he, hk⟩ := BuildSort.kap_mem hm
  zunki; exact h.key_bounds_mem he
theorem kap_cut (hm : m < S.length) : M.IsCut zthh ztjzi :=
  h.isCut_iff.2 (BuildSort.kap_mem hm)
theorem length_S : S.length = 2 * L.length := by
  rw [h.perm.length_eq]
  unfold events
  rw [length_flatMap]
  have : ∀ i ∈ List.range L.length, (evPair M Q L i).length = 2 := fun i _ => rfl
  rw [List.map_congr_left this, map_const', length_range, sum_replicate, smul_eq_mul, mul_comm]

/-- **A gap is an arc** of the region of its label. -/
theorem arc_of_gap (hm : m + 1 < S.length) (hlt : kap S m < kap S ztbl) :
    M.IsArc zthh (reg M Q L S (BuildStack.label ztbuq ztbl))
      ztjzi ztyrd := by
  have ha := h.kap_bounds (m := m) by_omega
  have hb := h.kap_bounds hm
  have hin : ∀ x, sideInArc ztjzi ztyrd x ↔ kap S m < x ∧ x < kap S ztbl := by
    zujbv
  have hnocut : ∀ x, sideInArc ztjzi ztyrd x → ¬ M.IsCut zthh x := by
    zumhr
    zubik
    zufxv
    rcases BuildSort.key_le_or_ge h.sorted hm he with h1 | h1 <;> linarith [hx.1, hx.2]
  refine ⟨ha.1, ha.2, hb.1, hb.2, Or.inl ⟨h.kap_cut by_omega, h.kap_cut hm, hlt.ne⟩, hnocut,
    fun p t hp ht0 ht1 hx => ?_⟩
  zukbn
  have hf := (h.faces_reg hp by_simp_all hcut).2
  zubik
  zumss
  rwa [BuildSort.cntBelow_gap h.sorted hm hx.1 hx.2] at hf

/-- The label of the full word and of the empty prefix is the root. -/
theorem label_ends : BuildStack.label ztbuq 0 = none ∧
    BuildStack.label ztbuq S.length = none := by
  obtain ⟨hnc, htw⟩ := h.word
  zubee
  unfold BuildStack.label
  rw [← length_map, take_length, BuildStack.run_eq_nil htw hnc]
  rfl

/-- **The wrapping gap is an arc of the root region.** -/
theorem arc_of_wrap (hK : 0 < L.length) :
    M.IsArc zthh ztpdn ztyre ztoce := by
  have hlen := h.length_S
  have hS : 0 < S.length := by_omega
  have ha := h.kap_bounds (m := S.length - 1) by_omega
  have hb := h.kap_bounds hS
  -- the first key is below the last one
  have hlt : kap S 0 < kap S ztdgf := by
    obtain ⟨k1, hk1, e1k⟩ := BuildSort.index_of_mem (h.e1_mem hK)
    obtain ⟨k2, hk2, e2k⟩ := BuildSort.index_of_mem (h.e2_mem hK)
    have := BuildSort.kap_mono h.sorted (Nat.zero_le k1) hk1
    have := BuildSort.kap_mono h.sorted (show k2 ≤ S.length - 1 by omega) by_omega
    simp only [e1, e2] at e1k e2k
    linarith [h.lo_lt_hi hK]
  have hin : ∀ x, sideInArc ztyre ztoce x ↔
      kap S ztdgf < x ∨ x < kap S 0 := by
    zujbu
  have hnocut : ∀ x, sideInArc ztyre ztoce x →
      ¬ M.IsCut zthh x := by
    zumhr
    zubik
    zufxv
    obtain ⟨k, hk, hke⟩ := BuildSort.index_of_mem he
    have h1 := BuildSort.kap_mono h.sorted ztvai hk
    have h2 := BuildSort.kap_mono h.sorted ztmob by_omega
    grind
  refine ⟨ha.1, ha.2, hb.1, hb.2, Or.inl ⟨h.kap_cut by_omega, h.kap_cut hS, hlt.ne'⟩, hnocut,
    fun p t hp ht0 ht1 hx => ?_⟩
  zukbn
  have hf := (h.faces_reg hp by_grind hcut).2
  zubik
  zumss
  zuky
  · rwa [BuildSort.cntBelow_last h.sorted hS hx, h.label_ends.2] at hf
  · rwa [BuildSort.cntBelow_first h.sorted hx, h.label_ends.1] at hf

/-- **Every arc is a gap** (with chords). -/
theorem gap_of_arc (hK : 0 < L.length) {U : Set Point} {a b : ℝ}
    (harc : M.IsArc zthh U a b) :
    (∃ m, m + 1 < S.length ∧ kap S m < kap S ztbl ∧ a = kap S m ∧ b = kap S ztbl) ∨
      (a = kap S ztdgf ∧ b = kap S 0) := by
  classical
  have hne : zthh ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨_, chordSet_mem hK⟩
  obtain ⟨-, -, -, -, hcuts, hfree, -⟩ := harc
  obtain ⟨hca, hcb, hab⟩ := hcuts.resolve_right by_simp_all
  obtain ⟨ea, hea, hak⟩ := h.isCut_iff.1 hca
  obtain ⟨eb, heb, hbk⟩ := h.isCut_iff.1 hcb
  obtain ⟨k₁, hk₁, hk₁e⟩ := BuildSort.index_of_mem hea
  obtain ⟨k₂, hk₂, hk₂e⟩ := BuildSort.index_of_mem heb
  rw [hak] at hk₁e
  rw [hbk] at hk₂e
  have hlen : 0 < S.length := by_omega
  zujec
  · left
    have hin : ztiek := by
      zujbv
    have hex : ∃ j, a < kap S j ∧ j < S.length := by_grind
    set j₀ := Nat.find hex with hj₀
    obtain ⟨hj₀a, hj₀l⟩ := Nat.find_spec hex
    have hmin : ∀ j < j₀, ¬ (a < kap S j ∧ j < S.length) := by_simp_all
    have hj₀pos : j₀ ≠ 0 := by
      zubww
      have := BuildSort.kap_mono h.sorted (Nat.zero_le k₁) hk₁
      grind
    have hk₁m : k₁ ≤ j₀ - 1 := by
      zukr
      have := BuildSort.kap_mono h.sorted (show j₀ ≤ k₁ by omega) hk₁
      grind
    have hm1 : kap S zttqa ≤ a := by
      grind
    have hm2 : a ≤ kap S zttqa := by
      have := BuildSort.kap_mono h.sorted hk₁m by_omega
      grind
    have hj₀k₂ : j₀ ≤ k₂ := by_grind
    have hb1 : kap S j₀ ≤ b := by
      have := BuildSort.kap_mono h.sorted hj₀k₂ hk₂; grind
    have hb2 : b ≤ kap S j₀ := by
      zux

      exact hfree _ by_grind (h.kap_cut hj₀l)
    refine ⟨j₀ - 1, by_omega, ?_, by_linarith, ?_⟩
    · grind
    grind
  · right
    have hin : ztiel := by
      zujbu
    have h1 : kap S ztdgf ≤ a := by
      zuca
      exact hfree _ ((hin _).2 ztjkr) (h.kap_cut by_omega)
    have h2 : a ≤ kap S ztdgf := by
      have := BuildSort.kap_mono h.sorted (show k₁ ≤ S.length - 1 by omega) by_omega
      simp_all
    have h3 : b ≤ kap S 0 := by
      zuca
      exact hfree _ by_simp_all (h.kap_cut hlen)
    have h4 : kap S 0 ≤ b := by
      have := BuildSort.kap_mono h.sorted (Nat.zero_le k₂) hk₂
      simp_all
    grind

/-- Without chords the family is empty. -/
theorem fam_empty (hK : L.length = 0) : famOf M Q L = ∅ := by
  have  := List.length_eq_zero_iff.1 hK
  zumo
  zuiua

/-- **Without chords, the pinned arc `(0, 0)` is an arc of the root region.** -/
theorem arc_of_empty (hK : L.length = 0) :
    M.IsArc zthh ztpdn 0 0 := by
  zulhv
  have hS : ztumc := by
    rw [List.eq_nil_iff_forall_not_mem]
    zubre
    have := (h.mem_cases he).1; omega
  have hnocut : ∀ x, ¬ M.IsCut zthh x := by
    rintro x ⟨c, hc, -⟩; simp_all
  -- the walk has an edge
  zuesh
  obtain ⟨-, hcard⟩ := hsys.regionsIn_finite_ncard h.walk.preconn h.walk.nonempty subset_rfl
  obtain ⟨U, hU⟩ : ztrzb :=
    Set.nonempty_of_ncard_ne_zero (by
      zuhcg
      omega)
  obtain ⟨p, t, hp, -⟩ := h.walk.exists_faces_nc h.adm h.finite hU
  have hn : ztcfu := by exact_mod_cast (Nat.zero_lt_of_lt hp)
  refine ⟨le_rfl, hn, le_rfl, hn, Or.inr ⟨hF, rfl, rfl⟩, fun x _ => hnocut x,
    fun p t hp ht0 ht1 _ => ?_⟩
  have hf := (h.faces_reg hp ztcoy ztvvs).2
  have hlab : ztzqf := by unfold gapLabel; zvojf; rfl
  simp_all

/-- **Without chords every arc is the pinned `(0, 0)`.** -/
theorem gap_of_arc_empty (hK : L.length = 0) {U : Set Point} {a b : ℝ}
    (harc : M.IsArc zthh U a b) : a = 0 ∧ b = 0 := by
  zulhv
  obtain ⟨-, -, -, -, hcuts, -⟩ := harc
  rcases hcuts with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, ha, hb⟩
  · simp_all
  simp_all
end Ctx
end
end BuildRegions
namespace BuildNF
@[expose] public section
open Set List
open BuildSort (Ev EvLe kap cntBelow)
open BuildRegions (eL eR crec famOf e1 e2 kl kr gapLabel reg LabelOK)

/-- The event of an event code. -/
noncomputable def evOf (M : Model) (Q : Polygon) (L : List zte) (c : ℕ) : Ev :=
  if c % 2 = 0 then eL M Q L ztbek else eR M Q L ztbek

/-- The walk position of an event code. -/
def wposOf (L : List zte) (c : ℕ) : WPos :=
  if c % 2 = 0 then (crec L ztbek).lpos else (crec L ztbek).rpos

/-- The region index of a label. -/
def ridx : Option ℕ → ℕ
  | none => 0
  | some i => i + 1

/-- The label of a region index. -/
def lab (r : ℕ) : Option ℕ := if r = 0 then none else some (r - 1)
theorem lab_ridx (ℓ : Option ℕ) : lab (ridx ℓ) = ℓ := by
  cases ℓ <;> simp [lab, ridx]
theorem ridx_lab (r : ℕ) : ridx ztqss = r := by
  unfold lab; split_ifs with h
  · tauto
  · zunvx; omega
variable (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ)

/-- The sorted events. -/
noncomputable def evs : List Ev := E.map zthwm

/-- The chord word. -/
noncomputable def word : List ℕ := (evs M Q L E).map Prod.fst

/-- The label outside chord `i` (before its first event). -/
noncomputable def outside (i : ℕ) : Option ℕ :=
  BuildStack.label ztgmt ((evs M Q L E).idxOf ztdnh)

/-- The chord record of chord `i`. -/
noncomputable def chordRec (i : ℕ) : CRec :=
  { h := (L.getD i ztt).1, lp := (L.getD i ztt).2.1, rp := (L.getD i ztt).2.2,
    up := if kl M Q L i < kr M Q L i then ridx ztilq else i + 1,
    dn := if kl M Q L i < kr M Q L i then i + 1 else ridx ztilq }

/-- The gap starts: the indices `m` with `kap m < kap (m + 1)`, and the last index. -/
noncomputable def gapStarts : List ℕ :=
  (List.range E.length).filter fun m =>
    decide ztxrb

/-- The arc record of the gap starting at `m`. -/
noncomputable def arcRec (m : ℕ) : ARec :=
  { reg := ridx (BuildStack.label ztgmt ztbl),
    s := wposOf L ztbgr, e := wposOf L ztwkh }

/-- The arc records. -/
noncomputable def arcList : List ARec :=
  if L.length = 0 then [ztgp] else (gapStarts M Q L E).map ztgfc

/-- The arcs of region `r`. -/
noncomputable def regArcs (r : ℕ) : List ℕ :=
  (List.range (arcList M Q L E).length).filter fun j =>
    decide (((arcList M Q L E).getD j ztgp).reg = r)

/-- The exit chords of region `r`. -/
noncomputable def regChords (r : ℕ) : List ℕ :=
  (List.range L.length).filter fun i =>
    decide ((chordRec M Q L E i).up = r ∨ (chordRec M Q L E i).dn = r)

/-- The weight of an arc record. -/
noncomputable def arcW (a : ARec) : ℕ := M.arcWt (M.key Q a.s) (M.key Q a.e)

/-- The weight of region `r`: the largest weight of its arcs. -/
noncomputable def regWt (r : ℕ) : ℕ :=
  ((regArcs M Q L E r).map fun j =>
    arcW M Q ((arcList M Q L E).getD j ztgp)).foldr max 0

/-- **The normal form computed by `BuildNF`.** -/
noncomputable def buildNF : NF where
  chords := (List.range L.length).map (chordRec M Q L E)
  arcs := arcList M Q L E
  regions := (List.range ztkr).map fun r =>
    ⟨regArcs M Q L E r, regChords M Q L E r, regWt M Q L E r⟩
  seq := List.range (arcList M Q L E).length
  dec := []
  root := 0
  lpar := []
open Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt sideKey_inj TouchesIn)
open BuildOrder (events evPair chordSet mem_events chordSet_inj chordSet_mem getD_mem)
open BuildRegions (lo hi Ctx)
variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-- **The hypotheses**: a walk-axiom model, a valid chord list, and a sorted ordering of the event
codes. -/
structure Input (M : Model) (Q : Polygon) (L : List zte) (E : List ℕ) : Prop where
  walk : WalkAx M
  valid : ChordTriplesOK M Q L
  perm : E.Perm ztct
  sorted : (E.map zthwm).Pairwise ztmaw
theorem range_map_evOf (n : ℕ) :
    (List.range ztssk).map zthwm = (List.range n).flatMap ztrph := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * ztkk = 2 * n + 1 + 1 by ring, List.range_succ, List.range_succ, map_append,
      map_append, ih, List.range_succ, flatMap_append]
    simp only [map_cons, map_nil, flatMap_cons, flatMap_nil, append_nil, append_assoc,
      singleton_append]
    have h1 : evOf M Q L ztssk = eL M Q L n := by
      unfold evOf; simp
    have h2 : evOf M Q L (2 * n + 1) = eR M Q L n := by
      unfold evOf; grind
    zubuw
    rfl
theorem key_wposOf (c : ℕ) : M.key Q ztbbg = (evOf M Q L c).2.1 := by
  unfold wposOf evOf
  zujpl

/-- The supremum of the values of a list of naturals is its `foldr max 0`. -/
theorem sSup_list (l : List ℕ) : sSup {x | x ∈ l} = l.foldr max 0 := by
  have hle : ∀ y ∈ l, y ≤ l.foldr max 0 := by
    zusy
    induction l with
    | nil => exact by_simp_all
    | cons x l ih =>
      zummj
      rcases mem_cons.1 hy with rfl | hy
      · omega
      · simp_all
  rcases l with _ | ⟨x, l⟩
  · simp
  · have hmem : ∀ (x : ℕ) (l : List ℕ), (x :: l).foldr max 0 ∈ x :: l := by
      intro x l
      induction l generalizing x with
      | nil => simp
      | cons y l ih =>
        zummj
        rcases le_total x ((y :: l).foldr max 0) with h1 | h1
        · simp_all
        · simp_all
    exact IsGreatest.csSup_eq ⟨by_simp_all, hle⟩
namespace Input
variable (h : Input M Q L E)
include h

/-- The sorted events form a `Ctx`. -/
theorem ctx : Ctx M Q L ztll where
  walk := h.walk
  valid := h.valid
  perm := by
    unfold evs events
    rw [← range_map_evOf]
    exact h.perm.map _
  sorted := h.sorted
theorem length_E : E.length = 2 * L.length := by
  rw [h.perm.length_eq, length_range]
omit h in
theorem length_evs (_h : Input M Q L E) : (evs M Q L E).length = E.length := length_map _
variable {m : ℕ} {i : ℕ} {j : ℕ}
/-- The key of the walk position of the `m`-th event is the `m`-th key. -/
theorem key_s (hm : m < E.length) :
    M.key Q ztwwn = kap ztll m := by
  rw [key_wposOf, BuildSort.kap_eq ztmdi]
  unfold evs
  simp_all
omit h in
/-- The chords of the computed normal form are the chords of the list. -/
theorem F_eq (_h : Input M Q L E) : (buildNF M Q L E).F M Q = famOf M Q L := by
  zubcj
  simp only [NF.F, buildNF, List.mem_map, List.mem_range, mem_ofPred_eq, famOf]
  constructor
  · zubsg
    exact ⟨_, getD_mem hi, rfl⟩
  · zuod
    zuve
    refine ztexo
    have : ztxpo := by
      simp_all
    unfold chordRec
    zubk
    rfl
omit h in
/-- The chord record `i` of the computed normal form. -/
theorem chord_eq (hi : i < L.length) : (buildNF M Q L E).chord i = chordRec M Q L E i := by
  unfold NF.chord buildNF
  simp_all
omit h in
theorem nChords : (buildNF M Q L E).nChords = L.length := by
  simp [NF.nChords, buildNF]
omit h in
theorem nRegions : (buildNF M Q L E).nRegions = L.length + 1 := by
  zuggb
omit h in
/-- The chord of a record of the computed normal form. -/
theorem toSet_chord (i : ℕ) : (chordRec M Q L E i).toSet M Q = chordSet M Q L i := rfl

/-- The split of the sorted events at the first event of chord `i`. -/
theorem split_first (hi : i < L.length) :
    ∃ u v, evs M Q L E = u ++ e1 M Q L i :: v ∧ u.length = (evs M Q L E).idxOf ztdnh := by
  obtain ⟨u, v, hsplit⟩ := List.append_of_mem (h.ctx.e1_mem hi)
  refine ⟨u, v, hsplit, ?_⟩
  have hnd := h.ctx.nodup
  grind

/-- The region of index `r`. -/
noncomputable def regF (r : ℕ) : Set Point := reg M Q L ztll ztqss
omit h in
theorem labelOK_lab {r : ℕ} (hr : r < L.length + 1) : LabelOK L.length ztqss := by
  zug
  unfold lab at hi
  grind
omit h in
theorem ridx_lt {ℓ : Option ℕ} (hℓ : LabelOK L.length ℓ) : ridx ℓ < L.length + 1 := by
  cases ℓ with
  | none => zuoyx
  | some i => have := hℓ i rfl; zunvx; omega

/-- **The region correspondence** of the computed normal form. -/
theorem regionCorr : RegionCorr M Q ztob (regF (M := M) (Q := Q) (L := L) (E := E)) := by
  obtain ⟨h1, h2, h3⟩ := h.ctx.regions_corr
  rw [RegionCorr, h.F_eq, nRegions]
  refine ⟨fun r hr => h1 _ ztvxy, fun r r' hr hr' heq => ?_, fun U hU => ?_⟩
  · have := h2 _ _ ztvxy (labelOK_lab hr') heq
    rw [← ridx_lab r, ← ridx_lab r', this]
  · obtain ⟨ℓ, hℓ, hU⟩ := h3 U hU
    exact ⟨ridx ℓ, ridx_lt hℓ, by unfold regF; zuozd; exact hU⟩

/-- **The sides of the chord records.** -/
theorem sides_rec (hi : i < L.length) :
    (chordRec M Q L E i).up < L.length + 1 ∧ (chordRec M Q L E i).dn < L.length + 1 ∧
      M.AboveOf ztrz (regF (M := M) (Q := Q) (L := L) (E := E) (chordRec M Q L E i).up) ∧
      M.BelowOf ztrz (regF (M := M) (Q := Q) (L := L) (E := E) (chordRec M Q L E i).dn) := by
  obtain ⟨u, v, hsplit, hlen⟩ := h.split_first hi
  zudnj
  have hsides := hC.sides hsplit hi
  have hfirst := hC.label_first hsplit hi
  have hout : outside M Q L E i = BuildStack.label ztgmt u.length := by
    unfold outside; simp_all
  have hOK : LabelOK L.length ztilq := by zuoze; exact hC.label_ok _
  have hword : word M Q L E = (evs M Q L E).map Prod.fst := rfl
  rw [hword] at hout
  rw [hfirst] at hsides
  have hri : ridx (some i) = i + 1 := rfl
  unfold chordRec regF
  zulss
  · refine ⟨ridx_lt hOK, ?_, ?_, ?_⟩
    · simp_all
    · zuolr; simp_all
    tauto
  · have hk' :=
      lt_of_le_of_ne (not_lt.1 hk) (Ne.symm (hC.kl_ne_kr hi))
    refine ⟨?_, ridx_lt hOK, ?_, ?_⟩
    · grind
    · rw [← hri, lab_ridx]; grind
    · zuolr; grind

/-- **The chord sides** of the computed normal form. -/
theorem chordSidesOK :
    ChordSidesOK M Q ztob (regF (M := M) (Q := Q) (L := L) (E := E)) := by
  zug
  zugfc
  rw [nRegions, chord_eq hi]
  zueug
  refine ⟨hup, hdn, fun z hz hzD => ?_⟩
  rw [toSet_chord] at hz
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ((hA z hz hzD).and (hB z hz hzD))
  exact ⟨ε₀, hε₀, fun ε h1 h2 => hsub by_simp_all⟩

/-! ## Arcs -/
omit h in
theorem mem_gapStarts :
    m ∈ gapStarts M Q L E ↔ m < E.length ∧
      ztxrb := by
  zumst
  simp
omit h in
/-- The gap starts are increasing. -/
theorem gapStarts_sorted : (gapStarts M Q L E).Pairwise ztfvn :=
  (List.pairwise_lt_range).filter _
omit h in
/-- The arc record at index `j` (with chords). -/
theorem arc_eq (hK : L.length ≠ 0) (hj : j < (arcList M Q L E).length) :
    (buildNF M Q L E).arc j = arcRec M Q L E (ztdon[j]'(by
      unfold arcList at hj; simp_all)) := by
  unfold NF.arc buildNF
  zubi
  unfold arcList
  grind

/-- The start key of the arc of the gap at `m`. -/
theorem key_arcRec_s (hm : m < E.length) :
    M.key Q (arcRec M Q L E m).s = kap ztll m := h.key_s hm

/-- The end key of the arc of the gap at `m`. -/
theorem key_arcRec_e (hm : m < E.length) :
    M.key Q (arcRec M Q L E m).e = kap ztll ztxei :=
  h.key_s ztcv

/-- **The arc of a gap is an arc of the region of its record.** -/
theorem arcRec_isArc (hK : L.length ≠ 0) (hm : m ∈ gapStarts M Q L E) :
    (arcRec M Q L E m).reg < L.length + 1 ∧
      M.IsArc zthh (regF (M := M) (Q := Q) (L := L) (E := E) (arcRec M Q L E m).reg)
        (M.key Q (arcRec M Q L E m).s) (M.key Q (arcRec M Q L E m).e) := by
  rw [mem_gapStarts] at hm
  obtain ⟨hml, hgap⟩ := hm
  zudnj
  zumdv
  refine ⟨ridx_lt (hC.label_ok _), ?_⟩
  unfold regF
  rw [h.key_arcRec_s hml, h.key_arcRec_e hml]
  simp only [arcRec]
  zuozd
  rcases hgap with hlast | hlt
  · have hS : (evs M Q L E).length = m + 1 := by_omega
    rw [hlast, Nat.mod_self, show word M Q L E = (evs M Q L E).map Prod.fst from rfl, ← hlev,
      hC.label_ends.2, show m = (evs M Q L E).length - 1 by omega]
    exact hC.arc_of_wrap ztqas
  · have hm1 : ztskg := by
      rcases lt_or_ge ztbl E.length with h1 | h1
      · zubvv
      · exfalso
        have h1' : m + 1 = (evs M Q L E).length := by_omega
        have h0 : kap ztll ztbl = 0 := by
          zumtd
        have := (hC.kap_bounds (m := m) by_omega).1
        linarith
    rw [Nat.mod_eq_of_lt hm1]
    exact hC.arc_of_gap by_omega hlt

/-- Two arcs with the same keys of regions of the computed normal form have the same region. -/
theorem reg_eq_of_arcs (hK : L.length ≠ 0) {r r' : ℕ} (hr : r < L.length + 1)
    (hr' : r' < L.length + 1) {a b : ℝ}
    (h1 : M.IsArc zthh (regF (M := M) (Q := Q) (L := L) (E := E) r) a b)
    (h2 : M.IsArc zthh (regF (M := M) (Q := Q) (L := L) (E := E) r') a b) : r = r' := by
  zuegv

  have hne : (famOf M Q L).Nonempty := ⟨_, chordSet_mem ztqas⟩
  obtain ⟨p, hp, t, ht, hin, -, hf⟩ := WalkAx.exists_pos_in_arc hne h1
  have hf' := h2.2.2.2.2.2.2 p t hp ht.1 ht.2 hin
  exact hcorr.2.1 r r' hr hr' (WalkAx.faces_unique by_grind (hcorr.1 r' hr') hf hf')

/-- **The arc records** of the computed normal form. -/
theorem arcsOK : ArcsOK M Q ztob (regF (M := M) (Q := Q) (L := L) (E := E)) := by
  zudnj
  zumdv
  have harcsN : (buildNF M Q L E).arcs = arcList M Q L E := rfl
  have hregion : ∀ r, r < L.length + 1 → (buildNF M Q L E).region r =
      ⟨regArcs M Q L E r, regChords M Q L E r, regWt M Q L E r⟩ := by
    zuz
    zujqc

  have hlast : ∀ r, r < (buildNF M Q L E).nRegions → ∀ j,
      (j ∈ ((buildNF M Q L E).region r).arcs ↔
        j < (buildNF M Q L E).arcs.length ∧ ((buildNF M Q L E).arc j).reg = r) := by
    intro r hr j
    zukxu
    rw [hregion r hr, harcsN]
    unfold regArcs
    rw [mem_filter, List.mem_range, decide_eq_true_eq]
    rfl
  unfold ArcsOK
  rw [h.F_eq, nRegions, harcsN]
  zubsy
  · -- no chord: the single pinned arc
    zuglk
    have hkey0 : M.key Q ztbqw = 0 := by zunpm
    have harc0 : ztycb := by
      unfold NF.arc; simp_all
    have hreg0 : regF 0 = reg M Q L ztll none := rfl
    refine ⟨fun j hj => ?_, fun j j' hj hj' _ _ => ?_, fun r hr a b harc => ?_, ?_⟩
    · zuiin
      zudgu
      zumo
      zummv
      refine zthml
      show M.IsArc _ _ _ _
      rw [hkey0, hreg0]
      exact hC.arc_of_empty hK
    · simp_all
    · obtain ⟨rfl, rfl⟩ := hC.gap_of_arc_empty hK harc
      simp_all
    · zubxb
  · have hA : arcList M Q L E = (gapStarts M Q L E).map ztgfc := by
      zuhah
    have hlenA : ztddw := by_simp_all
    refine ⟨fun j hj => ?_, fun j j' hj hj' hreg hkey => ?_, fun r hr a b harc => ?_, ?_⟩
    · zukqf
      exact h.arcRec_isArc hK ztvri
    · rw [arc_eq hK hj, arc_eq hK hj'] at hkey
      zufgs

      have hmem := fun k (hk : k < (gapStarts M Q L E).length) =>
        (mem_gapStarts).1 ztvrj
      rw [h.key_arcRec_s by_simp_all, h.key_arcRec_s by_simp_all] at hkey
      zuct
      have hsorted := pairwise_iff_getElem.1 (gapStarts_sorted (M := M) (Q := Q) (L := L) (E := E))
      -- the earlier gap start is followed by a strictly larger key
      have key_lt : ∀ k k', (hk : k < (gapStarts M Q L E).length) →
          (hk' : k' < (gapStarts M Q L E).length) → k < k' →
          kap ztll ztdon[k] < kap ztll ztdon[k'] := by
        intro k k' hk hk' hkk
        have hlt := hsorted k k' hk hk' hkk
        obtain ⟨hml, hgap⟩ := hmem k hk
        have hml' := (hmem k' hk').1
        rcases hgap with hlast | hgap
        · omega
        · exact hgap.trans_le (BuildSort.kap_mono hC.sorted hlt by_omega)
      grind
    · have hS := hlev
      -- the gap of the arc
      obtain ⟨m, hmG, rfl, rfl⟩ : ∃ m ∈ gapStarts M Q L E,
          a = kap ztll m ∧ b = kap ztll ztxei := by
        rcases hC.gap_of_arc ztqas harc with ⟨m, hm1, hlt, rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine ⟨m, (mem_gapStarts).2
            by_grind, rfl, ?_⟩
          zuey
        · have hE : ztgaa := by rw [h.length_E]; omega
          refine ⟨E.length - 1, (mem_gapStarts).2
            by_omega, by zvojf, ?_⟩
          rw [Nat.sub_add_cancel hE, Nat.mod_self]
      obtain ⟨j, hj, hjm⟩ := List.mem_iff_getElem.1 hmG
      have hjA : j < (arcList M Q L E).length := by_omega
      have hmE := ((mem_gapStarts).1 hmG).1
      obtain ⟨hreg, harc'⟩ := h.arcRec_isArc hK hmG
      rw [h.key_arcRec_s hmE, h.key_arcRec_e hmE] at harc'
      refine ⟨j, hjA, ?_, ?_, ?_⟩
      · zunpn
        zunwd
        exact (h.reg_eq_of_arcs hK hr hreg harc harc').symm
      · zunpn; zunwd; exact h.key_arcRec_s hmE
      · zunpn; zunwd; exact h.key_arcRec_e hmE
    · zubxb

/-! ## Regions and the sequence -/
omit h in
theorem region_eq (_h : Input M Q L E) {r : ℕ}
    (hr : r < L.length + 1) : (buildNF M Q L E).region r =
    ⟨regArcs M Q L E r, regChords M Q L E r, regWt M Q L E r⟩ := by
  zujqc

/-- The two side regions of a chord are the regions of its `up` and `dn` records. -/
theorem touches_iff (hi : i < L.length) {r : ℕ} (hr : r < L.length + 1) :
    TouchesIn M.D ztrz (regF (M := M) (Q := Q) (L := L) (E := E) r) ↔
      (chordRec M Q L E i).up = r ∨ (chordRec M Q L E i).dn = r := by
  zuegv

  have hsys := h.walk.sys _ h.ctx.adm h.ctx.finite
  obtain ⟨Up, Dn, hUp, hDn, -, hside, htouch⟩ := chordSides_of_system hsys ztdcw
  zueug
  obtain ⟨z, hzc, hzD⟩ := (hsys.chord_inter_nonempty_isPreconnected ztdcw).1
  have heqU : regF (M := M) (Q := Q) (L := L) (E := E) (chordRec M Q L E i).up = Up := by
    obtain ⟨δ, h1, h2, -⟩ := ((hA z hzc hzD).and ztlpv).exists
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint (hcorr.1 _ hup) hUp with h' | h'
    · zuclh
    grind
  have heqD : regF (M := M) (Q := Q) (L := L) (E := E) (chordRec M Q L E i).dn = Dn := by
    obtain ⟨δ, h1, -, h2⟩ := ((hB z hzc hzD).and ztlpv).exists
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint (hcorr.1 _ hdn) hDn with h' | h'
    · zuclh
    grind
  rw [htouch _ ztjxq, ← heqU, ← heqD]
  grind

/-- **The region records** of the computed normal form. -/
theorem regionsOK : RegionsOK M Q ztob (regF (M := M) (Q := Q) (L := L) (E := E)) := by
  have harcs := h.arcsOK
  zuz
  zukxu
  rw [h.region_eq hr, h.F_eq]
  refine ⟨fun i => ?_, (nodup_range).filter _, (nodup_range).filter _, ?_⟩
  · zubi
    unfold regChords
    rw [mem_filter, List.mem_range, decide_eq_true_eq, nChords]
    constructor
    · zukok
      refine ztfwp
      rw [chord_eq hi, toSet_chord]
      exact (h.touches_iff hi hr).2 hc
    · zukok
      rw [chord_eq hi, toSet_chord] at hc
      exact ⟨hi, (h.touches_iff hi hr).1 hc⟩
  · -- the weight
    zubi
    unfold Model.weight regWt
    rw [← sSup_list]
    zucr
    obtain ⟨h1, -, h3, h4⟩ := harcs
    rw [h.F_eq, nRegions] at h1 h3
    zumx
    constructor
    · zuetb
      zufyo
      have hj' := (h4 r ztmdv j).1 (by rw [h.region_eq hr]; exact hj)
      obtain ⟨-, harc⟩ := h1 j hj'.1
      rw [hj'.2] at harc
      exact ⟨(M.key Q ((buildNF M Q L E).arc j).s, M.key Q ((buildNF M Q L E).arc j).e), harc, rfl⟩
    · rintro ⟨ab, harc, rfl⟩
      obtain ⟨j, hj, hjr, hs, he⟩ := h3 r hr ab.1 ab.2 harc
      have hjr' := (h4 r ztmdv j).2 by_omega
      rw [h.region_eq hr] at hjr'
      refine List.mem_map.2 ⟨j, hjr', ?_⟩
      show M.arcWt zthrj zthri = _
      simp_all

/-- **The arc sequence** of the computed normal form. -/
theorem seqOK : SeqOK M Q ztob := by
  refine ⟨Perm.refl _, ?_⟩
  show (List.range (arcList M Q L E).length).Pairwise
    (fun j j' => M.key Q ((buildNF M Q L E).arc j).s ≤ M.key Q ((buildNF M Q L E).arc j').s)
  rw [pairwise_iff_getElem]
  zukjo
  simp only [getElem_range]
  rw [length_range] at hj hj'
  zubsy
  · have : (arcList M Q L E).length = 1 := by unfold arcList; simp_all
    omega
  · zudnj
    have hlenA : ztddw := by
      zuhah
    rw [arc_eq hK hj, arc_eq hK hj']
    zufgs

    have hmem := fun k (hk : k < (gapStarts M Q L E).length) =>
      (mem_gapStarts).1 ztvrj
    rw [h.key_arcRec_s by_simp_all, h.key_arcRec_s by_simp_all]
    have hlt := pairwise_iff_getElem.1 (gapStarts_sorted)
      j j' hj1 hj1' hjj
    exact BuildSort.kap_mono hC.sorted hlt.le (by zuoyt; simp_all)

/-- The walk positions of the events are positions of the walk proper. -/
theorem properPos_wposOf {c : ℕ} (hc : c ∈ E) : ProperPos M Q Q.n ztbbg := by
  have hc2 := List.mem_range.1 ztvry
  zubgd
  zudnj
  have hh : (crec L _).h < Q.n := h.valid.2.2.2 _ ztdoo
  zulci
  split_ifs
  · have hA := hC.attL hi
    exact ztrcr
  · have hA := hC.attR hi
    exact ztrcr

/-- The ends of the arc records are positions of the walk proper. -/
theorem properPos_arcs (hj : j < (arcList M Q L E).length) :
    ProperPos M Q Q.n ((buildNF M Q L E).arc j).s ∧ ProperPos M Q Q.n ((buildNF M Q L E).arc j).e := by
  zubsy
  · zuglk
    zuiin
    zudgu
    zumo
    have harc0 : ztycb := by
      unfold NF.arc; show (arcList M Q L E).getD 0 _ = _; simp_all
    zummv
    have hp : ProperPos M Q Q.n ztbqw := ⟨le_refl _, by_positivity, Nat.zero_le _⟩
    simp_all
  · zukqf
    have hlenA : ztddw := by
      zuhah
    have hj1 : ztccc := by_omega
    have hm := ((mem_gapStarts).1 (getElem_mem hj1)).1
    have hgetD : ∀ k, k < E.length → E.getD k 0 ∈ E := by_simp_all
    exact ⟨h.properPos_wposOf by_simp_all, h.properPos_wposOf (hgetD _ ztcv)⟩

/-- **WP-C: the computed normal form is valid** (`IsNF`), with the chords of the list in order
and no decomposition. -/
theorem isNF : IsNF M Q ztob ∧
    (buildNF M Q L E).chords.map ztwma = L ∧ (buildNF M Q L E).dec = [] := by
  zudnj
  refine ⟨⟨?_, fun i i' hi hi' heq => ?_, fun i hi => ?_, regF, h.regionCorr, h.chordSidesOK,
    h.arcsOK, h.regionsOK, h.seqOK, fun i hi => ?_, fun j hj => h.properPos_arcs hj⟩, ?_, rfl⟩
  · rw [h.F_eq]; exact h.valid.1
  · rw [nChords] at hi hi'
    rw [chord_eq hi, chord_eq hi', toSet_chord, toSet_chord] at heq
    exact chordSet_inj h.valid hi hi' heq
  · zugfc
    zulpl
    exact h.valid.2.2.1 _ ztdoo
  · zugfc
    zulpl
    exact h.valid.2.2.2 _ ztdoo
  · simp only [buildNF, List.map_map]
    zulda
    intro k hk1 hk2
    simp only [getElem_map, getElem_range, Function.comp_apply, chordRec]
    simp_all
end Input
open BuildSort (cycDist)
noncomputable def tieBit (M : Model) (L : List zte) (c : ℕ) : ℕ :=
  if (M.wb (wposOf L c).edge).2 < (M.wa (wposOf L c).edge).2 then 1 - c % 2 else c % 2

/-- **The comparator of the event sort**: by key, then by tie bit. -/
def codeLe (M : Model) (Q : Polygon) (L : List zte) (c c' : ℕ) : Prop :=
  M.key Q ztbbg < M.key Q ztbuh ∨
    (M.key Q ztbbg = M.key Q ztbuh ∧ tieBit M L c ≤ tieBit M L c')

/-- The comparator is total. -/
theorem codeLe_total (M : Model) (Q : Polygon) (L : List zte) (c c' : ℕ) :
    codeLe M Q L c c' ∨ codeLe M Q L c' c := by
  zului
  grind

/-- The comparator is transitive. -/
theorem codeLe_trans (M : Model) (Q : Polygon) (L : List zte) {a b c : ℕ}
    (h1 : codeLe M Q L a b) (h2 : codeLe M Q L b c) : codeLe M Q L a c := by
  unfold codeLe at *
  grind
variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)}

/-- The attachment of the position of an event code. -/
theorem attach_wposOf (hL : ChordTriplesOK M Q L) {c : ℕ} (hc : c < 2 * L.length) :
    SideAttach M.W (chordSet M Q L ztbek) (wposOf L c).edge ztzuc := by
  zubgd
  zukbb
  zulci
  split_ifs
  · exact hatt.1
  · exact hatt.2
variable {c : ℕ}
theorem wposOf_even (hc : c % 2 = 0) : wposOf L c = (crec L ztbek).lpos := by
  zumvk
theorem wposOf_odd (hc : c % 2 = 1) : wposOf L c = (crec L ztbek).rpos := by
  zumvk
theorem evOf_even (hc : c % 2 = 0) : evOf M Q L c = eL M Q L ztbek := by
  zumsp
theorem evOf_odd (hc : c % 2 = 1) : evOf M Q L c = eR M Q L ztbek := by
  zumsp

/-- The left endpoint is left of the right endpoint (for a chord of a valid list). -/
theorem pos_lt' (hM : WalkAx M) (hL : ChordTriplesOK M Q L) {i : ℕ} (hi : i < L.length) :
    (M.pos Q (crec L i).lpos).1 < (M.pos Q (crec L i).rpos).1 :=
  BuildOrder.endpoints hM (hL.1.2.1 ztdcw) (hL.2.2.1 _ ztdoo)

/-- **The tie between a left-endpoint event and a right-endpoint event at one position.** -/
theorem tie_codes (hM : WalkAx M) (hL : ChordTriplesOK M Q L) {e o : ℕ}
    (he : e < 2 * L.length) (ho : o < 2 * L.length) (hee : e % 2 = 0) (hoo : o % 2 = 1)
    (_hij : e / 2 ≠ o / 2) (hpe : (wposOf L e).edge = (wposOf L o).edge)
    (hpt : M.param Q (wposOf L e) = M.param Q (wposOf L o)) :
    (M.wb (wposOf L e).edge).2 ≠ (M.wa (wposOf L e).edge).2 ∧
      ((M.wb (wposOf L e).edge).2 < (M.wa (wposOf L e).edge).2 →
        cycDist M.W.n (evOf M Q L e).2.1 (evOf M Q L e).2.2 <
          cycDist M.W.n (evOf M Q L o).2.1 (evOf M Q L o).2.2) ∧
      ((M.wa (wposOf L e).edge).2 < (M.wb (wposOf L e).edge).2 →
        cycDist M.W.n (evOf M Q L o).2.1 (evOf M Q L o).2.2 <
          cycDist M.W.n (evOf M Q L e).2.1 (evOf M Q L e).2.2) := by
  set i := e / 2
  set i' := o / 2
  have hi : ztsjb := by_omega
  have hi' : i' < L.length := by_omega
  zumcy
  zuixx
  have hattI := hL.2.2.1 _ ztdoo
  have hattI' := hL.2.2.1 _ (getD_mem hi')
  -- the common position
  set p := (crec L i).lp
  set t := M.param Q (crec L i).lpos
  have hpos' : (crec L i').rp = p ∧ M.param Q (crec L i').rpos = t := by
    rw [wposOf_even hee, wposOf_odd hoo] at hpe hpt
    tauto
  have hAe : SideAttach M.W ztrz p t := hattI.1
  have hAw : SideAttach M.W ztqjr p t := by
    have : SideAttach M.W ztqjr (crec L i').rp (M.param Q (crec L i').rpos) :=
      hattI'.2
    simp_all
  -- directions
  have hptE : sidePt M.W p t = M.pos Q (crec L i).lpos := rfl
  have hE : ∀ z ∈ chordSet M Q L i, (sidePt M.W p t).1 ≤ z.1 := by
    rintro z ⟨-, hz, -⟩; tauto
  have hptW : sidePt M.W p t = M.pos Q (crec L i').rpos := by
    show sidePt M.W p t = sidePt M.W (crec L i').rp _
    simp_all
  have hW : ∀ z ∈ chordSet M Q L i', z.1 ≤ (sidePt M.W p t).1 := by
    rintro z ⟨-, -, hz⟩; zuoyu; exact hz
  -- the other ends
  have hBe := hattI.2
  have hBe' : sidePt M.W (crec L i).rp ztgec ≠ sidePt M.W p t := by
    zuhgj
    have : M.pos Q (crec L i).rpos = M.pos Q (crec L i).lpos := h'
    have hlt := pos_lt' hM hL hi
    simp_all
  have hBw := hattI'.1
  have hBw' : sidePt M.W (crec L i').lp (M.param Q (crec L i').lpos) ≠ sidePt M.W p t := by
    zuhgj
    have : M.pos Q (crec L i').lpos = M.pos Q (crec L i').rpos := by rw [← hptW]; exact h'
    have hlt := pos_lt' hM hL hi'
    simp_all
  have hedge : (wposOf L e).edge = p := by rw [wposOf_even hee]; rfl
  obtain ⟨-, hhor, -⟩ := hM.tie_shape hadm ztdcw zterh hAe hAw hE hW
  have hev : evOf M Q L e = ztila := by rw [evOf_even hee]; rfl
  have hov : evOf M Q L o = (i', kr M Q L i', kl M Q L i') := by rw [evOf_odd hoo]; rfl
  have hkl : kl M Q L i = (p : ℝ) + t := rfl
  have hkr' : kr M Q L i' = (p : ℝ) + t := by
    show ((crec L i').rp : ℝ) + M.param Q (crec L i').rpos = p + t
    simp_all
  rw [hedge, hev, hov]
  refine ⟨hhor, fun hdown => ?_, fun hup => ?_⟩
  · obtain ⟨ht0, hlt⟩ := BuildOrder.tie_rule_down hM hadm hfin ztdcw zterh
      hAe hAw hE hW hdown hBe hBe' hBw hBw'
    zubi
    zugea

  · obtain ⟨ht0, hlt⟩ := BuildOrder.tie_rule_up hM hadm hfin ztdcw zterh
      hAe hAw hE hW hup hBe hBe' hBw hBw'
    zubi
    zugea

/-- **The comparator implies the event order** (for distinct codes of a valid chord list). -/
theorem evLe_of_codeLe (hM : WalkAx M) (hL : ChordTriplesOK M Q L) {c c' : ℕ}
    (hc : c < 2 * L.length) (hc' : c' < 2 * L.length) (hne : c ≠ c')
    (hle : codeLe M Q L c c') : EvLe M.W.n ztqmo (evOf M Q L c') := by
  unfold codeLe at hle
  rw [key_wposOf, key_wposOf] at hle
  rcases hle with hlt | ⟨heq, htb⟩
  · tauto
  · refine Or.inr ⟨heq, ?_⟩
    have hA := attach_wposOf hL hc
    have hA' := attach_wposOf hL hc'
    have heq' : ((wposOf L c).edge : ℝ) + M.param Q ztbbg =
        (wposOf L c').edge + M.param Q ztbuh := by
      rw [← Model.key, ← Model.key, key_wposOf, key_wposOf]; omega
    obtain ⟨hpe, hpt⟩ := sideKey_inj hA.2.1 hA.2.2.1 hA'.2.1 hA'.2.2.1 heq'
    zubgd
    have hi' : c' / 2 < L.length := by_omega
    have hposeq : M.pos Q ztbbg = M.pos Q ztbuh := by
      zulbf
    -- the two chords differ
    have hij : c / 2 ≠ c' / 2 := by
      intro hij
      rcases Nat.mod_two_eq_zero_or_one c with h0 | h0
      · have h1 : c' % 2 = 1 := by_omega
        rw [wposOf_even h0, wposOf_odd h1, ← hij] at hposeq
        have := pos_lt' hM hL hi
        simp_all
      · have h1 : c' % 2 = 0 := by_omega
        rw [wposOf_odd h0, wposOf_even h1, ← hij] at hposeq
        have := pos_lt' hM hL hi
        simp_all
    zumcy
    -- the common position
    have hA'' : SideAttach M.W (chordSet M Q L ztthi) (wposOf L c).edge
        ztzuc := by_simp_all
    have hsp : sidePt M.W (wposOf L c).edge _ = M.pos Q _ := rfl
    have hEast : ∀ d, d % 2 = 0 → ∀ z ∈ chordSet M Q L ztcmw, (M.pos Q ztudh).1 ≤ z.1 := by
      intro d hd z hz; rw [wposOf_even hd]; exact hz.2.1
    have hWest : ∀ d, d % 2 = 1 → ∀ z ∈ chordSet M Q L ztcmw, z.1 ≤ (M.pos Q ztudh).1 := by
      intro d hd z hz; rw [wposOf_odd hd]; exact hz.2.2
    have htbc : tieBit M L c = if (M.wb (wposOf L c).edge).2 < (M.wa (wposOf L c).edge).2
        then 1 - c % 2 else c % 2 := rfl
    have htbc' : tieBit M L c' = if (M.wb (wposOf L c).edge).2 < (M.wa (wposOf L c).edge).2
        then 1 - c' % 2 else c' % 2 := by unfold tieBit; zungd
    rw [htbc, htbc'] at htb
    rcases Nat.mod_two_eq_zero_or_one c with h0 | h0 <;>
      rcases Nat.mod_two_eq_zero_or_one c' with h1 | h1
    · exfalso
      apply hij
      refine chordSet_inj hL hi hi' (hM.attach_east_unique hadm ztdcw zterh
        hA hA'' ?_ ?_)
      · grind
      grind
    · obtain ⟨hhor, hdown, hup⟩ := tie_codes hM hL hc hc' h0 h1 hij hpe hpt
      grind
    · obtain ⟨hhor, hdown, hup⟩ := tie_codes hM hL hc' hc h1 h0 ztjko hpe.symm hpt.symm
      grind
    · exfalso
      apply hij
      refine chordSet_inj hL hi hi' (hM.attach_west_unique hadm ztdcw zterh
        hA hA'' ?_ ?_)
      · grind
      grind

/-- **Codes sorted by the comparator give events sorted by the tie rule.** -/
theorem sorted_of_codeLe (hM : WalkAx M) (hL : ChordTriplesOK M Q L) {E : List ℕ}
    (hperm : E.Perm ztct) (hsort : E.Pairwise ztxi) :
    (E.map zthwm).Pairwise ztmaw := by
  have hnd := hperm.nodup_iff.2 nodup_range
  rw [pairwise_map]
  zudsq
  exact evLe_of_codeLe hM hL by_grind
    by_grind hab.2 hab.1

/-- **WP-C: the normal form computed from comparator-sorted event codes is valid.** -/
theorem isNF_of_codeLe (hM : WalkAx M) (hL : ChordTriplesOK M Q L) {E : List ℕ}
    (hperm : E.Perm ztct) (hsort : E.Pairwise ztxi) :
    IsNF M Q ztob ∧
      (buildNF M Q L E).chords.map ztwma = L ∧ (buildNF M Q L E).dec = [] :=
  Input.isNF ⟨hM, hL, hperm, sorted_of_codeLe hM hL hperm hsort⟩

/-- **The good-model form**: for a good model and a valid chord list of `Q`, sorting the event
codes by `codeLe` and building `buildNF` gives a valid normal form with the chords of the list. -/
theorem isNF_goodModel (hM : GoodModel M) (hL : ChordTriplesOK M Q L) {E : List ℕ}
    (hperm : E.Perm ztct) (hsort : E.Pairwise ztxi) :
    IsNF M Q ztob ∧
      (buildNF M Q L E).chords.map ztwma = L ∧ (buildNF M Q L E).dec = [] :=
  isNF_of_codeLe (walkAx_of_goodModel hM) hL hperm hsort
open Chazelle.Machine (Stmt)

/-- **The RAM part of `BuildNFSpec`**: the procedure writes the computed normal form of a sorted
ordering of the event codes. -/
def BuildNFRamSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s {bBuild, bSort, bSign}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      ModelDescWF P ztm c.nmem ztue ∧
      ∃ M L, ModelDescAt c.nmem ztue zta M ∧
      GoodModel M ∧ rd c bBuild 2 = L.length ∧ rd c bBuild 1 + 3 * L.length ≤ c.nreg ALLOC ∧
      ChordListAt c.nmem ztbis L ∧ ChordTriplesOK M zta L)
    (fun P c c' => ∀ M L, ModelDescAt c.nmem ztue zta M →
      rd c bBuild 2 = L.length → ChordListAt c.nmem ztbis L →
        ∃ E : List ℕ, E.Perm ztct ∧ E.Pairwise ztwqj ∧
          c.nreg ALLOC ≤ rd c' bBuild 3 ∧
          NFWithin c'.nmem ztdph ztdo (buildNF M zta L E))
    ztzj

/-- A chord list in memory is determined by its length. -/
theorem chordListAt_unique {m : ℕ → ℕ} {A : ℕ} {L L' : List zte} (h : ChordListAt m A L)
    (h' : ChordListAt m A L') (hlen : L.length = L'.length) : L = L' := by
  apply List.ext_getElem hlen
  zugoh
  zurw
  obtain ⟨b1, b2, b3⟩ := h' i hi'
  grind

/-- **The reduction**: the RAM part implies `BuildNFSpec`. -/
theorem buildNFSpec_of_ram (hram : BuildNFRamSpec) : BuildNFSpec := by
  obtain ⟨s, κ, hs⟩ := hram
  refine ⟨s, κ, fun P W c hw hpre hcost => ?_⟩
  obtain ⟨c', k, hexec, hk, hpost, hframe⟩ := hs P W c hw hpre hcost
  refine ⟨c', k, hexec, hk, fun M L hM hlen hL => ?_, hframe⟩
  obtain ⟨-, -, -, M₀, L₀, hM₀, hgood, hlen₀, -, hL₀, hok⟩ := hpre
  obtain rfl := NFLoc.modelDesc_unique hM₀ hM
  obtain rfl := chordListAt_unique hL₀ hL (hlen₀.symm.trans hlen)
  obtain ⟨E, hperm, hsort, hB, hN⟩ := hpost M₀ L₀ hM hlen hL
  obtain ⟨hnf, hch, hdec⟩ := isNF_goodModel hgood hok hperm hsort
  grind
end
end BuildNF
end Chazelle.Core
namespace Chazelle.Core
namespace BuildNF
@[expose] public section
open List
open BuildSort (Ev EvLe kap cntBelow)
open BuildRegions (eL eR crec famOf e1 e2 kl kr lo hi)
variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
theorem evOf_fst (M : Model) (Q : Polygon) (L : List zte) (c : ℕ) :
    (evOf M Q L c).1 = c / 2 := by
  unfold evOf; split_ifs <;> rfl

/-- **The chord word** is the list of chords of the codes. -/
theorem word_eq (M : Model) (Q : Polygon) (L : List zte) (E : List ℕ) :
    word M Q L E = E.map ztcfk := by
  unfold word evs
  zugwd
  exact map_congr_left fun c _ => evOf_fst M Q L c
namespace Input
variable (h : Input M Q L E)
include h
variable {i : ℕ}
/-- The first occurrence of chord `i` in the word is the first event of `i`. -/
theorem first_e1 (hi : i < L.length) :
    (word M Q L E).idxOf i < E.length ∧
      ztll[(word M Q L E).idxOf i]? = some ztdnh ∧
      (evs M Q L E).idxOf ztdnh = (word M Q L E).idxOf i := by
  zumdc
  set S := evs M Q L E with hS
  have hmem : e1 M Q L i ∈ S := hc.e1_mem hi
  set k := S.idxOf ztdnh with hk
  have hkl : k < S.length := idxOf_lt_length_of_mem hmem
  have hSk : S[k] = e1 M Q L i := getElem_idxOf hkl
  have hsplit : S = S.take k ++ e1 M Q L i :: S.drop zts := by
    conv_lhs => rw [← take_append_drop k S]
    rw [drop_eq_getElem_cons hkl, hSk]
  have hcnt := hc.count_prefix_self hsplit hi
  have hni : i ∉ (S.take k).map Prod.fst := fun h' => by
    grind
  have hw : word M Q L E = (S.take k).map Prod.fst ++ i :: (S.drop zts).map Prod.fst := by
    show S.map Prod.fst = _
    conv_lhs => rw [hsplit]
    rw [map_append, map_cons]
    rfl
  have hidx : (word M Q L E).idxOf i = k := by
    grind
  have hlen : S.length = E.length := length_map _
  grind

/-- **The label outside chord `i`** is the label before its first occurrence. -/
theorem outside_eq (hi : i < L.length) :
    outside M Q L E i = BuildStack.label ztgmt ztckk := by
  unfold outside
  rw [(h.first_e1 hi).2.2]

/-- The code at the first occurrence of chord `i`. -/
theorem first_code (hi : i < L.length) :
    evOf M Q L (E.getD ztckk 0) = e1 M Q L i := by
  obtain ⟨hlt, hget, -⟩ := h.first_e1 hi
  unfold evs at hget
  simp_all

/-- The first occurrence of chord `i` is an event of chord `i`. -/
theorem first_div (hi : i < L.length) :
    E.getD ztckk 0 / 2 = i := by
  have := congrArg Prod.fst (h.first_code hi)
  rw [evOf_fst] at this
  tauto

/-- **The first event is the left endpoint iff `kl < kr`.** -/
theorem first_parity (hi : i < L.length) :
    E.getD ztckk 0 % 2 = 0 ↔ kl M Q L i < kr M Q L i := by
  zumdc
  have hcode := h.first_code hi
  have hdiv := h.first_div hi
  have hne := hc.kl_ne_kr hi
  generalize E.getD ztckk 0 = c at hcode hdiv
  subst hdiv
  unfold evOf at hcode
  rcases hc.e1_e2_cases ztbek with ⟨hlt, he1, -⟩ | ⟨hle, he1, -⟩
  · zukub
    refine ⟨fun _ => hlt, fun _ => ?_⟩
    by_contra hodd
    rw [ite_eq_right hodd] at hcode
    have := congrArg (fun e : Ev => e.2.1) hcode
    tauto
  · zukub
    refine ⟨fun hev => ?_, fun hlt => absurd hlt ztwan⟩
    rw [ite_eq_left hev] at hcode
    have := congrArg (fun e : Ev => e.2.1) hcode
    tauto

/-- **The chord record** from the first occurrence `m` of the chord: `up`/`dn` are the label
before it and the chord itself, by the parity of the code there. -/
theorem chordRec_eq (hi : i < L.length) :
    chordRec M Q L E i =
      { h := (L.getD i ztt).1, lp := (L.getD i ztt).2.1,
        rp := (L.getD i ztt).2.2,
        up := if E.getD ztxcb 0 % 2 = 0 then
            ridx ztbarc else i + 1,
        dn := if E.getD ztxcb 0 % 2 = 0 then i + 1 else
            ridx ztbarc } := by
  have hp := h.first_parity hi
  rw [word_eq] at hp
  unfold chordRec
  rw [h.outside_eq hi, word_eq]
  grind

/-- The word is a parenthesis word. -/
theorem word_ok : BuildStack.NoCross ztyhl ∧ BuildStack.Twice ztyhl := by
  have := h.ctx.word
  rw [← word_eq M Q L E]
  tauto
end Input

/-! ## The stack pass -/
variable {w : List ℕ}
/-- **The pass pops** at a letter iff that letter occurred before. -/
theorem push_iff (htw : BuildStack.Twice w) (hnc : BuildStack.NoCross w) {m : ℕ}
    (hm : m < w.length) :
    (BuildStack.run ztibp).head? = some w[m] ↔ w[m] ∈ w.take m := by
  have hpre : w.take m ++ [w[m]] ++ w.drop ztbl = w := by
    simp
  have hxw : w.count w[m] = 2 := htw _ ztvrk
  have hcx : (w.take m).count w[m] ≤ 1 := by
    grind
  rw [BuildStack.run_eq_openList htw hnc (take_prefix m w), ← count_pos_iff]
  constructor
  · zujba
    have := BuildStack.mem_openList.1 (mem_of_mem_head? hh)
    omega
  · zulmx
    obtain ⟨rest, hrest⟩ := BuildStack.head_openList htw hnc hpre.symm by_omega
    simp_all

/-- The first occurrence of a new letter. -/
theorem idxOf_new {m : ℕ} (hm : m < w.length) (hn : w[m] ∉ w.take m) :
    w.idxOf w[m] = m := by
  generalize hx : w[m] = x at hn
  have hw : w = w.take m ++ x :: w.drop ztbl := by
    rw [← hx, ← drop_eq_getElem_cons hm, take_append_drop]
  grind

/-! ## The gaps -/

/-- **The gap starts** are the last position and the positions where the key strictly increases. -/
theorem Input.gap_iff (h : Input M Q L E) {m : ℕ} (hm : m < E.length) :
    m ∈ gapStarts M Q L E ↔ (m + 1 = E.length ∨
      M.key Q ztwwn < M.key Q (wposOf L (E.getD ztbl 0))) := by
  zumst
  rw [mem_filter, decide_eq_true_iff]
  simp only [mem_range, hm, true_and]
  constructor
  · zudst
    · omega
    · zuhtg
      · omega
      · right; rw [h.key_s hm, h.key_s by_omega]; exact h1
  · zudst
    · omega
    · zuhtg
      · omega
      · right; rw [← h.key_s hm, ← h.key_s by_omega]; exact h1
end
end BuildNF
@[expose] public section
open Set
open BuildNF (codeLe wposOf tieBit)
namespace DownBase
section generic
variable {α : Type} (f : α → Bool)

/-- The number of kept entries before position `i`. -/
def rankF (L : List α) (i : ℕ) : ℕ := ((L.take i).filter f).length
theorem getD_filter_rank {L : List α} {i : ℕ} (d : α) (hi : i < L.length)
    (hf : f ztjjn = true) : (L.filter f).getD (rankF f L i) d = L.getD i d := by
  induction L generalizing i with
  | nil => simp at hi
  | cons x L ih =>
    cases i with
    | zero =>
      simp only [List.getD_cons_zero] at hf ⊢
      simp [rankF, hf]
    | succ k =>
      simp only [List.getD_cons_succ] at hf ⊢
      have ih' := ih by_simp_all hf
      unfold rankF at ih' ⊢
      simp only [List.take_succ_cons, List.filter_cons]
      split_ifs <;> (try simp only [List.length_cons, List.getD_cons_succ]) <;> exact ih'
theorem rankF_add (L : List α) (i m : ℕ) :
    rankF f L ztjym = rankF f L i + (((L.drop i).take m).filter f).length := by
  unfold rankF
  grind
theorem rankF_lt_of {L : List α} {i j : ℕ} (d : α) (hij : i < j) (hi : i < L.length)
    (hf : f ztjjn = true) : rankF f L i < rankF f L j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = i + (m + 1) := ztoov
  zufog
theorem rankF_lt_length {L : List α} {i : ℕ} (d : α) (hi : i < L.length)
    (hf : f ztjjn = true) : rankF f L i < (L.filter f).length := by
  have := rankF_lt_of f d (show i < i + 1 by omega) hi hf
  have h2 : rankF f L ztg ≤ (L.filter f).length := by
    unfold rankF
    exact ((List.take_sublist _ _).filter f).length_le
  omega
theorem rankF_length (L : List α) : rankF f L L.length = (L.filter f).length := by
  unfold rankF; simp
theorem rankF_succ {L : List α} {i : ℕ} (d : α) (hi : i < L.length) :
    rankF f L ztg = rankF f L i + if f ztjjn then 1 else 0 := by
  zufog

/-- The kept codes below `2 i`: twice the kept chords below `i`. -/
theorem count_codes {L : List α} (d : α) {i : ℕ} (hi : i ≤ L.length) :
    ((List.range ztvd).filter fun c => f (L.getD ztbek d)).length = 2 * rankF f L i := by
  induction i with
  | zero => zuocx
  | succ k ih =>
    rw [rankF_succ f d by_omega, show 2 * zts = 2 * k + 1 + 1 by ring, List.range_succ,
      List.range_succ, List.filter_append, List.filter_append, List.length_append,
      List.length_append, show 2 * k + 1 = 2 * k + 1 from rfl, ih by_omega]
    have e1 : ztckt / 2 = k := by_omega
    have e2 : ztekz / 2 = k := by_omega
    simp only [List.filter_cons, List.filter_nil, e1, e2]
    split_ifs <;> simp; omega
end generic

/-! ## The kept list and the renumbering -/
variable (li : Bool) (n : ℕ)

/-- **The kept chord triples.** -/
def keepL (L : List zte) : List zte := L.filter ztse

/-- The event code `c` belongs to a kept chord. -/
def keptC (L : List zte) (c : ℕ) : Bool := keepX li n (L.getD ztbek ztt)

/-- The renumbered event code. -/
def newCode (L : List zte) (c : ℕ) : ℕ := 2 * rankF ztse L ztbek + c % 2

/-- **The renumbered event list.** -/
def dropE (L : List zte) (E : List ℕ) : List ℕ :=
  (E.filter (keptC li n L)).map (newCode li n L)
variable {li n}
theorem getD_keepL {L : List zte} {i : ℕ} (hi : i < L.length)
    (hk : keepX li n ztwrk = true) :
    (keepL li n L).getD (rankF ztse L i) ztt = L.getD i ztt :=
  getD_filter_rank _ _ hi hk
theorem wposOf_newCode {L : List zte} {c : ℕ} (hc : c < 2 * L.length)
    (hk : keptC li n L c = true) : wposOf ztdou ztkbk = wposOf L c := by
  zuglb
  have h2 : newCode li n L c / 2 = rankF ztse L ztbek := by unfold newCode; omega
  zulci
  zubuw
  zulrn
  rw [getD_keepL by_omega hk]
variable (M : Model) (Q : Polygon)
theorem tieBit_newCode {L : List zte} {c : ℕ} (hc : c < 2 * L.length)
    (hk : keptC li n L c = true) : tieBit M ztdou ztkbk = tieBit M L c := by
  zuglb
  unfold tieBit
  rw [wposOf_newCode hc hk, h1]
theorem codeLe_newCode {L : List zte} {c c' : ℕ}
    (hc : c < 2 * L.length) (hk : keptC li n L c = true) (hc' : c' < 2 * L.length)
    (hk' : keptC li n L c' = true) :
    codeLe M Q ztdou ztkbk (newCode li n L c') ↔ codeLe M Q L c c' := by
  zului
  rw [wposOf_newCode hc hk, wposOf_newCode hc' hk', tieBit_newCode M hc hk,
    tieBit_newCode M hc' hk']
theorem newCode_lt {L : List zte} {c : ℕ} (hc : c < 2 * L.length)
    (hk : keptC li n L c = true) : newCode li n L c < 2 * (keepL li n L).length := by
  have := rankF_lt_length ztse ztt (show c / 2 < L.length by omega) hk
  unfold newCode keepL
  omega
theorem newCode_inj {L : List zte} {c c' : ℕ} (hc : c < 2 * L.length)
    (hk : keptC li n L c = true) (hc' : c' < 2 * L.length) (hk' : keptC li n L c' = true)
    (h : newCode li n L c = newCode li n L c') : c = c' := by
  unfold newCode at h
  rcases lt_trichotomy ztbek ztthi with h1 | h1 | h1
  · have := rankF_lt_of ztse ztt h1 by_omega hk
    omega
  · omega
  · have := rankF_lt_of ztse ztt h1 by_omega hk'
    omega
variable {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
theorem mem_lt (hperm : E.Perm ztct) {c : ℕ} (hc : c ∈ E) :
    c < 2 * L.length := List.mem_range.1 (hperm.mem_iff.1 hc)

/-- **The renumbered event list is sorted.** -/
theorem dropE_pairwise (hperm : E.Perm ztct)
    (hsort : E.Pairwise ztxi) :
    (dropE li n L E).Pairwise (codeLe M Q ztdou) := by
  zulum
  zuczn
  refine (hsort.filter _).imp_of_mem fun {a b} ha hb hab => ?_
  zujgv
  exact (codeLe_newCode M Q zttth ha.2 zttti hb.2).2 hab

/-- **The renumbered event list is a permutation of the new codes.** -/
theorem dropE_perm (hperm : E.Perm ztct) :
    (dropE li n L E).Perm (List.range ztldj) := by
  zuiyq
  have hnd' : (dropE li n L E).Nodup := by
    zulum
    refine (hnd.filter _).map_on fun a ha b hb hab => ?_
    zujgv
    exact newCode_inj zttth ha.2 zttti hb.2 hab
  have hsub : dropE li n L E ⊆ List.range ztldj := by
    zuh
    unfold dropE at hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_filter] at hc
    exact List.mem_range.2 (newCode_lt (mem_lt hperm hc.1) hc.2)
  have hlen : (dropE li n L E).length = 2 * (keepL li n L).length := by
    zulum
    rw [List.length_map, (hperm.filter _).length_eq]
    have := count_codes ztse (L := L) ztt (le_refl L.length)
    rw [rankF_length] at this
    tauto
  exact (hnd'.subperm hsub).perm_of_length_le by_simp_all

/-- **The kept triples are valid.** -/
theorem chordTriplesOK_keepL {M : Model} {Q : Polygon} (h : ChordTriplesOK M Q L) :
    ChordTriplesOK M Q ztdou := by
  obtain ⟨hF, hnd, hat, hlt⟩ := h
  have hsub : {c | ∃ x ∈ keepL li n L, c = (recOf x).toSet M Q} ⊆
      {c | ∃ x ∈ L, c = (recOf x).toSet M Q} := by
    zueq
    exact ⟨x, (List.mem_filter.1 hx).1, rfl⟩
  refine ⟨⟨hF.1.subset hsub, hsub.trans hF.2.1, fun c hc => hF.2.2 c ztvwi⟩,
    hnd.sublist (List.filter_sublist.map _), fun x hx => hat x (List.mem_filter.1 hx).1,
    fun x hx => hlt x (List.mem_filter.1 hx).1⟩

/-- **The kept family is the family intersected with the vertex chords** (interior model). -/
theorem family_keepL {Q : Polygon} (hQ : Q.Simple) (hDH : DistinctHeights Q)
    (hli : li = true ↔ Mountain.LeftInside Q) (h : ChordTriplesOK ztd Q L) :
    {c | ∃ x ∈ keepL li Q.n L, c = (recOf x).toSet ztd Q} =
      {c | ∃ x ∈ L, c = (recOf x).toSet ztd Q} ∩ (interiorModel Q).Full := by
  obtain ⟨hF, -, hat, hlt⟩ := h
  have hiff : ∀ x ∈ L, ((recOf x).toSet ztd Q ∈ (interiorModel Q).Full ↔
      keepX li Q.n x = true) := fun x hx =>
    mem_full_iff hQ hDH hli (hat x hx) (hF.2.1 ztcyj) (hlt x hx)
  zubcj
  constructor
  · zuod
    obtain ⟨hxL, hk⟩ := List.mem_filter.1 hx
    grind
  · rintro ⟨⟨x, hx, rfl⟩, hfull⟩
    exact ⟨x, List.mem_filter.2 ⟨hx, (hiff x hx).1 hfull⟩, rfl⟩
end DownBase
open OracleQ OracleR
namespace OracleQ
structure NodeMemOK (m : ℕ → ℕ) (V : QV) (N : NF) : Prop where
  nf : NFAt m V.NB N
  AB : m ztfos = V.AB
  RB : m zttdv = V.RB
  SB : m ztfot = V.SB
  LB : m zttdw = V.LB
  A : V.A = N.arcs.length
  pos : ∀ j, j < V.A → m ztfou < V.A ∧ N.seq.getD ztzgk 0 = j
variable {C : Chain} {Q : Polygon} {N : NF} {m : ℕ → ℕ} {V : QV}
theorem arcSe_eq (hm : NodeMemOK m V N) {j : ℕ} (hj : j < V.A) :
    arcSe m V j = (N.arc j).s.edge := by
  have := (hm.nf.2.2.2.2.2.2.1 j ztljh).2.1
  unfold arcSe; zuosk; omega
theorem arcEe_eq (hm : NodeMemOK m V N) {j : ℕ} (hj : j < V.A) :
    arcEe m V j = (N.arc j).e.edge := by
  have := (hm.nf.2.2.2.2.2.2.1 j ztljh).2.2.2.1
  unfold arcEe; zuosk; omega

/-- **The points scanned for an arc record** are the scanned points of its spine position. -/
theorem arcPts_eq (hN : IsNF ztc Q N) (hP : C.P.Simple) (hm : NodeMemOK m V N)
    (hVm : V.m = C.m) {j : ℕ} (hj : j < V.A) :
    arcPts m V C j = scanSet C Q N ztdlm := by
  zugpm
  have hnW : ztkyz := by rw [walk_n, hVm]
  zukfr
  zumx
  rw [mem_scanSet_iff, scanLen_eq C Q N hN hP ztmec]
  unfold arcPts scanned
  zuwb
  have hlen : scanLenR N (chainModel C).W.n N.arcs.length ztdlm = arcLenM m V j := by
    zumul
    rw [hsj, hnW, ← hm.A, arcSe_eq hm hj, arcEe_eq hm hj]
  have hidx : ∀ k, scanIdx (chainModel C).W.n N ztdlm k =
      scanW zthn ztlfy k := by
    intro k; unfold scanIdx scanW; rw [hsj, hnW, arcSe_eq hm hj]
  simp_all

/-- **The points scanned for a node are its `nodeScan`.** -/
theorem nodePts_eq (hN : IsNF ztc Q N) (hP : C.P.Simple) (hm : NodeMemOK m V N)
    (hVm : V.m = C.m) (v : ℕ) : nodePts m V C v = nodeScan C Q N v := by
  zuzl
  have hsl := NFLoc.seq_length hN
  zumx
  simp only [nodePts, nodeScan, mem_ofPred_eq]
  zunwe
  by_cases hv : v < V.A
  swap
  · omega
  have hvA : v < N.arcs.length := by zunwe; exact hv
  -- the region of the node
  have hj0 : ztorf := by
    have := hm.nf.2.2.2.2.2.2.2.2.1 v by_omega
    zucrf
  zuhyt
  have hr : ztorg := by
    have := (hm.nf.2.2.2.2.2.2.1 _ hj0A).1
    zucag
  zufwf
  zubhd
  have hna' : ztygu := by
    zucff
  have hls : ∀ t, t < (N.region ztcax).arcs.length →
      nodeArc m V v t = (N.region ztcax).arcs.getD t 0 := by
    zucj
    zubiw
  have hmemR := hA.2.2.2 _ hrR
  constructor
  · rintro ⟨-, t, ht, hx⟩
    zumks
    zugej
    rw [hls t ht] at hx
    set j := (N.region ztcax).arcs.getD t 0 with hj
    have hjmem : ztyyt := by
      grind
    obtain ⟨hjA, hjr⟩ := (hmemR j).1 hjmem
    zuegx
    zugpn
    refine ⟨arcPos m V j, hpA, ?_, ?_⟩
    · show (N.arc (N.seq.getD ztzgk 0)).reg = rgi N v
      simp_all
    · rw [← arcPts_eq hN hP hm hVm hjA']; exact hx
  · rintro ⟨-, p, hp, hrp, hx⟩
    zumks
    have hpN : p < N.arcs.length := by zunwe; exact hp
    set j := sj N p with hj
    have hjA : ztsjo := NFLoc.seq_lt hN hpN
    zuegx
    have hjmem : ztyyt := (hmemR j).2 ⟨hjA, hrp⟩
    obtain ⟨t, ht, htj⟩ := List.getElem_of_mem hjmem
    zugpn
    have hpp : arcPos m V j = p := sj_inj hN ztmec hpN hpj
    refine ztreq
    rw [hls t ht, NFLoc.getD_of_lt 0 ht, htj, arcPts_eq hN hP hm hVm hjA', hpp]
    zufsg
end OracleQ
end
namespace DownBase
open Machine Machine.Stmt Programs
@[expose] public section
def dSetup : Stmt := block [.constN 200100 1, .constN 200101 0, .constN 200105 2,
  .inputSize 200102, .subN 200104 200102 200100, .addN 200116 200000 200100,
  .loadN 200106 200116, .constN 200103 0, .addN 200136 200002 200002, .copyN 200004 9999,
  .copyN 200121 9999, .addN 200121 200121 200002, .addN 200121 200121 200002,
  .addN 200121 200121 200002, .addN 200122 200121 200136, .addN 9999 200122 200136,
  .copyN 200006 200122, .constN 200110 0, .copyN 200111 200001, .copyN 200117 200121,
  .constN 200118 0, .copyN 200119 200004]

/-- The normalised bit: `1` iff the raw bit is `1`. -/
def dBit : Stmt :=
  .ifLtN 200106 200105 (.ifLtN 200101 200106 (.instr (.constN 200103 1)) .skip) .skip

/-- Load the triple; clear the flag. -/
def dLoad : Stmt := block [.loadN 200112 200111, .addN 200111 200111 200100,
  .loadN 200113 200111, .addN 200111 200111 200100, .loadN 200114 200111,
  .addN 200111 200111 200100, .constN 200115 0]

/-- Raise the flag if the height vertex starts the walk edge in register `p`. -/
def dTest (p : ℕ) : Stmt :=
  .seq ztfej
    (.ifLtN 200112 200116 .skip (.ifLtN 200116 200112 .skip ztotv))

/-- A kept chord: append the triple, table entries `2j + 1`, `2j + 2`. -/
def dKeep : Stmt := block [.storeN 200119 200112, .addN 200119 200119 200100,
  .storeN 200119 200113, .addN 200119 200119 200100, .storeN 200119 200114,
  .addN 200119 200119 200100, .addN 200120 200118 200118, .addN 200120 200120 200100,
  .storeN 200117 200120, .addN 200117 200117 200100, .addN 200120 200120 200100,
  .storeN 200117 200120, .addN 200117 200117 200100, .addN 200118 200118 200100]

/-- A dropped chord: table entries `0, 0`. -/
def dDrop : Stmt := block [.storeN 200117 200101, .addN 200117 200117 200100,
  .storeN 200117 200101, .addN 200117 200117 200100]

/-- One chord. -/
def dBody1 : Stmt :=
  .seq dLoad (.seq (dTest 200113) (.seq (dTest 200114)
    (.seq ztpro (.instr (.addN 200110 200110 200100)))))

/-- The chord pass. -/
def dLoop1 : Stmt := .whileLtN 200110 200002 dBody1

/-- Between the passes. -/
def dMid : Stmt := block [.copyN 200005 200118, .constN 200130 0, .copyN 200131 200003,
  .copyN 200134 200122]

/-- One event. -/
def dBody2 : Stmt :=
  .seq (block [.loadN 200132 200131, .addN 200131 200131 200100, .addN 200135 200121 200132,
      .loadN 200133 200135])
    (.seq (.ifLtN 200101 200133 (block [.subN 200133 200133 200100, .storeN 200134 200133,
      .addN 200134 200134 200100]) .skip) (.instr (.addN 200130 200130 200100)))

/-- The event pass. -/
def dLoop2 : Stmt := .whileLtN 200130 200136 dBody2

/-- **The procedure of `DropAugSpec`.** -/
def dropStmt : Stmt := .seq dSetup (.seq dBit (.seq dLoop1 (.seq dMid dLoop2)))

/-! ## The memory of the chord pass -/

/-- Word `q` of a triple list. -/
def tw (L' : List zte) (q : ℕ) : ℕ :=
  if q % 3 = 0 then (L'.getD ztoev ztt).1
  else if q % 3 = 1 then (L'.getD ztoev ztt).2.1 else (L'.getD ztoev ztt).2.2

/-- The code table: new code plus one, or `0` for a dropped chord. -/
def tbl (li : Bool) (n : ℕ) (L : List zte) (q : ℕ) : ℕ :=
  if keptC li n L q then newCode li n L q + 1 else 0

/-- The memory after `i` chords. -/
def mem1 (m₀ : ℕ → ℕ) (li : Bool) (n : ℕ) (L : List zte) (B' X i a : ℕ) : ℕ :=
  if B' ≤ a ∧ a < B' + 3 * rankF ztse L i then tw ztdou ztjnv
  else if X ≤ a ∧ a < X + 2 * i then tbl li n L zttel else m₀ a
theorem rankF_le (f : ℕ × ℕ × ℕ → Bool) (L : List zte) (i : ℕ) : rankF f L i ≤ i := by
  unfold rankF
  grind
variable {m₀ m : ℕ → ℕ} {li : Bool} {n : ℕ} {L : List (ℕ × ℕ × ℕ)} {B' X i : ℕ}
/-- The memory step of a kept chord. -/
theorem mem1_keep
    (hm : ∀ a, m a = mem1 m₀ li n L B' X i a) (hi : i < L.length) (hBX : B' + 3 * L.length ≤ X)
    (hk : keepX li n ztwrk = true) (a : ℕ) :
    (if a = X + 2 * i + 1 then 2 * rankF ztse L i + 2
      else if a = X + 2 * i then 2 * rankF ztse L i + 1
      else if a = B' + 3 * rankF ztse L i + 2 then (L.getD i ztt).2.2
      else if a = B' + 3 * rankF ztse L i + 1 then (L.getD i ztt).2.1
      else if a = B' + 3 * rankF ztse L i then (L.getD i ztt).1 else m a) =
      mem1 m₀ li n L B' X ztg a := by
  zuize
  zueyo
  zuere
  zuhoi
  have hg := getD_keepL hi hk
  zuezw
  have hkc : ∀ s, s < 2 → keptC li n L ztjfh = true := fun s hs => by
    zumte
  have hnc : ∀ s, s < 2 → newCode li n L ztjfh = 2 * j + s := fun s hs => by
    unfold newCode; grind
  zubyr
  zulby
  zubim
  zufea
  · zucuj
    rw [ite_eq_left rfl, ite_eq_right by_omega, ite_eq_left by_omega, show X + 2 * i + 1 - X = 2 * i + 1 by
      omega, tbl, ite_eq_left by_simp_all, hnc 1 by_norm_num]
  zugje
  · zuhqi
    rw [ite_eq_right h1, ite_eq_left rfl, ite_eq_right by_omega, ite_eq_left by_omega, show X + 2 * i - X = 2 * i by
      omega, tbl, show 2 * i = 2 * i + 0 by rfl, ite_eq_left (hkc 0 by_norm_num),
      hnc 0 by_norm_num]
  zunxw
  have htw : ∀ s, s < 3 → tw _ _ =
      if s = 0 then (L.getD i ztt).1 else if s = 1 then (L.getD i ztt).2.1
      else (L.getD i ztt).2.2 := fun s hs => by
    zuqd

  zuccp
  · subst h3
    rw [ite_eq_left rfl, ite_eq_left by_omega, show B' + 3 * j + 2 - B' = 3 * j + 2 by omega,
      htw 2 by_norm_num]
    simp
  zuccq
  · subst h4
    rw [ite_eq_right h3, ite_eq_left rfl, ite_eq_left by_omega, show B' + 3 * j + 1 - B' = 3 * j + 1 by omega,
      htw 1 by_norm_num]
    simp
  zucup
  · subst h5
    rw [ite_eq_right h3, ite_eq_right h4, ite_eq_left rfl, ite_eq_left by_omega,
      show B' + 3 * j - B' = 3 * j + 0 by omega, htw 0 by_norm_num]
    simp
  grind

/-- The memory step of a dropped chord. -/
theorem mem1_drop
    (hm : ∀ a, m a = mem1 m₀ li n L B' X i a) (hi : i < L.length) (hBX : B' + 3 * L.length ≤ X)
    (hk : keepX li n ztwrk = false) (a : ℕ) :
    (if a = X + 2 * i + 1 then 0 else if a = X + 2 * i then 0 else m a) =
      mem1 m₀ li n L B' X ztg a := by
  zuize
  zugdz
  zunu
  zuere
  have hkc : ∀ s, s < 2 → keptC li n L ztjfh = false := fun s hs => by
    zumte
  zubyr
  zulby
  zubim
  zufea
  · zucuj
    rw [ite_eq_left rfl, ite_eq_right by_omega, ite_eq_left by_omega, show X + 2 * i + 1 - X = 2 * i + 1 by
      omega, tbl, hkc 1 by_norm_num]
    simp
  zugje
  · zuhqi
    rw [ite_eq_right h1, ite_eq_left rfl, ite_eq_right by_omega, ite_eq_left by_omega, show X + 2 * i - X = 2 * i + 0
      by omega, tbl, hkc 0 by_norm_num]
    simp
  grind

/-! ## The pieces of one chord -/
section exec
variable {P : Polygon} {W : ℕ}
variable (c : Config)
set_option maxHeartbeats 4000000 in
theorem dLoad_exec (hw : WordsBounded W c) {a : ℕ} (h111 : c.nreg 200111 = a)
    (h100 : c.nreg 200100 = 1) (haW : a + 3 ≤ W) :
    ∃ c' k, Exec P W dLoad c c' k ∧ k = 7 ∧ c'.nreg 200112 = c.nmem a ∧
      c'.nreg 200113 = c.nmem ztdf ∧ c'.nreg 200114 = c.nmem ztvj ∧
      c'.nreg 200111 = a + 3 ∧ c'.nreg 200115 = 0 ∧
      (∀ r, r ≠ 200111 → r ≠ 200112 → r ≠ 200113 → r ≠ 200114 → r ≠ 200115 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold dLoad
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h111, h100]; omega)
  simp_all

/-- The equality test of the flag. -/
theorem dEq_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W (.ifLtN 200112 200116 .skip (.ifLtN 200116 200112 .skip
        ztotv)) c c' k ∧ k ≤ 5 ∧
      c'.nreg 200115 = (if c.nreg 200112 = c.nreg 200116 then 1 else c.nreg 200115) ∧
      (∀ r, r ≠ 200115 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  by_cases h1 : c.nreg 200112 < c.nreg 200116
  · exact ⟨c, _, .ifLtN_true h1 ztjd, by_omega, by_grind,
      by omega, rfl, rfl, rfl, rfl⟩
  by_cases h2 : c.nreg 200116 < c.nreg 200112
  · exact ⟨c, _, .ifLtN_false h1 ztxdj, by_omega,
      by grind, by_omega, rfl, rfl, rfl, rfl⟩
  have e := Exec.constN (P := P) hw 200115 1 hW
  exact ⟨_, _, .ifLtN_false h1 ztjdj, by_omega, by simp [show c.nreg 200112 =
    c.nreg 200116 by omega], by_simp_all, rfl, rfl, rfl, rfl⟩

/-- **The start-vertex test.** -/
theorem dTest_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) {li : Bool} {n p : ℕ}
    (_hp1 : p ≠ 200116) (h101 : c.nreg 200101 = 0)
    (hbit : c.nreg 200103 = if li then 1 else 0) (h104 : c.nreg 200104 = n - 1) :
    ∃ c' k, Exec P W (dTest p) c c' k ∧ k ≤ 8 ∧
      c'.nreg 200115 = (if c.nreg 200112 = wStart li n ztfgw then 1 else c.nreg 200115) ∧
      (∀ r, r ≠ 200115 → r ≠ 200116 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W
      ztfej c c₁ k₁ ∧
      k₁ ≤ 3 ∧ c₁.nreg 200116 = wStart li n ztfgw ∧
      (∀ r, r ≠ 200116 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧
      c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    cases li
    · have h : ¬ c.nreg 200101 < c.nreg 200103 := by_simp_all
      exact ⟨_, _, .ifLtN_false h (Exec.subN hw 200116 200104 p), by_omega,
        by simp [wStart, h104], by_simp_all, rfl, rfl, rfl, rfl⟩
    · have h : c.nreg 200101 < c.nreg 200103 := by_simp_all
      exact ⟨_, _, .ifLtN_true h (Exec.copyN hw 200116 p), by_omega,
        by rfl, by_simp_all, rfl, rfl, rfl, rfl⟩
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, r₂, m₂, rr₂, rm₂, o₂⟩ := dEq_exec (P := P) c₁ e₁.wb_right hW
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, ?_, by_simp_all, by_simp_all,
    by simp_all, by_simp_all, by_simp_all⟩
  simp_all
set_option maxHeartbeats 4000000 in
/-- **A kept chord.** -/
theorem dKeep_exec (hw : WordsBounded W c) {w x j : ℕ} (h119 : c.nreg 200119 = w)
    (h117 : c.nreg 200117 = x) (h118 : c.nreg 200118 = j) (h100 : c.nreg 200100 = 1)
    (hwW : w + 3 ≤ W) (hxW : x + 2 ≤ W) (hjW : 2 * j + 2 ≤ W) :
    ∃ c' k, Exec P W dKeep c c' k ∧ k = 14 ∧ c'.nreg 200119 = w + 3 ∧
      c'.nreg 200117 = x + 2 ∧ c'.nreg 200118 = j + 1 ∧
      (∀ r, r ≠ 200117 → r ≠ 200118 → r ≠ 200119 → r ≠ 200120 → c'.nreg r = c.nreg r) ∧
      (∀ a, c'.nmem a = if a = x + 1 then 2 * j + 2 else if a = x then 2 * j + 1
        else if a = w + 2 then c.nreg 200114 else if a = w + 1 then c.nreg 200113
        else if a = w then c.nreg 200112 else c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dKeep
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h119, h117, h118, h100]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r a1 a2 a3 a4 => ?_, fun a => ?_, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h119, h117, h118, h100]
  zudi
  grind
set_option maxHeartbeats 4000000 in
/-- **A dropped chord.** -/
theorem dDrop_exec (hw : WordsBounded W c) {x : ℕ} (h117 : c.nreg 200117 = x)
    (h100 : c.nreg 200100 = 1) (h101 : c.nreg 200101 = 0) (hxW : x + 2 ≤ W) :
    ∃ c' k, Exec P W dDrop c c' k ∧ k = 4 ∧ c'.nreg 200117 = x + 2 ∧
      (∀ r, r ≠ 200117 → c'.nreg r = c.nreg r) ∧
      (∀ a, c'.nmem a = if a = x + 1 then 0 else if a = x then 0 else c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dDrop
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h117, h100]; omega)
  refine ⟨rfl, ?_, fun r a1 => ?_, fun a => ?_, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h117, h100, h101]
  rfl
end exec
structure Inv1 (m₀ : ℕ → ℕ) (li : Bool) (n : ℕ) (L : List zte) (B B' X : ℕ)
    (c₀ d : Config) : Prop where
  i_le : d.nreg 200110 ≤ L.length
  rK : d.nreg 200002 = L.length
  r111 : d.nreg 200111 = B + 3 * d.nreg 200110
  r117 : d.nreg 200117 = X + 2 * d.nreg 200110
  r118 : d.nreg 200118 = rankF ztse L ztqlk
  r119 : d.nreg 200119 = B' + 3 * rankF ztse L ztqlk
  r100 : d.nreg 200100 = 1
  r101 : d.nreg 200101 = 0
  r103 : d.nreg 200103 = if li then 1 else 0
  r104 : d.nreg 200104 = n - 1
  fr : ∀ r, zthjs → d.nreg r = c₀.nreg r
  rr : d.rreg = c₀.rreg
  rm : d.rmem = c₀.rmem
  out : d.output = c₀.output
  mem : ∀ a, d.nmem a = mem1 m₀ li n L B' X ztqlk a
section exec
variable {P : Polygon} {W : ℕ}
variable {m₀ : ℕ → ℕ} {li : Bool} {n : ℕ} {L : List (ℕ × ℕ × ℕ)} {B B' X : ℕ}
set_option maxHeartbeats 4000000 in
/-- **One chord.** -/
theorem dBody1_exec
    (hL : ChordListAt m₀ B L) (hB : B + 3 * L.length ≤ B') (hX : X = B' + 3 * L.length)
    (hXW : X + 2 * L.length + 2 ≤ W) {c₀ d : Config} (hw : WordsBounded W d)
    (hI : Inv1 m₀ li n L B B' X c₀ d) (ht : d.nreg 200110 < d.nreg 200002) :
    ∃ d' k, Exec P W dBody1 d d' k ∧ WordsBounded W d' ∧ Inv1 m₀ li n L B B' X c₀ d' ∧
      d'.nreg 200110 = d.nreg 200110 + 1 ∧ 13 ≤ k ∧ k ≤ 45 := by
  rw [hI.rK] at ht
  set i := d.nreg 200110 with hi
  set x := L.getD i ztt with hx
  zuhoi
  zuere
  obtain ⟨l1, l2, l3⟩ := hL i ht
  have hmL : ∀ q, q < 3 → d.nmem ztnjg = m₀ ztnjg := fun q hq => by
    zuocy; unfold mem1; grind
  zudk
  -- load
  obtain ⟨d₁, k₁, e₁, hk₁, v12, v13, v14, v11, v15, r₁, m₁, rr₁, rm₁, o₁⟩ :=
    dLoad_exec (P := P) d hw hI.r111 hI.r100 by_omega
  rw [← hi] at v12 v13 v14 v11
  zucdc

  rw [hm0, l1] at v12
  rw [hmL 1 by_norm_num, l2] at v13
  rw [hmL 2 by_norm_num, l3] at v14
  -- the two tests
  obtain ⟨d₂, k₂, e₂, hk₂, v₂, r₂, m₂, rr₂, rm₂, o₂⟩ := dTest_exec (P := P) d₁ e₁.wb_right hW1
    (li := li) (n := n) (p := 200113) by_norm_num
    (by rw [r₁ _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num, hI.r101])
    (by rw [r₁ _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num, hI.r103])
    (by rw [r₁ _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num, hI.r104])
  obtain ⟨d₃, k₃, e₃, hk₃, v₃, r₃, m₃, rr₃, rm₃, o₃⟩ := dTest_exec (P := P) d₂ e₂.wb_right hW1
    (li := li) (n := n) (p := 200114) by_norm_num
    (by rw [r₂ _ by_norm_num by_norm_num, r₁ _ by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num, hI.r101])
    (by rw [r₂ _ by_norm_num by_norm_num, r₁ _ by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num, hI.r103])
    (by rw [r₂ _ by_norm_num by_norm_num, r₁ _ by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num, hI.r104])
  -- registers of `d₃`
  have g3 : ∀ r, r ≠ 200111 → r ≠ 200112 → r ≠ 200113 → r ≠ 200114 → r ≠ 200115 →
      r ≠ 200116 → d₃.nreg r = d.nreg r := fun r a1 a2 a3 a4 a5 a6 => by
    grind
  have e12 : d₃.nreg 200112 = x.1 := by
    grind
  have e13 : d₃.nreg 200113 = x.2.1 := by
    grind
  have e14 : d₃.nreg 200114 = x.2.2 := by
    grind
  have hflag : d₃.nreg 200115 = if keepX li n x = true then 1 else 0 := by
    rw [v₃, v₂, v15, r₂ _ by_norm_num by_norm_num, v12, v13,
      r₂ _ by_norm_num by_norm_num, v14]
    zulrg
    have hk := keepX_iff li n x
    grind
  have hm3 : ztpoi := by_grind
  -- the branch and the increment
  have hB' : B' + 3 * L.length ≤ X := by_omega
  obtain ⟨d₄, k₄, e₄, hk₄, hk₄', g4, mem4, n117, n118, n119, rr₄, rm₄, o₄⟩ : ∃ d₄ k₄,
      Exec P W ztpro d₃ d₄ k₄ ∧ 5 ≤ k₄ ∧ k₄ ≤ 16 ∧
      (∀ r, r ≠ 200117 → r ≠ 200118 → r ≠ 200119 → r ≠ 200120 → d₄.nreg r = d₃.nreg r) ∧
      (∀ a, d₄.nmem a = mem1 m₀ li n L B' X ztg a) ∧
      d₄.nreg 200117 = X + 2 * ztg ∧
      d₄.nreg 200118 = rankF ztse L ztg ∧
      d₄.nreg 200119 = B' + 3 * rankF ztse L ztg ∧
      d₄.rreg = d₃.rreg ∧ d₄.rmem = d₃.rmem ∧ d₄.output = d₃.output := by
    have h101 : d₃.nreg 200101 = 0 := by
      rw [g3 _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
        by_norm_num, hI.r101]
    have h117 : d₃.nreg 200117 = X + 2 * i := by
      rw [g3 _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
        by_norm_num, hI.r117]
    have h100 : d₃.nreg 200100 = 1 := by
      rw [g3 _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
        by_norm_num, hI.r100]
    have hr := rankF_succ ztse ztt (L := L) ht
    cases hk : keepX li n x
    · -- dropped
      zukuq
      zvnhh at hflag
      have hn : ¬ d₃.nreg 200101 < d₃.nreg 200115 := by_omega
      obtain ⟨d₄, k₄, e₄, hk₄, w117, r₄, mm₄, rr₄, rm₄, o₄⟩ :=
        dDrop_exec (P := P) d₃ e₃.wb_right h117 h100 h101 by_omega
      zuvt
      zunu
      refine ⟨d₄, _, .ifLtN_false hn e₄, by_omega, by_omega, fun r a1 a2 a3 a4 => r₄ r a1,
        fun a => ?_, by_omega, ?_, ?_, rr₄, rm₄, o₄⟩
      · rw [mm₄, hm3]
        exact mem1_drop hI.mem ht hB' hk a
      · rw [r₄ _ by_norm_num, g3 _ by_norm_num by_norm_num by_norm_num by_norm_num
          by_norm_num by_norm_num, hI.r118, hr]
      · rw [r₄ _ by_norm_num, g3 _ by_norm_num by_norm_num by_norm_num by_norm_num
          by_norm_num by_norm_num, hI.r119, hr]
    · -- kept
      zukuq
      simp only [ite_true] at hflag
      have hp : d₃.nreg 200101 < d₃.nreg 200115 := by_omega
      have h119 : d₃.nreg 200119 = B' + 3 * j := by
        rw [g3 _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
          by_norm_num, hI.r119]
      have h118 : d₃.nreg 200118 = j := by
        rw [g3 _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
          by_norm_num, hI.r118]
      obtain ⟨d₄, k₄, e₄, hk₄, w119, w117, w118, r₄, mm₄, rr₄, rm₄, o₄⟩ :=
        dKeep_exec (P := P) d₃ e₃.wb_right h119 h117 h118 h100 by_omega by_omega by_omega
      zuvt
      zufbp
      refine ⟨d₄, _, .ifLtN_true hp e₄, by_omega, by_omega, r₄, fun a => ?_,
        by omega, by_omega, by_omega, rr₄, rm₄, o₄⟩
      rw [mm₄, e12, e13, e14, hm3]
      exact mem1_keep hI.mem ht hB' hk a
  have h110 : d₄.nreg 200110 = i := by
    grind
  have h100 : d₄.nreg 200100 = 1 := by
    rw [g4 _ by_norm_num by_norm_num by_norm_num by_norm_num,
      g3 _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num,
      hI.r100]
  have e₅ := Exec.addN (P := P) e₄.wb_right 200110 200110 200100 by_omega
  set d₅ : Config := { d₄ with nreg := upd d₄.nreg 200110 (d₄.nreg 200110 + d₄.nreg 200100) }
    with hd₅
  have g5 : ∀ r, r ≠ 200110 → d₅.nreg r = d₄.nreg r := fun r hr => by zuouk; zumwy
  have v5 : d₅.nreg 200110 = i + 1 := by zuouk; simp [h110, h100]
  have g : ∀ r, zthjs → d₅.nreg r = d.nreg r := fun r hr => by
    rw [g5 r by_omega, g4 r by_omega by_omega by_omega by_omega,
      g3 r by_omega by_omega by_omega by_omega by_omega by_omega]
  have X' : Exec P W dBody1 d d₅ (k₁ + (k₂ + (k₃ + (k₄ + 1)))) :=
    .seq e₁ ztbq
  refine ⟨d₅, _, X', e₅.wb_right, ?_, v5, by_omega, by_omega⟩
  refine ⟨by_omega, by zunhi, ?_, ?_, ?_, ?_,
    by grind, by zunxu,
    by rw [g _ by_norm_num, hI.r103], by rw [g _ by_norm_num, hI.r104],
    fun r hr => by zunac, ?_, ?_, ?_, fun a => ?_⟩
  · grind
  · grind
  · grind
  · grind
  · show d₄.rreg = c₀.rreg; zunlv
  · show d₄.rmem = c₀.rmem; zunlw
  · show d₄.output = c₀.output; zunlx
  grind

/-- **The chord pass.** -/
theorem dLoop1_exec
    (hL : ChordListAt m₀ B L) (hB : B + 3 * L.length ≤ B') (hX : X = B' + 3 * L.length)
    (hXW : X + 2 * L.length + 2 ≤ W) {c₀ d : Config} (hw : WordsBounded W d)
    (hI : Inv1 m₀ li n L B B' X c₀ d) (h0 : d.nreg 200110 = 0) :
    ∃ d' k, Exec P W dLoop1 d d' k ∧ WordsBounded W d' ∧ Inv1 m₀ li n L B B' X c₀ d' ∧
      d'.nreg 200110 = L.length ∧ 13 * L.length ≤ k ∧ k ≤ 47 * L.length + 2 := by
  obtain ⟨d', k, e, ⟨hw', hI'⟩, htest, hk, hψ⟩ := SortR.whileLtN_potential_lb (P := P) (W := W)
    (a := 200110) (b := 200002) (body := dBody1)
    (fun d => WordsBounded W d ∧ Inv1 m₀ li n L B B' X c₀ d)
    (fun d => 47 * (L.length - d.nreg 200110)) (fun d => 13 * d.nreg 200110) ztoe
    (fun d ⟨hwd, hId⟩ ht => by
      obtain ⟨d', k, e, hw', hI', hi', hk1, hk2⟩ := dBody1_exec hL hB hX hXW hwd hId ht
      have := hId.rK
      refine zthmv
      · omega
      omega)
    ⟨hw, hI⟩
  zucdb

  · omega
  omega
end exec
variable {m₁ m : ℕ → ℕ}
theorem dropE_take_succ {E : List ℕ} {t : ℕ}
    (ht : t < E.length) :
    dropE li n L ztbadz = dropE li n L ztffi ++
      if keptC li n L zthan then [newCode li n L zthan] else [] := by
  have he : E.getD t 0 = E[t] := by
    simp_all
  zulum
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some, List.filter_append,
    List.map_append, he]
  grind
theorem dropE_take_length_le {E : List ℕ} (t : ℕ) :
    (dropE li n L ztffi).length ≤ t := by
  zulum
  grind

/-- The memory after `t` events. -/
def mem2 (m₁ : ℕ → ℕ) (li : Bool) (n : ℕ) (L : List zte) (E : List ℕ) (SE' t a : ℕ) :
    ℕ :=
  if SE' ≤ a ∧ a < SE' + (dropE li n L ztffi).length then
    (dropE li n L ztffi).getD zttek 0
  else m₁ a
theorem mem2_keep {li : Bool} {n : ℕ} {L : List zte} {E : List ℕ}
    {SE' t : ℕ} (hm : ∀ a, m a = mem2 m₁ li n L E SE' t a) (ht : t < E.length)
    (hk : keptC li n L zthan = true) (a : ℕ) :
    (if a = SE' + (dropE li n L ztffi).length then newCode li n L zthan else m a) =
      mem2 m₁ li n L E SE' ztbx a := by
  zubyr
  zulbz
  rw [dropE_take_succ ht, ite_eq_left hk, List.length_append, List.length_singleton]
  grind
theorem mem2_skip {li : Bool} {n : ℕ} {L : List zte} {E : List ℕ}
    {SE' t : ℕ} (hm : ∀ a, m a = mem2 m₁ li n L E SE' t a) (ht : t < E.length)
    (hk : keptC li n L zthan = false) (a : ℕ) : m a = mem2 m₁ li n L E SE' ztbx a := by
  zubyr
  zulbz
  rw [dropE_take_succ ht, hk]
  simp

/-- The invariant of the event pass. -/
structure Inv2 (m₁ : ℕ → ℕ) (li : Bool) (n : ℕ) (L : List zte) (E : List ℕ)
    (SE X SE' : ℕ) (c₁ d : Config) : Prop where
  t_le : d.nreg 200130 ≤ E.length
  r136 : d.nreg 200136 = E.length
  r131 : d.nreg 200131 = SE + d.nreg 200130
  r134 : d.nreg 200134 = SE' + (dropE li n L (E.take ztvok)).length
  r121 : d.nreg 200121 = X
  r100 : d.nreg 200100 = 1
  r101 : d.nreg 200101 = 0
  fr : ∀ r, zthjt → d.nreg r = c₁.nreg r
  rr : d.rreg = c₁.rreg
  rm : d.rmem = c₁.rmem
  out : d.output = c₁.output
  mem : ∀ a, d.nmem a = mem2 m₁ li n L E SE' ztvok a
section exec
variable {P : Polygon} {W : ℕ}
variable {m₁ : ℕ → ℕ} {li : Bool} {n : ℕ} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {SE X SE' : ℕ}
set_option maxHeartbeats 4000000 in
/-- **One event.** -/
theorem dBody2_exec
 (hE : ∀ t, t < E.length → m₁ ztnpg = E.getD t 0)
    (hSE : SE + E.length ≤ SE') (hX : ∀ c, c < E.length → m₁ ztnqi = tbl li n L c)
    (hXS : X + E.length ≤ SE') (hEl : E.length = 2 * L.length)
    (hperm : E.Perm ztct) (hW : SE' + E.length + 1 ≤ W)
    {c₁ d : Config} (hw : WordsBounded W d) (hI : Inv2 m₁ li n L E SE X SE' c₁ d)
    (ht : d.nreg 200130 < d.nreg 200136) :
    ∃ d' k, Exec P W dBody2 d d' k ∧ WordsBounded W d' ∧ Inv2 m₁ li n L E SE X SE' c₁ d' ∧
      d'.nreg 200130 = d.nreg 200130 + 1 ∧ 7 ≤ k ∧ k ≤ 11 := by
  rw [hI.r136] at ht
  set t := d.nreg 200130 with htdef
  set l := dropE li n L ztffi with hl
  have hll : l.length ≤ t := dropE_take_length_le t
  set c := E.getD t 0 with hc
  have hcE : c ∈ E := by
    simp_all
  have hc2 : c < E.length := by_grind
  have mSE : d.nmem ztnpg = c := by
    zuhlk
  have mX : d.nmem ztnqi = tbl li n L c := by
    zuhlk
  -- the load block
  obtain ⟨d₁, k₁, e₁, hk₁, v32, v31, v35, v33, r₁, m₁', rr₁, rm₁, o₁⟩ : ∃ d₁ k₁, Exec P W
      (block [.loadN 200132 200131, .addN 200131 200131 200100, .addN 200135 200121 200132,
        .loadN 200133 200135]) d d₁ k₁ ∧ k₁ = 4 ∧ d₁.nreg 200132 = c ∧
      d₁.nreg 200131 = SE + t + 1 ∧ d₁.nreg 200135 = X + c ∧ d₁.nreg 200133 = tbl li n L c ∧
      (∀ r, r ≠ 200131 → r ≠ 200132 → r ≠ 200133 → r ≠ 200135 → d₁.nreg r = d.nreg r) ∧
      d₁.nmem = d.nmem ∧ d₁.rreg = d.rreg ∧ d₁.rmem = d.rmem ∧ d₁.output = d.output := by
    have h131 := hI.r131
    have h100 := hI.r100
    have h121 := hI.r121
    rw [← htdef] at h131
    exec_block
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, h131, h100, h121, mSE]; omega)
    simp_all
  have g1 : ∀ r, (r < 200130 ∨ 200135 < r ∨ r = 200130 ∨ r = 200134) →
      d₁.nreg r = d.nreg r := fun r hr => r₁ r by_omega by_omega by_omega by_omega
  -- the branch
  obtain ⟨d₂, k₂, e₂, hk₂, hk₂', g2, n134, mem2', rr₂, rm₂, o₂⟩ : ∃ d₂ k₂,
      Exec P W (.ifLtN 200101 200133 (block [.subN 200133 200133 200100, .storeN 200134 200133,
        .addN 200134 200134 200100]) .skip) d₁ d₂ k₂ ∧ 2 ≤ k₂ ∧ k₂ ≤ 4 ∧
      ztgsk ∧
      d₂.nreg 200134 = SE' + (dropE li n L ztbadz).length ∧
      (∀ a, d₂.nmem a = mem2 m₁ li n L E SE' ztbx a) ∧
      d₂.rreg = d₁.rreg ∧ d₂.rmem = d₁.rmem ∧ d₂.output = d₁.output := by
    have h101 : d₁.nreg 200101 = 0 := by rw [g1 _ by_omega, hI.r101]
    have h134 : d₁.nreg 200134 = SE' + l.length := by rw [g1 _ by_omega, hI.r134]
    have h100 : d₁.nreg 200100 = 1 := by rw [g1 _ by_omega, hI.r100]
    have hsucc := dropE_take_succ (li := li) (n := n) (L := L) ht
    rw [← hc, ← hl] at hsucc
    cases hk : keptC li n L c
    · have hv : d₁.nreg 200133 = 0 := by zunxv; rfl
      have hn : ¬ d₁.nreg 200101 < d₁.nreg 200133 := by_omega
      zukur
      simp only [Bool.false_eq_true, ite_false, List.append_nil] at hsucc
      refine ⟨d₁, _, .ifLtN_false hn ztekc, le_rfl, by_omega, fun _ _ _ => rfl,
        by grind, fun a => ?_, rfl, rfl, rfl⟩
      rw [m₁']
      exact mem2_skip hI.mem ht hk a
    · have hv : d₁.nreg 200133 = newCode li n L c + 1 := by zunxv; rfl
      have hp : d₁.nreg 200101 < d₁.nreg 200133 := by_omega
      zukur
      simp only [ite_true] at hsucc
      obtain ⟨d₂, k₂, e₂, hk₂, w134, r₂, mm₂, rr₂, rm₂, o₂⟩ : ∃ d₂ k₂, Exec P W
          (block [.subN 200133 200133 200100, .storeN 200134 200133,
            .addN 200134 200134 200100]) d₁ d₂ k₂ ∧ k₂ = 3 ∧
          d₂.nreg 200134 = SE' + l.length + 1 ∧
          ztgsk ∧
          (∀ a, d₂.nmem a = if a = SE' + l.length then newCode li n L c else d₁.nmem a) ∧
          d₂.rreg = d₁.rreg ∧ d₂.rmem = d₁.rmem ∧ d₂.output = d₁.output := by
        zuka
        exec_block
        all_goals try (simp (disch := omega) only [Machine.upd_same,
          Machine.upd_other, h134, h100, hv]; omega)
        refine ⟨rfl, ?_, fun r a1 a2 => ?_, fun a => ?_, rfl, rfl, rfl⟩
        all_goals simp (disch := omega) only [Machine.upd_same,
          Machine.upd_other, h134, h100, hv, Machine.upd_apply]
        simp
      refine ⟨d₂, _, .ifLtN_true hp e₂, by_omega, by_omega, r₂,
        by grind, fun a => ?_,
        rr₂, rm₂, o₂⟩
      rw [mm₂, m₁']
      exact mem2_keep hI.mem ht hk a
  -- the increment
  have h130 : d₂.nreg 200130 = t := by_grind
  have h100 : d₂.nreg 200100 = 1 := by
    rw [g2 _ by_omega by_omega, g1 _ by_omega, hI.r100]
  have e₃ := Exec.addN (P := P) e₂.wb_right 200130 200130 200100 by_omega
  set d₃ : Config := { d₂ with nreg := upd d₂.nreg 200130 (d₂.nreg 200130 + d₂.nreg 200100) }
    with hd₃
  have g3 : ∀ r, r ≠ 200130 → d₃.nreg r = d₂.nreg r := fun r hr => by rw [hd₃]; zumwy
  have v3 : d₃.nreg 200130 = t + 1 := by rw [hd₃]; simp [h130, h100]
  have g : ∀ r, zthjt → d₃.nreg r = d.nreg r := fun r hr => by
    grind
  refine ⟨d₃, _, .seq e₁ ztcr, e₃.wb_right, ?_, v3, by_omega, by_omega⟩
  refine ⟨by_omega, by rw [g _ by_norm_num, hI.r136], ?_, ?_,
    by rw [g _ by_norm_num, hI.r121], by_grind,
    by zunxu, fun r hr => by zunac, ?_, ?_, ?_,
    fun a => ?_⟩
  · grind
  · grind
  · show d₂.rreg = c₁.rreg; rw [rr₂, rr₁, hI.rr]
  · show d₂.rmem = c₁.rmem; rw [rm₂, rm₁, hI.rm]
  · show d₂.output = c₁.output; rw [o₂, o₁, hI.out]
  grind

/-- **The event pass.** -/
theorem dLoop2_exec
 (hE : ∀ t, t < E.length → m₁ ztnpg = E.getD t 0)
    (hSE : SE + E.length ≤ SE') (hX : ∀ c, c < E.length → m₁ ztnqi = tbl li n L c)
    (hXS : X + E.length ≤ SE') (hEl : E.length = 2 * L.length)
    (hperm : E.Perm ztct) (hW : SE' + E.length + 1 ≤ W)
    {c₁ d : Config} (hw : WordsBounded W d) (hI : Inv2 m₁ li n L E SE X SE' c₁ d)
    (h0 : d.nreg 200130 = 0) :
    ∃ d' k, Exec P W dLoop2 d d' k ∧ WordsBounded W d' ∧ Inv2 m₁ li n L E SE X SE' c₁ d' ∧
      d'.nreg 200130 = E.length ∧ 7 * E.length ≤ k ∧ k ≤ 13 * E.length + 2 := by
  obtain ⟨d', k, e, ⟨hw', hI'⟩, htest, hk, hψ⟩ := SortR.whileLtN_potential_lb (P := P) (W := W)
    (a := 200130) (b := 200136) (body := dBody2)
    (fun d => WordsBounded W d ∧ Inv2 m₁ li n L E SE X SE' c₁ d)
    (fun d => 13 * (E.length - d.nreg 200130)) (fun d => 7 * d.nreg 200130) ztoe
    (fun d ⟨hwd, hId⟩ ht => by
      obtain ⟨d', k, e, hw', hI', hi', hk1, hk2⟩ :=
        dBody2_exec hE hSE hX hXS hEl hperm hW hwd hId ht
      have := hId.r136
      refine zthmv
      · omega
      omega)
    ⟨hw, hI⟩
  have hi := hI'.t_le
  rw [hI'.r136] at htest
  have hend : d'.nreg 200130 = E.length := by_omega
  refine ⟨d', k, e, hw', hI', hend, ?_, ?_⟩
  · omega
  omega
end exec
end
end DownBase
namespace BoxT
@[expose] public section
open List BuildNF
open BuildSort (Ev kap)
open BuildRegions (eL eR crec kl kr lo hi e1)
variable {M M' : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)}

/-- **Two models agree on a chord list**: the keys of the chord endpoints compare alike, the arcs
between them weigh alike, and their walk edges go down alike. -/
structure KeyCongr (M M' : Model) (Q : Polygon) (L : List zte) : Prop where
  lt : ∀ c c', c < 2 * L.length → c' < 2 * L.length →
    (M'.key Q ztbbg < M'.key Q ztbuh ↔
      M.key Q ztbbg < M.key Q ztbuh)
  wt : ∀ c c', c < 2 * L.length → c' < 2 * L.length →
    M'.arcWt (M'.key Q ztbbg) (M'.key Q ztbuh) =
      M.arcWt ztztx (M.key Q ztbuh)
  wt0 : L = [] → M'.arcWt ztztw ztztw =
    M.arcWt ztxvi ztxvi
  dir : ∀ c, c < 2 * L.length →
    ((M'.wb (wposOf L c).edge).2 < (M'.wa (wposOf L c).edge).2 ↔
      (M.wb (wposOf L c).edge).2 < (M.wa (wposOf L c).edge).2)

/-- The index of an image in a mapped list, for a map injective at the element. -/
theorem idxOf_map_of_inj {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (f : α → β)
    (l : List α) (a : α) (h : ∀ x ∈ l, f x = f a → x = a) :
    (l.map f).idxOf ztbaa = l.idxOf a := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [map_cons, idxOf_cons, idxOf_cons]
    by_cases hx : x = a
    · grind
    · grind
theorem wposOf_even (L : List zte) (i : ℕ) : wposOf L ztvd = (crec L i).lpos := by
  simp [wposOf]
theorem wposOf_odd (L : List zte) (i : ℕ) : wposOf L ztmj = (crec L i).rpos := by
  simp only [wposOf]
  grind
theorem kl_eq (M : Model) (Q : Polygon) (L : List zte) (i : ℕ) :
    kl M Q L i = M.key Q (wposOf L ztvd) := by
  rw [wposOf_even]; rfl
theorem kr_eq (M : Model) (Q : Polygon) (L : List zte) (i : ℕ) :
    kr M Q L i = M.key Q (wposOf L ztmj) := by
  rw [wposOf_odd]; rfl

/-- The keys of the chord endpoints. -/
def InS (M : Model) (Q : Polygon) (L : List zte) (x : ℝ) : Prop :=
  ∃ c, c < 2 * L.length ∧ M.key Q ztbbg = x

/-- The key map from `M` to `M'` on the keys of the chord endpoints. -/
noncomputable def gmap (M M' : Model) (Q : Polygon) (L : List zte) (x : ℝ) : ℝ := by
  classical
  exact if h : InS M Q L x then M'.key Q (wposOf L h.choose) else x

/-- The map of events. -/
noncomputable def mapEv (g : ℝ → ℝ) (e : Ev) : Ev := (e.1, g e.2.1, g e.2.2)
namespace KeyCongr
variable (hK : KeyCongr M M' Q L)
include hK
variable {c c' : ℕ} {x y : ℝ} {i : ℕ}
theorem eq_iff (hc : c < 2 * L.length) (hc' : c' < 2 * L.length) :
    M'.key Q ztbbg = M'.key Q ztbuh ↔
      M.key Q ztbbg = M.key Q ztbuh := by
  have h1 := hK.lt c c' hc hc'
  have h2 := hK.lt c' c hc' hc
  grind
theorem gmap_key {c : ℕ} (hc : c < 2 * L.length) :
    gmap M M' Q L ztztx = M'.key Q ztbbg := by
  have h : InS M Q L _ := ⟨c, hc, rfl⟩
  unfold gmap
  zulpp
  exact (hK.eq_iff h.choose_spec.1 hc).2 h.choose_spec.2
theorem gmap_lt (hx : InS M Q L x) (hy : InS M Q L y) :
    gmap M M' Q L x < gmap M M' Q L y ↔ x < y := by
  zugox
  obtain ⟨c', hc', rfl⟩ := hy
  rw [hK.gmap_key hc, hK.gmap_key hc']
  exact hK.lt c c' hc hc'
theorem gmap_inj (hx : InS M Q L x) (hy : InS M Q L y)
    (e : gmap M M' Q L x = gmap M M' Q L y) : x = y := by
  rcases lt_trichotomy x y with l | l | l
  · exact absurd e ((hK.gmap_lt hx hy).2 l).ne
  · exact l
  · exact absurd e ((hK.gmap_lt hy hx).2 l).ne'
omit hK in
theorem inS_kl (hi : i < L.length) : InS M Q L ztciq :=
  ⟨2 * i, by_omega, (kl_eq M Q L i).symm⟩
omit hK in
theorem inS_kr (hi : i < L.length) : InS M Q L ztcir :=
  ⟨2 * i + 1, by_omega, (kr_eq M Q L i).symm⟩
theorem kl' (hi : i < L.length) : kl M' Q L i = gmap M M' Q L ztciq := by
  rw [kl_eq, kl_eq, hK.gmap_key by_omega]
theorem kr' (hi : i < L.length) : kr M' Q L i = gmap M M' Q L ztcir := by
  rw [kr_eq, kr_eq, hK.gmap_key by_omega]
theorem klr_lt_iff (hi : i < L.length) : kl M' Q L i < kr M' Q L i ↔ kl M Q L i < kr M Q L i := by
  rw [hK.kl' hi, hK.kr' hi, hK.gmap_lt ztvxc ztvxd]
theorem evOf_eq {c : ℕ} (hc : c < 2 * L.length) :
    evOf M' Q L c = mapEv ztjxc ztqmo := by
  zubgd
  unfold evOf
  split_ifs
  · simp only [eL, mapEv, hK.kl' hi, hK.kr' hi]
  · simp only [eR, mapEv, hK.kl' hi, hK.kr' hi]
theorem e1_eq (hi : i < L.length) : e1 M' Q L i = mapEv ztjxc ztdnh := by
  have hlt := hK.klr_lt_iff hi
  have hgt : kr M' Q L i < kl M' Q L i ↔ kr M Q L i < kl M Q L i := by
    rw [hK.kl' hi, hK.kr' hi, hK.gmap_lt ztvxd ztvxc]
  simp only [e1, mapEv, lo, BuildRegions.hi]
  zuieo
  · have h' : kl M' Q L i ≤ kr M' Q L i := by_grind
    rw [min_eq_left h, max_eq_right h, min_eq_left h', max_eq_right h', hK.kl' hi, hK.kr' hi]
  · have h' : kr M' Q L i ≤ kl M' Q L i := by_grind
    rw [min_eq_right h, max_eq_left h, min_eq_right h', max_eq_left h', hK.kl' hi, hK.kr' hi]
omit hK in
/-- The keys of the events of codes. -/
theorem evOf_inS {c : ℕ} (hc : c < 2 * L.length) :
    InS M Q L (evOf M Q L c).2.1 ∧ InS M Q L (evOf M Q L c).2.2 := by
  zubgd
  unfold evOf
  split_ifs
  · exact ztrdl
  · exact ztrdm
omit hK in
theorem e1_inS (hi : i < L.length) :
    InS M Q L (e1 M Q L i).2.1 ∧ InS M Q L (e1 M Q L i).2.2 := by
  simp only [e1, lo, BuildRegions.hi]
  zuieo
  · zunxx; exact ztrdl
  · rw [min_eq_right h, max_eq_left h]; exact ztrdm
variable {E : List ℕ} (hE : ∀ c ∈ E, c < 2 * L.length)
include hE
theorem evs_eq : evs M' Q L E = (evs M Q L E).map (mapEv ztjxc) := by
  unfold evs
  zugwd
  exact map_congr_left fun c hc => hK.evOf_eq by_simp_all
theorem word_eq : word M' Q L E = word M Q L E := by
  unfold word
  rw [hK.evs_eq hE, map_map]
  rfl
theorem outside_eq (hi : i < L.length) : outside M' Q L E i = outside M Q L E i := by
  unfold outside
  rw [hK.word_eq hE, hK.evs_eq hE, hK.e1_eq hi, idxOf_map_of_inj]
  intro x hx e
  unfold evs at hx
  zufxu
  have h1 := evOf_inS (M := M) (Q := Q) (hE c hc)
  have h2 := e1_inS (M := M) (Q := Q) hi
  simp only [mapEv, Prod.mk.injEq] at e
  obtain ⟨e1', e2', e3'⟩ := e
  exact Prod.ext e1' (Prod.ext (hK.gmap_inj h1.1 h2.1 e2') (hK.gmap_inj h1.2 h2.2 e3'))
theorem chordRec_eq (hi : i < L.length) : chordRec M' Q L E i = chordRec M Q L E i := by
  unfold chordRec
  rw [hK.outside_eq hE hi]
  simp only [hK.klr_lt_iff hi]
theorem kap_eq' {m : ℕ} (hm : m < E.length) :
    kap (evs M' Q L E) m = gmap M M' Q L ztzwq ∧
      InS M Q L ztzwq := by
  have hm' : ztgax := by simpa [evs] using hm
  have hm'' : m < (evs M' Q L E).length := by simpa [evs] using hm
  rw [BuildSort.kap_eq hm'', BuildSort.kap_eq hm']
  constructor
  · simp only [hK.evs_eq hE, getElem_map, mapEv]
  · simp only [evs, getElem_map]
    exact (evOf_inS by_simp_all).1
theorem gapStarts_eq : gapStarts M' Q L E = gapStarts M Q L E := by
  zumst
  zuldd
  zucng
  rw [mem_range] at hm
  by_cases hl : m + 1 = E.length
  · simp_all
  · have hm1 : ztskg := by_omega
    obtain ⟨a1, a2⟩ := hK.kap_eq' hE hm
    obtain ⟨b1, b2⟩ := hK.kap_eq' hE hm1
    simp only [hl, false_or, a1, b1, hK.gmap_lt a2 b2]
theorem arcList_eq : arcList M' Q L E = arcList M Q L E := by
  unfold arcList arcRec
  rw [hK.gapStarts_eq hE, hK.word_eq hE]
theorem regArcs_eq (r : ℕ) : regArcs M' Q L E r = regArcs M Q L E r := by
  unfold regArcs; zuorc
theorem regChords_eq (r : ℕ) : regChords M' Q L E r = regChords M Q L E r := by
  unfold regChords
  zuldd
  zug
  rw [hK.chordRec_eq hE ztqtk]
theorem arcW_eq {a : ARec} (ha : a ∈ arcList M Q L E) : arcW M' Q a = arcW M Q a := by
  unfold arcList at ha
  split_ifs at ha with h0
  · rw [mem_singleton] at ha
    subst ha
    exact hK.wt0 (length_eq_zero_iff.1 h0)
  · obtain ⟨m, hm, rfl⟩ := mem_map.1 ha
    have hmE := mem_range.1 (mem_filter.1 hm).1
    have hpos : ztgaa := by_omega
    have hs : ztpjh := by
      simp_all
    have he : E.getD ztxei 0 < 2 * L.length := by
      rw [getD_eq_getElem _ _ ztnnk]; simp_all
    exact hK.wt _ _ hs he
theorem regWt_eq (r : ℕ) : regWt M' Q L E r = regWt M Q L E r := by
  unfold regWt
  rw [hK.regArcs_eq hE, hK.arcList_eq hE]
  zucr
  apply map_congr_left
  zun
  have hj' := mem_range.1 (mem_filter.1 hj).1
  rw [getD_eq_getElem _ _ hj']
  exact hK.arcW_eq hE ztvri

/-- **Congruence of `buildNF`**: models that agree on the chord list compute the same normal
form from the same event order. -/
theorem buildNF_eq : buildNF M' Q L E = buildNF M Q L E := by
  unfold buildNF
  zuorc
  zucr
  · exact map_congr_left fun i hi => hK.chordRec_eq hE ztqtk
  · exact map_congr_left fun r _ => by
      rw [hK.regArcs_eq hE, hK.regChords_eq hE, hK.regWt_eq hE]
omit hE
theorem tieBit_eq {c : ℕ} (hc : c < 2 * L.length) : tieBit M' L c = tieBit M L c := by
  unfold tieBit
  simp only [hK.dir c hc]

/-- **The comparators agree** on the event codes. -/
theorem codeLe_iff (hc : c < 2 * L.length) (hc' : c' < 2 * L.length) :
    codeLe M' Q L c c' ↔ codeLe M Q L c c' := by
  zului
  rw [hK.lt c c' hc hc', hK.eq_iff hc hc', hK.tieBit_eq hc, hK.tieBit_eq hc']

/-- An event order sorted for `M` is sorted for `M'`. -/
theorem sorted {E : List ℕ} (hperm : E.Perm ztct)
    (hsort : E.Pairwise ztxi) : E.Pairwise (codeLe M' Q L) := by
  apply hsort.imp_of_mem
  zubto
  have ha' : a < 2 * L.length := by_grind
  have hb' : b < 2 * L.length := by_grind
  exact (hK.codeLe_iff ha' hb').2 h
end KeyCongr

/-! ## Degrees and weights from the records -/
namespace IsNFRec
variable {N : NF}

/-- The exit chords of a region are the chords of the indices listed in its record. -/
theorem exits_eq {reg : ℕ → Set Point} (hN : ∀ i i', i < N.nChords → i' < N.nChords →
      (N.chord i).toSet M Q = (N.chord i').toSet M Q → i = i')
    (hR : RegionsOK M Q N reg) {r : ℕ} (hr : r < N.nRegions) :
    {c | c ∈ N.F M Q ∧ Chazelle.Chain.TouchesIn M.D c ztcz}.ncard =
      (N.region r).chords.length := by
  obtain ⟨hmem, hnd, -, -⟩ := hR r hr
  have hset : {c | c ∈ N.F M Q ∧ Chazelle.Chain.TouchesIn M.D c ztcz} =
      ztdcz '' {i | i ∈ (N.region r).chords} := by
    zubcj
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, ht⟩
      zubhg
      have hc : ztpks := by
        zuub
      refine ⟨i, (hmem i).2 ztfwp, ?_⟩
      · simp_all
      simp_all
    · zuin
      zueue
      refine ⟨ztfju, ht⟩
      unfold NF.chord; rw [getD_eq_getElem _ _ hi']; grind
  have hinj : Set.InjOn ztdcz {i | i ∈ (N.region r).chords} :=
    fun i hi i' hi' e => by_grind
  rw [hset, hinj.ncard_image]
  have : {i | i ∈ (N.region r).chords} = ((N.region r).chords.toFinset : Set ℕ) := by
    simp
  rw [this, Set.ncard_coe_finset, toFinset_card_of_nodup hnd]

/-- **Bounded degree from the records.** -/
theorem degLe_iff (h : IsNF M Q N) (d : ℕ) :
    M.DegLe ztdu d ↔ ∀ r, r < N.nRegions → (N.region r).chords.length ≤ d := by
  obtain ⟨-, hinj, -, reg, hC, -, -, hR, -⟩ := h
  constructor
  · intro hD r hr
    rw [← exits_eq hinj hR hr]
    exact hD _ zttmb
  · intro hD U hU
    zufkn
    zuhqm
    rw [exits_eq hinj hR hr]
    simp_all

/-- **Semigranularity from the records.** -/
theorem semigranular_iff (h : IsNF M Q N) (γ : ℕ) :
    M.Semigranular ztdu γ ↔ ∀ r, r < N.nRegions → (N.region r).wt ≤ γ := by
  obtain ⟨-, -, -, reg, hC, -, -, hR, -⟩ := h
  constructor
  · intro hS r hr
    rw [(hR r hr).2.2.2]
    exact hS _ zttmb
  · intro hS U hU
    zufkn
    rw [← (hR r hr).2.2.2]
    simp_all

/-- **Transfer of degree and weight bounds** between two models in which the same record is a
valid normal form. -/
theorem transfer {N : NF} (h : IsNF M Q N) (h' : IsNF M' Q N) {d γ : ℕ}
    (hd : M.DegLe ztdu d) (hγ : M.Semigranular ztdu γ) :
    M'.DegLe zttai d ∧ M'.Semigranular zttai γ :=
  ⟨(degLe_iff h' d).2 ((degLe_iff h d).1 hd),
    (semigranular_iff h' γ).2 ((semigranular_iff h γ).1 hγ)⟩
end IsNFRec
open Set Chazelle.Chain Chazelle.Visibility
open BuildRegions (famOf)
variable {C C' : Chain}
def InBand (C C' : Chain) (Q : Polygon) (L : List zte) : Prop :=
  ∀ x ∈ L, |(Q.vtx x.1).2| < bnd C C'

/-- The walk position of an event code is an end of a chord of the list. -/
theorem wposOf_mem {c : ℕ} (hc : c < 2 * L.length) :
    ∃ x ∈ L, wposOf L c = (recOf x).lpos ∨ wposOf L c = (recOf x).rpos := by
  zubgd
  refine ⟨L[c / 2], getElem_mem _, ?_⟩
  have hcr : crec L ztbek = recOf L[c / 2] := by
    unfold crec; simp_all
  zulci
  grind

/-- The facts about the ends of an attached band chord. -/
theorem end_facts (hband : InBand C C' Q L) (hL : ChordTriplesOK ztc Q L)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ L) {w : WPos} (hw : w = (recOf x).lpos ∨ w = (recOf x).rpos) :
    w.edge < (chainModel C).W.n ∧ BandPos C C' Q w ∧
      (0 ≤ (chainModel C).param Q w ∧ (chainModel C).param Q w < 1) := by
  zugpl
  have hb : |(Q.vtx x.1).2| < bnd C C' := hband x hx
  zukmo
  · exact ⟨hl.1, Or.inr ztrew, hl.2.1, hl.2.2.1⟩
  · exact ⟨hr.1, Or.inr ztrew, hr.2.1, hr.2.2.1⟩
theorem phi_injective : Function.Injective zttwe := fun _ _ e =>
  (stretchHomeo (bnd_nonneg (C := C) (C' := C')) (kk_pos (C := C) (C' := C'))).injective e
namespace Twin
variable (h : Twin C C')
include h

/-- The chords of the list in the model of `C'` are the stretched chords. -/
theorem toSet_rec (hband : InBand C C' Q L) (hL : ChordTriplesOK ztc Q L)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ L) :
    (recOf x).toSet ztbmo Q = phi C C' '' (recOf x).toSet ztc Q := by
  obtain ⟨hl, -, hml⟩ := end_facts hband hL hx ztp
  obtain ⟨hr, -, hmr⟩ := end_facts hband hL hx ztbt
  exact h.toSet_eq zttnf hl hr hml hmr

/-- **The chord list is valid for the twin chain.** -/
theorem chordTriplesOK (hband : InBand C C' Q L) (hL : ChordTriplesOK ztc Q L) :
    ChordTriplesOK ztbmo Q L := by
  have hL0 := hL
  obtain ⟨⟨-, hadm, -⟩, hnd, hatt, hh⟩ := hL
  refine ⟨ztcg, ?_, ?_, hh⟩
  · refine ((List.finite_toSet L).image fun x => (recOf x).toSet ztbmo Q).subset ?_
    zueq
    grind
  · zueq
    obtain ⟨hl, hbl, hml⟩ := end_facts hband hL0 hx ztp
    obtain ⟨hr, hbr, hmr⟩ := end_facts hband hL0 hx ztbt
    have hc := hadm ztcyj
    have e : (recOf x).toSet ztbmo Q = hseg (Q.vtx x.1).2
        (stretch ztes zteq ((chainModel C).pos Q (recOf x).lpos).1)
        (stretch ztes zteq ((chainModel C).pos Q (recOf x).rpos).1) := by
      unfold CRec.toSet
      rw [h.pos_eq hl hbl hml, h.pos_eq hr hbr hmr]
      rfl
    zui
    exact h.augChords_transfer zttnf hc
  · zueq
    tauto
  · have e : L.map (fun x => (recOf x).toSet ztbmo Q) =
        (L.map fun x => (recOf x).toSet ztc Q).map (image zttwe) := by
      zugwd
      exact map_congr_left fun x hx => h.toSet_rec hband hL0 hx
    zui
    exact hnd.map (Set.image_injective.2 phi_injective)
  · zuh
    have hL := hL0
    obtain ⟨hl, hbl, hml⟩ := end_facts hband hL hx ztp
    obtain ⟨hr, hbr, hmr⟩ := end_facts hband hL hx ztbt
    have hdy : ∀ z ∈ (recOf x).toSet ztc Q, z.2 = (Q.vtx (recOf x).h).2 :=
      fun z hz => hz.1
    rw [CRec.Attached, h.toSet_rec hband hL hx]
    exact ⟨h.attach_transfer hdy (h.pos_eq hl hbl hml) ((h.param_mem_iff hbl).2 hml)
        (h.param_eq_zero_iff hbl).symm (hatt x hx).1,
      h.attach_transfer hdy (h.pos_eq hr hbr hmr) ((h.param_mem_iff hbr).2 hmr)
        (h.param_eq_zero_iff hbr).symm (hatt x hx).2⟩

/-- **The two chain models agree on the chord list.** -/
theorem keyCongr (hband : InBand C C' Q L) (hL : ChordTriplesOK ztc Q L) :
    KeyCongr ztc ztbmo Q L where
  lt c c' hc hc' := by
    zuob

    exact h.key_lt_iff hb hb' hm hm'
  wt c c' hc hc' := by
    zuob

    exact h.arcWt_eq hb hb' hm hm'
  wt0 _ := by
    have hb : BandPos C C' Q ztbqw := Or.inl rfl
    have hm : 0 ≤ (chainModel C).param Q ztbqw ∧ (chainModel C).param Q ztbqw < 1 := by
      simp [Model.param]
    exact h.arcWt_eq hb hb hm hm
  dir c _ := by
    zukro
    exact sig_lt_iff
end Twin

/-- The chord family of a normal form with chord list `L`. -/
theorem F_eq_famOf {M : Model} {N : NF}
    (hmap : N.chords.map ztwma = L) : N.F M Q = famOf M Q L := by
  zubcj
  constructor
  · zuoc
    exact ⟨ztlm, hmap ▸ mem_map_of_mem hr, rfl⟩
  · zuod
    rw [← hmap] at hx
    zucog
    tauto

/-- A comparator-sorted event order exists. -/
theorem exists_sorted (M : Model) (Q : Polygon) (L : List zte) :
    ∃ E : List ℕ, E.Perm ztct ∧ E.Pairwise ztxi := by
  classical
  have : Std.Total ztxi := ⟨codeLe_total M Q L⟩
  have : IsTrans ℕ ztxi := ⟨fun _ _ _ => codeLe_trans M Q L⟩
  exact ⟨_, perm_insertionSort _ _, pairwise_insertionSort _ _⟩

/-- **Box transport of a band chord list** (B3′, per-chord form).  For twin chains of simple
hosts and a valid chord list of `C` in the band, the list is valid for `C'`, and bounded degree
and `γ`-semigranularity of its chord family transfer from `C` to `C'`. -/
theorem transport (h : Twin C C') (hP : C.P.Simple) (hP' : C'.P.Simple)
    (hband : InBand C C' Q L) (hL : ChordTriplesOK ztc Q L) {d γ : ℕ}
    (hd : (chainModel C).DegLe ztwyc d)
    (hγ : (chainModel C).Semigranular ztwyc γ) :
    ChordTriplesOK ztbmo Q L ∧
      (chainModel C').DegLe ztzlr d ∧
      (chainModel C').Semigranular ztzlr γ := by
  have hL' := h.chordTriplesOK hband hL
  have hK := h.keyCongr hband hL
  obtain ⟨E, hperm, hsort⟩ := exists_sorted ztc Q L
  have hE : ∀ c ∈ E, c < 2 * L.length := fun c hc => mem_range.1 (hperm.subset hc)
  obtain ⟨hN, hmap, -⟩ := isNF_goodModel ztxgi hL hperm hsort
  obtain ⟨hN', -, -⟩ := isNF_goodModel (Or.inl ⟨C', hP', rfl⟩) hL' hperm (hK.sorted hperm hsort)
  rw [hK.buildNF_eq hE] at hN'
  have e1 := F_eq_famOf (M := chainModel C) (Q := Q) hmap
  have e2 := F_eq_famOf (M := chainModel C') (Q := Q) hmap
  rw [← e1] at hd hγ
  zulqv
  exact ⟨hL', IsNFRec.transfer hN hN' hd hγ⟩
def WallRec (x : ℕ × ℕ × ℕ) : Prop := (x.2.1 = 1 ∨ x.2.1 = 3) ∧ zthld
instance (x : ℕ × ℕ × ℕ) : Decidable ztvee := by unfold WallRec; infer_instance

/-- The chord list without its wall-to-wall chords. -/
def dropWalls (L : List zte) : List zte := L.filter fun x => !decide ztvee
theorem mem_dropWalls {L : List zte} {x : ℕ × ℕ × ℕ} :
    x ∈ dropWalls L ↔ x ∈ L ∧ ¬ WallRec x := by
  simp [dropWalls]
variable {M : Model} {Q : Polygon}
/-- A sublist of a valid chord list is valid. -/
theorem chordTriplesOK_sublist {L L' : List zte}
    (hs : L' <+ L) (hL : ChordTriplesOK M Q L) : ChordTriplesOK M Q L' := by
  obtain ⟨⟨hfin, hadm, hht⟩, hnd, hatt, hh⟩ := hL
  have sub : {c | ∃ x ∈ L', c = (recOf x).toSet M Q} ⊆ {c | ∃ x ∈ L, c = (recOf x).toSet M Q} := by
    grind
  exact ⟨⟨hfin.subset sub, sub.trans hadm, fun c hc => hht c (sub hc)⟩,
    hnd.sublist (hs.map _), fun x hx => hatt x ztvwf, fun x hx => hh x ztvwf⟩
theorem chordTriplesOK_dropWalls {L : List zte}
    (hL : ChordTriplesOK M Q L) : ChordTriplesOK M Q ztgih :=
  chordTriplesOK_sublist filter_sublist hL
variable {C C' : Chain}
namespace Twin
variable (h : Twin C C')
include h

/-- **Heights at walk points off the side walls.**  A point of a walk edge other than a side wall
at a height `y` of the open box not above the top is in the fixed band. -/
theorem band_of_edge {e : ℕ} (he : e < (C.sideWalk C.sideBeta).n) (h1 : e ≠ 1) (h3 : e ≠ 3)
    {t : ℝ} (ht : 0 ≤ t ∧ t < 1) {y : ℝ} (hpy : (sidePt ztcs e t).2 = y)
    (hyt : y ≤ C.top.2) (hyR : |y| < C.radius) : |y| ≤ bnd C C' - 1 / 2 := by
  zuern
  have htop := h.abs_le_of_mem C.top_mem_set
  have hbR : bnd C C' < C.radius := bnd_lt
  have htR : C.top.2 < C.radius := by_grind
  zuliu
  zuhbb

  rcases Nat.lt_or_ge e 6 with h6 | h6
  · have hmod : ztycw := by
      zucjs
    zukvc
    interval_cases e
    · zuigf
      zubzk
      linarith
    · omega
    · zuigd
      simp_all
    · omega
    · zuifz
      zubzk
      linarith
    · zuify
      zubzk
      nlinarith
  · rcases Nat.lt_or_ge e ztcc with h' | h'
    · have hmod : ztycw := by
        zucjs
      zukvc
      have hu := h.abs_le_of_mem ztrxl
      have hv := h.abs_le_of_mem (tour_mem C (by omega : 6 ≤ e + 1) by_omega)
      have hb := abs_lerp_le hu hv ht.1 ht.2.le
      simp_all
    · zufup
      zulta
      zuige
      zubzk
      have hy : y = C.top.2 := by_nlinarith
      simp_all
variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)}
/-- The height of a chord of a valid chord list of a chain, at an end off the side walls, is in
the fixed band. -/
theorem band_of_end (hL : ChordTriplesOK ztc Q L)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ L) {w : WPos} (hw : w = (recOf x).lpos ∨ w = (recOf x).rpos)
    (h1 : w.edge ≠ 1) (h3 : w.edge ≠ 3) : |(Q.vtx x.1).2| ≤ bnd C C' - 1 / 2 := by
  zugpl
  have hA : SideAttach ztcs ((recOf x).toSet ztc Q) w.edge
      ztgvu := by rcases hw with rfl | rfl <;> assumption
  zueiu
  zudjg
  have hmem' := hmem
  zvmwe at hmem'
  have hy1 : (sidePt ztcs w.edge ztgvu).2 =
      (Q.vtx x.1).2 := hmem.1
  have hy2 : (sidePt ztcs w.edge ztgvu).2 = y' := hmem'.1
  have hyy : (Q.vtx x.1).2 = y' := hy1.symm.trans hy2
  have hR : |y'| < C.radius := by
    zuerj

  rw [hyy]
  exact h.band_of_edge hp h1 h3 ztcoy hy2 hyt hR

/-- **The chords off the side walls are in the band.** -/
theorem inBand_dropWalls
    (hL : ChordTriplesOK ztc Q L) : InBand C C' Q ztgih := by
  zuh
  obtain ⟨hx, hw⟩ := mem_dropWalls.1 hx
  have hb : bnd C C' - 1 / 2 < bnd C C' := by_linarith
  unfold WallRec at hw
  by_cases hl : x.2.1 = 1 ∨ x.2.1 = 3
  · have hr : ¬ zthld := fun hr => hw ztuhr
    rw [not_or] at hr
    exact lt_of_le_of_lt (h.band_of_end hL hx ztbt hr.1 hr.2) hb
  · rw [not_or] at hl
    exact lt_of_le_of_lt (h.band_of_end hL hx ztp hl.1 hl.2) hb
end Twin
theorem mem_set_lerp (C : Chain) {z : Point} (hz : z ∈ C.set) :
    ∃ k, k < C.m ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      z.2 = (C.vertex k).2 + t * ((C.vertex zts).2 - (C.vertex k).2) := by
  obtain ⟨k, hk, hzk⟩ := hz
  rw [C.chainEdge_eq] at hzk
  obtain ⟨t, ht0, ht1, rfl⟩ := hzk
  grind

/-- Every chain point is at least as high as some vertex. -/
theorem vertex_below (C : Chain) {z : Point} (hz : z ∈ C.set) :
    ∃ k, k ≤ C.m ∧ (C.vertex k).2 ≤ z.2 := by
  zuder
  zudsm
  · exact ⟨k, hk.le, by zvmwe; nlinarith⟩
  · exact ⟨k + 1, hk, by zvmwe; nlinarith⟩

/-- **A line missing the chain, not above the top, lies below the chain.** -/
theorem chain_above (C : Chain) {y : ℝ} (hno : ∀ z ∈ C.set, z.2 ≠ y) (htop : y < C.top.2) :
    ∀ z ∈ C.set, y < z.2 := by
  have step : ∀ k, k < C.m → (y < (C.vertex k).2 ↔ y < (C.vertex zts).2) := by
    zugf
    have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        (((C.vertex k).1 + t * ((C.vertex _).1 - (C.vertex k).1),
          (C.vertex k).2 + t * ztjcb) : Point) ∈ C.set :=
      fun t h0 h1 => ⟨k, hk, by rw [C.chainEdge_eq]; exact ztopq⟩
    have ha := hno _ (C.vertex_mem_set hk.le)
    have hb := hno _ ztdkv
    set a := (C.vertex k).2
    set b := (C.vertex zts).2
    zuct
    have hcross : (y < a ∧ b < y) ∨ zthdk := by
      grind
    rcases hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hpos : 0 < a - b := by_linarith
      refine hno _ (hseg ((a - y) / zttem) zttjc
        ztosq) ?_
      grind
    · have hpos : ztmsn := by_linarith
      refine hno _ (hseg (ztkhj / zthu) zttjc
        ztosq) ?_
      grind
  have hall : ∀ k, k ≤ C.m → (y < (C.vertex k).2 ↔ y < (C.vertex 0).2) := by
    zugf
    induction k with
    | zero => exact Iff.rfl
    | succ k ih => exact by_grind
  have h0 := (hall _ C.topIdx_le).1 htop
  have hv : ∀ k, k ≤ C.m → y < (C.vertex k).2 := by_simp_all
  zugh
  zuder
  have h1 := hv k hk.le
  have h2 := hv zts hk
  zui
  zudsm
  · have := mul_nonneg ht0 (sub_nonneg.2 h); linarith
  · have := mul_le_mul_of_nonpos_right ht1 (sub_nonpos.2 h); linarith

/-! ## Cuts of augmented chords -/
theorem sidePt_small (C : Chain) {p : ℕ} (hp : p < 6) (t : ℝ) :
    sidePt ztcs p t =
      Geometry.lerp ((C.sideWalk C.sideBeta).vtx p) ((C.sideWalk C.sideBeta).vtx ztr) t := by
  zucky
  rw [C.sideWalk_n, Nat.mod_eq_of_lt by_omega]

/-- **The cuts of an augmented chord.** -/
theorem cut_cases (C : Chain) {e : Set Point} {y : ℝ} (hey : ∀ z ∈ e, z.2 = y)
    (hyR : |y| < C.radius) (hyt : y ≤ C.top.2) {p : ℕ} {t : ℝ}
    (hA : SideAttach ztcs e p t) :
    (p = 1 ∧ y = C.radius - 2 * C.radius * t) ∨ (p = 3 ∧ y = -C.radius + 2 * C.radius * t) ∨
      (6 ≤ p ∧ ∀ y', (∀ z ∈ C.set, y' < z.2) → y' < y) := by
  zueiu
  have hpy := hey _ hmem
  zuern
  zugne
  zuliu
  zuidp
  · rw [sidePt_small C h6, Geometry.lerp_snd] at hpy
    interval_cases p
    · zuigf
      zuhow
    · rw [C.sideWalk_vtx_one, C.sideWalk_vtx_two] at hpy
      grind
    · zuigd
      grind
    · rw [C.sideWalk_vtx_three, C.sideWalk_vtx_four] at hpy
      grind
    · zuifz
      zuhow
    · zuify
      simp only [Chain.slitTop] at hpy; nlinarith
  · zulw
    refine ⟨h6, fun y' hy' => ?_⟩
    zuhbb

    zuidq
    · rw [hn, Nat.mod_eq_of_lt by_omega] at hpy
      have hu := hy' _ ztrxl
      have hv := hy' _ (tour_mem C (by omega : 6 ≤ p + 1) by_omega)
      zujmg
    · zudzk

      zuige
      zubzk
      have := hy' _ C.top_mem_set
      zujmg

/-! ## Records -/
variable {C : Chain} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)}

/-- The equality of horizontal segments. -/
theorem hseg_eq {y u v y' a b : ℝ} (he : hseg y u v = hseg y' a b) (hab : a < b) :
    y = y' ∧ u = a ∧ v = b := by
  have ha : (ztteu : Point) ∈ hseg y u v := by zvmxm; exact ztgpm
  have hb : (zttfq : Point) ∈ hseg y u v := by zvmxm; exact ztgpl
  have hyy := ha.1
  zulau
  have hu : ((u, y') : Point) ∈ hseg y' a b := by
    zvndl; exact ⟨rfl, le_rfl, le_trans ha.2.1 ha.2.2⟩
  have hv : ((v, y') : Point) ∈ hseg y' a b := by
    zvndl; exact ⟨rfl, le_trans ha.2.1 ha.2.2, le_rfl⟩
  exact ⟨rfl, le_antisymm ha.2.1 hu.2.1, le_antisymm hv.2.2 hb.2.2⟩

/-- The height facts of a chord of a valid list. -/
theorem rec_facts (hL : ChordTriplesOK ztc Q L) {x : ℕ × ℕ × ℕ} (hx : x ∈ L) :
    (∀ z ∈ (recOf x).toSet ztc Q, z.2 = (Q.vtx x.1).2) ∧
      |(Q.vtx x.1).2| < C.radius ∧ (Q.vtx x.1).2 ≤ C.top.2 ∧
      ∃ a b, IsHChordIn C.dom (Q.vtx x.1).2 a b ∧
        (recOf x).toSet ztc Q = hseg (Q.vtx x.1).2 a b := by
  zudjg
  have hmem := (hL.2.2.1 x hx).1.2.2.2.1
  have hmem' : sidePt ztcs (recOf x).lp
      _ ∈ hseg y' a b := e ▸ hmem
  have hyy := hmem.1.symm.trans hmem'.1
  rw [← hyy] at hh hyt e
  have hR : |(Q.vtx x.1).2| < C.radius := by
    zuerj

  exact ⟨fun z hz => hz.1, hR, hyt, a, b, hh, e⟩
theorem wall_x {p : ℕ} (hp : p = 1 ∨ p = 3) (t : ℝ) :
    (sidePt ztcs p t).1 = -C.radius ∨
      (sidePt ztcs p t).1 = C.radius := by
  zugaa
  · left
    rw [sidePt_small C by_norm_num, Geometry.lerp_fst, C.sideWalk_vtx_one, C.sideWalk_vtx_two]
    ring
  · right
    rw [sidePt_small C by_norm_num, Geometry.lerp_fst, C.sideWalk_vtx_three,
      C.sideWalk_vtx_four]
    ring

/-- **A wall-to-wall record is the full-width chord.** -/
theorem wall_shape (hL : ChordTriplesOK ztc Q L) {x : ℕ × ℕ × ℕ} (hx : x ∈ L)
    (hw : WallRec x) :
    (recOf x).toSet ztc Q = hseg (Q.vtx x.1).2 (-C.radius) C.radius ∧
      IsHChordIn C.dom (Q.vtx x.1).2 (-C.radius) C.radius := by
  obtain ⟨-, -, -, a, b, hh, e⟩ := rec_facts hL hx
  have e' := e
  unfold CRec.toSet at e'
  obtain ⟨-, hu, hv⟩ := hseg_eq e' hh.lt
  zubo
  have h1 := wall_x (C := C) hw.1 ((chainModel C).param Q (recOf x).lpos)
  have h2 := wall_x (C := C) hw.2 ((chainModel C).param Q (recOf x).rpos)
  have hlt := hh.lt
  have hu' := hu
  have hv' := hv
  have hpl : (chainModel C).pos Q (recOf x).lpos =
      sidePt ztcs x.2.1 _ := rfl
  have hpr : (chainModel C).pos Q (recOf x).rpos =
      sidePt ztcs x.2.2 _ := rfl
  grind

/-- A full-width chord lies below the chain. -/
theorem wall_below {y : ℝ} (hh : IsHChordIn C.dom y (-C.radius) C.radius) (hyt : y ≤ C.top.2) :
    ∀ z ∈ C.set, y < z.2 := by
  have hno : ∀ z ∈ C.set, z.2 ≠ y := by
    zumhu
    have hb := C.set_subset_box hz
    rw [mem_box_iff, abs_lt, abs_lt] at hb
    have hm := hh.open_mem z.1 hb.1.1 hb.1.2
    rw [← hzy] at hm
    exact C.not_mem_set_of_mem_dom hm hz
  exact chain_above C hno (lt_of_le_of_ne hyt (Ne.symm (hno _ C.top_mem_set)))
variable {M : Model} {C' : Chain}
theorem famOf_mono {L₁ L₂ : List zte} (h : ∀ x ∈ L₁, x ∈ L₂) :
    famOf M Q L₁ ⊆ famOf M Q L₂ := by
  rintro c ⟨x, hx, rfl⟩; exact ⟨x, by_simp_all, rfl⟩

/-- **Dropping the wall-to-wall chords** (design finding M6): the chord family without its
wall-to-wall chords keeps the degree bound and is `2γ`-semigranular. -/
theorem drop_ok (hP : C.P.Simple) (hL : ChordTriplesOK ztc Q L) {d γ : ℕ}
    (hd : (chainModel C).DegLe ztwyc d)
    (hγ : (chainModel C).Semigranular ztwyc γ) :
    (chainModel C).DegLe ztzlt d ∧
      (chainModel C).Semigranular ztzlt ztjfj := by
  zubzd
  set F := famOf M Q L
  set F' := famOf M Q _
  have hM : ztgpz := walkAx_of_goodModel ztzz
  have hFA := hL.1.2.1
  zuixx
  have hsub : F' ⊆ F := famOf_mono fun x hx => (mem_dropWalls.1 hx).1
  zubo
  by_cases hwall : ∃ x ∈ L, WallRec x
  swap
  · push Not at hwall
    have hLL : dropWalls L = L := by
      unfold dropWalls
      simp_all
    have hFF : F' = F := by_grind
    rw [hFF]
    exact ⟨hd, fun U hU => (hγ U hU).trans by_omega⟩
  -- the highest wall-to-wall chord
  obtain ⟨xs, ⟨hxsL, hxsw⟩, hxsmax⟩ := Set.exists_max_image {x | x ∈ L ∧ WallRec x}
    (fun x => (Q.vtx x.1).2) ((List.finite_toSet L).subset fun x hx => hx.1)
    by_tauto
  set ys := (Q.vtx xs.1).2 with hysdef
  obtain ⟨-, hysR, hyst, -⟩ := rec_facts hL hxsL
  have hbelow := wall_below (wall_shape hL hxsL hxsw).2 hyst
  -- heights of the kept chords
  have hkept : ∀ x ∈ dropWalls L, ys < (Q.vtx x.1).2 := by
    zuh
    obtain ⟨hxL, hxw⟩ := mem_dropWalls.1 hx
    obtain ⟨hey, hyR, hyt, -⟩ := rec_facts hL hxL
    obtain ⟨hl, hr⟩ := hL.2.2.1 x hxL
    have hthird : ∀ {p : ℕ} {t : ℝ}, SideAttach ztcs
        ((recOf x).toSet M Q) p t → p ≠ 1 → p ≠ 3 → ys < (Q.vtx x.1).2 := by
      intro p t hA h1 h3
      rcases cut_cases C hey hyR hyt hA with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
      · omega
      · omega
      grind
    unfold WallRec at hxw
    by_cases hlw : x.2.1 = 1 ∨ x.2.1 = 3
    · have hrw : ¬ zthld := by_omega
      rw [not_or] at hrw
      exact hthird hr hrw.1 hrw.2
    · rw [not_or] at hlw
      exact hthird hl hlw.1 hlw.2
  -- the level `yp`
  set Hs : Finset ℝ := (Finset.range ztbpj).image ztmjt ∪
    ((dropWalls L).map fun x => (Q.vtx x.1).2).toFinset with hHs
  have hHne : Hs.Nonempty := ⟨(C.vertex 0).2, by_grind⟩
  set yp := Hs.min' hHne with hyp
  have hyp_v : ∀ k, k ≤ C.m → yp ≤ (C.vertex k).2 := fun k hk =>
    Hs.min'_le _ by_grind
  have hyp_k : ∀ x ∈ dropWalls L, yp ≤ (Q.vtx x.1).2 := fun x hx =>
    Hs.min'_le _ (Finset.mem_union_right _ (List.mem_toFinset.2 (List.mem_map_of_mem hx)))
  have hlt : ys < yp := by
    obtain ⟨h, hmem, e⟩ : ∃ h ∈ Hs, h = yp := ⟨yp, Hs.min'_mem hHne, rfl⟩
    zulqw
    rcases Finset.mem_union.1 hmem with h1 | h1
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h1
      exact hbelow _ (C.vertex_mem_set by_grind)
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 h1)
      grind
  have hypt : yp ≤ C.top.2 := hyp_v _ C.topIdx_le
  zugne
  have hysR' := abs_lt.1 hysR
  zujx
  · -- degrees
    refine degLe_drop (hM.sys F hFA hfin) hfin hsub hR hysR'.1.le hlt
      (fun z hz => C.dom_subset_box hz) ?_ ?_ ?_ hd
    · intro z h1 h2 h3 h4
      refine (C.mem_dom_iff).2 ⟨ztsr, fun hz => ?_, fun hz => ?_⟩
      · obtain ⟨k, hk, hkz⟩ := vertex_below C hz
        grind
      · have := (C.mem_slit_iff.1 hz).2.1
        linarith
    · rintro c ⟨x, hx, rfl⟩ z hz
      rw [(rec_facts hL (mem_dropWalls.1 hx).1).1 z hz]
      grind
    · rintro c ⟨x, hx, rfl⟩ hc' z hz
      rw [(rec_facts hL hx).1 z hz]
      zuldn
      · grind
      · exact absurd ztpge hc'
  · -- weights
    set R := C.radius
    have h2R : 0 < 2 * R := by_linarith
    refine semigranular_drop hM hFA hfin hsub (lo := 1 + ztjlz / ztdex)
      (hi := 3 + zthlj / ztdex) ?_ ?_ ?_ hγ
    · zucpj
      zuldn
      · right
        obtain ⟨hey, hyR, hyt, -⟩ := rec_facts hL hx
        have hyx := hxsmax x by_grind
        zumew
        have hbx := wall_below (wall_shape hL hx hw).2 hyt
        rcases cut_cases C hey hyR hyt hA with ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨-, h⟩
        · have : ztjlz / ztdex ≤ t := by zuors; linarith
          grind
        · have : t ≤ zthlj / ztdex := by rw [le_div_iff₀ h2R]; linarith
          have : ztjlz / ztdex ≤ 1 := by zuors; linarith
          have := hA.2.1
          grind
        grind
      · left
        exact ⟨_, ztpge, p, t, hA, rfl⟩
    · zucpj
      obtain ⟨hey, hyR, hyt, -⟩ := rec_facts hL (mem_dropWalls.1 hx).1
      have hyx := hkept x hx
      zuerb
      have ht0 := hA.2.1
      rcases cut_cases C hey hyR hyt hA with ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨h6, -⟩
      · left
        have : t < ztjlz / ztdex := by rw [lt_div_iff₀ h2R]; linarith
        grind
      · right
        have : zthlj / ztdex < t := by rw [div_lt_iff₀ h2R]; linarith
        grind
      · right
        have : ztfzu := by exact_mod_cast h6
        linarith
    · zuda
      have h6 : ztfzu := by exact_mod_cast hp.1
      zuerb
      linarith

/-! ## Box transport (B3′) -/

/-- **Box transport of a chain chord list** (B3′ with the filter of finding M6).  For twin chains
of simple hosts and a valid chord list of `C` whose family has degree `≤ d` and is
`γ`-semigranular, the list without its wall-to-wall chords is valid for `C'`, and its family in
the model of `C'` has degree `≤ d` and is `2γ`-semigranular. -/
theorem boxTransport (h : Twin C C') (hP : C.P.Simple) (hP' : C'.P.Simple)
    (hL : ChordTriplesOK ztc Q L) {d γ : ℕ}
    (hd : (chainModel C).DegLe ztwyc d)
    (hγ : (chainModel C).Semigranular ztwyc γ) :
    ChordTriplesOK ztbmo Q ztgih ∧
      (chainModel C').DegLe ztzls d ∧
      (chainModel C').Semigranular ztzls ztjfj := by
  obtain ⟨hd', hγ'⟩ := drop_ok hP hL hd hγ
  exact transport h hP hP' (h.inBand_dropWalls hL) (chordTriplesOK_dropWalls hL) hd' hγ'

/-- The chord triples of a valid normal form are a valid chord list. -/
theorem chordTriplesOK_of_isNF {N : NF} (hN : IsNF M Q N) :
    ChordTriplesOK M Q ztxgh := by
  obtain ⟨hfam, hinj, hatt, reg, -, -, -, -, -, hh, -⟩ := hN
  have hF := F_eq_famOf (M := M) (Q := Q) (L := N.chords.map fun r => ztlm)
    rfl
  have hget : ∀ i (hi : i < N.chords.length), N.chord i = N.chords[i] := fun i hi => by
    zuub
  refine ⟨by have := hF ▸ hfam; tauto, ?_, ?_, ?_⟩
  · zugwd
    zujgx
    intro i j e
    simp only [List.get_eq_getElem, getElem_map, Function.comp_apply] at e
    have hi := i.2; have hj := j.2
    simp only [length_map] at hi hj
    have := hinj i j hi hj (by rw [hget i hi, hget j hj]; exact e)
    omega
  · zuh
    zucog
    zuep
    have := hatt i hi
    rw [hget i hi] at this
    tauto
  · zuh
    zucog
    zuep
    have := hh i hi
    grind

/-- **Box transport of a normal form** (B3′, record form): the chord triples of a valid normal
form of `C` of degree `≤ d` that is `γ`-semigranular, without the wall-to-wall chords, are a
valid chord list of the twin chain `C'`, whose family has degree `≤ d` and is
`2γ`-semigranular. -/
theorem boxTransport_nf (h : Twin C C') (hP : C.P.Simple) (hP' : C'.P.Simple)
    {N : NF} (hN : IsNF ztc Q N) {d γ : ℕ}
    (hd : (chainModel C).DegLe ztwjh d)
    (hγ : (chainModel C).Semigranular ztwjh γ) :
    ChordTriplesOK ztbmo Q (dropWalls ztxgh) ∧
      (chainModel C').DegLe
        ztbanu d ∧
      (chainModel C').Semigranular
        ztbanu ztjfj := by
  have hF := F_eq_famOf (M := chainModel C) (Q := Q)
    (L := N.chords.map fun r => ztlm) rfl
  zvoij at hd hγ
  exact boxTransport h hP hP' (chordTriplesOK_of_isNF hN) hd hγ
end
end BoxT
namespace DrvR
@[expose] public section
open Machine

/-! ## 1. Interior oracles -/

/-- The models the interior oracles must serve: the interior model of the geometry polygon. -/
def OkInt (P : Polygon) (M : Model) : Prop := M = interiorModel zta

/-- The bands of the interior oracles: the oracle bands and the band `bUp` (finding E7-B1). -/
def ioBandsD : Finset ℕ := insert bUp oracleBands

/-- The shooter cost of `ShootCutSpec`, with constant `κ`. -/
noncomputable def shCost (κ : ℕ) (γ : ℕ) : ℕ :=
  κ * ztxd * rpowCeil ztwku ztby + κ

/-- The cutter cost of `ShootCutSpec` (number of pieces), with constant `κ`. -/
def cuCost (κ : ℕ) (γ : ℕ) : ℕ := κ * ztxd

/-- **Obligation (interior oracles, firm): the interior oracles.**  A shooter and a cutter serving
the interior model of `Qof P` on `gradeCtx O`, writing `insert bUp oracleBands`, with the cost
shape of `ShootCutSpec O`. -/
def IntOraclesSpec (O : OracleIface) : Prop :=
  ∃ (sh cu : Stmt) (κ : ℕ),
    ShooterOK sh ioBandsD (shCost κ) ztsy OkInt ∧
    CutterOK cu ioBandsD (cuCost κ) cutGran ztsy OkInt
theorem bRestore_notin_ioBandsD : bRestore ∉ ioBandsD := by_decide
theorem oracleBands_subset_ioBandsD : oracleBands ⊆ ioBandsD := Finset.subset_insert _ _

/-! ## 2.1 The host of a region -/

/-- The vertex of `Q` at walk vertex `p` of the interior walk (`li` the `LeftInside` bit). -/
def ivB (li : Bool) (n p : ℕ) : ℕ := if li then p else n - 1 - p

/-- The edge of `Q` carrying the walk edge `e` of the interior walk. -/
def qE (li : Bool) (n e : ℕ) : ℕ := if li then e else if e + 1 < n then n - 2 - e else n - 1

/-- The position is at the walk vertex starting its edge (distinct heights: its height vertex is
that vertex). -/
def atVtx (li : Bool) (n : ℕ) (x : WPos) : Bool := decide (x.hgt - 1 = ivB li n x.edge)

/-- The host point of a walk position; `isEnd`: the position ends an arc. -/
def ptI (li : Bool) (n : ℕ) (x : WPos) (isEnd : Bool) : HostItem :=
  .pt (.onEdge ztefn
    ztzs)

/-- The other end of the exit chord of region `r` attached at `x` (`x` itself if none). -/
def partner (N : NF) (r : ℕ) (x : WPos) : WPos :=
  match (N.region r).chords.find? (fun i => decide ztdee)
  with
  | some i => if (N.chord i).lpos = x then (N.chord i).rpos else (N.chord i).lpos
  | none => x

/-- The number of walk vertices strictly inside the arc from `s` to `e`. -/
def runCnt (li : Bool) (n : ℕ) (s e : WPos) : ℕ :=
  (e.edge + (if atVtx li n e then 0 else 1) + n - 1 - s.edge) % n

/-- The run of walk vertices strictly inside the arc from `s` to `e` (as host items, empty or one
`.run` in increasing index of `Q`). -/
def runItems (li : Bool) (n : ℕ) (s e : WPos) : List HostItem :=
  if runCnt li n s e = 0 then []
  else if li then [.run (zttzp % n) ztohb]
  else [.run (n - 1 - ztohl % n) ztohb]

/-- The items of arc `j` after its predecessor arc `jp` (junction point, start, run, end). -/
def arcItems (li : Bool) (n : ℕ) (N : NF) (r jp j : ℕ) : List HostItem :=
  (if partner N r (N.arc jp).e = (N.arc j).s then [] else [ptI li n ztglf false]) ++
    [ptI li n (N.arc j).s false] ++ runItems li n (N.arc j).s (N.arc j).e ++
    [ptI li n (N.arc j).e true]

/-- The host items of region `r` in walk order, starting after the end of its first arc. -/
def walkItems (li : Bool) (n : ℕ) (N : NF) (r : ℕ) : List HostItem :=
  (List.range (N.region r).arcs.length).flatMap fun t =>
    arcItems li n N r ztml
      ztwjr

/-- **The host description of region `r`** written by the driver (items in increasing index of
`Q`). -/
def regHost (li : Bool) (n : ℕ) (N : NF) (r : ℕ) : Host :=
  if li then walkItems li n N r else (walkItems li n N r).reverse

/-- **Obligation H-R1/H-R2 (mathematics, firm).**  For region `r` of `N = buildNF I Q L E` (valid
sorted input, at least one chord, degree `≤ 4`) and the region correspondence `reg` of `N`, the
driver's host `H = regHost li n N r` (`li` the `LeftInside` bit of `Q`) is well formed and regular,
its polygon is simple, has interior `reg r` and boundary on `∂Q ∪ ⋃ S`, contains every vertex of
`hostPoly Q S (reg r)`, and the chain `⟨H.poly Q, 0, #points - 1⟩` satisfies the extraction facts. -/
noncomputable def HostR1Spec : Prop :=
  open Classical in
  ∀ (P : Polygon) (L : List zte) (E : List ℕ) (reg : ℕ → Set Point) (r : ℕ),
    GoodEnv P → L ≠ [] →
    ChordTriplesOK ztwiq zta L → E.Perm ztct →
    E.Pairwise ztbajk →
    (interiorModel zta).DegLe
      ztbajd 4 →
    Restore.NFRegs ztwiq zta
      ztbaja reg →
    r < (BuildNF.buildNF ztwiq zta L E).nRegions →
    let Q := Qof P
    let N := BuildNF.buildNF ztd Q L E
    let S := N.F ztd Q
    let H := regHost ztbahl Q.n N r
    HostWF Q.n H ∧ HostRegular Q.n H ∧ (H.poly Q).Simple ∧
      (H.poly Q).filled \ (H.poly Q).boundary = reg r ∧
      (H.poly Q).boundary ⊆ Q.boundary ∪ ⋃₀ S ∧
      (∀ j, j < (DownHost.hostPoly Q S ztcz).n →
        ∃ j', j' < (H.poly Q).n ∧ (H.poly Q).vtx j' = (DownHost.hostPoly Q S ztcz).vtx j) ∧
      ∀ C : Chain, C.P = H.poly Q → C.s = 0 → C.m + 1 = C.P.n → DownDrv.ExtractOK Q S ztcz C
def HostRamSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s {bDownDrv}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ c.nreg 215002 ≤ 1 ∧
      ztxks ∧
      ∃ (L : List zte) (E : List ℕ), L ≠ [] ∧
        ChordTriplesOK ztwiq zta L ∧ E.Perm ztct ∧
        E.Pairwise ztbajk ∧
        (interiorModel zta).DegLe
          ((BuildNF.buildNF ztwiq zta L E).F ztwiq
            zta) 4 ∧
        NFWithin c.nmem ztghd ztm
          ztbaja ∧
        c.nreg 215001 < (BuildNF.buildNF ztwiq zta L E).nRegions)
    (fun P c c' =>
      ztbff ∧
      ∀ (L : List zte) (E : List ℕ), L ≠ [] →
        ChordTriplesOK ztwiq zta L → E.Perm ztct →
        E.Pairwise ztbajk →
        NFAt c.nmem ztghd ztbaja →
        let H := regHost ztzei (Qof P).n
          ztbaja ztdzj
        c.nreg ALLOC ≤ c'.nreg 215010 ∧ c'.nreg 215010 + 3 * H.length + 1 ≤ c'.nreg ALLOC ∧
          HostAt c'.nmem ztmfe H ∧ c'.nreg 215011 = H.length ∧
          c'.nreg 215012 = (H.pts (Qof P).n).length)
    ztqne
