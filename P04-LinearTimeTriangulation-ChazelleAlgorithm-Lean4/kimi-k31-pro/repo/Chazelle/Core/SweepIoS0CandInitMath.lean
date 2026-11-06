module

public import Chazelle.Core.SweepIoS0CandAux
public import Chazelle.Core.SweepIoCand1G
public import Chazelle.Core.SweepEvShot
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.MiscTactics

/-!
# The sweep RAM (WP-D), answers: the slot table of the side-0 candidates (mathematics)

* `iniLogKey`, `search_exact`: the binary search in the log (`lsPr`) is downward closed, and its
  answer is the index of a log record with the key of the target;
* `attach_idx`: an attachment of a chord of `F₂⁺` on the `C₁` part at a stored position is a
  log record;
* `SlotVal`, `slotOK_store`: a slot written with a candidate origin keeps the table good;
* `endPos_facts`, `stopPos`, `stop_slot`, `tab_slot`: the origin positions of the stop records
  and the regular table entries.
-/

namespace Chazelle.Core

namespace SweepIo

namespace S0C

open Set
open Chazelle.Chain (sidePt SideAttach)
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep SweepEv

@[expose] public section

/-! ## The search in the log -/

/-- The key of a log record in memory. -/
theorem iniLogKey (P : Polygon) (J : Merge.Junction) (N : NF) {m : ℕ → ℕ} {AL : ℕ}
    {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)} (hrec : LogRecsAt m AL ls) {j : ℕ}
    (hj : j < ls.length) :
    (chainModel J.whole).key (Qof P) ⟨m (AL + 7 * j), m (AL + 7 * j + 1)⟩ =
      (((logOf J (Qof P) N ls).getD j (0, 0, ∅)).1 : ℝ) +
        ((logOf J (Qof P) N ls).getD j (0, 0, ∅)).2.1 := by
  obtain ⟨a1, a2, -⟩ := hrec j hj
  obtain ⟨l1, l2⟩ := logOf_getD J (Qof P) N hj
  rw [l1, l2, ← a1, ← a2]
  rfl

/-- **The search in the log**: `lsPr` is downward closed, and an answer of the search is the
index of a log record whose key is the target's. -/
theorem search_exact {P : Polygon} {J : Merge.Junction} {N : NF} {S₂ : Set (Set Point)}
    {m : ℕ → ℕ} {AL G : ℕ} {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)} (hG : G = gW J)
    (hrec : LogRecsAt m AL ls) (hLog : LogOK J S₂ (logOf J (Qof P) N ls)) (x : WPos) :
    (∀ a b, a ≤ b → b < ls.length → lsPr P J m AL G x b → lsPr P J m AL G x a) ∧
    ∀ i, i < ls.length → m (AL + 7 * i) = x.edge →
      (chainModel J.whole).param (Qof P) (logPos m AL i) = (chainModel J.whole).param (Qof P) x →
      ∀ t, (∀ j, j < t → lsPr P J m AL G x j) →
        (∀ j, t ≤ j → j < ls.length → ¬ lsPr P J m AL G x j) → t = i := by
  obtain ⟨-, -, -, hsort, -⟩ := hLog
  set es := logOf J (Qof P) N ls with hes
  have hlen : es.length = ls.length := by rw [hes]; ufs logOf
  have hpr : ∀ j, j < ls.length → (lsPr P J m AL G x j ↔
      oW J ((es.getD j (0, 0, ∅)).1 + (es.getD j (0, 0, ∅)).2.1) <
        oW J ((chainModel J.whole).key (Qof P) x)) := by
    intro j hj
    unfold lsPr
    rw [iniLogKey P J N hrec hj, hG]
    rfl
  have hlt : ∀ a b, a < b → b < ls.length →
      oW J ((es.getD a (0, 0, ∅)).1 + (es.getD a (0, 0, ∅)).2.1) <
        oW J ((es.getD b (0, 0, ∅)).1 + (es.getD b (0, 0, ∅)).2.1) := by
    intro a b hab hb
    have ha' : a < es.length := by omega
    have hb' : b < es.length := by omega
    rw [List.getD_eq_getElem _ _ ha', List.getD_eq_getElem _ _ hb']
    exact List.pairwise_iff_getElem.1 hsort a b ha' hb' hab
  refine ⟨fun a b hab hb h => ?_, fun i hi he hp t h1 h2 => ?_⟩
  · rcases hab.lt_or_eq with hab | rfl
    · rw [hpr a (by omega)]
      rw [hpr b hb] at h
      exact lt_trans (hlt a b hab hb) h
    · exact h
  · have hki : (chainModel J.whole).key (Qof P) (logPos m AL i) =
        (chainModel J.whole).key (Qof P) x := by
      unfold Model.key
      rw [hp]
      show ((m (AL + 7 * i) : ℕ) : ℝ) + _ = _
      rw [he]
    have hni : ¬ lsPr P J m AL G x i := by
      unfold lsPr
      show ¬ off _ _ ((chainModel J.whole).key (Qof P) (logPos m AL i)) < _
      rw [hki]; exact lt_irrefl _
    have hKi : oW J ((es.getD i (0, 0, ∅)).1 + (es.getD i (0, 0, ∅)).2.1) =
        oW J ((chainModel J.whole).key (Qof P) x) := by
      rwr [← iniLogKey P J N hrec hi, ← hki]
    rcases lt_trichotomy t i with h | h | h
    · exfalso
      apply h2 t le_rfl (by omega)
      rw [hpr t (by omega), ← hKi]
      exact hlt t i h hi
    · exact h
    · exact absurd (h1 i h) hni

/-- **An attachment at a stored position is a log record.** -/
theorem attach_idx {P : Polygon} {J : Merge.Junction} {N : NF} {S₂ : Set (Set Point)}
    {m : ℕ → ℕ} {AL : ℕ} {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hrec : LogRecsAt m AL ls) (hLog : LogOK J S₂ (logOf J (Qof P) N ls)) {e : Set Point}
    (he : e ∈ F₂plus J S₂) {x : WPos}
    (hA : SideAttach (chainModel J.whole).W e x.edge ((chainModel J.whole).param (Qof P) x))
    (hst : (Lst J : ℝ) ≤ oW J (x.edge + (chainModel J.whole).param (Qof P) x)) :
    ∃ i, i < ls.length ∧ m (AL + 7 * i) = x.edge ∧
      (chainModel J.whole).param (Qof P) (logPos m AL i) =
        (chainModel J.whole).param (Qof P) x := by
  obtain ⟨i, hi, h1, h2⟩ := cut_key J hLog he hA hst
  have hlen : (logOf J (Qof P) N ls).length = ls.length := by ufs logOf
  rw [hlen] at hi
  obtain ⟨l1, l2⟩ := logOf_getD J (Qof P) N hi
  obtain ⟨a1, a2, -⟩ := hrec i hi
  refine ⟨i, hi, by rw [a1, ← l1, h1], ?_⟩
  unfold logPos
  rw [a1, a2, ← l2, h2]

/-! ## Slots -/

/-- **The content of a good flagged slot**: a proper position of the model of `C₂` whose point is
a candidate origin for `w` in the direction of the slot. -/
def SlotVal (P : Polygon) (J : Merge.Junction) (u : WPos) (s : ℕ) (w : Point) : Prop :=
  u.edge < (chainModel J.right).W.n ∧ ProperPos (chainModel J.right) (Qof P) P.n u ∧
    CandAt J ((chainModel J.right).pos (Qof P) u) (dS s) w

/-- The memory after writing the slot `(t, s)` with `(1, e, h)`. -/
def slotW (m : ℕ → ℕ) (B t s e h : ℕ) : ℕ → ℕ :=
  upd (upd (upd m (slotA B t s) 1) (slotA B t s + 1) e) (slotA B t s + 2) h

theorem slotW_other {m : ℕ → ℕ} {B t s e h a : ℕ} (ha : a < slotA B t s ∨ slotA B t s + 2 < a) :
    slotW m B t s e h a = m a := by
  unfold slotW
  rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]

theorem slotW_flag {m : ℕ → ℕ} {B t s e h : ℕ} : slotW m B t s e h (slotA B t s) = 1 := by
  unfold slotW
  rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_same]

/-- Two different slots do not overlap. -/
theorem slot_sep {B i s t s' d : ℕ} (hs : s ≤ 1) (hs' : s' ≤ 1) (hd : d < 3)
    (hne : ¬ (i = t ∧ s = s')) :
    slotA B i s + d < slotA B t s' ∨ slotA B t s' + 2 < slotA B i s + d := by
  unfold slotA
  omega

/-- **Writing a slot with a candidate origin keeps the slots good.** -/
theorem slotOK_store {P : Polygon} {J : Merge.Junction} {m : ℕ → ℕ} {B AL E t s e h : ℕ}
    (hsep : AL + 7 * E ≤ B) (ht : t < E) (hs : s ≤ 1)
    (hok : ∀ i, i < E → ∀ s', s' ≤ 1 → SlotOK P J m B AL i s')
    (hv : SlotVal P J ⟨e, h⟩ s (logPt P J m AL t)) :
    ∀ i, i < E → ∀ s', s' ≤ 1 → SlotOK P J (slotW m B t s e h) B AL i s' := by
  intro i hi s' hs'
  have hL : ∀ j, j < E → logPt P J (slotW m B t s e h) AL j = logPt P J m AL j := by
    intro j hj
    have h0 : slotW m B t s e h (AL + 7 * j) = m (AL + 7 * j) :=
      slotW_other (Or.inl (by ufo slotA))
    have h1 : slotW m B t s e h (AL + 7 * j + 1) = m (AL + 7 * j + 1) :=
      slotW_other (Or.inl (by ufo slotA))
    unfold logPt logPos
    rw [h0, h1]
  by_cases hit : i = t ∧ s' = s
  · obtain ⟨rfl, rfl⟩ := hit
    have f0 : slotW m B i s' e h (slotA B i s') = 1 := slotW_flag
    have f1 : slotW m B i s' e h (slotA B i s' + 1) = e := by
      unfold slotW; rw [upd_other _ _ _ (by omega), upd_same]
    have f2 : slotW m B i s' e h (slotA B i s' + 2) = h := by
      unfold slotW; rw [upd_same]
    unfold SlotOK
    rw [f0, f1, f2, hL i hi]
    exact ⟨le_rfl, fun _ => hv⟩
  · have g : ∀ d, d < 3 → slotW m B t s e h (slotA B i s' + d) = m (slotA B i s' + d) :=
      fun d hd => slotW_other (slot_sep hs' hs hd hit)
    have g0 : slotW m B t s e h (slotA B i s') = m (slotA B i s') := by
      simpa using g 0 (by norm_num)
    unfold SlotOK
    rw [g0, g 1 (by norm_num), g 2 (by norm_num), hL i hi]
    exact hok i hi s' hs'

/-! ## Origin positions -/

/-- **The normalised end position of a chord** of `N₂`: a proper position of the model of `C₂`
whose point is the endpoint origin `2 k + s`. -/
theorem endPos_facts {P : Polygon} {J : Merge.Junction} {N : NF}
    (hN : IsNF (chainModel J.right) (Qof P) N) {k s : ℕ} (hk : k < N.nChords) (hs : s ≤ 1) :
    (endPos N k s).edge < (chainModel J.right).W.n ∧
      ProperPos (chainModel J.right) (Qof P) P.n
        ⟨(endPos N k s).edge, nhgt (chainModel J.right) (Qof P) (endPos N k s)⟩ ∧
      (chainModel J.right).pos (Qof P)
        ⟨(endPos N k s).edge, nhgt (chainModel J.right) (Qof P) (endPos N k s)⟩ =
        endOrigin J (Qof P) N (2 * k + s) ∧
      (nhgt (chainModel J.right) (Qof P) (endPos N k s) = 0 ↔
        (chainModel J.right).param (Qof P)
          ⟨(endPos N k s).edge, nhgt (chainModel J.right) (Qof P) (endPos N k s)⟩ = 0) := by
  have hA := hN.2.2.1 k hk
  have hhn := (regOf_spec hN).2.2.2.2.2.1 k hk
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hpl : ProperPos (chainModel J.right) (Qof P) P.n (N.chord k).lpos :=
    ⟨hA.1.2.1, hA.1.2.2.1, by show (N.chord k).h + 1 ≤ P.n; rwo [← hQn]⟩
  have hpr : ProperPos (chainModel J.right) (Qof P) P.n (N.chord k).rpos :=
    ⟨hA.2.2.1, hA.2.2.2.1, by show (N.chord k).h + 1 ≤ P.n; rwo [← hQn]⟩
  have hp : ProperPos (chainModel J.right) (Qof P) P.n (endPos N k s) := by
    unfold endPos; split_ifs
    · exact hpl
    · exact hpr
  have he : (endPos N k s).edge < (chainModel J.right).W.n := by
    unfold endPos; split_ifs
    · exact hA.1.1
    · exact hA.2.1
  obtain ⟨n1, -, n3, n4⟩ := nhgt_facts hp
  have hj : 2 * k + s < 2 * N.nChords := by omega
  obtain ⟨o1, -⟩ := endOrigin_eq J hN hj
  have e1 : (2 * k + s) / 2 = k := by omega
  have e2 : (2 * k + s) % 2 = s := by omega
  rw [e1, e2] at o1
  exact ⟨he, n1, by rw [n3, o1], n4⟩

/-- The origin position of a stop record `(kind, k, b)`. -/
noncomputable def stopPos (P : Polygon) (J : Merge.Junction) (N : NF) (kind k b : ℕ) : WPos :=
  if kind = 0 then ⟨cstR J 1, 0⟩
  else if kind = 1 then
    ⟨(endPos N k (sOf b)).edge, nhgt (chainModel J.right) (Qof P) (endPos N k (sOf b))⟩
  else ⟨6, 0⟩

theorem ini_dS_sOf (b : ℕ) : dS (sOf b) = dirOf b := by
  unfold dS sOf dirOf
  by_cases h : b = 1 <;> simp [h]

theorem ini_sOf_le (b : ℕ) : sOf b ≤ 1 := by unfold sOf; splao

/-- **The origin position of a stop record.** -/
theorem stopPos_facts {P : Polygon} {J : Merge.Junction} {N : NF} (hP : J.P.Simple)
    (hN : IsNF (chainModel J.right) (Qof P) N) {kind k b : ℕ} (_hkind : kind ≤ 2)
    (hk : kind = 1 → k < N.nChords) :
    (stopPos P J N kind k b).edge < (chainModel J.right).W.n ∧
      ProperPos (chainModel J.right) (Qof P) P.n (stopPos P J N kind k b) ∧
      (chainModel J.right).pos (Qof P) (stopPos P J N kind k b) = stopOrig J (Qof P) N kind k b := by
  have hn := cm_n J.right
  have ht := tpos_lt J.right 0
  unfold stopPos stopOrig
  by_cases h0 : kind = 0
  · simp [ite_eq_left h0]
    have hlt : cstR J 1 < (chainModel J.right).W.n := by
      rw [hn]; show 6 + tpos J.right 0 < _; omega
    have hp0 := Cand1.param_hgt0 (chainModel J.right) (Qof P) (cstR J 1)
    refine ⟨hlt, ⟨by rw [hp0], by rwn [hp0], Nat.zero_le _⟩, ?_⟩
    exact (Cand1.shared_iffR hP (Qof P) hlt (by rw [hp0]) (by rwn [hp0])).2
      ⟨hp0, Or.inl rfl⟩
  · simp [ite_eq_right h0]
    by_cases h1 : kind = 1
    · simp [ite_eq_left h1]
      obtain ⟨a1, a2, a3, -⟩ := endPos_facts hN (hk h1) (ini_sOf_le b)
      refine ⟨a1, a2, ?_⟩
      rw [a3]
      congr 1
      unfold sOf; by_cases hb : b = 1 <;> norm_num [hb, dirOf]
    · simp [ite_eq_right h1]
      have hlt : (6 : ℕ) < (chainModel J.right).W.n := by rwo [hn]
      have hp0 := Cand1.param_hgt0 (chainModel J.right) (Qof P) 6
      refine ⟨hlt, ⟨by rw [hp0], by rwn [hp0], Nat.zero_le _⟩, ?_⟩
      exact (Cand1.top_iffR hP (Qof P) hlt (by rw [hp0]) (by rwn [hp0])).2
        ⟨hp0, Or.inl rfl⟩

end

end S0C

end SweepIo

end Chazelle.Core
