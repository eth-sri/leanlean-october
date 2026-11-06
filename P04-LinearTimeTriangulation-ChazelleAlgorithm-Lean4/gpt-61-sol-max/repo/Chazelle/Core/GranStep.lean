module

public import Chazelle.Core.GranState

/-!
# WP-F, part 7: one step of the worklist — popping, and the removability test

The worklist step pops the chord `c = st.cur`.  If it is dead, or not removable, the state is only
popped (`Inv.pop_dead`, `Inv.pop_keep`).  Removability is decided from the state
(`Inv.removable_iff`): one of the two classes of `c` has fewer than `3` exit chords, and the
weight `St.mu` of the merged region is at most `γ`, where `St.mu` is computed from the two class
weights and the gaps of the new submap around the attachment keys of `c` that stop being cuts
(`Inv.mu_eq`: `St.mu` is the weight of the merged region).  The removal itself is in
`GranStep2`.
-/

namespace Chazelle.Core

namespace Gran

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt ChordSystem freeIn regionsIn TouchesIn)

namespace St

variable (E : Env) (st : St)

/-- Pop the worklist. -/
def pop : St := { st with top := st.top - 1 }

/-- The chord on top of the worklist. -/
def cur : ℕ := st.stk (st.top - 1)

/-- Position `j` stops being live when chord `c` is removed. -/
def dd (c j : ℕ) : Bool :=
  (decide (j = st.nd0 c) && decide (st.cnt (st.nd0 c) = 1)) ||
    (decide (j = st.nd1 c) && decide (st.cnt (st.nd1 c) = 1))

section
variable (c k : ℕ)
include c k
/-- The live predecessor of `k` after the removal of `c` (skipping one dead position). -/
def prD : ℕ := if st.dd c (st.prv k) then st.prv (st.prv k) else st.prv k

/-- The live successor of `k` after the removal of `c`. -/
def suD : ℕ := if st.dd c (st.nxt k) then st.nxt (st.nxt k) else st.nxt k

/-- The weight of the gap around position `k` after the removal of `c`, if `k` dies. -/
def jw : ℕ :=
  if st.cnt k = 1 then gwt E.sz st.eg st.pz (st.prD c k) (st.suD c k) else 0


end

/-- **The merged weight** (the weight of the region of the new submap merging the two classes of
`c`). -/
def mu (c : ℕ) : ℕ :=
  if st.nlive = 1 then cntIn E.ch E.m 0 E.n
  else max (max (st.wt (st.s0 c)) (st.wt (st.s1 c))) (max (st.jw E c (st.nd0 c))
    (st.jw E c (st.nd1 c)))

end St

variable {E : Env} {st : St}

/-! ## Popping -/

section
variable (h : Inv E st) (htop : 0 < st.top)
include h htop
theorem Inv.pop_of
    (hc : st.cur ∈ st.L E → ¬ Merge.Removable E.M.D E.M.weight E.γ (st.F E)
      (cs E.M E.Q E.N st.cur)) : Inv E st.pop := by
  show Inv E { st with top := st.top - 1 }
  refine ⟨h.stat.congr rfl rfl rfl rfl, h.live01, h.nlive, h.degLe, h.semi, h.sides, h.cls, h.refInj, h.cnt, h.ring,
    fun t ht => h.stk t (by simp only at ht; omega), ?_, ?_⟩
  · have := h.topLe; simp only; omega
  · intro i hi hno
    by_cases hic : i = st.cur
    · subst hic; exact hc hi
    · refine h.work i hi fun t ht => ?_
      by_cases htt : t = st.top - 1
      · subst htt; exact fun e => hic e.symm
      · exact hno t (by simp only; omega)

/-- **Popping a dead chord.** -/
theorem Inv.pop_dead (hd : st.live st.cur ≠ 1) :
    Inv E st.pop := h.pop_of htop fun hi => absurd hi.2 hd

/-- **Popping a live chord that is not removable.** -/
theorem Inv.pop_keep
    (hnr : ¬ Merge.Removable E.M.D E.M.weight E.γ (st.F E) (cs E.M E.Q E.N st.cur)) :
    Inv E st.pop := h.pop_of htop fun _ => hnr

/-! ## Gaps -/


end

/-- **Two gaps containing the same key coincide.** -/
theorem gap_unique {M : Model} {G : Set (Set Point)} {l r l' r' x : ℝ} (hg : Gap M G l r)
    (hg' : Gap M G l' r') (hx : sideInArc l r x) (hx' : sideInArc l' r' x) : l = l' ∧ r = r' := by
  obtain ⟨hl, hr, hlr, hf⟩ := hg
  obtain ⟨hl', hr', hlr', hf'⟩ := hg'
  have hxl : x ≠ l := fun e => hf x hx (e ▸ hl)
  have hxl' : x ≠ l' := fun e => hf' x hx' (e ▸ hl')
  have hxr : x ≠ r := fun e => hf x hx (e ▸ hr)
  have hxr' : x ≠ r' := fun e => hf' x hx' (e ▸ hr')
  refine ⟨cyc_start_eq' (Ne.symm hxl) (Ne.symm hxl') (fun h1 => hf l' (cyc_sub_mid hx h1) hl')
    (fun h1 => hf' l (cyc_sub_mid hx' h1) hl), cyc_end_eq hxr hxr'
      (fun h1 => hf r' (cyc_sub_mid' hx h1) hr') (fun h1 => hf' r (cyc_sub_mid' hx' h1) hr)⟩

/-! ## Counting the chords at a position -/

theorem card_filter_two (K : ℕ) (P₀ P₁ : ℕ → Prop) [DecidablePred P₀] [DecidablePred P₁] {c : ℕ}
    (hcK : c < K) (h0 : P₀ c) (h1 : ¬ P₁ c) :
    ((Finset.range K).filter P₀).card + ((Finset.range K).filter P₁).card = 1 ↔
      ∀ i, i < K → i ≠ c → ¬ P₀ i ∧ ¬ P₁ i := by
  have hc0 : c ∈ (Finset.range K).filter P₀ := by simp [hcK, h0]
  constructor
  · intro h i hi hic
    have hpos := Finset.card_pos.2 ⟨c, hc0⟩
    have h1' : ((Finset.range K).filter P₁).card = 0 := by omega
    have h0' : ((Finset.range K).filter P₀).card = 1 := by omega
    rw [Finset.card_eq_zero] at h1'
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h0'
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · have hi0 : i ∈ (Finset.range K).filter P₀ := by simp [hi, hp]
      rw [ha] at hi0 hc0
      simp only [Finset.mem_singleton] at hi0 hc0
      exact hic (hi0.trans hc0.symm)
    · have : i ∈ (Finset.range K).filter P₁ := by simp [hi, hp]
      rw [h1'] at this
      exact absurd this (Finset.notMem_empty _)
  · intro h
    have e0 : (Finset.range K).filter P₀ = {c} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hi, hp⟩
        by_contra hic
        exact (h i hi hic).1 hp
      · rintro rfl; exact ⟨hcK, h0⟩
    have e1 : (Finset.range K).filter P₁ = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
      intro hi hp
      by_cases hic : i = c
      · subst hic; exact h1 hp
      · exact (h i hi hic).2 hp
    rw [e0, e1]; rfl

section
variable (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E)
include hE h hc
/-- The two positions of a live chord differ. -/
theorem Inv.nd_ne :
    st.nd0 c ≠ st.nd1 c := by
  intro e
  have h0 := (h.stat.nd0 c hc.1).2
  have h1 := (h.stat.nd1 c hc.1).2
  rw [e, h1] at h0
  exact lkey_ne_rkey hE.hNF hE.hM hc.1 h0.symm

/-- **A position of a live chord `c` has count `1` iff no other live chord is attached there.** -/
theorem Inv.cnt_eq_one_iff {j : ℕ}
    (hj : j = st.nd0 c ∨ j = st.nd1 c) :
    st.cnt j = 1 ↔ ∀ i ∈ st.L E, i ≠ c → st.nd0 i ≠ j ∧ st.nd1 i ≠ j := by
  have hjA : j < E.A := by
    rcases hj with rfl | rfl
    · exact (h.stat.nd0 c hc.1).1
    · exact (h.stat.nd1 c hc.1).1
  rw [h.cnt j hjA]
  unfold St.cntOf
  have hne := h.nd_ne hE hc
  rcases hj with rfl | rfl
  · rw [card_filter_two E.K _ _ hc.1 ⟨hc.2, rfl⟩ (fun hp => hne hp.2.symm)]
    constructor
    · intro h' i hi hic
      obtain ⟨a, b⟩ := h' i hi.1 hic
      exact ⟨fun e => a ⟨hi.2, e⟩, fun e => b ⟨hi.2, e⟩⟩
    · intro h' i hi hic
      refine ⟨fun hp => (h' i ⟨hi, hp.1⟩ hic).1 hp.2, fun hp => (h' i ⟨hi, hp.1⟩ hic).2 hp.2⟩
  · rw [add_comm, card_filter_two E.K _ _ hc.1 ⟨hc.2, rfl⟩ (fun hp => hne hp.2)]
    constructor
    · intro h' i hi hic
      obtain ⟨a, b⟩ := h' i hi.1 hic
      exact ⟨fun e => b ⟨hi.2, e⟩, fun e => a ⟨hi.2, e⟩⟩
    · intro h' i hi hic
      refine ⟨fun hp => (h' i ⟨hi, hp.1⟩ hic).2 hp.2, fun hp => (h' i ⟨hi, hp.1⟩ hic).1 hp.2⟩

/-! ## The submap without `c` -/


end

/-- The live set without `c`. -/
theorem fam_diff (hE : E.Good) {c : ℕ} (hc : c ∈ st.L E) :
    fam E.M E.Q E.N (st.L E \ {c}) = st.F E \ {cs E.M E.Q E.N c} := by
  ext d
  constructor
  · rintro ⟨i, ⟨hiL, hic⟩, hi, rfl⟩
    refine ⟨⟨i, hiL, hi, rfl⟩, fun he => hic ?_⟩
    exact cs_inj hE.hNF hi hc.1 he
  · rintro ⟨⟨i, hiL, hi, rfl⟩, hne⟩
    exact ⟨i, ⟨hiL, fun e => hne (by rw [mem_singleton_iff] at e; subst e; rfl)⟩, hi, rfl⟩

section
variable (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E)
include hE h c hc
/-- **The cuts after the removal of `c`**: the start keys of the live positions that do not die. -/
theorem Inv.cut_sdiff_iff (k : ℝ) :
    E.M.IsCut (st.F E \ {cs E.M E.Q E.N c}) k ↔
      ∃ j, j < E.A ∧ st.Lv j ∧ st.dd c j = false ∧ E.key j = k := by
  rw [← fam_diff hE hc, isCut_fam_iff hE.hNF hE.hM]
  constructor
  · rintro ⟨i, ⟨hiL, hic⟩, hi, hk⟩
    have hic' : i ≠ c := fun e => hic (by rw [e]; rfl)
    -- the position of the attachment
    have hpos : ∃ j, (j = st.nd0 i ∨ j = st.nd1 i) ∧ j < E.A ∧ E.key j = k := by
      rcases hk with hk | hk
      · exact ⟨st.nd0 i, Or.inl rfl, (h.stat.nd0 i hi).1, by rw [(h.stat.nd0 i hi).2, hk]⟩
      · exact ⟨st.nd1 i, Or.inr rfl, (h.stat.nd1 i hi).1, by rw [(h.stat.nd1 i hi).2, hk]⟩
    obtain ⟨j, hji, hj, hkj⟩ := hpos
    refine ⟨j, hj, (h.lv_iff hj).2 ⟨i, hiL, hji.elim (fun e => Or.inl e.symm)
      (fun e => Or.inr e.symm)⟩, ?_, hkj⟩
    unfold St.dd
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨?_, ?_⟩
    · by_cases hj0 : j = st.nd0 c
      · right
        intro h1
        have := ((h.cnt_eq_one_iff hE hc (Or.inl rfl)).1 h1 i hiL hic')
        rcases hji with e | e
        · exact this.1 (e.symm.trans hj0)
        · exact this.2 (e.symm.trans hj0)
      · left; exact hj0
    · by_cases hj1 : j = st.nd1 c
      · right
        intro h1
        have := ((h.cnt_eq_one_iff hE hc (Or.inr rfl)).1 h1 i hiL hic')
        rcases hji with e | e
        · exact this.1 (e.symm.trans hj1)
        · exact this.2 (e.symm.trans hj1)
      · left; exact hj1
  · rintro ⟨j, hj, hL, hdd, rfl⟩
    obtain ⟨i, hiL, hij⟩ := (h.lv_iff hj).1 hL
    -- if `i = c`, another live chord is attached at `j`
    have hkey : ∀ i', i' ∈ st.L E → (st.nd0 i' = j ∨ st.nd1 i' = j) →
        (E.key j = E.M.key E.Q (E.N.chord i').lpos ∨
          E.key j = E.M.key E.Q (E.N.chord i').rpos) := by
      rintro i' hi' (e | e)
      · left; rw [← e]; exact (h.stat.nd0 i' hi'.1).2
      · right; rw [← e]; exact (h.stat.nd1 i' hi'.1).2
    by_cases hic : i = c
    · subst hic
      unfold St.dd at hdd
      simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hdd
      obtain ⟨h0, h1⟩ := hdd
      have hj' : j = st.nd0 i ∨ j = st.nd1 i := hij.elim (fun e => Or.inl e.symm)
        (fun e => Or.inr e.symm)
      have hnot : st.cnt j ≠ 1 := by
        rcases hj' with e | e
        · rcases h0 with h0 | h0
          · exact absurd e h0
          · rw [e]; exact h0
        · rcases h1 with h1 | h1
          · exact absurd e h1
          · rw [e]; exact h1
      have hnot' := mt (h.cnt_eq_one_iff hE hiL hj').2 hnot
      push Not at hnot'
      replace hnot := hnot'
      obtain ⟨i', hi', hi'c, hi'j⟩ := hnot
      have hi'j' : st.nd0 i' = j ∨ st.nd1 i' = j := by
        by_cases e : st.nd0 i' = j
        · exact Or.inl e
        · exact Or.inr (hi'j e)
      exact ⟨i', ⟨hi', by rw [mem_singleton_iff]; exact hi'c⟩, hi'.1, hkey i' hi' hi'j'⟩
    · exact ⟨i, ⟨hiL, by rw [mem_singleton_iff]; exact hic⟩, hiL.1, hkey i hiL hij⟩

/-! ## The removal split of a live chord -/

theorem Inv.cl_mem :
    st.cl E (st.s0 c) ∈ E.M.regions (st.F E) ∧ st.cl E (st.s1 c) ∈ E.M.regions (st.F E) :=
  ⟨(St.cl_spec hE (h.sides c hc).1).1, (St.cl_spec hE (h.sides c hc).2.1).1⟩

/-- **Removing a live chord merges its two classes.** -/
theorem Inv.split :
    ∃ P, Merge.IsSplit E.M.D (st.F E \ {cs E.M E.Q E.N c}) (cs E.M E.Q E.N c) P
      (st.cl E (st.s0 c)) (st.cl E (st.s1 c)) := by
  have hsys := hE.hM.sys _ (St.F_adm (st := st) hE) (St.F_finite (st := st) hE)
  obtain ⟨P, R₁, R₂, hs⟩ := Merge.exists_removal_split hsys subset_rfl (St.cs_mem_F hc)
  obtain ⟨-, -, -, htouch⟩ := h.sides c hc
  have hm₁ := split_mem₁ (St.cs_mem_F hc) hs
  have hm₂ := split_mem₂ (St.cs_mem_F hc) hs
  have t₁ := (split_touches_iff hE.hM (St.F_adm (st := st) hE) (St.F_finite (st := st) hE) (St.cs_mem_F hc) hs hm₁).2
    (Or.inl rfl)
  have t₂ := (split_touches_iff hE.hM (St.F_adm (st := st) hE) (St.F_finite (st := st) hE) (St.cs_mem_F hc) hs hm₂).2
    (Or.inr rfl)
  have hne := hs.ne
  rcases (htouch R₁ hm₁).1 t₁ with e1 | e1 <;> rcases (htouch R₂ hm₂).1 t₂ with e2 | e2
  · exact absurd (e1.trans e2.symm) hne
  · subst e1 e2; exact ⟨P, hs⟩
  · subst e1 e2; exact ⟨P, hs.symm⟩
  · exact absurd (e1.trans e2.symm) hne

/-- **Removability from the state.** -/
theorem Inv.removable_iff {P : Set Point}
    (hs : Merge.IsSplit E.M.D (st.F E \ {cs E.M E.Q E.N c}) (cs E.M E.Q E.N c) P
      (st.cl E (st.s0 c)) (st.cl E (st.s1 c))) :
    Merge.Removable E.M.D E.M.weight E.γ (st.F E) (cs E.M E.Q E.N c) ↔
      (st.deg (st.s0 c) < 3 ∨ st.deg (st.s1 c) < 3) ∧
        E.M.weight (st.F E \ {cs E.M E.Q E.N c}) P ≤ E.γ := by
  obtain ⟨-, -, hne, htouch⟩ := h.sides c hc
  obtain ⟨hX, hY⟩ := h.cl_mem hE hc
  have dX : st.deg (st.s0 c) = (Merge.exitsIn E.M.D (st.F E) (st.cl E (st.s0 c))).ncard :=
    (h.cls _ ⟨c, hc, Or.inl rfl⟩).1
  have dY : st.deg (st.s1 c) = (Merge.exitsIn E.M.D (st.F E) (st.cl E (st.s1 c))).ncard :=
    (h.cls _ ⟨c, hc, Or.inr rfl⟩).1
  constructor
  · rintro ⟨-, U, hU, V, hV, hUV, hcU, hcV, hlow, hW⟩
    rcases (htouch U hU).1 hcU with rfl | rfl <;> rcases (htouch V hV).1 hcV with rfl | rfl
    · exact absurd rfl hUV
    · exact ⟨by rw [dX, dY]; exact hlow, hW P hs.mem hs.sub₁⟩
    · exact ⟨by rw [dX, dY]; exact hlow.symm, hW P hs.mem hs.sub₂⟩
    · exact absurd rfl hUV
  · rintro ⟨hlow, hw⟩
    refine ⟨St.cs_mem_F hc, _, hX, _, hY, hne, (htouch _ hX).2 (Or.inl rfl),
      (htouch _ hY).2 (Or.inr rfl), by rw [← dX, ← dY]; exact hlow, fun W hW hsub => ?_⟩
    rw [Chazelle.Chain.regionsIn_eq_of_subset hW hs.mem (Chazelle.Chain.regionsIn_nonempty hX)
      hsub hs.sub₁]
    exact hw

/-! ## The merged weight -/

section
variable {n : ℕ} (hn : n = st.nd0 c ∨ n = st.nd1 c)
include n hn
/-- The key of a position of a live chord is a cut of the current submap. -/
theorem Inv.key_nd_cut : n < E.A ∧ st.Lv n ∧ E.M.IsCut (st.F E) (E.key n) := by
  have hnA : n < E.A := by
    rcases hn with rfl | rfl
    · exact (h.stat.nd0 c hc.1).1
    · exact (h.stat.nd1 c hc.1).1
  have hL : st.Lv n := (h.lv_iff hnA).2 ⟨c, hc, hn.elim (fun e => Or.inl e.symm)
    (fun e => Or.inr e.symm)⟩
  exact ⟨hnA, hL, (h.cut_iff hE _).2 ⟨n, hnA, hL, rfl⟩⟩

/-- `dd` at a position of `c`. -/
theorem Inv.dd_iff : st.dd c n = true ↔ st.cnt n = 1 := by
  have hne := h.nd_ne hE hc
  unfold St.dd
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rcases hn with rfl | rfl
  · constructor
    · rintro (⟨-, h1⟩ | ⟨e, -⟩)
      · exact h1
      · exact absurd e hne
    · intro h1; exact Or.inl ⟨rfl, h1⟩
  · constructor
    · rintro (⟨e, -⟩ | ⟨-, h1⟩)
      · exact absurd e.symm hne
      · exact h1
    · intro h1; exact Or.inr ⟨rfl, h1⟩



end

end

/-- The dying positions are the positions of `c` with count `1`. -/
theorem Inv.dd_cases (_hE : E.Good) (_h : Inv E st) {c : ℕ} (_hc : c ∈ st.L E) {j : ℕ}
    (hj : st.dd c j = true) : (j = st.nd0 c ∨ j = st.nd1 c) ∧ st.cnt j = 1 := by
  have hj' := hj
  unfold St.dd at hj'
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hj'
  rcases hj' with ⟨rfl, h1⟩ | ⟨rfl, h1⟩
  · exact ⟨Or.inl rfl, h1⟩
  · exact ⟨Or.inr rfl, h1⟩

section
variable (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E)
include hE h hc
/-- **The lost keys of `c`** are the start keys of its positions of count `1`. -/
theorem Inv.lost_iff {k : ℝ} :
    k ∈ lostKeys E.M (st.F E) (cs E.M E.Q E.N c) ↔
      ∃ n, (n = st.nd0 c ∨ n = st.nd1 c) ∧ st.cnt n = 1 ∧ k = E.key n := by
  constructor
  · rintro hk
    obtain ⟨p, t, hA, rfl, -⟩ := lost_attach (St.cs_mem_F hc) hk
    have hkeys := attach_keys hE.hNF hE.hM hc.1 hA
    have hpos : ∃ n, (n = st.nd0 c ∨ n = st.nd1 c) ∧ (p : ℝ) + t = E.key n := by
      rcases hkeys with e | e
      · exact ⟨st.nd0 c, Or.inl rfl, by rw [e, (h.stat.nd0 c hc.1).2]⟩
      · exact ⟨st.nd1 c, Or.inr rfl, by rw [e, (h.stat.nd1 c hc.1).2]⟩
    obtain ⟨n, hn, hkn⟩ := hpos
    obtain ⟨hnA, hL, -⟩ := h.key_nd_cut hE hc hn
    refine ⟨n, hn, ?_, hkn⟩
    rw [← h.dd_iff hE hc hn]
    by_contra hdd
    exact hk.2 ((h.cut_sdiff_iff hE hc _).2 ⟨n, hnA, hL, by simpa using hdd, hkn.symm⟩)
  · rintro ⟨n, hn, h1, rfl⟩
    obtain ⟨hnA, hL, hcut⟩ := h.key_nd_cut hE hc hn
    refine ⟨hcut, fun hcut' => ?_⟩
    obtain ⟨j, hj, -, hdd, hkj⟩ := (h.cut_sdiff_iff hE hc _).1 hcut'
    have := key_inj hE hj hnA hkj
    subst this
    rw [(h.dd_iff hE hc hn).2 h1] at hdd
    exact Bool.noConfusion hdd

/-- **The gap around a dying position** after the removal of `c`. -/
theorem Inv.dead_gap
    (hne' : (st.F E \ {cs E.M E.Q E.N c}).Nonempty) {n : ℕ}
    (hn : n = st.nd0 c ∨ n = st.nd1 c) (h1 : st.cnt n = 1) :
    st.prD c n < E.A ∧ st.suD c n < E.A ∧
      Gap E.M (st.F E \ {cs E.M E.Q E.N c}) (E.key (st.prD c n)) (E.key (st.suD c n)) ∧
      sideInArc (E.key (st.prD c n)) (E.key (st.suD c n)) (E.key n) := by
  obtain ⟨hnA, hnL, -⟩ := h.key_nd_cut hE hc hn
  have hDn : st.dd c n = true := (h.dd_iff hE hc hn).2 h1
  set m := if n = st.nd0 c then st.nd1 c else st.nd0 c with hm
  have hD : ∀ j, st.dd c j = true → j = n ∨ j = m := by
    intro j hj
    obtain ⟨hj', -⟩ := h.dd_cases hE hc hj
    rcases hn with rfl | rfl <;> rcases hj' with rfl | rfl
    · exact Or.inl rfl
    · right; rw [hm, ite_eq_left rfl]
    · right; rw [hm, ite_eq_right (h.nd_ne hE hc).symm]
    · exact Or.inl rfl
  -- two cuts remain
  have hS'adm : st.F E \ {cs E.M E.Q E.N c} ⊆ E.M.Adm :=
    sdiff_subset.trans (St.F_adm (st := st) hE)
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := hE.hM.two_cuts hS'adm hne'
  obtain ⟨j₁, hj₁, hL₁, hd₁, rfl⟩ := (h.cut_sdiff_iff hE hc _).1 hk₁
  obtain ⟨j₂, hj₂, hL₂, hd₂, rfl⟩ := (h.cut_sdiff_iff hE hc _).1 hk₂
  have hex : ∃ i, i < E.A ∧ st.Lv i ∧ ¬ st.dd c i = true := ⟨j₁, hj₁, hL₁, by simp [hd₁]⟩
  have hp := pred_skip (Dd := fun j => st.dd c j = true) h.ring hnA hnL hDn hD hex
  have hs := succ_skip (Dd := fun j => st.dd c j = true) h.ring hnA hnL hDn hD hex
  have hpe : st.prD c n = (if st.dd c (st.prv n) = true then st.prv (st.prv n) else st.prv n) :=
    rfl
  have hse : st.suD c n = (if st.dd c (st.nxt n) = true then st.nxt (st.nxt n) else st.nxt n) :=
    rfl
  rw [← hpe] at hp
  rw [← hse] at hs
  have hps : st.prD c n ≠ st.suD c n := by
    intro e
    rw [← e] at hs
    have e1 := only_of_pred_eq_succ hnA (fun h' => h'.2 hDn) hp hs hj₁ ⟨hL₁, by simp [hd₁]⟩
    have e2 := only_of_pred_eq_succ hnA (fun h' => h'.2 hDn) hp hs hj₂ ⟨hL₂, by simp [hd₂]⟩
    exact hk (by rw [e1, e2])
  obtain ⟨hin, hfree⟩ := gap_of_pred_succ hnA (fun h' => h'.2 hDn) hp hs hps
  have hpA := hp.1
  have hsA := hs.1
  refine ⟨hpA, hsA, ⟨(h.cut_sdiff_iff hE hc _).2 ⟨_, hpA, hp.2.1.1, by simpa using hp.2.1.2, rfl⟩,
    (h.cut_sdiff_iff hE hc _).2 ⟨_, hsA, hs.2.1.1, by simpa using hs.2.1.2, rfl⟩,
    fun e => hps (key_inj hE hpA hsA e), fun k hk' hcut => ?_⟩,
    (key_cyc_iff hE hpA hsA hnA).2 hin⟩
  obtain ⟨j, hj, hjL, hjd, rfl⟩ := (h.cut_sdiff_iff hE hc _).1 hcut
  exact hfree j hj ⟨hjL, by simp [hjd]⟩ ((key_cyc_iff hE hpA hsA hj).1 hk')

/-- **The merged weight** computed by the state is the weight of the merged region. -/
theorem Inv.mu_eq {P : Set Point}
    (hs : Merge.IsSplit E.M.D (st.F E \ {cs E.M E.Q E.N c}) (cs E.M E.Q E.N c) P
      (st.cl E (st.s0 c)) (st.cl E (st.s1 c))) :
    st.mu E c = E.M.weight (st.F E \ {cs E.M E.Q E.N c}) P := by
  have hSadm := St.F_adm (st := st) hE
  have hSfin := St.F_finite (st := st) hE
  have hcS := St.cs_mem_F hc
  unfold St.mu
  by_cases h1 : st.nlive = 1
  · rw [ite_eq_left h1]
    -- the only live chord is `c`
    have hL1 : st.L E = {c} := by
      have hfin : (st.L E).Finite := (Set.finite_lt_nat E.K).subset fun i hi => hi.1
      rw [h.nlive] at h1
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
      rw [ha] at hc ⊢
      rw [mem_singleton_iff.1 hc]
    have he : st.F E \ {cs E.M E.Q E.N c} = ∅ := by
      rw [← fam_diff hE hc, hL1, sdiff_self]
      ext d; simp [fam]
    rw [weight_merged_empty hE.hM hs he, size_eq hE]
  · rw [ite_eq_right h1]
    have hne' : (st.F E \ {cs E.M E.Q E.N c}).Nonempty := by
      have hfin : (st.L E).Finite := (Set.finite_lt_nat E.K).subset fun i hi => hi.1
      have h2 : 1 < (st.L E).ncard := by
        have := Set.ncard_pos hfin |>.2 ⟨c, hc⟩
        rw [h.nlive] at h1
        omega
      obtain ⟨a, ha, hac⟩ := Set.exists_ne_of_one_lt_ncard h2 c
      rw [← fam_diff hE hc]
      exact ⟨cs E.M E.Q E.N a, a, ⟨ha, by rw [mem_singleton_iff]; exact hac⟩, ha.1, rfl⟩
    have wX : st.wt (st.s0 c) = E.M.weight (st.F E) (st.cl E (st.s0 c)) :=
      (h.cls _ ⟨c, hc, Or.inl rfl⟩).2.1
    have wY : st.wt (st.s1 c) = E.M.weight (st.F E) (st.cl E (st.s1 c)) :=
      (h.cls _ ⟨c, hc, Or.inr rfl⟩).2.1
    -- each joined gap
    have hjw : ∀ n, (n = st.nd0 c ∨ n = st.nd1 c) →
        st.jw E c n ≤ E.M.weight (st.F E \ {cs E.M E.Q E.N c}) P := by
      intro n hn
      unfold St.jw
      split_ifs with hcnt
      · obtain ⟨hpA, hsA, hgap, hin⟩ := h.dead_gap hE hc hne' hn hcnt
        rw [gw_eq hE h.stat hpA hsA]
        exact gap_le_merged hE.hM hSadm hSfin hcS hs ((h.lost_iff hE hc).2 ⟨n, hn, hcnt, rfl⟩)
          hgap hin
      · exact Nat.zero_le _
    refine le_antisymm ?_ ?_
    · refine max_le (max_le ?_ ?_) (max_le (hjw _ (Or.inl rfl)) (hjw _ (Or.inr rfl)))
      · rw [wX]; exact weight_le_merged₁ hE.hM hSadm hSfin hcS hs
      · rw [wY]; exact weight_le_merged₂ hE.hM hSadm hSfin hcS hs
    · refine weight_merged_le hE.hM hSadm hSfin hcS hs hne'
        (by rw [← wX]; exact le_max_of_le_left (le_max_left _ _))
        (by rw [← wY]; exact le_max_of_le_left (le_max_right _ _)) ?_
      rintro l r hg ⟨k, hk, hkin⟩
      obtain ⟨n, hn, hcnt, rfl⟩ := (h.lost_iff hE hc).1 hk
      obtain ⟨hpA, hsA, hgap, hin⟩ := h.dead_gap hE hc hne' hn hcnt
      obtain ⟨rfl, rfl⟩ := gap_unique hg hgap hkin hin
      have : E.M.arcWt (E.key (st.prD c n)) (E.key (st.suD c n)) = st.jw E c n := by
        unfold St.jw; rw [ite_eq_left hcnt, gw_eq hE h.stat hpA hsA]
      rw [this]
      rcases hn with rfl | rfl
      · exact le_max_of_le_right (le_max_left _ _)
      · exact le_max_of_le_right (le_max_right _ _)


end

end

end Gran

end Chazelle.Core
