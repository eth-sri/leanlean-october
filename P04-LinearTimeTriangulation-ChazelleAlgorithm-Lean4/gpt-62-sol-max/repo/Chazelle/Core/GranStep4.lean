module

public import Chazelle.Core.GranStep3

/-!
# WP-F, part 10: the removal preserves the invariant (counts, ring, worklist) — `Inv.remove`
-/

namespace Chazelle.Core

namespace Gran

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt ChordSystem freeIn regionsIn TouchesIn)

variable {E : Env} {st : St}

section Rm4

variable (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E)
include hE h hc

/-- **The counts after the removal.** -/
theorem cnt_rm (μ : ℕ) {j : ℕ} (hj : j < E.A) :
    (st.remove c μ).cnt j = (st.remove c μ).cntOf E j := by
  have hne := h.nd_ne hE hc
  have hcK := hc.1
  have k0 : ((Finset.range E.K).filter fun i => (st.remove c μ).live i = 1 ∧
      (st.remove c μ).nd0 i = j) =
      ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd0 i = j).erase c := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    show (_ ∧ Function.update st.live c 0 i = 1 ∧ st.nd0 i = j) ↔ _
    by_cases hic : i = c
    · subst hic; simp
    · rw [Function.update_of_ne hic]; tauto
  have k1 : ((Finset.range E.K).filter fun i => (st.remove c μ).live i = 1 ∧
      (st.remove c μ).nd1 i = j) =
      ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd1 i = j).erase c := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    show (_ ∧ Function.update st.live c 0 i = 1 ∧ st.nd1 i = j) ↔ _
    by_cases hic : i = c
    · subst hic; simp
    · rw [Function.update_of_ne hic]; tauto
  unfold St.cntOf
  rw [k0, k1]
  show Function.update (Function.update st.cnt (st.nd0 c) (st.cnt (st.nd0 c) - 1)) (st.nd1 c)
      (st.cnt (st.nd1 c) - 1) j = _
  have e := h.cnt j hj
  unfold St.cntOf at e
  have m0 : c ∈ ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd0 i = j) ↔
      st.nd0 c = j := by simp [hcK, hc.2]
  have m1 : c ∈ ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd1 i = j) ↔
      st.nd1 c = j := by simp [hcK, hc.2]
  by_cases h1 : j = st.nd1 c
  · subst h1
    rw [Function.update_self, Finset.card_erase_of_mem (m1.2 rfl),
      Finset.erase_eq_of_notMem (fun hm => hne (m0.1 hm)), h.cnt _ hj]
    unfold St.cntOf
    have := Finset.card_pos.2 ⟨c, m1.2 rfl⟩
    omega
  · rw [Function.update_of_ne h1]
    by_cases h0 : j = st.nd0 c
    · subst h0
      rw [Function.update_self, Finset.card_erase_of_mem (m0.2 rfl),
        Finset.erase_eq_of_notMem (fun hm => h1 (m1.1 hm).symm), h.cnt _ hj]
      unfold St.cntOf
      have := Finset.card_pos.2 ⟨c, m0.2 rfl⟩
      omega
    · rw [Function.update_of_ne h0, Finset.erase_eq_of_notMem (fun hm => h0 (m0.1 hm).symm),
        Finset.erase_eq_of_notMem (fun hm => h1 (m1.1 hm).symm), e]

/-- The live positions after the removal. -/
theorem lv_rm (μ : ℕ) {j : ℕ} (hj : j < E.A) :
    (st.remove c μ).Lv j ↔ st.Lv j ∧ st.dd c j = false := by
  have hne := h.nd_ne hE hc
  unfold St.Lv
  show 0 < Function.update (Function.update st.cnt (st.nd0 c) (st.cnt (st.nd0 c) - 1))
      (st.nd1 c) (st.cnt (st.nd1 c) - 1) j ↔ _
  by_cases h1 : j = st.nd1 c
  · subst h1
    rw [Function.update_self]
    have hL := (h.key_nd_cut hE hc (Or.inr rfl)).2.1
    have hd := h.dd_iff hE hc (Or.inr rfl)
    unfold St.Lv at hL
    constructor
    · intro hp
      refine ⟨hL, ?_⟩
      by_contra hdd
      simp only [Bool.not_eq_false] at hdd
      rw [hd.1 hdd] at hp; omega
    · rintro ⟨-, hdd⟩
      have : st.cnt (st.nd1 c) ≠ 1 := fun e => by rw [hd.2 e] at hdd; exact Bool.noConfusion hdd
      omega
  · rw [Function.update_of_ne h1]
    by_cases h0 : j = st.nd0 c
    · subst h0
      rw [Function.update_self]
      have hL := (h.key_nd_cut hE hc (Or.inl rfl)).2.1
      have hd := h.dd_iff hE hc (Or.inl rfl)
      unfold St.Lv at hL
      constructor
      · intro hp
        refine ⟨hL, ?_⟩
        by_contra hdd
        simp only [Bool.not_eq_false] at hdd
        rw [hd.1 hdd] at hp; omega
      · rintro ⟨-, hdd⟩
        have : st.cnt (st.nd0 c) ≠ 1 := fun e => by rw [hd.2 e] at hdd; exact Bool.noConfusion hdd
        omega
    · rw [Function.update_of_ne h0]
      constructor
      · intro hp
        refine ⟨hp, ?_⟩
        by_contra hdd
        simp only [Bool.not_eq_false] at hdd
        obtain ⟨hj', -⟩ := h.dd_cases hE hc hdd
        rcases hj' with e | e
        · exact h0 e
        · exact h1 e
      · exact fun h' => h'.1

/-- **The ring after the removal.** -/
theorem ring_rm (μ : ℕ) :
    RingOK (st.remove c μ).Lv E.A (st.remove c μ).nxt (st.remove c μ).prv := by
  have hne := h.nd_ne hE hc
  have hl := fun {j : ℕ} (hj : j < E.A) => lv_rm hE h hc μ hj
  by_cases hemp : ∀ j, j < E.A → ¬ (st.remove c μ).Lv j
  · exact ringOK_empty hemp _ _
  push Not at hemp
  obtain ⟨j₀, hj₀, hL₀⟩ := hemp
  -- two distinct surviving positions
  obtain ⟨hL₀', hd₀⟩ := (hl hj₀).1 hL₀
  have hcut₀ := (h.cut_sdiff_iff hE hc _).2 ⟨j₀, hj₀, hL₀', hd₀, rfl⟩
  have hne' : (st.F E \ {cs E.M E.Q E.N c}).Nonempty := by
    obtain ⟨d, hd, -⟩ := hcut₀
    exact ⟨d, hd⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := hE.hM.two_cuts
    (sdiff_subset.trans (St.F_adm (st := st) hE)) hne'
  obtain ⟨a, ha, haL, had, rfl⟩ := (h.cut_sdiff_iff hE hc _).1 hk₁
  obtain ⟨b, hb, hbL, hbd, rfl⟩ := (h.cut_sdiff_iff hE hc _).1 hk₂
  have hab : a ≠ b := fun e => hk (by rw [e])
  have hn1 := h.key_nd_cut hE hc (Or.inl rfl)
  have hn2 := h.key_nd_cut hE hc (Or.inr rfl)
  -- positions that die are not `a`, `b`
  have hdead : ∀ n, st.dd c n = true → a ≠ n ∧ b ≠ n := fun n hn =>
    ⟨fun e => by rw [e, hn] at had; exact Bool.noConfusion had,
      fun e => by rw [e, hn] at hbd; exact Bool.noConfusion hbd⟩
  -- the first unlink
  set Lv1 : ℕ → Prop := fun j => st.Lv j ∧ (st.cnt (st.nd0 c) = 1 → j ≠ st.nd0 c)
  set r1 := if st.cnt (st.nd0 c) = 1 then St.unl (st.nxt, st.prv) (st.nd0 c)
    else (st.nxt, st.prv)
  have hR1 : RingOK Lv1 E.A r1.1 r1.2 := by
    by_cases d1 : st.cnt (st.nd0 c) = 1
    · have hd1 : st.dd c (st.nd0 c) = true := (h.dd_iff hE hc (Or.inl rfl)).2 d1
      have e1 : r1 = St.unl (st.nxt, st.prv) (st.nd0 c) := ite_eq_left d1
      rw [e1]
      refine (ringOK_unl (r := (st.nxt, st.prv)) h.ring hn1.1 hn1.2.1
        ⟨a, b, ha, hb, haL, hbL, (hdead _ hd1).1, (hdead _ hd1).2, hab⟩).congr
        (fun j _ => ?_) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      simp only [Lv1]
      exact ⟨fun h' => ⟨h'.1, h'.2 d1⟩, fun h' => ⟨h'.1, fun _ => h'.2⟩⟩
    · have e1 : r1 = (st.nxt, st.prv) := ite_eq_right d1
      rw [e1]
      exact h.ring.congr (fun j _ => by simp only [Lv1]; exact ⟨fun h' => h'.1,
        fun h' => ⟨h', fun e => absurd e d1⟩⟩) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  -- the second unlink
  have hring2 : (st.ring2 c) = if st.cnt (st.nd1 c) = 1 then St.unl r1 (st.nd1 c) else r1 := rfl
  have hLv1a : Lv1 a := ⟨haL, fun d1 e => (hdead _ ((h.dd_iff hE hc (Or.inl rfl)).2 d1)).1 e⟩
  have hLv1b : Lv1 b := ⟨hbL, fun d1 e => (hdead _ ((h.dd_iff hE hc (Or.inl rfl)).2 d1)).2 e⟩
  have hfin : RingOK (fun j => Lv1 j ∧ (st.cnt (st.nd1 c) = 1 → j ≠ st.nd1 c)) E.A
      (st.ring2 c).1 (st.ring2 c).2 := by
    rw [hring2]
    by_cases d2 : st.cnt (st.nd1 c) = 1
    · have hd2 : st.dd c (st.nd1 c) = true := (h.dd_iff hE hc (Or.inr rfl)).2 d2
      rw [ite_eq_left d2]
      have hn2L : Lv1 (st.nd1 c) := ⟨hn2.2.1, fun _ e => hne e.symm⟩
      refine (ringOK_unl hR1 hn2.1 hn2L
        ⟨a, b, ha, hb, hLv1a, hLv1b, (hdead _ hd2).1, (hdead _ hd2).2, hab⟩).congr
        (fun j _ => ?_) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      exact ⟨fun h' => ⟨h'.1, h'.2 d2⟩, fun h' => ⟨h'.1, fun _ => h'.2⟩⟩
    · rw [ite_eq_right d2]
      exact hR1.congr (fun j _ => ⟨fun h' => h'.1, fun h' => ⟨h', fun e => absurd e d2⟩⟩)
        (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  refine hfin.congr (fun j hj => ?_) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  rw [hl hj]
  simp only [Lv1]
  constructor
  · rintro ⟨hL, hdd⟩
    refine ⟨⟨hL, fun d1 e => ?_⟩, fun d2 e => ?_⟩
    · rw [e, (h.dd_iff hE hc (Or.inl rfl)).2 d1] at hdd; exact Bool.noConfusion hdd
    · rw [e, (h.dd_iff hE hc (Or.inr rfl)).2 d2] at hdd; exact Bool.noConfusion hdd
  · rintro ⟨⟨hL, h1⟩, h2⟩
    refine ⟨hL, ?_⟩
    by_contra hdd
    simp only [Bool.not_eq_false] at hdd
    obtain ⟨hj', hcnt⟩ := h.dd_cases hE hc hdd
    rcases hj' with e | e
    · exact h1 (e ▸ hcnt) e
    · exact h2 (e ▸ hcnt) e

end Rm4

/-- **The removal preserves the invariant.** -/
theorem Inv.remove (hE : E.Good) (h : Inv E st) (htop : 0 < st.top)
    (hc : st.cur ∈ st.L E)
    (hrem : Merge.Removable E.M.D E.M.weight E.γ (st.F E) (cs E.M E.Q E.N st.cur)) :
    Inv E (st.remove st.cur (st.mu E st.cur)) := by
  set c := st.cur with hcdef
  obtain ⟨P, hs⟩ := h.split hE hc
  obtain ⟨hlow, hw⟩ := (h.removable_iff hE hc hs).1 hrem
  have hmu : st.mu E c ≤ E.γ := by rw [h.mu_eq hE hc hs]; exact hw
  set μ := st.mu E c
  set st' := st.remove c μ
  have hL' : st'.L E = st.L E \ {c} := rm_L hE h hc μ
  have hF' : st'.F E = st.F E \ {cs E.M E.Q E.N c} := rm_F hE h hc μ
  have hfinL : (st.L E).Finite := (Set.finite_lt_nat E.K).subset fun i hi => hi.1
  have hnl : 1 ≤ st.nlive := by
    rw [h.nlive]; exact (Set.ncard_pos hfinL).2 ⟨c, hc⟩
  have hlen := newEx_le hE h hc hs hlow
  refine ⟨h.stat.congr rfl rfl rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- live bits
    intro i hi
    show Function.update st.live c 0 i ≤ 1
    by_cases hic : i = c
    · subst hic; simp
    · rw [Function.update_of_ne hic]; exact h.live01 i hi
  · -- the number of live chords
    show st.nlive - 1 = (st'.L E).ncard
    rw [hL', ncard_sdiff_singleton_of_mem hc, h.nlive]
  · -- degrees
    rw [hF']
    intro Z hZ
    by_cases hZP : Z = P
    · subst hZP; rw [deg_P hE h hc hs]; exact hlen
    · rw [deg_other hE h hc hs hZ hZP]
      exact h.degLe Z (other_ne hE h hc hs hZ hZP).1
  · -- weights
    rw [hF']
    intro Z hZ
    by_cases hZP : Z = P
    · subst hZP; rw [← h.mu_eq hE hc hs]; exact hmu
    · rw [weight_other' hE h hc hs hZ hZP]
      exact h.semi Z (other_ne hE h hc hs hZ hZP).1
  · -- sides
    intro i hi
    rw [hL'] at hi
    exact sides_rm hE h hc hs hi.1 (fun e => hi.2 (by rw [e]; rfl)) μ
  · -- classes
    intro x hx
    exact cls_rm hE h hc hs hlow hx
  · -- distinct classes
    intro x y hx hy he
    exact refInj_rm hE h hc hs μ hx hy he
  · -- counts
    intro j hj
    exact cnt_rm hE h hc μ hj
  · -- ring
    exact ring_rm hE h hc μ
  · -- worklist entries
    intro t ht
    show (if st.top - 1 ≤ t ∧ t < st.top - 1 + (st.newEx c).length then
      (st.newEx c).getD (t - (st.top - 1)) 0 else st.stk t) < E.K
    change t < st.top - 1 + (st.newEx c).length at ht
    split_ifs with h1
    · have hk : t - (st.top - 1) < (st.newEx c).length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      exact ((mem_newEx hE h hc hs _).1 (List.getElem_mem hk)).1.1
    · exact h.stk t (by omega)
  · -- the worklist bound
    show st.top - 1 + (st.newEx c).length + E.D * (st.nlive - 1) ≤ E.K + E.D * E.K
    have := h.topLe
    have e : E.D * st.nlive = E.D * (st.nlive - 1) + E.D := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega
  · -- the worklist property
    intro i hi hno
    rw [hL'] at hi
    have hic : i ≠ c := fun e => hi.2 (by rw [e]; rfl)
    have hiL := hi.1
    -- `i` is not a new exit
    have hnotnew : i ∉ st.newEx c := by
      intro hm
      obtain ⟨k, hk, hki⟩ := List.getElem_of_mem hm
      refine hno (st.top - 1 + k) (by show _ < st.top - 1 + (st.newEx c).length; omega) ?_
      show (if st.top - 1 ≤ st.top - 1 + k ∧ st.top - 1 + k < st.top - 1 + (st.newEx c).length
        then (st.newEx c).getD (st.top - 1 + k - (st.top - 1)) 0 else st.stk _) = i
      rw [ite_eq_left ⟨by omega, by omega⟩, show st.top - 1 + k - (st.top - 1) = k by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      exact hki
    -- `i` was not on the old worklist
    have hold : ∀ t, t < st.top → st.stk t ≠ i := by
      intro t ht
      by_cases htt : t = st.top - 1
      · subst htt; exact fun e => hic e.symm
      · have := hno t (by show _ < st.top - 1 + (st.newEx c).length; omega)
        show st.stk t ≠ i
        intro e
        apply this
        show (if st.top - 1 ≤ t ∧ t < st.top - 1 + (st.newEx c).length then _ else st.stk t) = i
        rw [ite_eq_right (by omega)]; exact e
    have hnr := h.work i hiL hold
    rw [hF']
    intro hr
    apply hnr
    have hsys := hsys_F hE h hc hs
    refine Merge.removable_of_removable_sdiff hsys
      (weightLocal hE.hM (St.F_adm (st := st) hE) (St.F_finite (st := st) hE)) subset_rfl
      (St.cs_mem_F hc) (fun e => hic (cs_inj hE.hNF hiL.1 hc.1 e)) (fun Z hZ hcZ hiZ => ?_) hr
    have hZ12 := (split_touches_iff hE.hM (St.F_adm (st := st) hE) (St.F_finite (st := st) hE)
      (St.cs_mem_F hc) hs hZ).1 hcZ
    apply hnotnew
    rw [mem_newEx hE h hc hs]
    refine ⟨hiL, hic, (touch_P hE h hc hs hiL hic).2 ?_⟩
    rcases hZ12 with rfl | rfl
    · exact Or.inl hiZ
    · exact Or.inr hiZ

end

end Gran

end Chazelle.Core
