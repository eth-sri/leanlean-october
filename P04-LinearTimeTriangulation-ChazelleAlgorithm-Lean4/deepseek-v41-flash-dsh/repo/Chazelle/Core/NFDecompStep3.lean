module

public import Chazelle.Golf

public import Chazelle.Core.NFDecompStep2

/-!
# Tree decomposition (WP-C), part 7: `rinv_next`

The round invariant `RInv` is preserved by one round `next` (with the ghosts `gcNext`,
`crNext`), given the characterisation of the top pass and the degree bound `D`.
-/

namespace Chazelle.Core.Dec

@[expose] public section

open Relation Finset

set_option linter.unusedSectionVars false

section step3

variable {R K D : ℕ} {up dn ord pos prg pch isdn chOf : ℕ → ℕ}
variable (h : Rooted R K up dn ord pos prg pch)
variable (hch : ∀ e, e < K → chOf e < R ∧ chOf e ≠ 0 ∧ pch (chOf e) = e)
variable {σ : RS} {top best bestv : ℕ → ℕ}
variable (hT : ∀ u, u < R → top u < R ∧ IsTop pch σ.rem (top u) ∧ AncX R prg pch σ.rem (top u) u)
variable (hB : ∀ t, t < R → IsTop pch σ.rem t →
      (∀ c, c < R → AncX R prg pch σ.rem t c → c ≠ t → cval R prg pch σ.rem t c ≤ bestv t) ∧
      ((best t = t ∧ ∀ c, c < R → AncX R prg pch σ.rem t c → c = t) ∨
        (best t < R ∧ AncX R prg pch σ.rem t (best t) ∧ best t ≠ t ∧
          bestv t = cval R prg pch σ.rem t (best t))))
variable {j : ℕ} {gc : ℕ → Finset ℕ} {cr : ℕ → ℕ}
variable (hI : RInv R K D prg pch isdn chOf j σ gc cr)

include h hch hT hB hI

local notation "σ'" => next R K prg pch isdn chOf top best σ
local notation "gc'" => gcNext R K prg pch chOf top best σ gc
local notation "cr'" => crNext K chOf top best σ j cr

/-- At round `0` the root component is everything. -/
theorem sub_root0 (hj : j = 0) : sub R prg pch σ.rem 0 = range R := by
  ext v
  Ξ mem_sub, Finset.mem_range
  exact ⟨fun hh => hh.1, fun hv => ⟨hv, anc_root_of h hv (hI.i7 hj).1⟩⟩

/-- A component with a proper member has at least two regions. -/
theorem two_le_sz {t c : ℕ} (hc : c < R) (htc : AncX R prg pch σ.rem t c) (hne : c ≠ t) :
    2 ≤ sz R prg pch σ.rem t := by
  have := sz_lt h htc (Ne.symm hne) hc
  have := sz_pos h (rem := σ.rem) hc
  omega

theorem next_i1 : ∀ e, e < K → (σ').rem e = 1 →
    gc' e ⊆ range R ∧ chOf e ∈ gc' e ∧ prg (chOf e) ∈ gc' e ∧ cr' e < j + 1 ∧
      cr' e < rounds D K ∧
      (((σ').dpar e = 2 * e ∧ cr' e = 0 ∧ (σ').root = 2 * e ∧ gc' e = range R) ∨
        (∃ p, p < K ∧ (σ').rem p = 1 ∧ (σ').dpar e = 2 * p ∧ cr' p + 1 = cr' e ∧
          gc' e ⊆ gc' p)) := by
  intro e he hr'
  rcases (rem_next h hch hT hB hI he).1 hr' with hr | hc
  · -- an old chord
    have hnc : ¬ Chosen σ top best chOf e := fun hh => hh.1 hr
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hI.i1 e he hr
    rw [gc_old h hch hT hB hI hr, cr_old h hch hT hB hI hr]
    have hdpar : (σ').dpar e = σ.dpar e := by
      simp only [next, ite_eq_left he, ite_eq_right hnc]
      by_cases hp : σ.pend e = 1
      · rw [ite_eq_left hp]
      · rw [ite_eq_right hp]
    refine ⟨g1, g2, g3, by omega, g5, ?_⟩
    rw [hdpar, root_next_pos h hch hT hB hI (by omega)]
    rcases g6 with ⟨a1, a2, a3, a4⟩ | ⟨p, hp, hrp, a1, a2, a3⟩
    · exact Or.inl ⟨a1, a2, a3, a4⟩
    · refine Or.inr ⟨p, hp, rem_mono h hch hT hB hI hrp, a1, ?_, ?_⟩
      · rw [cr_old h hch hT hB hI hrp]; exact a2
      · rw [gc_old h hch hT hB hI hrp]; exact a3
  · -- a chord cut now
    obtain ⟨t1, t2, t3, t4, t5, t6, t7, c1, c2, c3, c4⟩ := chosen_facts h hch hT hB hI he hc
    rw [gc_new h hch hT hB hI he hc, cr_new h hch hT hB hI he hc]
    have h2 := two_le_sz h hch hT hB hI c1 t7 t5
    have h6 := (hI.i6 _ t1 t2 t3).1
    have hj : j < rounds D K := lt_rounds (by omega)
    have hprg : AncX R prg pch σ.rem (top (chOf e)) (prg (chOf e)) := by
      rcases (AncX.back_iff h).1 t7 with e' | ⟨-, -, -, hh⟩
      · exact absurd e'.symm t5
      · exact hh
    refine ⟨fun v hv => by rw [mem_sub] at hv; exact Finset.mem_range.2 hv.1,
      (mem_sub).2 ⟨c1, t7⟩, (mem_sub).2 ⟨h.prg_lt _ c1 c2, hprg⟩, by omega, hj, ?_⟩
    have hdpar : (σ').dpar e = (if σ.side (top (chOf e)) = 2 then 2 * e
        else 2 * σ.cpar (top (chOf e))) := by
      simp only [next, ite_eq_left he, ite_eq_right c4, ite_eq_left hc]
    rcases hI.i4 _ t1 t2 t3 with ⟨s2, s0, sj⟩ | ⟨s1, s2, s3, s4⟩
    · left
      rw [hdpar, ite_eq_left s2]
      refine ⟨rfl, sj, ?_, by rw [s0]; exact sub_root0 h hch hT hB hI sj⟩
      have ⟨a0, s0'⟩ := (hI.i7 sj).2
      simp only [next, ite_eq_left a0, ite_eq_left s0', code]
      rw [← s0, t4, ite_eq_right t5, c3]
    · right
      have hs2 : σ.side (top (chOf e)) ≠ 2 := by omega
      set p := σ.cpar (top (chOf e)) with hpdef
      have hrp := hI.i0 p s2 s3
      refine ⟨p, s2, rem_mono h hch hT hB hI hrp, by rw [hdpar, ite_eq_right hs2], ?_, ?_⟩
      · rw [cr_old h hch hT hB hI hrp]; exact (hI.i3 p s2 s3).1
      · rw [gc_old h hch hT hB hI hrp, s4]; exact Finset.inter_subset_left

theorem next_i2 : ∀ e, e < K → (σ').rem e = 1 → (σ').pend e ≠ 1 → ∀ s, s ≤ 1 →
    ValidC R K pch (σ') (if s = 0 then (σ').dlo e else (σ').dhi e) ∧
    compOf gc' (if s = 0 then (σ').dlo e else (σ').dhi e) =
      gc' e ∩ sideSet R prg pch isdn chOf s e ∧
    pcode (σ') (if s = 0 then (σ').dlo e else (σ').dhi e) = 2 * e := by
  intro e he hr' hp' s hs
  have hnc : ¬ Chosen σ top best chOf e := fun hh =>
    hp' ((pend_next h hch hT hB hI he).2 hh)
  have hr : σ.rem e = 1 := ((rem_next h hch hT hB hI he).1 hr').resolve_right hnc
  rw [gc_old h hch hT hB hI hr]
  by_cases hp : σ.pend e = 1
  · -- the chord was cut in the previous round: its slots are filled now
    obtain ⟨t, ht, htop, hact, hcpar, hside, hsub⟩ := (hI.i3 e he hp).2 s hs
    have hx : (if s = 0 then (σ').dlo e else (σ').dhi e) = code best pch t := by
      have hpc := pend_child h hch hT hB hI he hp ht htop hsub
      by_cases hs0 : s = 0
      · subst hs0
        simp only [next, ite_eq_left he, ite_eq_left hp, ite_true]
        rw [loTop_eq h hch hT hB hI, hpc]
      · have hs1 : s = 1 := by omega
        subst hs1
        simp only [next, ite_eq_left he, ite_eq_left hp, one_ne_zero, ite_false]
        rw [hiTop_eq h hch hT hB hI, hpc]
    rw [hx]
    obtain ⟨v1, v2, v3⟩ := code_next h hch hT hB hI ht htop hact
    refine ⟨v1, by rw [v2, hsub], ?_⟩
    rw [v3, ite_eq_right (by omega), hcpar]
  · -- the slots were filled earlier
    have hx : (if s = 0 then (σ').dlo e else (σ').dhi e) =
        (if s = 0 then σ.dlo e else σ.dhi e) := by
      by_cases hs0 : s = 0
      · simp only [hs0, ite_true, next, ite_eq_left he, ite_eq_right hp]
      · simp only [hs0, ite_false, next, ite_eq_left he, ite_eq_right hp]
    rw [hx]
    obtain ⟨o1, o2, o3⟩ := hI.i2 e he hr hp s hs
    obtain ⟨v1, v2, v3⟩ := valid_next h hch hT hB hI o1
    exact ⟨v1, v2.trans o2, v3.trans o3⟩

theorem next_i3 : ∀ e, e < K → (σ').pend e = 1 → cr' e + 1 = j + 1 ∧ ∀ s, s ≤ 1 → ∃ t, t < R ∧
    IsTop pch (σ').rem t ∧ (σ').act t = 1 ∧ (σ').cpar t = e ∧ (σ').side t = s ∧
    sub R prg pch (σ').rem t = gc' e ∩ sideSet R prg pch isdn chOf s e := by
  intro e he hp'
  have hc : Chosen σ top best chOf e := (pend_next h hch hT hB hI he).1 hp'
  refine ⟨by rw [cr_new h hch hT hB hI he hc], fun s hs => ?_⟩
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, c1, c2, c3, c4⟩ := chosen_facts h hch hT hB hI he hc
  obtain ⟨sc, sp⟩ := sub_new_sides h hch hT hB hI (s := s) he hc
  obtain ⟨n1, n2, n3⟩ := new_top_facts h hch hT hB hI he hc
  by_cases hcond : (isdn (chOf e) = 1 ↔ s = 0)
  · refine ⟨chOf e, c1, (istop_next h hch hT hB hI c1).2 (Or.inr ⟨c2, by rw [c3]; exact hc⟩),
      n1, n2, ?_, sc hcond⟩
    rw [n3]
    by_cases hd : isdn (chOf e) = 1
    · rw [ite_eq_left hd]; exact (hcond.1 hd).symm
    · rw [ite_eq_right hd]
      have : s ≠ 0 := fun h0 => hd (hcond.2 h0)
      omega
  · have hbt : best (top (chOf e)) ≠ top (chOf e) := by rw [t4]; exact t5
    refine ⟨top (chOf e), t1, (istop_next h hch hT hB hI t1).2 (Or.inl t2), ?_, ?_, ?_, sp hcond⟩
    · rw [act_top h hch hT hB hI t1 t2, ite_eq_left t3, ite_eq_right hbt]; exact t3
    · rw [cpar_top h hch hT hB hI t1 t2, ite_eq_left t3, ite_eq_right hbt, t4, c3]
    · rw [side_top h hch hT hB hI t1 t2, ite_eq_left t3, ite_eq_right hbt, t4]
      by_cases hd : isdn (chOf e) = 1
      · rw [ite_eq_left hd]
        have : s ≠ 0 := fun h0 => hcond ⟨fun _ => h0, fun _ => hd⟩
        omega
      · rw [ite_eq_right hd]
        by_contra hs0
        exact hcond ⟨fun hh => absurd hh hd, fun hh => absurd hh (Ne.symm hs0)⟩

theorem next_i4 : ∀ t, t < R → IsTop pch (σ').rem t → (σ').act t = 1 →
    ((σ').side t = 2 ∧ t = 0 ∧ j + 1 = 0) ∨
    ((σ').side t ≤ 1 ∧ (σ').cpar t < K ∧ (σ').pend ((σ').cpar t) = 1 ∧
      sub R prg pch (σ').rem t = gc' ((σ').cpar t) ∩
        sideSet R prg pch isdn chOf ((σ').side t) ((σ').cpar t)) := by
  intro t ht htop' hact'
  right
  by_cases htop : IsTop pch σ.rem t
  · -- an old top: it must be a cut component
    Ξ' act_top h hch hT hB hI ht htop at hact'
    have hact : σ.act t = 1 := by
      by_contra hh; Ξ' ite_eq_right hh at hact'; exact hh hact'
    Ξ' ite_eq_left hact at hact'
    have hbt : best t ≠ t := by
      intro hh; Ξ' ite_eq_left hh at hact'; exact absurd hact' (⊛)
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := cut_chosen h hch hT hB hI ht htop hact hbt
    have hcp : (σ').cpar t = pch (best t) := by
      Ξ cpar_top h hch hT hB hI ht htop, ite_eq_left hact, ite_eq_right hbt
    have hsd : (σ').side t = (if isdn (best t) = 1 then 1 else 0) := by
      Ξ side_top h hch hT hB hI ht htop, ite_eq_left hact, ite_eq_right hbt
    Ξ hcp, hsd
    refine ⟨by split_ifs <;> omega, b4, (pend_next h hch hT hB hI b4).2 b7, ?_⟩
    have := (sub_new_sides h hch hT hB hI (s := if isdn (best t) = 1 then 1 else 0) b4 b7).2
    Ξ' b5, b6 at this
    apply this
    by_cases hd : isdn (best t) = 1
    · rw [ite_eq_left hd]; exact fun hh => absurd (hh.1 hd) (⊛)
    · rw [ite_eq_right hd]; exact fun hh => hd (hh.2 rfl)
  · -- a new top
    obtain ⟨ht0, hc⟩ := ((istop_next h hch hT hB hI ht).1 htop').resolve_left htop
    have hpk := h.pch_lt t ht ht0
    have hco := chOf_pch h hch hT hB hI ht ht0
    obtain ⟨n1, n2, n3⟩ := new_top_facts h hch hT hB hI hpk hc
    Ξ' hco at n2 n3
    Ξ n2, n3
    refine ⟨by split_ifs <;> omega, hpk, (pend_next h hch hT hB hI hpk).2 hc, ?_⟩
    have := (sub_new_sides h hch hT hB hI (s := if isdn t = 1 then 0 else 1) hpk hc).1
    Ξ' hco at this
    apply this
    by_cases hd : isdn t = 1
    · rw [ite_eq_left hd]; exact ⟨fun _ => rfl, fun _ => hd⟩
    · rw [ite_eq_right hd]; exact ⟨fun hh => absurd hh hd, fun hh => absurd hh (⊛)⟩

theorem next_i5 : ∀ t, t < R → IsTop pch (σ').rem t → (σ').act t ≠ 1 →
    sub R prg pch (σ').rem t = {t} ∧
    (((σ').lpar t = 2 * t + 1 ∧ (σ').root = 2 * t + 1 ∧ K = 0) ∨
      (∃ p, p < K ∧ (σ').rem p = 1 ∧ (σ').lpar t = 2 * p ∧ cr' p + 1 ≤ rounds D K ∧
        t ∈ gc' p)) := by
  intro t ht htop' hact'
  by_cases htop : IsTop pch σ.rem t
  · rw [act_top h hch hT hB hI ht htop] at hact'
    by_cases hact : σ.act t = 1
    · -- a singleton finished now
      rw [ite_eq_left hact] at hact'
      have hbt : best t = t := by
        by_contra hh; rw [ite_eq_right hh] at hact'; exact hact' hact
      have hsing : sub R prg pch σ.rem t = {t} := by
        ext v
        rw [mem_sub, Finset.mem_singleton]
        constructor
        · rintro ⟨hv, htv⟩
          rcases (hB t ht htop).2 with ⟨-, b2⟩ | ⟨-, -, b3, -⟩
          · exact b2 v hv htv
          · exact absurd hbt b3
        · rintro rfl; exact ⟨ht, ReflTransGen.refl⟩
      refine ⟨by rw [sub_uncut h hch hT hB hI ht htop (fun _ => hbt), hsing], ?_⟩
      have hlp : (σ').lpar t = (if σ.side t = 2 then 2 * t + 1 else 2 * σ.cpar t) := by
        rw [lpar_top h hch hT hB hI ht htop, ite_eq_left hact, ite_eq_left hbt]
      rcases hI.i4 t ht htop hact with ⟨s2, s0, sj⟩ | ⟨s1, s2, s3, s4⟩
      · left
        subst s0
        have hR1 : R = 1 := by
          have := congrArg Finset.card (sub_root0 h hch hT hB hI sj)
          rw [hsing, Finset.card_singleton, Finset.card_range] at this
          omega
        refine ⟨by rw [hlp, ite_eq_left s2], ?_, by have := h.hR; omega⟩
        simp only [next, ite_eq_left hact, ite_eq_left s2, code, ite_eq_left hbt]
      · right
        have hrp := hI.i0 _ s2 s3
        refine ⟨σ.cpar t, s2, rem_mono h hch hT hB hI hrp, by rw [hlp, ite_eq_right (by omega)],
          ?_, ?_⟩
        · rw [cr_old h hch hT hB hI hrp, (hI.i3 _ s2 s3).1]
          obtain ⟨-, -, -, -, h5, -⟩ := hI.i1 _ s2 hrp
          have := (hI.i3 _ s2 s3).1
          omega
        · rw [gc_old h hch hT hB hI hrp]
          have : t ∈ sub R prg pch σ.rem t := (mem_sub).2 ⟨ht, ReflTransGen.refl⟩
          rw [s4] at this
          exact (Finset.mem_inter.1 this).1
    · -- an old finished leaf
      obtain ⟨l1, l2⟩ := hI.i5 t ht htop hact
      refine ⟨by rw [sub_uncut h hch hT hB hI ht htop (fun hh => absurd hh hact), l1], ?_⟩
      have hlp : (σ').lpar t = σ.lpar t := by
        rw [lpar_top h hch hT hB hI ht htop, ite_eq_right hact]
      rw [hlp]
      rcases l2 with ⟨a1, a2, a3⟩ | ⟨p, hp, hrp, a1, a2, a3⟩
      · left
        refine ⟨a1, ?_, a3⟩
        rcases Nat.eq_zero_or_pos j with hj | hj
        · -- at round `0` the only top is the active root
          have := (hI.i7 hj).2.1
          have hR := h.hR
          have ht0 : t = 0 := by omega
          rw [ht0] at hact; exact absurd this hact
        · rw [root_next_pos h hch hT hB hI hj]; exact a2
      · right
        refine ⟨p, hp, rem_mono h hch hT hB hI hrp, a1, ?_, ?_⟩
        · rw [cr_old h hch hT hB hI hrp]; exact a2
        · rw [gc_old h hch hT hB hI hrp]; exact a3
  · obtain ⟨ht0, hc⟩ := ((istop_next h hch hT hB hI ht).1 htop').resolve_left htop
    have hpk := h.pch_lt t ht ht0
    have hco := chOf_pch h hch hT hB hI ht ht0
    obtain ⟨n1, -, -⟩ := new_top_facts h hch hT hB hI hpk hc
    rw [hco] at n1
    exact absurd n1 hact'

theorem next_i6 (hdeg : ∀ v, v < R → (kids R prg pch rem0 v).card + (if v = 0 then 0 else 1) ≤ D) :
    ∀ t, t < R → IsTop pch (σ').rem t → (σ').act t = 1 →
    sz R prg pch (σ').rem t ≤ (hstep D)^[j + 1] K + 1 ∧ (j + 1 = 0 ∨ 1 ≤ (hstep D)^[j + 1 - 1] K) := by
  -- the bound for a cut component and its two parts
  have key : ∀ t, t < R → IsTop pch σ.rem t → σ.act t = 1 → best t ≠ t →
      sz R prg pch (σ').rem t ≤ (hstep D)^[j + 1] K + 1 ∧
      sz R prg pch (σ').rem (best t) ≤ (hstep D)^[j + 1] K + 1 ∧ 1 ≤ (hstep D)^[j] K := by
    intro t ht htop hact hbt
    obtain ⟨b1, b2, b3, -, -, -, -, -⟩ := cut_chosen h hch hT hB hI ht htop hact hbt
    obtain ⟨z1, z2⟩ := sz_cut h hch hT hB hI ht htop hact hbt
    have hn := two_le_sz h hch hT hB hI b1 b2 hbt
    have hlt := sz_lt h b2 (Ne.symm hbt) b1
    have h6 := (hI.i6 t ht htop hact).1
    have hD : 1 ≤ D := by
      have := hdeg _ b1
      Ξ' ite_eq_right b3 at this
      omega
    obtain ⟨c, hc, htc, hct, hgood⟩ := exists_good h hdeg ht htop hn
    have hmax := (hB t ht htop).1 c hc htc hct
    rcases (hB t ht htop).2 with ⟨e, -⟩ | ⟨-, -, -, hbv⟩
    · exact absurd e hbt
    Ξ' hbv at hmax
    have hm : sz R prg pch σ.rem (best t) + (sz R prg pch σ.rem t - sz R prg pch σ.rem (best t)) - 1 ≤
        D * min (sz R prg pch σ.rem (best t)) (sz R prg pch σ.rem t - sz R prg pch σ.rem (best t)) := by
      have : sz R prg pch σ.rem (best t) + (sz R prg pch σ.rem t - sz R prg pch σ.rem (best t)) =
          sz R prg pch σ.rem t := ⋄
      Ξ this
      exact hgood.trans (Nat.mul_le_mul_left _ hmax)
    have ha := sz_pos h (rem := σ.rem) b1
    obtain ⟨s1, s2⟩ := split_bound hD ha (⋄) hm
    have e1 : sz R prg pch σ.rem (best t) + (sz R prg pch σ.rem t - sz R prg pch σ.rem (best t)) - 1 =
        sz R prg pch σ.rem t - 1 := ⋄
    Ξ' e1 at s1 s2
    have m1 := le_hstep hD s1
    have m2 := le_hstep hD s2
    have m3 := hstep_mono D (show sz R prg pch σ.rem t - 1 ≤ (hstep D)^[j] K by omega)
    have m4 : hstep D (sz R prg pch σ.rem t - 1) ≤ (hstep D)^[j + 1] K := by
      rw [Function.iterate_succ_apply']; exact m3
    refine ⟨?_, ?_, ⋄⟩
    · omega
    · omega
  intro t ht htop' hact'
  by_cases htop : IsTop pch σ.rem t
  · Ξ' act_top h hch hT hB hI ht htop at hact'
    have hact : σ.act t = 1 := by
      by_contra hh; Ξ' ite_eq_right hh at hact'; exact hh hact'
    Ξ' ite_eq_left hact at hact'
    have hbt : best t ≠ t := by
      intro hh; Ξ' ite_eq_left hh at hact'; exact absurd hact' (⊛)
    obtain ⟨k1, -, k3⟩ := key t ht htop hact hbt
    exact ⟨k1, Or.inr (by simpa using k3)⟩
  · obtain ⟨ht0, hc⟩ := ((istop_next h hch hT hB hI ht).1 htop').resolve_left htop
    have hpk := h.pch_lt t ht ht0
    have hco := chOf_pch h hch hT hB hI ht ht0
    obtain ⟨t1, t2, t3, t4, t5, -, -, -, -, -, -⟩ := chosen_facts h hch hT hB hI hpk hc
    Ξ' hco at t1 t2 t3 t4 t5
    have hbt : best (top t) ≠ top t := by rw [t4]; exact t5
    obtain ⟨-, k2, k3⟩ := key (top t) t1 t2 t3 hbt
    Ξ' t4 at k2
    exact ⟨k2, Or.inr (by simpa using k3)⟩

theorem next_i8 : 1 ≤ j + 1 → ValidC R K pch (σ') (σ').root ∧ compOf gc' (σ').root = range R ∧
    pcode (σ') (σ').root = (σ').root := by
  intro _
  rcases Nat.eq_zero_or_pos j with hj | hj
  · obtain ⟨-, a0, s0⟩ := hI.i7 hj
    have hroot : (σ').root = code best pch 0 := by
      ϴ next, ite_eq_left a0, ite_eq_left s0
    Ξ hroot
    obtain ⟨v1, v2, v3⟩ := code_next h hch hT hB hI h.R_pos (Or.inl rfl) a0
    refine ⟨v1, by rw [v2]; exact sub_root0 h hch hT hB hI hj, Ρ v3, ite_eq_left s0⟩
  · Ξ root_next_pos h hch hT hB hI hj
    obtain ⟨o1, o2, o3⟩ := hI.i8 hj
    obtain ⟨v1, v2, v3⟩ := valid_next h hch hT hB hI o1
    exact ⟨v1, v2.trans o2, v3.trans o3⟩

theorem next_i9 : (σ').fin =
    ((range R).filter (fun t => IsTop pch (σ').rem t ∧ (σ').act t ≠ 1)).card := by
  have hsplit : (range R).filter (fun t => IsTop pch (σ').rem t ∧ (σ').act t ≠ 1) =
      (range R).filter (fun t => IsTop pch σ.rem t ∧ σ.act t ≠ 1) ∪
        (range R).filter (fun r => top r = r ∧ σ.act r = 1 ∧ best r = r) := by
    ext t
    ϴ Finset.mem_union, Finset.mem_filter, Finset.mem_range
    constructor
    · rintro ⟨ht, htop', hact'⟩
      by_cases htop : IsTop pch σ.rem t
      · Ξ' act_top h hch hT hB hI ht htop at hact'
        by_cases hact : σ.act t = 1
        · Ξ' ite_eq_left hact at hact'
          have hbt : best t = t := by
            by_contra hh; Ξ' ite_eq_right hh at hact'; exact hact' hact
          exact Or.inr ⟨ht, top_self h hch hT hB hI ht htop, hact, hbt⟩
        · exact Or.inl ⟨ht, htop, hact⟩
      · obtain ⟨ht0, hc⟩ := ((istop_next h hch hT hB hI ht).1 htop').resolve_left htop
        have hpk := h.pch_lt t ht ht0
        have hco := chOf_pch h hch hT hB hI ht ht0
        obtain ⟨n1, -, -⟩ := new_top_facts h hch hT hB hI hpk hc
        Ξ' hco at n1
        exact absurd n1 hact'
    · rintro (⟨ht, htop, hact⟩ | ⟨ht, htt, hact, hbt⟩)
      · refine ⟨ht, (istop_next h hch hT hB hI ht).2 (Or.inl htop), ?_⟩
        rw [act_top h hch hT hB hI ht htop, ite_eq_right hact]; exact hact
      · have htop := (top_iff h hch hT hB hI ht).1 htt
        refine ⟨ht, (istop_next h hch hT hB hI ht).2 (Or.inl htop), ?_⟩
        rw [act_top h hch hT hB hI ht htop, ite_eq_left hact, ite_eq_left hbt]; norm_num
  have hdisj : Disjoint ((range R).filter (fun t => IsTop pch σ.rem t ∧ σ.act t ≠ 1))
      ((range R).filter (fun r => top r = r ∧ σ.act r = 1 ∧ best r = r)) := by
    Ξ Finset.disjoint_filter
    intro t _ h1 h2
    exact h1.2 h2.2.1
  Ξ hsplit, Finset.card_union_of_disjoint hdisj, ← hI.i9
  rfl

/-- **Preservation of the round invariant.** -/
theorem rinv_next (hdeg : ∀ v, v < R → (kids R prg pch rem0 v).card + (if v = 0 then 0 else 1) ≤ D) :
    RInv R K D prg pch isdn chOf (j + 1) (σ') gc' cr' where
  i0 e he hp := by
    exact (rem_next h hch hT hB hI he).2 (Or.inr ((pend_next h hch hT hB hI he).1 hp))
  i1 := next_i1 h hch hT hB hI
  i2 := next_i2 h hch hT hB hI
  i3 := next_i3 h hch hT hB hI
  i4 := next_i4 h hch hT hB hI
  i5 := next_i5 h hch hT hB hI
  i6 := next_i6 h hch hT hB hI hdeg
  i7 hj := absurd hj (⋄)
  i8 := next_i8 h hch hT hB hI
  i9 := next_i9 h hch hT hB hI

end step3

end

end Chazelle.Core.Dec
