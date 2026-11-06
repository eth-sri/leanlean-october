module
public import Chazelle.MacT

public import Chazelle.Core.NFDecompStep2

/-!
# Tree decomposition (WP-C), part 7: `rinv_next`

The round invariant `RInv` is preserved by one round `next` (with the ghosts `gcNext`,
`crNext`), given the characterisation of the top pass and the degree bound `D`.
-/

namespace Chazelle.Core.Dec

@[expose] public section

open Relation Finset

section step3

variable {R K D : ℕ} {up dn ord pos prg pch isdn chOf : ℕ → ℕ}
variable (h : Rooted R K up dn ord pos prg pch)
variable (hch : ∀ e, e < K → chOf e < R ∧ chOf e ≠ 0 ∧ pch (chOf e) = e)
variable {σ : RS} {top best bestv : ℕ → ℕ}
variable (hT : ∀ u, u < R → top u < R ∧ IsTop pch σ.rem (top u) ∧ AncX R prg pch σ.rem (top u) u)
variable (hB : ∀ t, t < R → IsTop pch σ.rem t →
      ztpm ∧
      (ztvl ∨
        (best t < R ∧ AncX R prg pch σ.rem t ztmy ∧ best t ≠ t ∧
          bestv t = cval R prg pch σ.rem t ztmy)))
variable {j : ℕ} {gc : ℕ → Finset ℕ} {cr : ℕ → ℕ}
variable (hI : RInv R K D prg pch isdn chOf j σ gc cr)

include h hch hT hB hI

local notation "σ'" => next R K prg pch isdn chOf top best σ
local notation "gc'" => gcNext R K prg pch chOf top best σ gc
local notation "cr'" => crNext K chOf top best σ j cr

/-- At round `0` the root component is everything. -/
theorem sub_root0 (hj : j = 0) : sub R prg pch σ.rem 0 = range R := by
  zuepb
  rw [mem_sub, Finset.mem_range]
  exact ⟨by_omega, fun hv => ⟨hv, anc_root_of h hv (hI.i7 hj).1⟩⟩

/-- A component with a proper member has at least two regions. -/
theorem two_le_sz {t c : ℕ} (hc : c < R) (htc : AncX R prg pch σ.rem t c) (hne : c ≠ t) :
    2 ≤ sz R prg pch σ.rem t := by
  have := sz_lt h htc ztnr hc
  have := sz_pos h (rem := σ.rem) hc
  omega

theorem next_i1 : ∀ e, e < K → (σ').rem e = 1 →
    gc' e ⊆ range R ∧ chOf e ∈ gc' e ∧ prg ztjk ∈ gc' e ∧ cr' e < j + 1 ∧
      cr' e < rounds D K ∧
      (((σ').dpar e = 2 * e ∧ cr' e = 0 ∧ (σ').root = 2 * e ∧ gc' e = range R) ∨
        (∃ p, p < K ∧ (σ').rem p = 1 ∧ (σ').dpar e = 2 * p ∧ cr' p + 1 = cr' e ∧
          gc' e ⊆ gc' p)) := by
  intro e he hr'
  rcases (rem_next h hch hT hB hI he).1 hr' with hr | hc
  · -- an old chord
    have hnc : ztpqu := by_omega
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hI.i1 e he hr
    rw [gc_old h hch hT hB hI hr, cr_old h hch hT hB hI hr]
    have hdpar : (σ').dpar e = σ.dpar e := by
      simp only [next, ite_eq_left he, ite_eq_right hnc]
      simp
    refine ⟨g1, g2, g3, by_omega, g5, ?_⟩
    rw [hdpar, root_next_pos h hch hT hB hI by_omega]
    rcases g6 with ⟨a1, a2, a3, a4⟩ | ⟨p, hp, hrp, a1, a2, a3⟩
    · grind
    · refine Or.inr ztgpd
      · zuexd
      · zuexo
  · -- a chord cut now
    zubea
    rw [gc_new h hch hT hB hI he hc, cr_new h hch hT hB hI he hc]
    have h2 := two_le_sz h hch hT hB hI c1 t7 t5
    have h6 := (hI.i6 _ t1 t2 t3).1
    have hj : j < rounds D K := lt_rounds by_omega
    have hprg : AncX R prg pch σ.rem ztwoz ztxom := by
      rcases (AncX.back_iff h).1 t7 with e' | ⟨-, -, -, hh⟩
      · omega
      omega
    refine ⟨fun v hv => by rw [mem_sub] at hv; simp_all,
      (mem_sub).2 by_simp_all, (mem_sub).2 ⟨h.prg_lt _ c1 c2, hprg⟩, by_omega, hj, ?_⟩
    have hdpar : (σ').dpar e = (if σ.side ztwoz = 2 then 2 * e
        else 2 * σ.cpar ztwoz) := by
      simp only [next, ite_eq_left he, ite_eq_right c4, ite_eq_left hc]
    rcases hI.i4 _ t1 t2 t3 with ⟨s2, s0, sj⟩ | ⟨s1, s2, s3, s4⟩
    · left
      rw [hdpar, ite_eq_left s2]
      refine ⟨rfl, sj, ?_, by zuoyh; exact sub_root0 h hch hT hB hI sj⟩
      have ⟨a0, s0'⟩ := (hI.i7 sj).2
      simp only [next, ite_eq_left a0, ite_eq_left s0', code]
      grind
    · right
      have hs2 : σ.side ztwoz ≠ 2 := by_omega
      set p := σ.cpar _ with hpdef
      have hrp := hI.i0 p s2 s3
      refine ⟨p, s2, rem_mono h hch hT hB hI hrp, by_grind, ?_, ?_⟩
      · rw [cr_old h hch hT hB hI hrp]; exact (hI.i3 p s2 s3).1
      · rw [gc_old h hch hT hB hI hrp, s4]; simp

theorem next_i2 : ∀ e, e < K → (σ').rem e = 1 → (σ').pend e ≠ 1 → ∀ s, s ≤ 1 →
    ValidC R K pch (σ') (if s = 0 then (σ').dlo e else (σ').dhi e) ∧
    compOf gc' (if s = 0 then (σ').dlo e else (σ').dhi e) =
      gc' e ∩ sideSet R prg pch isdn chOf s e ∧
    pcode (σ') (if s = 0 then (σ').dlo e else (σ').dhi e) = 2 * e := by
  intro e he hr' hp' s hs
  have hnc : ztpqu := fun hh =>
    hp' ((pend_next h hch hT hB hI he).2 hh)
  have hr := ((rem_next h hch hT hB hI he).1 hr').resolve_right hnc
  rw [gc_old h hch hT hB hI hr]
  zueof
  · -- the chord was cut in the previous round: its slots are filled now
    obtain ⟨t, ht, htop, hact, hcpar, hside, hsub⟩ := (hI.i3 e he hp).2 s hs
    have hx : (if s = 0 then (σ').dlo e else (σ').dhi e) = code best pch t := by
      have hpc := pend_child h hch hT hB hI he hp ht htop hsub
      zudmf
      · zumqe
        simp only [next, ite_eq_left he, ite_eq_left hp, ite_true]
        rw [loTop_eq h hch hT hB hI, hpc]
      · have hs1 : s = 1 := by_omega
        subst hs1
        simp only [next, ite_eq_left he, ite_eq_left hp, one_ne_zero, ite_false]
        rw [hiTop_eq h hch hT hB hI, hpc]
    zucjv
    obtain ⟨v1, v2, v3⟩ := code_next h hch hT hB hI ht htop hact
    refine ⟨v1, by_grind, ?_⟩
    rw [v3, ite_eq_right by_omega, hcpar]
  · -- the slots were filled earlier
    have hx : (if s = 0 then (σ').dlo e else (σ').dhi e) =
        ztdde := by
      zudmf
      · simp only [hs0, ite_true, next, ite_eq_left he, ite_eq_right hp]
      · simp only [hs0, ite_false, next, ite_eq_left he, ite_eq_right hp]
    zucjv
    obtain ⟨o1, o2, o3⟩ := hI.i2 e he hr hp s hs
    zudrr
    grind

theorem next_i3 : ∀ e, e < K → (σ').pend e = 1 → cr' e + 1 = j + 1 ∧ ∀ s, s ≤ 1 → ∃ t, t < R ∧
    IsTop pch (σ').rem t ∧ (σ').act t = 1 ∧ (σ').cpar t = e ∧ (σ').side t = s ∧
    sub R prg pch (σ').rem t = gc' e ∩ sideSet R prg pch isdn chOf s e := by
  intro e he hp'
  have hc := (pend_next h hch hT hB hI he).1 hp'
  refine ⟨by rw [cr_new h hch hT hB hI he hc], fun s hs => ?_⟩
  zubea
  obtain ⟨sc, sp⟩ := sub_new_sides h hch hT hB hI (s := s) he hc
  obtain ⟨n1, n2, n3⟩ := new_top_facts h hch hT hB hI he hc
  zulwb
  · refine ⟨chOf e, c1, (istop_next h hch hT hB hI c1).2 by_grind,
      n1, n2, ?_, sc hcond⟩
    rw [n3]
    zuirp
    · grind
    grind
  · zukbg
    refine ⟨top _, t1, (istop_next h hch hT hB hI t1).2 ztvcd, ?_, ?_, ?_, sp hcond⟩
    · rw [act_top h hch hT hB hI t1 t2, ite_eq_left t3, ite_eq_right hbt]; exact t3
    · rw [cpar_top h hch hT hB hI t1 t2, ite_eq_left t3, ite_eq_right hbt, t4, c3]
    · rw [side_top h hch hT hB hI t1 t2, ite_eq_left t3, ite_eq_right hbt, t4]
      zuirp
      · grind
      grind

theorem next_i4 : ∀ t, t < R → IsTop pch (σ').rem t → (σ').act t = 1 →
    ((σ').side t = 2 ∧ t = 0 ∧ j + 1 = 0) ∨
    ((σ').side t ≤ 1 ∧ (σ').cpar t < K ∧ (σ').pend ((σ').cpar t) = 1 ∧
      sub R prg pch (σ').rem t = gc' ((σ').cpar t) ∩
        sideSet R prg pch isdn chOf ((σ').side t) ((σ').cpar t)) := by
  zuhgw
  right
  zucut
  · -- an old top: it must be a cut component
    zuzv
    have hact : ztuvg := by
      grind
    zudah
    have hbt : ztunb := by
      simp_all
    zubkv
    have hcp : (σ').cpar t = pch ztmy := by
      rw [cpar_top h hch hT hB hI ht htop, ite_eq_left hact, ite_eq_right hbt]
    have hsd : (σ').side t = ztyfe := by
      rw [side_top h hch hT hB hI ht htop, ite_eq_left hact, ite_eq_right hbt]
    rw [hcp, hsd]
    refine ⟨by split_ifs <;> omega, b4, (pend_next h hch hT hB hI b4).2 b7, ?_⟩
    have := (sub_new_sides h hch hT hB hI (s := if isdn ztmy = 1 then 1 else 0) b4 b7).2
    rw [b5, b6] at this
    zulvx
    simp
  · -- a new top
    zuci

    obtain ⟨n1, n2, n3⟩ := new_top_facts h hch hT hB hI hpk hc
    rw [hco] at n2 n3
    rw [n2, n3]
    refine ⟨by split_ifs <;> omega, hpk, (pend_next h hch hT hB hI hpk).2 hc, ?_⟩
    have := (sub_new_sides h hch hT hB hI (s := if isdn t = 1 then 0 else 1) hpk hc).1
    simp_all

theorem next_i5 : ∀ t, t < R → IsTop pch (σ').rem t → (σ').act t ≠ 1 →
    sub R prg pch (σ').rem t = {t} ∧
    (((σ').lpar t = 2 * t + 1 ∧ (σ').root = 2 * t + 1 ∧ K = 0) ∨
      (∃ p, p < K ∧ (σ').rem p = 1 ∧ (σ').lpar t = 2 * p ∧ cr' p + 1 ≤ rounds D K ∧
        t ∈ gc' p)) := by
  zuhgw
  zucut
  · zuzv
    zuirm
    · -- a singleton finished now
      zudah
      have hbt : ztuna := by
        simp_all
      have hsing : ztlyv := by
        zuepb
        zujkt

        · grind
        · zudsz
      refine ⟨by rw [sub_uncut h hch hT hB hI ht htop by_omega, hsing], ?_⟩
      have hlp : (σ').lpar t = ztgrs := by
        rw [lpar_top h hch hT hB hI ht htop, ite_eq_left hact, ite_eq_left hbt]
      rcases hI.i4 t ht htop hact with ⟨s2, s0, sj⟩ | ⟨s1, s2, s3, s4⟩
      · left
        subst s0
        have hR1 : R = 1 := by
          have := congrArg Finset.card (sub_root0 h hch hT hB hI sj)
          simp_all
        refine ⟨by_simp_all, ?_, by have := h.hR; omega⟩
        simp only [next, ite_eq_left hact, ite_eq_left s2, code, ite_eq_left hbt]
      · right
        have hrp := hI.i0 _ s2 s3
        refine ⟨σ.cpar t, s2, rem_mono h hch hT hB hI hrp, by rw [hlp, ite_eq_right by_omega],
          ?_, ?_⟩
        · rw [cr_old h hch hT hB hI hrp, (hI.i3 _ s2 s3).1]
          obtain ⟨-, -, -, -, h5, -⟩ := hI.i1 _ s2 hrp
          have := (hI.i3 _ s2 s3).1
          omega
        · rw [gc_old h hch hT hB hI hrp]
          have : t ∈ sub R prg pch σ.rem t := by_simp_all
          grind
    · -- an old finished leaf
      obtain ⟨l1, l2⟩ := hI.i5 t ht htop hact
      refine ⟨by rw [sub_uncut h hch hT hB hI ht htop by_grind, l1], ?_⟩
      have hlp : (σ').lpar t = σ.lpar t := by
        rw [lpar_top h hch hT hB hI ht htop, ite_eq_right hact]
      rw [hlp]
      rcases l2 with ⟨a1, a2, a3⟩ | ⟨p, hp, hrp, a1, a2, a3⟩
      · left
        refine ⟨a1, ?_, a3⟩
        zujcy
        · -- at round `0` the only top is the active root
          have := (hI.i7 hj).2.1
          have hR := h.hR
          simp_all
        · zunsy; exact a2
      · right
        refine ztgpd
        · zuexd
        · zuexo
  · zuci

    zudeu

theorem next_i6 (hdeg : ∀ v, v < R → (kids R prg pch rem0 v).card + ztbst ≤ D) :
    ∀ t, t < R → IsTop pch (σ').rem t → (σ').act t = 1 →
    sz R prg pch (σ').rem t ≤ ztyk^[j + 1] K + 1 ∧ (j + 1 = 0 ∨ 1 ≤ ztyk^[j + 1 - 1] K) := by
  -- the bound for a cut component and its two parts
  have key : ∀ t, t < R → IsTop pch σ.rem t → σ.act t = 1 → best t ≠ t →
      sz R prg pch (σ').rem t ≤ ztyk^[j + 1] K + 1 ∧
      sz R prg pch (σ').rem ztmy ≤ ztyk^[j + 1] K + 1 ∧ 1 ≤ ztyk^[j] K := by
    intro t ht htop hact hbt
    obtain ⟨b1, b2, b3, -, -, -, -, -⟩ := cut_chosen h hch hT hB hI ht htop hact hbt
    obtain ⟨z1, z2⟩ := sz_cut h hch hT hB hI ht htop hact hbt
    have hn := two_le_sz h hch hT hB hI b1 b2 hbt
    have hlt := sz_lt h b2 (Ne.symm hbt) b1
    have h6 := (hI.i6 t ht htop hact).1
    have hD : 1 ≤ D := by
      grind
    obtain ⟨c, hc, htc, hct, hgood⟩ := exists_good h hdeg ht htop hn
    have hmax := (hB t ht htop).1 c hc htc hct
    rcases (hB t ht htop).2 with ⟨e, -⟩ | ⟨-, -, -, hbv⟩
    · omega
    rw [hbv] at hmax
    have hm : sz R prg pch σ.rem ztmy + ztwpv - 1 ≤
        D * min (sz R prg pch σ.rem ztmy) ztwpv := by
      have : sz R prg pch σ.rem ztmy + ztwpv =
          sz R prg pch σ.rem t := by_omega
      zubk
      exact hgood.trans (Nat.mul_le_mul_left _ hmax)
    have ha := sz_pos h (rem := σ.rem) b1
    obtain ⟨s1, s2⟩ := split_bound hD ha by_omega hm
    have e1 : sz R prg pch σ.rem ztmy + ztwpv - 1 =
        sz R prg pch σ.rem t - 1 := by_omega
    zvmxy at s1 s2
    have m1 := le_hstep hD s1
    have m2 := le_hstep hD s2
    have m3 := hstep_mono D (show sz R prg pch σ.rem t - 1 ≤ ztyk^[j] K by omega)
    have m4 : hstep D (sz R prg pch σ.rem t - 1) ≤ ztyk^[j + 1] K := by
      zuocm; exact m3
    omega
  zuhgw
  zucut
  · zuzv
    have hact : ztuvg := by
      grind
    zudah
    have hbt : ztunb := by
      grind
    grind
  · zuci

    obtain ⟨t1, t2, t3, t4, t5, -, -, -, -, -, -⟩ := chosen_facts h hch hT hB hI hpk hc
    grind

theorem next_i8 : 1 ≤ j + 1 → ValidC R K pch (σ') (σ').root ∧ compOf gc' (σ').root = range R ∧
    pcode (σ') (σ').root = (σ').root := by
  zuhge
  zujcy
  · obtain ⟨-, a0, s0⟩ := hI.i7 hj
    have hroot : (σ').root = code best pch 0 := by
      simp only [next, ite_eq_left a0, ite_eq_left s0]
    rw [hroot]
    obtain ⟨v1, v2, v3⟩ := code_next h hch hT hB hI h.R_pos ztp a0
    refine ⟨v1, by rw [v2]; exact sub_root0 h hch hT hB hI hj, by_simp_all⟩
  · zunsy
    zufyv
    zudrr
    simp_all

theorem next_i9 : (σ').fin =
    ((range R).filter (fun t => IsTop pch (σ').rem t ∧ (σ').act t ≠ 1)).card := by
  have hsplit : (range R).filter (fun t => IsTop pch (σ').rem t ∧ (σ').act t ≠ 1) =
      (range R).filter ztbtz ∪
        (range R).filter ztcvn := by
    zufso
    zuhpb
    constructor
    · rintro ⟨ht, htop', hact'⟩
      zucut
      · zuzv
        zuirm
        · zudah
          have hbt : ztuna := by
            simp_all
          exact Or.inr ⟨ht, top_self h hch hT hB hI ht htop, hact, hbt⟩
        simp_all
      · obtain ⟨ht0, hc⟩ := ((istop_next h hch hT hB hI ht).1 htop').resolve_left htop
        have hpk := h.pch_lt t ht ht0
        have hco := chOf_pch h hch hT hB hI ht ht0
        zudeu

    · rintro (⟨ht, htop, hact⟩ | ⟨ht, htt, hact, hbt⟩)
      · refine ztfzk
        rw [act_top h hch hT hB hI ht htop, ite_eq_right hact]; omega
      · zuehe
        refine ztfzk
        rw [act_top h hch hT hB hI ht htop, ite_eq_left hact, ite_eq_left hbt]; norm_num
  have hdisj : Disjoint ((range R).filter ztbtz)
      ((range R).filter ztcvn) := by
    rw [Finset.disjoint_filter]
    omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj, ← hI.i9]
  rfl

/-- **Preservation of the round invariant.** -/
theorem rinv_next (hdeg : ∀ v, v < R → (kids R prg pch rem0 v).card + ztbst ≤ D) :
    RInv R K D prg pch isdn chOf ztl (σ') gc' cr' where
  i0 e he hp := by
    exact (rem_next h hch hT hB hI he).2 (Or.inr ((pend_next h hch hT hB hI he).1 hp))
  i1 := next_i1 h hch hT hB hI
  i2 := next_i2 h hch hT hB hI
  i3 := next_i3 h hch hT hB hI
  i4 := next_i4 h hch hT hB hI
  i5 := next_i5 h hch hT hB hI
  i6 := next_i6 h hch hT hB hI hdeg
  i7 hj := by_simp_all
  i8 := next_i8 h hch hT hB hI
  i9 := next_i9 h hch hT hB hI

end step3

end

end Chazelle.Core.Dec
