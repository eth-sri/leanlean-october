module

public import Chazelle.Core.DownPhaseBaseSpec
public import Chazelle.Core.ShearInv

/-!
# Down phase, A1: `dropAug : DropAugSpec`

The assembly of `dropStmt`: setup, the bit, the chord pass (`Inv1`), the event pass (`Inv2`),
then the post: the kept list and the renumbered events in memory, and the math of
`DownPhaseBaseList` (`family_keepL`, `chordTriplesOK_keepL`, `dropE_perm`, `dropE_pairwise`).
-/

namespace Chazelle.Core

namespace DownBase

open Machine Machine.Stmt Programs SortL
open BuildNF (codeLe)

@[expose] public section

theorem tw_eq (L' : List (ℕ × ℕ × ℕ)) (i q : ℕ) (hq : q < 3) :
    tw L' (3 * i + q) = if q = 0 then (L'.getD i (0, 0, 0)).1
      else if q = 1 then (L'.getD i (0, 0, 0)).2.1 else (L'.getD i (0, 0, 0)).2.2 := by
  unfold tw
  rw [show (3 * i + q) % 3 = q by omega, show (3 * i + q) / 3 = i by omega]

theorem mem1_zero (m₀ : ℕ → ℕ) (li : Bool) (n : ℕ) (L : List (ℕ × ℕ × ℕ)) (B' X a : ℕ) :
    mem1 m₀ li n L B' X 0 a = m₀ a := by
  unfold mem1
  have h0 : rankF (keepX li n) L 0 = 0 := by simp [rankF]
  rw [h0, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem mem1_low {m₀ : ℕ → ℕ} {li : Bool} {n : ℕ} {L : List (ℕ × ℕ × ℕ)} {B' X i a : ℕ}
    (h1 : a < B') (h2 : a < X) : mem1 m₀ li n L B' X i a = m₀ a := by
  unfold mem1
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem mem1_list {m₀ : ℕ → ℕ} {li : Bool} {n : ℕ} {L : List (ℕ × ℕ × ℕ)} {B' X i a : ℕ}
    (h1 : B' ≤ a) (h2 : a < B' + 3 * rankF (keepX li n) L i) :
    mem1 m₀ li n L B' X i a = tw (keepL li n L) (a - B') := by
  unfold mem1
  rw [ite_eq_left ⟨h1, h2⟩]

theorem mem2_low {m₁ : ℕ → ℕ} {li : Bool} {n : ℕ} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
    {SE' t a : ℕ} (h : a < SE') : mem2 m₁ li n L E SE' t a = m₁ a := by
  unfold mem2
  rw [ite_eq_right (by omega)]

theorem mem2_in {m₁ : ℕ → ℕ} {li : Bool} {n : ℕ} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
    {SE' t a : ℕ} (h1 : SE' ≤ a) (h2 : a < SE' + (dropE li n L (E.take t)).length) :
    mem2 m₁ li n L E SE' t a = (dropE li n L (E.take t)).getD (a - SE') 0 := by
  unfold mem2
  rw [ite_eq_left ⟨h1, h2⟩]

set_option maxHeartbeats 16000000 in
/-- **A1: `DropAugSpec`.** -/
theorem dropAug : DropAugSpec := by
  refine ⟨dropStmt, 80, ?_⟩
  intro P W c hw hpre hcost
  obtain ⟨hG, hWn, hDA, hli, L, hlen, hBL, hCL, hok, hSEL, hperm, hsort⟩ := hpre
  simp only [rd, bandReg, bDown, Nat.reduceMul, Nat.reduceAdd] at hDA hli hlen hBL hCL hSEL hperm hsort hcost ⊢
  set K := L.length with hK
  set D := c.nreg 200000 with hD
  set B := c.nreg 200001 with hB
  set SE := c.nreg 200003 with hSE
  set A₀ := c.nreg ALLOC with hA₀
  have hA : c.nreg 9999 = A₀ := rfl
  set li := liBit c.nmem D with hlidef
  set E := seg c.nmem SE (2 * K) with hEdef
  have hEl : E.length = 2 * K := seg_length
  set X := A₀ + 3 * K with hX
  set SE' := A₀ + 5 * K with hSE'
  have hcost' : A₀ + 80 * (K + 1) ≤ W := by
    have h := hcost
    beta_reduce at h
    rw [hlen] at h
    exact h
  have hnW : P.n ≤ W := by unfold hostWords at hWn; omega
  have hQn : (Qof P).n = P.n := shear_n _ _
  -- setup
  obtain ⟨c₁, k₁, e₁, hk₁, s100, s101, s105, s104, s106, s103, s136, s004, s121, s122, s9999,
      s006, s110, s111, s117, s118, s119, sfr, sin, sm, srr, srm, so⟩ :=
    dSetup_exec (P := P) c hw rfl rfl hlen hA (by omega) (by omega) hnW
  -- the bit
  obtain ⟨c₂, k₂, e₂, hk₂, b103, bfr, bm, brr, brm, bo⟩ :=
    dBit_exec (P := P) c₁ e₁.wb_right (by omega) s106 s105 s101 s103
  have g21 : ∀ r, r ≠ 200103 → c₂.nreg r = c₁.nreg r := bfr
  -- the chord pass
  have hI₁ : Inv1 c.nmem li P.n L B A₀ X c₂ c₂ :=
    { i_le := by rw [g21 _ (by norm_num), s110]; omega
      rK := by rw [g21 _ (by norm_num), sin _ ⟨by norm_num, by norm_num⟩, hlen]
      r111 := by rw [g21 _ (by norm_num), g21 _ (by norm_num), s111, s110]; ring
      r117 := by rw [g21 _ (by norm_num), g21 _ (by norm_num), s117, s110, hX]; ring
      r118 := by
        rw [g21 _ (by norm_num), g21 _ (by norm_num), s118, s110]; simp [rankF]
      r119 := by
        rw [g21 _ (by norm_num), g21 _ (by norm_num), s119, s110]; simp [rankF]
      r100 := by rw [g21 _ (by norm_num), s100]
      r101 := by rw [g21 _ (by norm_num), s101]
      r103 := by rw [b103]; simp [hlidef, liBit]; rfl
      r104 := by rw [g21 _ (by norm_num), s104]
      fr := fun _ _ => rfl
      rr := rfl
      rm := rfl
      out := rfl
      mem := fun a => by
        rw [bm, sm, g21 _ (by norm_num), s110]
        exact (mem1_zero c.nmem li P.n L A₀ X a).symm }
  obtain ⟨c₃, k₃, e₃, hw₃, hI₃, h3i, hk₃, hk₃'⟩ := dLoop1_exec (P := P) hCL (by omega) rfl
    (by omega) e₂.wb_right hI₁ (by rw [g21 _ (by norm_num), s110])
  -- between the passes
  obtain ⟨c₄, k₄, e₄, hk₄, m005, m130, m131, m134, mfr, mm, mrr, mrm, mo⟩ :=
    dMid_exec (P := P) c₃ hw₃
  -- registers of `c₃` outside the chord-pass scratch
  have g3 : ∀ r, (r < 200110 ∨ 200120 < r) → r ≠ 200103 → c₃.nreg r = c₁.nreg r :=
    fun r hr h103 => by rw [hI₃.fr r hr, g21 r h103]
  set m₁ := mem1 c.nmem li P.n L A₀ X K with hm₁
  have hI₂ : Inv2 m₁ li P.n L E SE X SE' c₄ c₄ :=
    { t_le := by rw [m130]; omega
      r136 := by
        rw [mfr _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
          g3 _ (by norm_num) (by norm_num), s136, hEl]
      r131 := by
        rw [m131, m130, g3 _ (by norm_num) (by norm_num), sin _ ⟨by norm_num, by norm_num⟩]
        rfl
      r134 := by
        rw [m134, m130, g3 _ (by norm_num) (by norm_num), s122]
        simp [dropE]
        rfl
      r121 := by
        rw [mfr _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
          g3 _ (by norm_num) (by norm_num), s121]
      r100 := by rw [mfr _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), hI₃.r100]
      r101 := by rw [mfr _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), hI₃.r101]
      fr := fun _ _ => rfl
      rr := rfl
      rm := rfl
      out := rfl
      mem := fun a => by
        rw [mm, hI₃.mem, h3i, m130]
        unfold mem2
        simp only [dropE, List.take_zero, List.filter_nil, List.map_nil, List.length_nil,
          Nat.add_zero]
        rw [ite_eq_right (by omega)] }
  have hrk : rankF (keepX li P.n) L K ≤ K := rankF_le _ _ _
  obtain ⟨c₅, k₅, e₅, hw₅, hI₅, h5t, hk₅, hk₅'⟩ := dLoop2_exec (P := P) (m₁ := m₁)
    (fun t ht => by
      rw [hm₁]; unfold mem1
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      exact BuildRam.seg_getD rfl (by omega))
    (by omega)
    (fun c' hc' => by
      rw [hm₁]; unfold mem1
      rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left])
    (by omega) hEl hperm (by omega) e₄.wb_right hI₂ m130
  -- the final configuration
  have g5 : ∀ r, (r < 200130 ∨ 200135 < r) → c₅.nreg r = c₄.nreg r := hI₅.fr
  have g51 : ∀ r, (r < 200110 ∨ 200135 < r) → r ≠ 200005 → r ≠ 200103 →
      c₅.nreg r = c₁.nreg r := fun r hr h5 h3 => by
    rw [g5 r (by omega), mfr r h5 (by omega) (by omega) (by omega), g3 r (by omega) h3]
  have f004 : c₅.nreg 200004 = A₀ := by
    rw [g51 _ (by norm_num) (by norm_num) (by norm_num), s004]
  have f006 : c₅.nreg 200006 = SE' := by
    rw [g51 _ (by norm_num) (by norm_num) (by norm_num), s006]
  have f9999 : c₅.nreg 9999 = A₀ + 7 * K := by
    rw [g51 _ (by norm_num) (by norm_num) (by norm_num), s9999]
  set L' := keepL li P.n L with hL'
  have hL'len : L'.length = rankF (keepX li P.n) L K := (rankF_length _ _).symm
  have f005 : c₅.nreg 200005 = L'.length := by
    rw [g5 _ (by norm_num), m005, hI₃.r118, h3i, hL'len]
  have hK' : L'.length ≤ K := by rw [hL'len]; exact hrk
  have hK2 : (keepL li P.n L).length ≤ K := hK'
  have hmem5 : ∀ a, c₅.nmem a = mem2 m₁ li P.n L E SE' E.length a := fun a => by
    rw [hI₅.mem, h5t]
  have hEt : E.take E.length = E := List.take_length
  have hdlen : (dropE li P.n L E).length = 2 * L'.length := by
    have := (dropE_perm (li := li) (n := P.n) hperm).length_eq
    rw [List.length_range] at this
    exact this
  have hCL' : ChordListAt c₅.nmem A₀ L' := by
    intro i hi
    have hm : ∀ q, q < 3 → c₅.nmem (A₀ + 3 * i + q) = tw L' (3 * i + q) := fun q hq => by
      rw [hmem5, mem2_low (by omega), hm₁, mem1_list (by omega) (by rw [← hL'len]; omega),
        show A₀ + 3 * i + q - A₀ = 3 * i + q by omega]
    refine ⟨?_, ?_, ?_⟩
    · have := hm 0 (by norm_num)
      rw [Nat.add_zero, Nat.add_zero] at this
      rw [this, show 3 * i = 3 * i + 0 from rfl, tw_eq L' i 0 (by norm_num)]
      rfl
    · rw [hm 1 (by norm_num), tw_eq L' i 1 (by norm_num)]
      rfl
    · rw [hm 2 (by norm_num), tw_eq L' i 2 (by norm_num)]
      rfl
  have hseg : seg c₅.nmem SE' (2 * L'.length) = dropE li P.n L E := by
    apply List.ext_getElem
    · rw [seg_length, hdlen]
    · intro u h1 h2
      simp only [seg, List.getElem_map, List.getElem_range]
      rw [hmem5, mem2_in (by omega) (by rw [hEt]; omega), hEt, List.getD_eq_getElem?_getD,
        Nat.add_sub_cancel_left, List.getElem?_eq_getElem h2, Option.getD_some]
  -- the math
  have hQ : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hG.1
  have hDH : DistinctHeights (Qof P) := (goodShear_epsOf hG.2).2.1
  have hli' : li = true ↔ Mountain.LeftInside (Qof P) := by
    rw [hlidef]
    simp only [liBit, decide_eq_true_eq]
    exact hli
  have hfam := family_keepL hQ hDH hli' hok
  rw [hQn] at hfam
  have X' : Exec P W dropStmt c c₅ (k₁ + (k₂ + (k₃ + (k₄ + k₅)))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  refine ⟨c₅, _, X', ?_, fun L₂ hlen₂ hL₂ => ?_, ?_⟩
  · show _ ≤ 80 * (c.nreg 200002 + 1)
    rw [hlen]
    omega
  · obtain rfl := BuildNF.chordListAt_unique hCL hL₂ (hlen.symm.trans hlen₂)
    rw [hQn]
    refine ⟨by rw [f004], ?_, by rw [f004]; exact hCL', f005, ?_, ?_, by rw [f006]; exact hseg,
      hfam, chordTriplesOK_keepL hok, dropE_perm hperm, dropE_pairwise _ _ hperm hsort⟩
    · rw [f004]; show _ ≤ c₅.nreg 9999; rw [f9999]; omega
    · rw [f006]; show A₀ ≤ A₀ + 5 * K; omega
    · rw [f006]; show _ ≤ c₅.nreg 9999; rw [f9999]; omega
  · refine ⟨fun r hr hra => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_, ?_, ?_⟩
    · have hr' : r < 200000 ∨ 210000 ≤ r := by
        simp only [Finset.mem_singleton, bandOf] at hr
        omega
      rw [g51 r (by omega) (by omega) (by omega), sfr r hr' hra]
    · rw [hI₅.rr, mrr, hI₃.rr, brr, srr]
    · have ha' : a < A₀ := ha
      rw [hmem5, mem2_low (by omega), hm₁, mem1_low (by omega) (by omega)]
    · rw [hI₅.rm, mrm, hI₃.rm, brm, srm]
    · rw [hI₅.out, mo, hI₃.out, bo, so]
    · show A₀ ≤ c₅.nreg 9999
      rw [f9999]
      omega
    · show c₅.nreg 9999 ≤ A₀ + _
      rw [f9999, hEl] at *
      omega

end

end DownBase

end Chazelle.Core
