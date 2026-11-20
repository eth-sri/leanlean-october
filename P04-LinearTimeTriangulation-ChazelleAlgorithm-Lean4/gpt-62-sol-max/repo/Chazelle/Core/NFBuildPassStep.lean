module

meta import Chazelle.Programs.RamEval

public import Chazelle.Core.NFBuildPass
public import Chazelle.Core.SortRam

/-!
# WP-C (BuildNF), RAM part 14: one iteration of the main pass

`passBody_step`: from `PassInv m` (with `m < 2K`), one execution of `passBody` reaches
`PassInv (m + 1)`, in at most `11700` steps.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open BuildNF (wposOf chordRec arcRec arcW cw stk topR gapP gapsB cf af)

@[expose] public section

theorem wr5_in (m : ℕ → ℕ) (b v0 v1 v2 v3 v4 f : ℕ) (hf : f < 5) :
    wr5 m b v0 v1 v2 v3 v4 (b + f) =
      if f = 0 then v0 else if f = 1 then v1 else if f = 2 then v2 else if f = 3 then v3 else v4 := by
  unfold wr5
  interval_cases f <;> simp

theorem wr5_out (m : ℕ → ℕ) (b v0 v1 v2 v3 v4 a : ℕ) (ha : a < b ∨ b + 5 ≤ a) :
    wr5 m b v0 v1 v2 v3 v4 a = m a := by
  unfold wr5
  ifs_omega

section exec

variable {P : Polygon} {W : ℕ}

/-- The stack top from the invariant. -/
theorem PassInv.top {M : Model} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
    {D H T SE B CT AT ST WT lo hd : ℕ} {mB : ℕ → ℕ}
    {F : PassFix P W M L E D H T SE B CT AT ST WT lo hd mB} {c₀ d : Config} {m : ℕ}
    (I : PassInv F c₀ d m) :
    (if d.nreg 43101 = 0 then 0 else d.nmem (d.nreg 44006 + d.nreg 43101 - 1)) = topR E m := by
  rw [BuildNF.topR_eq, I.r101, I.rST]
  split_ifs with h
  · rfl
  · rw [show ST + (stk E m).length - 1 = ST + ((stk E m).length - 1) by omega]
    exact I.stack _ (by omega)

end exec

theorem wr_passBody : wrM Bpass passBody = true := by
  
  
  
  
  simp only [passBody, write_check, block]
  decide

theorem Bpass_false {r : ℕ} (h : r < 10000 ∨ (10503 ≤ r ∧ r ≤ 40000) ∨ (40103 ≤ r ∧ r < 41110) ∨
    (41120 ≤ r ∧ r < 42110) ∨ (42117 < r ∧ r < 43100) ∨ (43104 ≤ r ∧ r < 43106) ∨
    (43106 < r ∧ r < 43110) ∨ (43111 < r ∧ r < 43113) ∨ (43117 < r ∧ r < 43120) ∨
    (43128 ≤ r ∧ r < 43130) ∨ (43135 ≤ r ∧ r < 43140) ∨ (43142 < r ∧ r < 43150) ∨ 43151 < r) :
    Bpass r = false := by
  have hg := Bgap_false (r := r) (by omega)
  simp only [Bpass, hg, Bstep, Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

theorem getD_dropLast {l : List ℕ} {k : ℕ} (hk : k < l.dropLast.length) :
    l.dropLast.getD k 0 = l.getD k 0 := by
  have hne : l ≠ [] := by rintro rfl; simp at hk
  conv_rhs => rw [← List.dropLast_append_getLast hne]
  ram_simp [List.getD_append]

section step

variable {P : Polygon} {W : ℕ}

section

variable {M : Model} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
    {D H T SE B CT AT ST WT lo hd : ℕ} {mB : ℕ → ℕ}
    (F : PassFix P W M L E D H T SE B CT AT ST WT lo hd mB) {c₀ d : Config}
include F c₀ d

set_option maxHeartbeats 4000000 in
/-- **One iteration of the main pass.** -/
theorem passBody_step {m : ℕ}
    (I : PassInv F c₀ d m) (hm : m < E.length) (hw : WordsBounded W d) :
    ∃ d' k, Exec P W passBody d d' k ∧ k ≤ 11700 ∧ 12 ≤ k ∧ WordsBounded W d' ∧
      PassInv F c₀ d' (m + 1) := by
  have hN := F.len
  set K := L.length with hK
  set N := E.length with hNdef
  have hl1 := F.l1; have hl2 := F.l2; have hl3 := F.l3; have hl4 := F.l4; have hl5 := F.l5
  have hTH := F.TH; have hBH := F.BH; have hSEH := F.SEH; have hHW := F.HW
  set c := E.getD m 0 with hc
  have hcN : c < N := by have := BuildNF.getD_lt_of_perm F.inp.perm hm; omega
  set x := c / 2 with hx
  have hxK : x < K := by omega
  obtain ⟨re, rh, rpar, rch⟩ := F.recs c (by omega)
  have lowd := I.low
  -- 1. the current code
  obtain ⟨d₁, k₁, x₁, hk₁, v10, v11, v12, v13, v14, f₁⟩ := curS_exec (P := P) d hw (c := c)
    (T := T) (by ram_rw [I.r103, lowd, F.codes m hm]) I.rT I.r1a I.r1 (by omega)
    (by ram_rw [lowd, rch]; omega)
  ram_rw [lowd, re] at v10
  ram_rw [lowd, rh] at v11
  ram_rw [lowd, rpar] at v12
  ram_rw [lowd, rch] at v13 v14
  have w₁ := x₁.wb_right
  have g₁ : ∀ r, Bpass r = false → d₁.nreg r = d.nreg r := fun r hr => f₁.1 r (by
    simp only [Bpass, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
    simp_all )
  have mm₁ := f₁.2.2.1
  have s₁ : d₁.nreg 43101 = d.nreg 43101 := f₁.1 _ (by decide)
  -- 2. the label before
  obtain ⟨d₂, k₂, x₂, hk₂, v15, f₂⟩ := topS_exec (P := P) d₁ w₁ (dst := 43115)
    (by frame_finish)
    (by frame_finish)
    (by rw [g₁ 44006 (Bpass_false (by omega)), s₁, I.rST, I.r101]; have := I.sp_le; omega)
  rw [g₁ 44006 (Bpass_false (by omega)), s₁, mm₁, I.top] at v15
  have w₂ := x₂.wb_right
  have g₂ : ∀ r, r ≠ 43115 → r ≠ 43116 → d₂.nreg r = d₁.nreg r := fun r a1 a2 => f₂.1 r (by
    simp_all )
  have mm₂ : d₂.nmem = d.nmem := by rw [f₂.2.2.1, mm₁]
  -- 3. the stack step
  have x13 : d₂.nreg 43113 = x := by frame_finish
  have x14 : d₂.nreg 43114 = x + 1 := by frame_finish
  have x12 : d₂.nreg 42112 = c % 2 := by simp [g₂, v12]
  have b₂ : d₂.nreg 43001 = B := by
    frame_finish
  have ct₂ : d₂.nreg 44001 = CT := by
    frame_finish
  have st₂ : d₂.nreg 44006 = ST := by
    frame_finish
  have o₂ : d₂.nreg 43011 = 1 := by
    frame_finish
  have sp₂ : d₂.nreg 43101 = (stk E m).length := by
    ram_finish [g₂, s₁, I.r101]
  have hsp := I.sp_le
  obtain ⟨d₃, k₃, x₃, hk₃, f₃, hpop, hpush⟩ := stepS_exec (P := P) d₂ w₂ (x := x) (B := B)
    (CT := CT) (ST := ST) x13 b₂ ct₂ st₂ o₂ (by omega) (by omega) (by rw [sp₂]; omega)
    (by rw [sp₂]; omega)
  have w₃ := x₃.wb_right
  have hpopiff : d₂.nreg 43115 = d₂.nreg 43114 ↔ x ∈ (cw E).take m := by
    rw [v15, x14]; exact F.inp.pop_iff hm
  have htake := BuildNF.take_succ_cw hm
  have S₃ : d₃.nreg 43101 = (stk E (m + 1)).length ∧ (stk E (m + 1)).length ≤ m + 1 ∧
      (∀ k, k < (stk E (m + 1)).length → d₃.nmem (ST + k) = (stk E (m + 1)).getD k 0 + 1) ∧
      (∀ a, (a < CT ∨ (CT + 5 * K ≤ a ∧ a < ST) ∨ ST + N ≤ a) → d₃.nmem a = d.nmem a) ∧
      (∀ x', x' < K → x' ∈ (cw E).take (m + 1) → ∀ f, f < 5 →
        d₃.nmem (CT + 5 * x' + f) = cf (chordRec M (Qof P) L E x') f) := by
    by_cases hin : x ∈ (cw E).take m
    · -- pop
      obtain ⟨p1, p2⟩ := hpop (hpopiff.2 hin)
      have hh := (BuildNF.topR_eq_succ_iff E m x).1 ((F.inp.pop_iff hm).2 hin)
      obtain ⟨e1, e2⟩ := BuildNF.stk_pop hm hh
      refine ⟨by rw [p1, sp₂]; omega, by omega, fun k hk => ?_, fun a _ => by rw [p2, mm₂],
        fun x' hx' hin' f hf => ?_⟩
      · ram_rw [p2, mm₂, I.stack k, e1, getD_dropLast (by rwa [← e1])]
      · rw [p2, mm₂]
        rw [htake, List.mem_append, List.mem_singleton] at hin'
        rcases hin' with h' | h'
        · exact I.chords x' hx' h' f hf
        · subst h'; exact I.chords _ hx' hin f hf
    · -- push
      obtain ⟨p1, p2⟩ := hpush (fun h => hin (hpopiff.1 h))
      have hh := fun h' =>
        hin ((F.inp.pop_iff hm).1 ((BuildNF.topR_eq_succ_iff E m x).2 h'))
      have e1 := BuildNF.stk_push hm hh
      have hlen : (stk E (m + 1)).length = (stk E m).length + 1 := by rw [e1]; simp
      unfold pushMem at p2
      rw [sp₂, x14, x12, v15] at p2
      refine ⟨by rw [p1, sp₂, hlen], by omega, fun k hk => ?_, fun a ha => ?_,
        fun x' hx' hin' f hf => ?_⟩
      · rw [p2]
        by_cases hk' : k = (stk E m).length
        · subst hk'
          rw [upd_same, e1, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]; rfl
        · ram_rw [upd_other _ _, wr5_out _ _ _ _ _ _ _, mm₂,
            I.stack k, e1, List.getD_append _ _ _]
      · ram_rw [p2, upd_other _ _, wr5_out _ _ _ _ _ _ _, mm₂]
      · ram_rw [p2, upd_other _ _]
        rw [htake, List.mem_append, List.mem_singleton] at hin'
        rcases hin' with h' | h'
        · have hne : x' ≠ x := fun h'' => hin (h'' ▸ h')
          ram_rw [wr5_out _ _ _ _ _ _ _, mm₂]
          exact I.chords x' hx' h' f hf
        · subst h'
          rw [wr5_in _ _ _ _ _ _ _ _ hf, F.inp.chordRec_new hm hxK hin, BuildNF.cf_mk, mm₂]
          obtain ⟨l1, l2, l3⟩ := F.chl x hxK
          ram_rw [lowd, lowd, lowd, l1, l2, l3]
  obtain ⟨sp₃, spl₃, stk₃, oth₃, ch₃⟩ := S₃
  have g₃ : ∀ r, (r < 43101 ∨ (43101 < r ∧ r < 43116) ∨ (43116 < r ∧ r < 43130) ∨ 43134 < r) →
      d₃.nreg r = d₂.nreg r := fun r hr => f₃.1 r (by
    simp only [Bstep, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  -- 4. the label after
  have G₂ : ∀ r, (r < 42110 ∨ (42112 < r ∧ r < 43110) ∨ (43111 < r ∧ r < 43113) ∨
      (43114 < r ∧ r < 43115) ∨ 43116 < r) → d₂.nreg r = d.nreg r := fun r hr => by
    ram_rw [g₂ r]
    exact f₁.1 r (by simp only [decide_eq_false_iff_not]; omega)
  obtain ⟨d₄, k₄, x₄, hk₄, v17, f₄⟩ := topS_exec (P := P) d₃ w₃ (dst := 43117)
    (by frame_finish)
    (by ram_rw [g₃ 43011, o₂])
    (by ram_rw [g₃ 44006, st₂, sp₃]; omega)
  have top₃ : (if d₃.nreg 43101 = 0 then 0 else d₃.nmem (d₃.nreg 44006 + d₃.nreg 43101 - 1)) =
      topR E (m + 1) := by
    ram_rw [BuildNF.topR_eq, sp₃, g₃ 44006, st₂]
    split_ifs with h
    · rfl
    · rw [show ST + (stk E (m + 1)).length - 1 = ST + ((stk E (m + 1)).length - 1) by omega]
      exact stk₃ _ (by omega)
  rw [top₃] at v17
  have w₄ := x₄.wb_right
  have g₄ : ∀ r, r ≠ 43117 → r ≠ 43116 → d₄.nreg r = d₃.nreg r := fun r a1 a2 => f₄.1 r (by
    simp only [decide_eq_false_iff_not]; omega)
  have mm₄ := f₄.2.2.1
  have G₄ : ∀ r, (r < 42110 ∨ (42112 < r ∧ r < 43101) ∨ (43101 < r ∧ r < 43110) ∨
      (43111 < r ∧ r < 43113) ∨ (43117 < r ∧ r < 43130) ∨ 43134 < r) →
      d₄.nreg r = d.nreg r := fun r hr => by
    ram_rw [g₄ r, g₃ r, G₂ r]
  -- 5. the gap
  have lowd₄ : MemEqBelow H d₄.nmem mB := fun a ha => by
    ram_rw [mm₄, oth₃ a, lowd a ha]
  obtain ⟨hM₄, hwf₄⟩ := desc_agree F.wf F.desc lowd₄
  have hA := I.r102
  have hAle := BuildNF.gapsB_length_le M (Qof P) L E m
  set A := (gapsB M (Qof P) L E m).length with hAdef
  have e110 : d₄.nreg 42110 = (wposOf L c).edge := by
    simp [g₄, g₃, g₂, v10]
  have e111 : d₄.nreg 42111 = (wposOf L c).hgt := by
    simp [g₄, g₃, g₂, v11]
  have e117 := v17
  have ec : ∀ {j}, j < E.length → E.getD j 0 < 2 * L.length := fun hj =>
    BuildNF.getD_lt_of_perm F.inp.perm hj
  obtain ⟨d₅, k₅, x₅, hk₅, f₅, hgap, hnogap⟩ := gapS_exec (P := P) F.good F.hwords d₄ w₄
    (M := M) (L := L) (E := E) (D := D) (H := H) (T := T) (SE := SE) (m := m) (A := A)
    (AT := AT) (WT := WT) F.inp.valid hN (fun j hj => ec hj) hm
    (by ram_rw [G₄ 43100, I.r100]) (by ram_rw [G₄ 42001, I.rN])
    (by ram_rw [G₄ 43103, I.r103]) (by ram_rw [G₄ 43104, I.r104])
    (fun j hj => by ram_simp [lowd₄, F.codes j hj])
    (by ram_rw [G₄ 42000, I.rT])
    (fun c' hc' => by
      obtain ⟨a1, a2, a3, a4⟩ := F.recs c' hc'
      exact ⟨by ram_simp [lowd₄, a1], by ram_simp [lowd₄, a2],
        by ram_simp [lowd₄, a3], by ram_simp [lowd₄, a4]⟩)
    (by ram_rw [G₄ 42102, I.r1a]) e110 e111
    (by ram_rw [G₄ 40000, I.rD]) hwf₄ hM₄ hHW
    (by ram_rw [G₄ 41023, I.r23, lowd₄ _ (by have := F.wf.1; omega)])
    (by ram_rw [G₄ 41019, I.r19]) (by ram_rw [G₄ 43102, hA])
    (by ram_rw [G₄ 44002, I.rAT]) (by ram_rw [G₄ 44007, I.rWT])
    (by ram_rw [G₄ 43011, I.r1]) (by omega) (by omega) (by omega) (by omega) hTH
    (by omega)
    (by ram_rw [G₄ 44020, G₄ 44021, I.rlo, I.rhd]; exact F.cnt)
  have w₅ := x₅.wb_right
  have g₅ := f₅.1
  -- 6. the next position
  have a100 : d₅.nreg 43100 = m := by
    ram_simp [g₅, G₄, I.r100] 
  have a103 : d₅.nreg 43103 = SE + m := by
    ram_simp [g₅, G₄, I.r103] 
  have a011 : d₅.nreg 43011 = 1 := by
    ram_simp [g₅, G₄, I.r1] 
  obtain ⟨d₆, k₆, x₆, hk₆, n100, n103, g₆, mm₆⟩ : ∃ d₆ k₆, Exec P W
      (block [.addN 43100 43100 43011, .addN 43103 43103 43011]) d₅ d₆ k₆ ∧ k₆ = 2 ∧
      d₆.nreg 43100 = m + 1 ∧ d₆.nreg 43103 = SE + (m + 1) ∧
      (∀ r, r ≠ 43100 → r ≠ 43103 → d₆.nreg r = d₅.nreg r) ∧ d₆.nmem = d₅.nmem := by
    exec_block
    · rw [a100, a011]; omega
    · config_simp; rw [a103, a011]; omega
    · refine ⟨rfl, ?_, ?_, fun r r1 r2 => ?_, rfl⟩ <;> config_simp
      · rw [a100, a011]
      · rw [a103, a011]; omega
      ram_simp []
  have X : Exec P W passBody d d₆ (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k₆))))) :=
    (by ram_path)
  have G₆ : ∀ r, (r < 10000 ∨ (10503 ≤ r ∧ r ≤ 40000) ∨ (40103 ≤ r ∧ r < 41110) ∨
      (41120 ≤ r ∧ r < 42110) ∨ (42117 < r ∧ r < 43100) ∨ (43104 ≤ r ∧ r < 43106) ∨
      (43106 < r ∧ r < 43110) ∨ (43117 < r ∧ r < 43120) ∨ (43128 ≤ r ∧ r < 43130) ∨
      (43135 ≤ r ∧ r < 43140) ∨ (43142 < r ∧ r < 43150) ∨ 43151 < r) →
      d₆.nreg r = d.nreg r := fun r hr => by
    ram_rw [g₆ r, g₅ r (Bgap_false (by omega)), G₄ r]
  have hgP := F.inp.gapP_iff hm
  have hsucc := BuildNF.gapsB_succ M (Qof P) L E m
  have hlo : d₄.nreg 44020 = lo := by ram_rw [G₄ 44020, I.rlo]
  have hhd : d₄.nreg 44021 = hd := by ram_rw [G₄ 44021, I.rhd]
  have oth₄ : ∀ a, (a < CT ∨ (CT + 5 * K ≤ a ∧ a < ST) ∨ ST + N ≤ a) → d₄.nmem a = d.nmem a :=
    fun a ha => by rw [mm₄, oth₃ a ha]
  
  -- the new memory and arc count
  have M₆ : d₆.nreg 43102 = (gapsB M (Qof P) L E (m + 1)).length ∧
      (MemEqBelow AT d₆.nmem d₃.nmem) ∧ (∀ a, ST ≤ a → a < WT → d₆.nmem a = d₃.nmem a) ∧
      (∀ j, j < (gapsB M (Qof P) L E (m + 1)).length →
        (∀ f, f < 5 → d₆.nmem (AT + 5 * j + f) =
          af (arcRec M (Qof P) L E ((gapsB M (Qof P) L E (m + 1)).getD j 0)) f) ∧
        d₆.nmem (WT + j) =
          arcW M (Qof P) (arcRec M (Qof P) L E ((gapsB M (Qof P) L E (m + 1)).getD j 0))) := by
    by_cases hg : gapP M (Qof P) L E m = true
    · obtain ⟨p1, pz, pz1, pziff, p2⟩ := hgap (hgP.1 hg)
      rw [hsucc, ite_eq_left hg]
      have hlen : (gapsB M (Qof P) L E m ++ [m]).length = A + 1 := by simp [hAdef]
      rw [mm₆, p2, hlen]
      refine ⟨by simp [g₆, p1], fun a ha => ?_, fun a h1 h2 => ?_,
        fun j hj => ?_⟩
      · ram_rw [upd_other _ _, wr5_out _ _ _ _ _ _ _, mm₄]
      · ram_rw [upd_other _ _, wr5_out _ _ _ _ _ _ _, mm₄]
      · by_cases hjA : j < A
        · rw [List.getD_append _ _ _ _ (by assumption)]
          obtain ⟨o1, o2⟩ := I.arcs j hjA
          refine ⟨fun f hf => ?_, ?_⟩
          · ram_rw [upd_other _ _, wr5_out _ _ _ _ _ _ _,
              oth₄, o1 f hf]
          · ram_rw [upd_other _ _, wr5_out _ _ _ _ _ _ _,
              oth₄, o2]
        · have hjA' : j = A := by omega
          subst hjA'
          rw [List.getD_append_right _ _ _ _ (by rw [hAdef]), hAdef, Nat.sub_self]
          simp only [List.getD_cons_zero]
          refine ⟨fun f hf => ?_, ?_⟩
          · ram_rw [upd_other _ _, wr5_in _ _ _ _ _ _ _ _ hf, BuildNF.arcRec_eq,
              BuildNF.af_mk, e117]
          · rw [upd_same, hlo, hhd]
            have hmem : m ∈ BuildNF.gapStarts M (Qof P) L E := by
              rw [← BuildNF.gapsB_full]
              exact List.mem_filter.2 ⟨List.mem_range.2 hm, hg⟩
            have he := edge_lt F.inp.valid (c := E.getD ((m + 1) % E.length) 0)
              (ec (Nat.mod_lt _ (by omega)))
            rw [F.inp.arcW_eq hm hmem F.cnt F.cntW pziff pz1,
              wtF_eq_wtG (by omega) (fun h => ((F.cnt _ he).1 (pziff.1 h).1).1) pz1,
              Nat.add_sub_cancel_left]
    · have hng := fun h => hg (hgP.2 h)
      obtain ⟨p1, p2⟩ := hnogap hng
      rw [hsucc, ite_eq_right hg, List.append_nil]
      rw [mm₆, p2]
      refine ⟨by ram_rw [g₆, p1], fun a _ => by rw [mm₄],
        fun a _ _ => by rw [mm₄], fun j hj => ?_⟩
      obtain ⟨o1, o2⟩ := I.arcs j hj
      exact ⟨fun f hf => by ram_rw [oth₄, o1 f hf], by ram_rw [oth₄, o2]⟩
  obtain ⟨q1, q2, q3, q4⟩ := M₆
  refine ⟨d₆, _, X, by omega, by omega, x₆.wb_right, ?_⟩
  exact
    { m_le := by omega
      r100 := n100
      r103 := n103
      r104 := by ram_rw [G₆ 43104, I.r104]
      r101 := by
        ram_rw [g₆, g₅ _ (Bgap_false (by omega)),
          g₄, sp₃]
      sp_le := spl₃
      r102 := q1
      rD := by ram_rw [G₆ 40000, I.rD]
      rT := by ram_rw [G₆ 42000, I.rT]
      rN := by ram_rw [G₆ 42001, I.rN]
      r1a := by ram_rw [G₆ 42102, I.r1a]
      rB := by ram_rw [G₆ 43001, I.rB]
      r0 := by ram_rw [G₆ 43010, I.r0]
      r1 := by ram_rw [G₆ 43011, I.r1]
      rCT := by ram_rw [G₆ 44001, I.rCT]
      rAT := by ram_rw [G₆ 44002, I.rAT]
      rST := by ram_rw [G₆ 44006, I.rST]
      rWT := by ram_rw [G₆ 44007, I.rWT]
      rlo := by ram_rw [G₆ 44020, I.rlo]
      rhd := by ram_rw [G₆ 44021, I.rhd]
      r19 := by ram_rw [G₆ 41019, I.r19]
      r23 := by ram_rw [G₆ 41023, I.r23]
      low := fun a ha => by ram_rw [q2 a, oth₃ a, lowd a ha]
      stack := fun k hk => by ram_simp [q3, stk₃ k hk]
      chords := fun x' hx' hin f hf => by ram_simp [q2, ch₃ x' hx' hin f hf]
      arcs := q4
      frame := I.frame.trans (exec_frameM X wr_passBody) }

/-- **The main pass**: from `PassInv 0`, the loop reaches `PassInv (2K)`. -/
theorem passLoop_exec
    (I : PassInv F c₀ d 0) (hw : WordsBounded W d) :
    ∃ d' k, Exec P W passLoop d d' k ∧ k ≤ 11702 * E.length + 2 ∧ 12 * E.length ≤ k ∧
      WordsBounded W d' ∧ PassInv F c₀ d' E.length := by
  obtain ⟨d', k, e, ⟨hw', m', I', hm'⟩, htest, hk, hψ⟩ := Exec.whileLtN_growth (P := P)
    (W := W) (a := 43100) (b := 42001) (body := passBody)
    (fun d => WordsBounded W d ∧ ∃ m, PassInv F c₀ d m ∧ d.nreg 43100 = m)
    (fun d => 11702 * (E.length - d.nreg 43100)) (fun d => 12 * d.nreg 43100) (fun d hd => hd.1)
    (fun d ⟨hwd, m, Id, hmd⟩ htest => by
      rw [Id.rN, hmd] at htest
      obtain ⟨d', k, x, hk, hk', hw', I'⟩ := passBody_step F Id htest hwd
      refine ⟨d', k, x, ⟨hw', m + 1, I', I'.r100⟩, ?_, ?_⟩
      · rw [I'.r100, hmd]; omega
      · rw [I'.r100, hmd]; omega)
    ⟨hw, 0, I, I.r100⟩
  have hmN := I'.m_le
  rw [I'.rN, hm'] at htest
  have : m' = E.length := by omega
  subst this
  refine ⟨d', k, e, ?_, ?_, hw', I'⟩
  · rw [I.r100] at hk; omega
  · rw [I.r100, hm'] at hψ
    omega

end

end step

end

end BuildRam

end Chazelle.Core
