module

public meta import Chazelle.Arithmetic

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
  grind [wr5]

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
  ram_grind

end exec

theorem wr_passBody : wrM Bpass passBody = true := by
  have h1 : wrM Bpass curS = true := wrM_of_wr (wr_mono (fun r hr => by
    aesop) wr_curS)
  have h2 : ∀ dst, (dst = 43115 ∨ dst = 43117) → wrM Bpass (topS dst) = true := fun dst hd =>
    wrM_of_wr (wr_mono (fun r hr => by
      aesop) (wr_topS dst))
  have h3 : wrM Bpass stepS = true := wrM_mono (fun r hr => by grind [Bpass]) wr_stepS
  have h4 : wrM Bpass gapS = true := wrM_mono (fun r hr => by grind [Bpass]) wr_gapS
  simp only [passBody, wrM, block, h1, h2 43115 (Or.inl rfl), h2 43117 (Or.inr rfl), h3, h4,
    Bool.and_true, Bool.true_and]
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
  core_grind

section step

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **One iteration of the main pass.** -/
theorem passBody_step {M : Model} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
    {D H T SE B CT AT ST WT lo hd : ℕ} {mB : ℕ → ℕ}
    (F : PassFix P W M L E D H T SE B CT AT ST WT lo hd mB) {c₀ d : Config} {m : ℕ}
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
  have lowd : ∀ a, a < H → d.nmem a = mB a := I.low
  -- 1. the current code
  obtain ⟨d₁, k₁, x₁, hk₁, v10, v11, v12, v13, v14, f₁⟩ := curS_exec (P := P) d hw (c := c)
    (T := T) (by rw [I.r103, lowd _ (by omega), F.codes m hm]) I.rT I.r1a I.r1 (by omega)
    (by grind)
  rw [lowd _ (by omega), re] at v10
  rw [lowd _ (by omega), rh] at v11
  rw [lowd _ (by omega), rpar] at v12
  rw [lowd _ (by omega), rch] at v13 v14
  have w₁ := x₁.wb_right
  have g₁ : ∀ r, Bpass r = false → d₁.nreg r = d.nreg r := fun r hr => f₁.1 r (by
    grind [Bpass, Bool.or_eq_false_iff, decide_eq_false_iff_not])
  have mm₁ : d₁.nmem = d.nmem := f₁.2.2.1
  have s₁ : d₁.nreg 43101 = d.nreg 43101 := f₁.1 _ (by decide)
  -- 2. the label before
  obtain ⟨d₂, k₂, x₂, hk₂, v15, f₂⟩ := topS_exec (P := P) d₁ w₁ (dst := 43115)
    (by rw [g₁ 43010 (Bpass_false (by omega)), I.r0])
    (by rw [g₁ 43011 (Bpass_false (by omega)), I.r1])
    (by rw [g₁ 44006 (Bpass_false (by omega)), s₁, I.rST, I.r101]; have := I.sp_le; omega)
  rw [g₁ 44006 (Bpass_false (by omega)), s₁, mm₁, I.top] at v15
  have w₂ := x₂.wb_right
  have g₂ : ∀ r, r ≠ 43115 → r ≠ 43116 → d₂.nreg r = d₁.nreg r := fun r a1 a2 => f₂.1 r (by
    grind)
  have mm₂ : d₂.nmem = d.nmem := by rw [f₂.2.2.1, mm₁]
  -- 3. the stack step
  have x13 : d₂.nreg 43113 = x := by grind
  have x14 : d₂.nreg 43114 = x + 1 := by grind
  have x12 : d₂.nreg 42112 = c % 2 := by grind
  have b₂ : d₂.nreg 43001 = B := by
    rw [g₂ _ (by norm_num) (by norm_num), g₁ 43001 (Bpass_false (by omega)), I.rB]
  have ct₂ : d₂.nreg 44001 = CT := by
    rw [g₂ _ (by norm_num) (by norm_num), g₁ 44001 (Bpass_false (by omega)), I.rCT]
  have st₂ : d₂.nreg 44006 = ST := by
    rw [g₂ _ (by norm_num) (by norm_num), g₁ 44006 (Bpass_false (by omega)), I.rST]
  have o₂ : d₂.nreg 43011 = 1 := by
    rw [g₂ _ (by norm_num) (by norm_num), g₁ 43011 (Bpass_false (by omega)), I.r1]
  have sp₂ : d₂.nreg 43101 = (stk E m).length := by
    rw [g₂ _ (by norm_num) (by norm_num), s₁, I.r101]
  have hsp := I.sp_le
  obtain ⟨d₃, k₃, x₃, hk₃, f₃, hpop, hpush⟩ := stepS_exec (P := P) d₂ w₂ (x := x) (B := B)
    (CT := CT) (ST := ST) x13 b₂ ct₂ st₂ o₂ (by omega) (by omega) (by omega)
    (by omega)
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
      refine ⟨by omega, by omega, fun k hk => ?_, fun a _ => by rw [p2, mm₂],
        fun x' hx' hin' f hf => ?_⟩
      · rw [p2, mm₂, I.stack k (by omega), e1, getD_dropLast (by grind)]
      · rw [p2, mm₂]
        rw [htake, List.mem_append, List.mem_singleton] at hin'
        rcases hin' with h' | h'
        · exact I.chords x' hx' h' f hf
        · subst h'; exact I.chords _ hx' hin f hf
    · -- push
      obtain ⟨p1, p2⟩ := hpush (fun h => hin (hpopiff.1 h))
      have hh : ¬ (BuildStack.run ((cw E).take m)).head? = some (E.getD m 0 / 2) := fun h' =>
        hin ((F.inp.pop_iff hm).1 ((BuildNF.topR_eq_succ_iff E m x).2 h'))
      have e1 := BuildNF.stk_push hm hh
      have hlen : (stk E (m + 1)).length = (stk E m).length + 1 := by grind
      unfold pushMem at p2
      rw [sp₂, x14, x12, v15] at p2
      refine ⟨by omega, by omega, fun k hk => ?_, fun a ha => ?_,
        fun x' hx' hin' f hf => ?_⟩
      · rw [p2]
        by_cases hk' : k = (stk E m).length
        · subst hk'
          rw [upd_same, e1, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]; rfl
        · rw [upd_other _ _ _ (by omega), wr5_out _ _ _ _ _ _ _ _ (by omega), mm₂,
            I.stack k (by omega), e1, List.getD_append _ _ _ _ (by omega)]
      · rw [p2, upd_other _ _ _ (by omega), wr5_out _ _ _ _ _ _ _ _ (by omega), mm₂]
      · rw [p2, upd_other _ _ _ (by omega)]
        rw [htake, List.mem_append, List.mem_singleton] at hin'
        rcases hin' with h' | h'
        · have hne : x' ≠ x := fun h'' => hin (h'' ▸ h')
          rw [wr5_out _ _ _ _ _ _ _ _ (by omega), mm₂]
          exact I.chords x' hx' h' f hf
        · subst h'
          rw [wr5_in _ _ _ _ _ _ _ _ hf, F.inp.chordRec_new hm hxK hin, BuildNF.cf_mk, mm₂]
          obtain ⟨l1, l2, l3⟩ := F.chl x hxK
          grind
  obtain ⟨sp₃, spl₃, stk₃, oth₃, ch₃⟩ := S₃
  have g₃ : ∀ r, (r < 43101 ∨ (43101 < r ∧ r < 43116) ∨ (43116 < r ∧ r < 43130) ∨ 43134 < r) →
      d₃.nreg r = d₂.nreg r := fun r hr => f₃.1 r (by
    simp only [Bstep, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  -- 4. the label after
  have G₂ : ∀ r, (r < 42110 ∨ (42112 < r ∧ r < 43110) ∨ (43111 < r ∧ r < 43113) ∨
      (43114 < r ∧ r < 43115) ∨ 43116 < r) → d₂.nreg r = d.nreg r := fun r hr => by
    rw [g₂ r (by omega) (by omega)]
    exact f₁.1 r (by simp only [decide_eq_false_iff_not]; omega)
  obtain ⟨d₄, k₄, x₄, hk₄, v17, f₄⟩ := topS_exec (P := P) d₃ w₃ (dst := 43117)
    (by rw [g₃ 43010 (by omega), G₂ 43010 (by omega), I.r0])
    (by grind)
    (by rw [g₃ 44006 (by omega), st₂, sp₃]; omega)
  have top₃ : (if d₃.nreg 43101 = 0 then 0 else d₃.nmem (d₃.nreg 44006 + d₃.nreg 43101 - 1)) =
      topR E (m + 1) := by
    rw [BuildNF.topR_eq, sp₃, g₃ 44006 (by omega), st₂]
    split_ifs with h
    · rfl
    · rw [show ST + (stk E (m + 1)).length - 1 = ST + ((stk E (m + 1)).length - 1) by omega]
      exact stk₃ _ (by omega)
  rw [top₃] at v17
  have w₄ := x₄.wb_right
  have g₄ : ∀ r, r ≠ 43117 → r ≠ 43116 → d₄.nreg r = d₃.nreg r := fun r a1 a2 => f₄.1 r (by
    grind)
  have mm₄ : d₄.nmem = d₃.nmem := f₄.2.2.1
  have G₄ : ∀ r, (r < 42110 ∨ (42112 < r ∧ r < 43101) ∨ (43101 < r ∧ r < 43110) ∨
      (43111 < r ∧ r < 43113) ∨ (43117 < r ∧ r < 43130) ∨ 43134 < r) →
      d₄.nreg r = d.nreg r := fun r hr => by
    rw [g₄ r (by omega) (by omega), g₃ r (by omega), G₂ r (by omega)]
  -- 5. the gap
  have lowd₄ : ∀ a, a < H → d₄.nmem a = mB a := fun a ha => by
    rw [mm₄, oth₃ a (by omega), lowd a ha]
  obtain ⟨hM₄, hwf₄⟩ := desc_agree F.wf F.desc lowd₄
  have hA := I.r102
  have hAle := BuildNF.gapsB_length_le M (Qof P) L E m
  set A := (gapsB M (Qof P) L E m).length with hAdef
  have e110 : d₄.nreg 42110 = (wposOf L c).edge := by
    rw [g₄ _ (by norm_num) (by norm_num), g₃ _ (by omega), g₂ _ (by norm_num) (by norm_num), v10]
  have e111 : d₄.nreg 42111 = (wposOf L c).hgt := by
    rw [g₄ _ (by norm_num) (by norm_num), g₃ _ (by omega), g₂ _ (by norm_num) (by norm_num), v11]
  have e117 : d₄.nreg 43117 = topR E (m + 1) := v17
  have ec : ∀ {j}, j < E.length → E.getD j 0 < 2 * L.length := fun hj =>
    BuildNF.getD_lt_of_perm F.inp.perm hj
  obtain ⟨d₅, k₅, x₅, hk₅, f₅, hgap, hnogap⟩ := gapS_exec (P := P) F.good F.hwords d₄ w₄
    (M := M) (L := L) (E := E) (D := D) (H := H) (T := T) (SE := SE) (m := m) (A := A)
    (AT := AT) (WT := WT) F.inp.valid hN (fun j hj => ec hj) hm
    (by rw [G₄ 43100 (by omega), I.r100]) (by rw [G₄ 42001 (by omega), I.rN])
    (by rw [G₄ 43103 (by omega), I.r103]) (by rw [G₄ 43104 (by omega), I.r104])
    (fun j hj => by rw [lowd₄ _ (by omega), F.codes j hj])
    (by rw [G₄ 42000 (by omega), I.rT])
    (fun c' hc' => by
      obtain ⟨a1, a2, a3, a4⟩ := F.recs c' hc'
      exact ⟨by rw [lowd₄ _ (by omega), a1], by rw [lowd₄ _ (by omega), a2],
        by rw [lowd₄ _ (by omega), a3], by rw [lowd₄ _ (by omega), a4]⟩)
    (by rw [G₄ 42102 (by omega), I.r1a]) e110 e111
    (by rw [G₄ 40000 (by omega), I.rD]) hwf₄ hM₄ hHW
    (by rw [G₄ 41023 (by omega), I.r23, lowd₄ _ (by have := F.wf.1; omega)])
    (by rw [G₄ 41019 (by omega), I.r19]) (by rw [G₄ 43102 (by omega), hA])
    (by rw [G₄ 44002 (by omega), I.rAT]) (by rw [G₄ 44007 (by omega), I.rWT])
    (by rw [G₄ 43011 (by omega), I.r1]) (by omega) (by omega) (by omega) (by omega) hTH
    (by omega)
    (by rw [G₄ 44020 (by omega), G₄ 44021 (by omega), I.rlo, I.rhd]; exact F.cnt)
  have w₅ := x₅.wb_right
  have g₅ : ∀ r, Bgap r = false → d₅.nreg r = d₄.nreg r := f₅.1
  -- 6. the next position
  have a100 : d₅.nreg 43100 = m := by
    rw [g₅ _ (Bgap_false (by omega)), G₄ 43100 (by omega), I.r100]
  have a103 : d₅.nreg 43103 = SE + m := by
    rw [g₅ _ (Bgap_false (by omega)), G₄ 43103 (by omega), I.r103]
  have a011 : d₅.nreg 43011 = 1 := by
    rw [g₅ _ (Bgap_false (by omega)), G₄ 43011 (by omega), I.r1]
  obtain ⟨d₆, k₆, x₆, hk₆, n100, n103, g₆, mm₆⟩ : ∃ d₆ k₆, Exec P W
      (block [.addN 43100 43100 43011, .addN 43103 43103 43011]) d₅ d₆ k₆ ∧ k₆ = 2 ∧
      d₆.nreg 43100 = m + 1 ∧ d₆.nreg 43103 = SE + (m + 1) ∧
      (∀ r, r ≠ 43100 → r ≠ 43103 → d₆.nreg r = d₅.nreg r) ∧ d₆.nmem = d₅.nmem := by
    exec_block
    · omega
    · config_simp; omega
    · refine ⟨rfl, ?_, ?_, fun r r1 r2 => ?_, rfl⟩ <;> config_simp
      · omega
      · omega
      · simp (disch := omega) only [upd_other]
  have X : Exec P W passBody d d₆ (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k₆))))) :=
    .seq x₁ (.seq x₂ (.seq x₃ (.seq x₄ (.seq x₅ x₆))))
  have G₆ : ∀ r, (r < 10000 ∨ (10503 ≤ r ∧ r ≤ 40000) ∨ (40103 ≤ r ∧ r < 41110) ∨
      (41120 ≤ r ∧ r < 42110) ∨ (42117 < r ∧ r < 43100) ∨ (43104 ≤ r ∧ r < 43106) ∨
      (43106 < r ∧ r < 43110) ∨ (43117 < r ∧ r < 43120) ∨ (43128 ≤ r ∧ r < 43130) ∨
      (43135 ≤ r ∧ r < 43140) ∨ (43142 < r ∧ r < 43150) ∨ 43151 < r) →
      d₆.nreg r = d.nreg r := fun r hr => by
    rw [g₆ r (by omega) (by omega), g₅ r (Bgap_false (by omega)), G₄ r (by omega)]
  have hgP := F.inp.gapP_iff hm
  have hsucc := BuildNF.gapsB_succ M (Qof P) L E m
  have hlo : d₄.nreg 44020 = lo := by rw [G₄ 44020 (by omega), I.rlo]
  have hhd : d₄.nreg 44021 = hd := by rw [G₄ 44021 (by omega), I.rhd]
  have oth₄ : ∀ a, (a < CT ∨ (CT + 5 * K ≤ a ∧ a < ST) ∨ ST + N ≤ a) → d₄.nmem a = d.nmem a :=
    fun a ha => by rw [mm₄, oth₃ a ha]
  
  -- the new memory and arc count
  have M₆ : d₆.nreg 43102 = (gapsB M (Qof P) L E (m + 1)).length ∧
      (∀ a, a < AT → d₆.nmem a = d₃.nmem a) ∧ (∀ a, ST ≤ a → a < WT → d₆.nmem a = d₃.nmem a) ∧
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
      refine ⟨by rw [g₆ _ (by norm_num) (by norm_num), p1], fun a ha => ?_, fun a h1 h2 => ?_,
        fun j hj => ?_⟩
      · rw [upd_other _ _ _ (by omega), wr5_out _ _ _ _ _ _ _ _ (by omega), mm₄]
      · rw [upd_other _ _ _ (by omega), wr5_out _ _ _ _ _ _ _ _ (by omega), mm₄]
      · by_cases hjA : j < A
        · rw [List.getD_append _ _ _ _ (by omega)]
          obtain ⟨o1, o2⟩ := I.arcs j hjA
          refine ⟨fun f hf => ?_, ?_⟩
          · rw [upd_other _ _ _ (by omega), wr5_out _ _ _ _ _ _ _ _ (by omega),
              oth₄ _ (by omega), o1 f hf]
          · rw [upd_other _ _ _ (by omega), wr5_out _ _ _ _ _ _ _ _ (by omega),
              oth₄ _ (by omega), o2]
        · have hjA' : j = A := by omega
          subst hjA'
          rw [List.getD_append_right _ _ _ _ (by rw [hAdef]), hAdef, Nat.sub_self]
          simp only [List.getD_cons_zero]
          refine ⟨fun f hf => ?_, ?_⟩
          · rw [upd_other _ _ _ (by omega), wr5_in _ _ _ _ _ _ _ _ hf, BuildNF.arcRec_eq,
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
    · have hng : ¬ (m + 1 = E.length ∨ M.key (Qof P) (wposOf L (E.getD m 0)) <
          M.key (Qof P) (wposOf L (E.getD ((m + 1) % E.length) 0))) := fun h => hg (hgP.2 h)
      obtain ⟨p1, p2⟩ := hnogap hng
      rw [hsucc, ite_eq_right hg, List.append_nil]
      rw [mm₆, p2]
      refine ⟨by rw [g₆ _ (by norm_num) (by norm_num), p1], fun a _ => by rw [mm₄],
        fun a _ _ => by rw [mm₄], fun j hj => ?_⟩
      obtain ⟨o1, o2⟩ := I.arcs j hj
      exact ⟨fun f hf => by rw [oth₄ _ (by omega), o1 f hf], by rw [oth₄ _ (by omega), o2]⟩
  obtain ⟨q1, q2, q3, q4⟩ := M₆
  refine ⟨d₆, _, X, by omega, by omega, x₆.wb_right, ?_⟩
  exact
    { m_le := by omega
      r100 := n100
      r103 := n103
      r104 := by rw [G₆ 43104 (by omega), I.r104]
      r101 := by
        rw [g₆ _ (by norm_num) (by norm_num), g₅ _ (Bgap_false (by omega)),
          g₄ _ (by norm_num) (by norm_num), sp₃]
      sp_le := spl₃
      r102 := q1
      rD := by rw [G₆ 40000 (by omega), I.rD]
      rT := by rw [G₆ 42000 (by omega), I.rT]
      rN := by rw [G₆ 42001 (by omega), I.rN]
      r1a := by rw [G₆ 42102 (by omega), I.r1a]
      rB := by rw [G₆ 43001 (by omega), I.rB]
      r0 := by rw [G₆ 43010 (by omega), I.r0]
      r1 := by rw [G₆ 43011 (by omega), I.r1]
      rCT := by rw [G₆ 44001 (by omega), I.rCT]
      rAT := by rw [G₆ 44002 (by omega), I.rAT]
      rST := by rw [G₆ 44006 (by omega), I.rST]
      rWT := by rw [G₆ 44007 (by omega), I.rWT]
      rlo := by rw [G₆ 44020 (by omega), I.rlo]
      rhd := by rw [G₆ 44021 (by omega), I.rhd]
      r19 := by rw [G₆ 41019 (by omega), I.r19]
      r23 := by rw [G₆ 41023 (by omega), I.r23]
      low := fun a ha => by rw [q2 a (by omega), oth₃ a (by omega), lowd a ha]
      stack := fun k hk => by rw [q3 _ (by omega) (by omega), stk₃ k hk]
      chords := fun x' hx' hin f hf => by rw [q2 _ (by omega), ch₃ x' hx' hin f hf]
      arcs := q4
      frame := I.frame.trans (exec_frameM X wr_passBody) }

/-- **The main pass**: from `PassInv 0`, the loop reaches `PassInv (2K)`. -/
theorem passLoop_exec {M : Model} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
    {D H T SE B CT AT ST WT lo hd : ℕ} {mB : ℕ → ℕ}
    (F : PassFix P W M L E D H T SE B CT AT ST WT lo hd mB) {c₀ d : Config}
    (I : PassInv F c₀ d 0) (hw : WordsBounded W d) :
    ∃ d' k, Exec P W passLoop d d' k ∧ k ≤ 11702 * E.length + 2 ∧ 12 * E.length ≤ k ∧
      WordsBounded W d' ∧ PassInv F c₀ d' E.length := by
  obtain ⟨d', k, e, ⟨hw', m', I', hm'⟩, htest, hk, hψ⟩ := SortR.whileLtN_potential_lb (P := P)
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
  · omega
  · rw [I.r100, hm'] at hψ
    omega

end step

end

end BuildRam

end Chazelle.Core
