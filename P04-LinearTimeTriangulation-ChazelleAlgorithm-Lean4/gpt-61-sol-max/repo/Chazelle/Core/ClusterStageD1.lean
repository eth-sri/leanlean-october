module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ClusterStageC3

/-!
# WP-I, part 52: stage D1 — the sizes of the blocks and their starts

* `bcS`: `CNT[b] = #{v < μ : v ∉ H, BLK[LEV[v]] = b}` (slot `42`, after a zero fill of `μ` cells);
* `pfxS`: the exclusive prefix sums in place: `CNT[b] = Σ_{b' < b} size b'`.

Registers `130850 … 130859`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- The registers of stage D. -/
def StDRG (r : ℕ) : Prop := (130150 ≤ r ∧ r ≤ 130154) ∨ (130800 ≤ r ∧ r ≤ 130805) ∨
  (130850 ≤ r ∧ r ≤ 130899)

/-- The block of a vertex, `μ` for the light levels. -/
def blkOf (μ : ℕ) (lev hl blk : ℕ → ℕ) (v : ℕ) : ℕ := if hl (lev v) = 1 then μ else blk (lev v)

/-- One vertex of the block count. -/
def bcBody : Stmt := .seq (block [.addN 130851 130033 130850, .loadN 130852 130851,
  .addN 130851 130066 130852, .loadN 130853 130851])
  (.seq (.ifLtN 130853 130001 (block [.addN 130851 130065 130852, .loadN 130854 130851,
    .addN 130851 130072 130854, .loadN 130855 130851, .addN 130855 130855 130001,
    .storeN 130851 130855]) .skip)
  (.instr (.addN 130850 130850 130001)))

/-- **The block sizes.** -/
def bcS : Stmt := .seq (fillWith 130072 130011 130009)
  (.seq (.instr (.constN 130850 0)) (.whileLtN 130850 130011 bcBody))

/-- The registers of the count step. -/
def BCRG (r : ℕ) : Prop := 130850 ≤ r ∧ r ≤ 130855

/-- The number of elements below `n` with value below `j`. -/
noncomputable def cntLt (f : ℕ → ℕ) (n j : ℕ) : ℕ := ((Finset.range n).filter (fun v => f v < j)).card

section
variable (f : ℕ → ℕ) (n j : ℕ)
theorem sum_cntBelow :
    ∑ i ∈ Finset.range j, cntBelow f n i = cntLt f n j := by
  induction j with
  | zero => simp [cntLt]
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    unfold cntLt cntBelow
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      grind
    simp_all [Finset.disjoint_left, Finset.mem_filter] <;> omega_nf

theorem cntLt_le : cntLt f n j ≤ n := by
  core_grind


end

/-- One block of the prefix sums. -/
def pfxBody : Stmt := block [.addN 130858 130072 130856, .loadN 130859 130858,
  .storeN 130858 130857, .addN 130857 130857 130859, .addN 130856 130856 130001]

/-- **The starts of the blocks** (exclusive prefix sums in place). -/
def pfxS : Stmt := .seq (block [.constN 130856 0, .constN 130857 0])
  (.whileLtN 130856 130011 pfxBody)

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 4000000 in
theorem bcS_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    {lev hl blk : ℕ → ℕ} (hlev : ∀ v, v < g.μ → c.nmem (g.base 3 + v) = lev v)
    (hlt : ∀ v, v < g.μ → lev v < g.μ) (hhl : ∀ l, l < g.μ → c.nmem (g.base 36 + l) = hl l)
    (hhl1 : ∀ l, l < g.μ → hl l ≤ 1) (hblk : ∀ l, l < g.μ → c.nmem (g.base 35 + l) = blk l)
    (hblt : ∀ l, l < g.μ → hl l ≠ 1 → blk l < g.μ) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W bcS c c' k ∧ k ≤ 20 * g.μ + 12 ∧ WordsBounded W c' ∧
      PFr StDRG (fun a => g.base 42 ≤ a ∧ a < g.base 42 + g.μ) c c' ∧
      ∀ b, b < g.μ → c'.nmem (g.base 42 + b) = cntBelow (blkOf g.μ lev hl blk) g.μ b := by
  have hU := g.U_ge; have hE := g.END_eq; have b3 := g.base_eq 3; have b35 := g.base_eq 35
  have b36 := g.base_eq 36; have b42 := g.base_eq 42
  unfold bcS
  obtain ⟨c1, k1, x1, hk1, hw1, hf1, hz1⟩ := fillWith_exec (P := P) hw hG.one
    (hG.rbase 42 (by omega)) hG.rμ hG.zero (by omega_nf) (by omega_nf)
    (by omega_nf) (by omega) (by omega)
  have e2 := Exec.constN (P := P) hw1 130850 0 (by omega)
  set c2 := { c1 with nreg := upd c1.nreg 130850 0 } with hc2
  have f2 : PFr StDRG (fun a => g.base 42 ≤ a ∧ a < g.base 42 + g.μ) c c2 :=
    (hf1.mono (fun r h => by grind [FillRG, StDRG]) (fun a h => h)).trans
      ⟨fun r hr => by ram_simp, rfl, rfl, rfl, fun a _ => rfl⟩
  have hG2 : GR g c2 := hG.frame (fun r hr => f2.1 r (by grind [GRReg, StDRG]))
  set Am : ℕ → Prop := fun a => g.base 42 ≤ a ∧ a < g.base 42 + g.μ with hAm
  obtain ⟨c', k, e, hk', hw', hi', hn', hf', hm'⟩ := forN (P := P) (W := W)
    (ri := 130850) (rn := 130011) (body := bcBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130850 = j ∧ c'.nreg 130011 = g.μ ∧
      PFr StDRG Am c c' ∧
      ∀ b, b < g.μ → c'.nmem (g.base 42 + b) = cntBelow (blkOf g.μ lev hl blk) j b)
    g.μ 13 (fun j c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c3 hj ⟨hw3, hi3, hn3, hf3, hm3⟩ => by
      have hG3 : GR g c3 := hG.frame (fun r hr => hf3.1 r (by
        unfold GRReg at hr; omega_nf))
      have r33 := hG3.rbase 3 (by omega); have r65 := hG3.rbase 35 (by omega)
      have r66 := hG3.rbase 36 (by omega); have r72 := hG3.rbase 42 (by omega)
      have r1 := hG3.one
      have hlj := hlt j hj
      have ml : c3.nmem (g.base 3 + j) = lev j := by rw [hf3.2.2.2.2 _ (by omega)]; grind
      have mh : c3.nmem (g.base 36 + lev j) = hl (lev j) := by
        rw [hf3.2.2.2.2 _ (by omega)]; grind
      have mb : c3.nmem (g.base 35 + lev j) = blk (lev j) := by
        rw [hf3.2.2.2.2 _ (by omega)]; grind
      have hcle : ∀ b, cntBelow (blkOf g.μ lev hl blk) j b ≤ j := fun b => cntBelow_le _ _ _
      obtain ⟨c4, k4, e4, hk4, hw4, hf4, h52, h53, h50, h4r⟩ : ∃ c4 k4, Exec P W
          (block [.addN 130851 130033 130850, .loadN 130852 130851,
            .addN 130851 130066 130852, .loadN 130853 130851]) c3 c4 k4 ∧ k4 = 4 ∧
          WordsBounded W c4 ∧ PFr BCRG (fun _ => False) c3 c4 ∧ c4.nreg 130852 = lev j ∧
          c4.nreg 130853 = hl (lev j) ∧ c4.nreg 130850 = j ∧
          (∀ r, ¬ BCRG r → c4.nreg r = c3.nreg r) := by
        exec_block
        · grind
        · config_simp; rw [r66, r33, hi3, ml]; omega
        · refine ⟨rfl, ‹_›, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩, ?_, ?_, ?_,
            fun r hr => ?_⟩
          · simp only; unfold BCRG at hr
            repeat ram_simp
          · config_simp; rw [r33, hi3, ml]
          · config_simp; rw [r66, r33, hi3, ml, mh]
          · ram_simp
          · simp only; unfold BCRG at hr
            repeat ram_simp
      have r1' : c4.nreg 130001 = 1 := by ram_simp
      obtain ⟨c5, k5, e5, hk5, hw5, hf5, hm5, h50'⟩ : ∃ c5 k5, Exec P W
          (.ifLtN 130853 130001 (block [.addN 130851 130065 130852, .loadN 130854 130851,
            .addN 130851 130072 130854, .loadN 130855 130851, .addN 130855 130855 130001,
            .storeN 130851 130855]) .skip) c4 c5 k5 ∧ k5 ≤ 7 ∧ WordsBounded W c5 ∧
          PFr BCRG Am c4 c5 ∧
          (∀ b, b < g.μ → c5.nmem (g.base 42 + b) = cntBelow (blkOf g.μ lev hl blk) (j + 1) b) ∧
          c5.nreg 130850 = j := by
        by_cases hp : c4.nreg 130853 < c4.nreg 130001
        · rw [h53, r1'] at hp
          have hh : hl (lev j) ≠ 1 := by omega
          have hbj : blk (lev j) < g.μ := hblt _ hlj hh
          have hbo : blkOf g.μ lev hl blk j = blk (lev j) := by grind [blkOf]
          have r65' : c4.nreg 130065 = g.base 35 := by ram_simp
          have r72' : c4.nreg 130072 = g.base 42 := by ram_simp
          have mb' : c4.nmem (g.base 35 + lev j) = blk (lev j) := by rw [hf4.2.2.2.2 _ id]; exact mb
          have mc : c4.nmem (g.base 42 + blk (lev j)) =
              cntBelow (blkOf g.μ lev hl blk) j (blk (lev j)) := by
            rw [hf4.2.2.2.2 _ id]; grind
          have hcl := hcle (blk (lev j))
          obtain ⟨c6, k6, e6, hk6, hw6, hf6, hm6, h50''⟩ : ∃ c6 k6, Exec P W
              (block [.addN 130851 130065 130852, .loadN 130854 130851,
                .addN 130851 130072 130854, .loadN 130855 130851, .addN 130855 130855 130001,
                .storeN 130851 130855]) c4 c6 k6 ∧ k6 = 6 ∧ WordsBounded W c6 ∧
              PFr BCRG Am c4 c6 ∧
              c6.nmem = upd c4.nmem (g.base 42 + blk (lev j))
                (cntBelow (blkOf g.μ lev hl blk) j (blk (lev j)) + 1) ∧
              c6.nreg 130850 = j := by
            exec_block
            · omega
            · config_simp; rw [r72', r65', h52, mb']; omega
            · config_simp; rw [r72', r65', h52, mb', mc, r1']; omega
            · refine ⟨rfl, ‹_›, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a ha => ?_⟩, ?_, ?_⟩
              · simp only; unfold BCRG at hr
                repeat (rw [Machine.upd_other _ _ _ (by omega)])
              · config_simp; rw [r72', r65', h52, mb', Machine.upd_other _ _ _ (by
                  omega)]
              · config_simp; rw [r72', r65', h52, mb', mc, r1']
              · ram_simp
          refine ⟨c6, k6 + 1, .ifLtN_true (by omega) e6, by omega, hw6, hf6,
            fun b hb => ?_, h50''⟩
          rw [hm6, Machine.upd_apply, cntBelow_succ, hbo]
          split_ifs with h1 h2 h2
          · grind
          · omega
          · omega
          · rw [hf4.2.2.2.2 _ id]; grind
        · rw [h53, r1'] at hp
          have hh : hl (lev j) = 1 := by grind
          have hbo : blkOf g.μ lev hl blk j = g.μ := by grind [blkOf]
          refine ⟨c4, 0 + 2, .ifLtN_false (by omega) (.skip hw4), by omega,
            hw4, PFr.refl c4, fun b hb => ?_, h50⟩
          rw [cntBelow_succ, hbo, ite_eq_right (by omega), Nat.add_zero, hf4.2.2.2.2 _ id]
          grind
      have e7 := Exec.addN (P := P) hw5 130850 130850 130001 (by
        rw [h50', hf5.1 _ (by omega_nf), r1']; omega)
      have hf7 : PFr BCRG Am c5
          { c5 with nreg := upd c5.nreg 130850 (c5.nreg 130850 + c5.nreg 130001) } :=
          ⟨fun r hr => by
            simp only [Machine.upd_other _ _ _ (show r ≠ 130850 by
              grind [BCRG])], rfl, rfl, rfl, fun a _ => rfl⟩
      refine ⟨_, k4 + (k5 + 1), .seq e4 (.seq e5 e7), by omega, e7.wb_right, ?_, ?_,
        hf3.trans (((hf4.mono (fun r h => h) (fun a h => h.elim)).trans (hf5.trans hf7)).mono
          (fun r h => by grind [BCRG, StDRG]) (fun a h => h)), hm5⟩
      · simp only [Machine.upd_same]
        rw [h50', hf5.1 _ (by omega_nf), r1']
      · simp only [Machine.upd_other _ _ _ (show (130011 : ℕ) ≠ 130850 by omega)]
        rw [hf5.1 _ (by omega_nf), hf4.1 _ (by omega_nf)]; exact hn3)
    (j₀ := 0) ⟨e2.wb_right, by simp [c2], hG2.rμ, f2, fun b hb => by
      grind [cntBelow]⟩ (Nat.zero_le _)
  exact ⟨c', k1 + (1 + k), .seq x1 (.seq e2 e), by omega, hw', hf', hm'⟩

theorem pfxS_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c) {f : ℕ → ℕ}
    (hcnt : ∀ b, b < g.μ → c.nmem (g.base 42 + b) = cntBelow f g.μ b) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W pfxS c c' k ∧ k ≤ 7 * g.μ + 4 ∧ WordsBounded W c' ∧
      PFr StDRG (fun a => g.base 42 ≤ a ∧ a < g.base 42 + g.μ) c c' ∧
      ∀ b, b < g.μ → c'.nmem (g.base 42 + b) = cntLt f g.μ b := by
  have hU := g.U_ge; have hE := g.END_eq; have b42 := g.base_eq 42
  unfold pfxS
  set Am : ℕ → Prop := fun a => g.base 42 ≤ a ∧ a < g.base 42 + g.μ with hAm
  obtain ⟨c1, k1, e1, hk1, hw1, h56, h57, hf1, hm1⟩ : ∃ c1 k1, Exec P W
      (block [.constN 130856 0, .constN 130857 0]) c c1 k1 ∧ k1 = 2 ∧ WordsBounded W c1 ∧
      c1.nreg 130856 = 0 ∧ c1.nreg 130857 = 0 ∧ PFr StDRG Am c c1 ∧ c1.nmem = c.nmem := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ‹_›, by config_simp, by config_simp, ⟨fun r hr => ?_, rfl, rfl, rfl,
      fun a _ => rfl⟩, rfl⟩
    simp only; unfold StDRG at hr
    repeat ram_simp
  have hG1 : GR g c1 := hG.frame (fun r hr => hf1.1 r (by grind [GRReg, StDRG]))
  obtain ⟨c', k, e, hk', hw', hi', hn', h57', hf', hm', -⟩ := forN (P := P) (W := W)
    (ri := 130856) (rn := 130011) (body := pfxBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130856 = j ∧ c'.nreg 130011 = g.μ ∧
      c'.nreg 130857 = cntLt f g.μ j ∧ PFr StDRG Am c c' ∧
      (∀ b, b < j → c'.nmem (g.base 42 + b) = cntLt f g.μ b) ∧
      (∀ b, j ≤ b → b < g.μ → c'.nmem (g.base 42 + b) = cntBelow f g.μ b))
    g.μ 5 (fun j c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c2 hj ⟨hw2, hi2, hn2, ha2, hf2, hlo2, hhi2⟩ => by
      have hG2 : GR g c2 := hG.frame (fun r hr => hf2.1 r (by
        grind [GRReg, StDRG]))
      have r72 := hG2.rbase 42 (by omega)
      have r1 := hG2.one
      have mj := hhi2 j le_rfl hj
      have hsum : cntLt f g.μ (j + 1) = cntLt f g.μ j + cntBelow f g.μ j := by
        rw [← sum_cntBelow, ← sum_cntBelow, Finset.sum_range_succ]
      have hle := cntLt_le f g.μ (j + 1)
      unfold pfxBody
      exec_block
      · grind
      · config_simp; grind
      · omega_nf
      · refine ⟨le_refl _, ‹_›, by ram_simp, by ram_simp,
          by config_simp; grind, hf2.trans ⟨fun r hr => ?_, rfl, rfl, rfl,
          fun a ha => ?_⟩, fun b hb => ?_, fun b hb1 hb2 => ?_⟩
        · simp only; simp only [StDRG] at hr
          repeat ram_simp
        · ram_simp
        all_goals (grind [Machine.upd_apply]))
    (j₀ := 0) ⟨hw1, h56, hG1.rμ, by simp_all [cntLt] , hf1, fun b hb => by omega,
      fun b _ hb => by omega_nf⟩
    (Nat.zero_le _)
  exact ⟨c', k1 + k, .seq e1 e, by omega, hw', hf', hm'⟩

end proofs

end

end Chazelle.Core.Cluster
