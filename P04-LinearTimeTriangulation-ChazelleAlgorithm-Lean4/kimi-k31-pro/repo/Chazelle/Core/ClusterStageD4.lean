module

public import Chazelle.Core.ClusterStageD3
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
set_option maxHeartbeats 4000000

/-!
# WP-I, part 56: stage D3 — the initial work stack

`stkS` scans the blocks `b < μ`; the block `b` occupies the positions
`[cntLt b, cntLt (b + 1))` (its end is `CNT[b]` after the placement), and is pushed on the stored
stack (with `pushOne 0`) when it has more than `s` items. The stack after the scan is `segL`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- The pushed blocks among the first `j`, the last one first. -/
noncomputable def segL (s μ : ℕ) (bo : ℕ → ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | j + 1 => optSeg s (cntLt bo μ j) (cntLt bo μ (j + 1)) ++ segL s μ bo j

theorem segL_length_le (s μ : ℕ) (bo : ℕ → ℕ) (j : ℕ) : (segL s μ bo j).length ≤ j := by
  induction j with
  | zero => simp [segL]
  | succ j ih =>
    simp [segL, List.length_append, optSeg]
    split_ifs <;> simp <;> omega

/-- One block of the stack scan. -/
def stkBody : Stmt := .seq (block [.addN 130872 130072 130870, .loadN 130671 130872,
  .copyN 130670 130871]) (.seq (pushOne 0) (block [.copyN 130871 130671,
  .addN 130870 130870 130001]))

/-- **The initial work stack.** -/
def stkS : Stmt := .seq (block [.constN 130870 0, .constN 130871 0, .constN 130701 0])
  (.whileLtN 130870 130011 stkBody)

/-- The registers of the stack scan. -/
def StkRG (r : ℕ) : Prop :=
  (130870 ≤ r ∧ r ≤ 130872) ∨ (130670 ≤ r ∧ r ≤ 130671) ∨ (130701 ≤ r ∧ r ≤ 130703)

section proofs

variable {P : Polygon} {W : ℕ}

theorem stkS_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c) {s : ℕ}
    {bo : ℕ → ℕ} (hs : c.nreg 130674 = s) (hS : c.nreg 130700 = g.base 46)
    (hcnt : ∀ b, b < g.μ → c.nmem (g.base 42 + b) = cntLt bo g.μ (b + 1)) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W stkS c c' k ∧ k ≤ 20 * g.μ + 5 ∧ WordsBounded W c' ∧
      PFr StkRG (fun a => g.base 46 ≤ a ∧ a < g.base 46 + 2 * g.μ) c c' ∧
      c'.nreg 130701 = 2 * (segL s g.μ bo g.μ).length ∧
      segL s g.μ bo g.μ = stkList c'.nmem (g.base 46) (segL s g.μ bo g.μ).length := by
  have hU := g.U_ge; have hE := g.END_eq; have b42 := g.base_eq 42; have b46 := g.base_eq 46
  set Am : ℕ → Prop := fun a => g.base 46 ≤ a ∧ a < g.base 46 + 2 * g.μ with hAm
  unfold stkS
  obtain ⟨c1, k1, e1, hk1, hw1, h70, h71, htp1, hf1⟩ : ∃ c1 k1, Exec P W
      (block [.constN 130870 0, .constN 130871 0, .constN 130701 0]) c c1 k1 ∧ k1 = 3 ∧
      WordsBounded W c1 ∧ c1.nreg 130870 = 0 ∧ c1.nreg 130871 = 0 ∧ c1.nreg 130701 = 0 ∧
      PFr StkRG Am c c1 := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ‹_›, by config_simp, by config_simp, by config_simp,
      ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩⟩
    simp; unfold StkRG at hr
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hG1 : GR g c1 := hG.frame (fun r hr => hf1.1 r (by unfold GRReg at hr; ufo StkRG))
  obtain ⟨c', k, e, hk', hw', hi', hn', h71', htp', hL', hf'⟩ := forN (P := P) (W := W)
    (ri := 130870) (rn := 130011) (body := stkBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130870 = j ∧ c'.nreg 130011 = g.μ ∧
      c'.nreg 130871 = cntLt bo g.μ j ∧ c'.nreg 130701 = 2 * (segL s g.μ bo j).length ∧
      segL s g.μ bo j = stkList c'.nmem (g.base 46) (segL s g.μ bo j).length ∧
      PFr StkRG Am c c')
    g.μ 18 (fun j c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c2 hj ⟨hw2, hi2, hn2, h712, htp2, hL2, hf2⟩ => by
      have hG2 : GR g c2 := hG.frame (fun r hr => hf2.1 r (by
        unfold GRReg at hr; ufo StkRG))
      have r72 := hG2.rbase 42 (by omega)
      have r1 := hG2.one
      have hlen := segL_length_le s g.μ bo j
      have mj : c2.nmem (g.base 42 + j) = cntLt bo g.μ (j + 1) := by
        rw [hf2.2.2.2.2 _ (by sio only [hAm])]; exact hcnt j hj
      have hle := cntLt_le bo g.μ (j + 1)
      obtain ⟨c3, k3, e3, hk3, hw3, h670, h671, htp3, h703, hf3, hm3, hrr3, hrm3, ho3⟩ : ∃ c3 k3, Exec P W
          (block [.addN 130872 130072 130870, .loadN 130671 130872, .copyN 130670 130871])
          c2 c3 k3 ∧ k3 = 3 ∧ WordsBounded W c3 ∧ c3.nreg 130670 = cntLt bo g.μ j ∧
          c3.nreg 130671 = cntLt bo g.μ (j + 1) ∧ c3.nreg 130701 = c2.nreg 130701 ∧
          c3.nreg 130870 = j ∧
          (∀ r, ¬ StkRG r → c3.nreg r = c2.nreg r) ∧ c3.nmem = c2.nmem ∧
          c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output := by
        exec_block
        · rwo [r72, hi2]
        · refine ⟨rfl, ‹_›, by config_simp; exact h712, by config_simp; rw [r72, hi2, mj],
            by config_simp, by config_simp; exact hi2, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
          simp; unfold StkRG at hr
          repeat (rw [Machine.upd_other _ _ _ (by omega)])
      obtain ⟨c4, k4, e4, hk4, hw4, hm4, htp4, hr4, hrr4, hrm4, ho4⟩ := pushOne_exec (P := P) hw3 0 (s := s) (bS := g.base 46)
        (tp := 2 * (segL s g.μ bo j).length)
        (by omega) (by rw [hf3 _ (by ufo StkRG), r1]) h670 h671
        (by rwx [hf3 _ (by ufo StkRG), hf2.1 _ (by ufo StkRG)])
        (by rwx [hf3 _ (by ufo StkRG), hf2.1 _ (by ufo StkRG)])
        (by rwx [htp3]) (by omega)
      have hpush : (c4.nmem, c4.nreg 130701) = pushF (g.base 46) s (cntLt bo g.μ j)
          (cntLt bo g.μ (j + 1)) (c3.nmem, 2 * (segL s g.μ bo j).length) := by
        rw [hm4, htp4]; unfold pushF; split_ifs <;> rfl
      obtain ⟨hL5, htp5, hout5⟩ := pushF_stk (bS := g.base 46) (s := s) (a := cntLt bo g.μ j)
        (b := cntLt bo g.μ (j + 1)) (q := (c3.nmem, 2 * (segL s g.μ bo j).length))
        (L := segL s g.μ bo j) (by rwx [hm3]) rfl
      rw [← hpush] at hL5 htp5 hout5
      have hlen' := segL_length_le s g.μ bo (j + 1)
      have r1' : c4.nreg 130001 = 1 := by
        rw [hr4 _ (by omega) (by omega) (by omega), hf3 _ (by ufo StkRG), r1]
      have h70' : c4.nreg 130870 = j := by
        rwx [hr4 _ (by omega) (by omega) (by omega)]
      have h671' : c4.nreg 130671 = cntLt bo g.μ (j + 1) := by
        rwx [hr4 _ (by omega) (by omega) (by omega)]
      obtain ⟨c6, k6, e6, hk6, hw6, h70'', h71'', hr6, hm6, hrr6, hrm6, ho6⟩ : ∃ c6 k6, Exec P W
          (block [.copyN 130871 130671, .addN 130870 130870 130001]) c4 c6 k6 ∧ k6 = 2 ∧
          WordsBounded W c6 ∧ c6.nreg 130870 = j + 1 ∧ c6.nreg 130871 = cntLt bo g.μ (j + 1) ∧
          (∀ r, r ≠ 130870 → r ≠ 130871 → c6.nreg r = c4.nreg r) ∧ c6.nmem = c4.nmem ∧
          c6.rreg = c4.rreg ∧ c6.rmem = c4.rmem ∧ c6.output = c4.output := by
        exec_block
        · config_simp; rwo [h70', r1']
        · refine ⟨rfl, ‹_›, by config_simp; rw [h70', r1'], by config_simp; exact h671',
            fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
          simp
          repeat (rw [Machine.upd_other _ _ _ (by omega)])
      have hseg : segL s g.μ bo (j + 1) = optSeg s (cntLt bo g.μ j) (cntLt bo g.μ (j + 1)) ++
          segL s g.μ bo j := rfl
      refine ⟨c6, k3 + (k4 + k6), .seq e3 (.seq e4 e6), by omega, hw6, h70'', ?_, h71'', ?_,
        ?_, ?_⟩
      · rw [hr6 _ (by omega) (by omega), hr4 _ (by omega) (by omega) (by omega),
          hf3 _ (by ufo StkRG)]; exact hn2
      · rwx [hr6 _ (by omega) (by omega), hseg]
      · rwx [hm6, hseg]
      · refine hf2.trans ⟨fun r hr => ?_, ?_, ?_, ?_, fun a ha => ?_⟩
        · unfold StkRG at hr
          rw [hr6 _ (by omega) (by omega), hr4 _ (by omega) (by omega) (by omega),
            hf3 _ (by ufo StkRG)]
        · rw [hrr6, hrr4, hrr3]
        · rw [hrm6, hrm4, hrm3]
        · rw [ho6, ho4, ho3]
        · rw [hm6]
          have := hout5 a (by
            simp [hAm] at ha
            rw [← hseg] at *
            omega)
          simp at this; rw [this, hm3])
    (j₀ := 0) ⟨hw1, h70, hG1.rμ, by rw [h71]; simp [cntLt], by rw [htp1]; simp [segL],
      by simp [segL, stkList], hf1⟩ (Nat.zero_le _)
  exact ⟨c', k1 + k, .seq e1 e, by omega, hw', hf', htp', hL'⟩

end proofs

end

end Chazelle.Core.Cluster
